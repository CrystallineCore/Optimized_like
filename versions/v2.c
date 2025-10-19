/*
 * optimized_like_roaring.c
 * PostgreSQL extension with unified Roaring Bitmap optimization
 * 
 * ALGORITHM OVERVIEW:
 * Maintains two indices (forward and backward) spanning n records:
 * - Forward index: char[pos] -> bitmap of records with char at position pos
 * - Backward index: char[-pos] -> bitmap of records with char at position -pos from end
 * - Character cache: char -> bitmap of records containing char anywhere
 * 
 * PATTERN HANDLING STRATEGIES:
 * 1. a_b%    -> intersect a[0] ∩ b[2] (anchored prefix)
 * 2. a%c_d   -> intersect a[0] ∩ c[-3] ∩ d[-1] (dual anchor)
 * 3. a__c_d  -> intersect a[0] ∩ c[3] ∩ d[5] (fixed positions)
 * 4. %a_b    -> intersect a[-3] ∩ b[-1] (anchored suffix)
 * 5. %a%_b   -> intersect b[-1] ∩ (⋃ a[i] for valid i) (suffix + contains)
 * 6. %a_b%   -> ⋃(a[i] ∩ b[i+2]) for all valid i (sliding window)
 * 7. %a%b%c% -> ⋃(a[i] ∩ b[j] ∩ c[k]) where 0≤i<j<k≤n (complex pattern)
 * 
 * OPTIMIZATION: Intelligently choose between forward/backward scanning
 * based on pattern structure to minimize bitmap operations.
 */

#include "postgres.h"
#include "fmgr.h"
#include "utils/builtins.h"
#include "utils/memutils.h"
#include "access/htup_details.h"
#include "catalog/pg_type.h"
#include "funcapi.h"
#include "executor/spi.h"
#include "lib/stringinfo.h"
#include "utils/timestamp.h"
#include <string.h>
#include <ctype.h>

#ifdef HAVE_ROARING
#include "roaring.h"
#else
typedef void roaring_bitmap_t;
#endif

#ifdef PG_MODULE_MAGIC
PG_MODULE_MAGIC;
#endif

/* ==================== ROARING BITMAP WRAPPER ==================== */

#ifdef HAVE_ROARING

typedef roaring_bitmap_t RoaringBitmap;

static RoaringBitmap* roaring_create(void) {
    return roaring_bitmap_create();
}

static void roaring_add(RoaringBitmap *rb, uint32_t value) {
    roaring_bitmap_add(rb, value);
}

static RoaringBitmap* roaring_and(const RoaringBitmap *a, const RoaringBitmap *b) {
    return roaring_bitmap_and(a, b);
}

static RoaringBitmap* roaring_or(const RoaringBitmap *a, const RoaringBitmap *b) {
    return roaring_bitmap_or(a, b);
}

static uint64_t roaring_count(const RoaringBitmap *rb) {
    return roaring_bitmap_get_cardinality(rb);
}

static bool roaring_is_empty(const RoaringBitmap *rb) {
    return roaring_bitmap_get_cardinality(rb) == 0;
}

static uint32_t* roaring_to_array(const RoaringBitmap *rb, uint64_t *count) {
    *count = roaring_bitmap_get_cardinality(rb);
    if (*count == 0) return NULL;
    uint32_t *array = (uint32_t *)palloc(*count * sizeof(uint32_t));
    roaring_bitmap_to_uint32_array(rb, array);
    return array;
}

static void roaring_free(RoaringBitmap *rb) {
    if (rb) roaring_bitmap_free(rb);
}

static RoaringBitmap* roaring_copy(const RoaringBitmap *rb) {
    return roaring_bitmap_copy(rb);
}

#else

/* Fallback bitmap implementation */
typedef struct {
    uint64_t *blocks;
    int num_blocks;
    int capacity;
} RoaringBitmap;

static RoaringBitmap* roaring_create(void) {
    RoaringBitmap *rb = (RoaringBitmap *)palloc(sizeof(RoaringBitmap));
    rb->num_blocks = 0;
    rb->capacity = 16;
    rb->blocks = (uint64_t *)palloc0(rb->capacity * sizeof(uint64_t));
    return rb;
}

static void roaring_add(RoaringBitmap *rb, uint32_t value) {
    int block = value >> 6;
    int bit = value & 63;
    
    if (block >= rb->capacity) {
        int new_cap = block + 1;
        rb->blocks = (uint64_t *)repalloc(rb->blocks, new_cap * sizeof(uint64_t));
        for (int i = rb->capacity; i < new_cap; i++)
            rb->blocks[i] = 0;
        rb->capacity = new_cap;
    }
    if (block >= rb->num_blocks)
        rb->num_blocks = block + 1;
    rb->blocks[block] |= (1ULL << bit);
}

static RoaringBitmap* roaring_and(const RoaringBitmap *a, const RoaringBitmap *b) {
    RoaringBitmap *result = roaring_create();
    int min_blocks = (a->num_blocks < b->num_blocks) ? a->num_blocks : b->num_blocks;
    
    if (min_blocks == 0) return result;
    
    if (result->capacity < min_blocks) {
        result->blocks = (uint64_t *)repalloc(result->blocks, min_blocks * sizeof(uint64_t));
        result->capacity = min_blocks;
    }
    result->num_blocks = min_blocks;
    
    for (int i = 0; i < min_blocks; i++)
        result->blocks[i] = a->blocks[i] & b->blocks[i];
    
    return result;
}

static RoaringBitmap* roaring_or(const RoaringBitmap *a, const RoaringBitmap *b) {
    RoaringBitmap *result = roaring_create();
    int max_blocks = (a->num_blocks > b->num_blocks) ? a->num_blocks : b->num_blocks;
    int min_blocks = (a->num_blocks < b->num_blocks) ? a->num_blocks : b->num_blocks;
    
    if (max_blocks == 0) return result;
    
    if (result->capacity < max_blocks) {
        result->blocks = (uint64_t *)repalloc(result->blocks, max_blocks * sizeof(uint64_t));
        result->capacity = max_blocks;
    }
    result->num_blocks = max_blocks;
    
    for (int i = 0; i < min_blocks; i++)
        result->blocks[i] = a->blocks[i] | b->blocks[i];
    
    if (a->num_blocks > min_blocks)
        memcpy(result->blocks + min_blocks, a->blocks + min_blocks,
               (a->num_blocks - min_blocks) * sizeof(uint64_t));
    else if (b->num_blocks > min_blocks)
        memcpy(result->blocks + min_blocks, b->blocks + min_blocks,
               (b->num_blocks - min_blocks) * sizeof(uint64_t));
    
    return result;
}

static uint64_t roaring_count(const RoaringBitmap *rb) {
    uint64_t count = 0;
    for (int i = 0; i < rb->num_blocks; i++)
        count += __builtin_popcountll(rb->blocks[i]);
    return count;
}

static bool roaring_is_empty(const RoaringBitmap *rb) {
    for (int i = 0; i < rb->num_blocks; i++)
        if (rb->blocks[i]) return false;
    return true;
}

static uint32_t* roaring_to_array(const RoaringBitmap *rb, uint64_t *count) {
    *count = roaring_count(rb);
    if (*count == 0) return NULL;
    
    uint32_t *array = (uint32_t *)palloc(*count * sizeof(uint32_t));
    int idx = 0;
    
    for (int i = 0; i < rb->num_blocks; i++) {
        uint64_t bits = rb->blocks[i];
        if (!bits) continue;
        
        uint64_t base = (uint64_t)i << 6;
        while (bits) {
            array[idx++] = (uint32_t)(base + __builtin_ctzll(bits));
            bits &= bits - 1;
        }
    }
    return array;
}

static void roaring_free(RoaringBitmap *rb) {
    if (rb) {
        if (rb->blocks) pfree(rb->blocks);
        pfree(rb);
    }
}

static RoaringBitmap* roaring_copy(const RoaringBitmap *rb) {
    RoaringBitmap *copy = roaring_create();
    if (rb->num_blocks > 0) {
        copy->blocks = (uint64_t *)repalloc(copy->blocks, rb->num_blocks * sizeof(uint64_t));
        copy->num_blocks = rb->num_blocks;
        copy->capacity = rb->num_blocks;
        memcpy(copy->blocks, rb->blocks, rb->num_blocks * sizeof(uint64_t));
    }
    return copy;
}

#endif

/* ==================== INDEX STRUCTURES ==================== */

#define MAX_POSITIONS 512
#define CHAR_RANGE 256

typedef struct {
    int pos;
    RoaringBitmap *bitmap;
} PosEntry;

typedef struct {
    PosEntry *entries;
    int count;
    int capacity;
} CharIndex;

typedef struct {
    CharIndex pos_idx[CHAR_RANGE];      /* Forward: char[pos] -> bitmap */
    CharIndex neg_idx[CHAR_RANGE];      /* Backward: char[-pos] -> bitmap */
    RoaringBitmap *char_cache[CHAR_RANGE];  /* char-anywhere cache */
    
    char **data;
    int *lengths;                        /* Cached string lengths */
    int num_records;
    int max_len;
    size_t memory_used;
} RoaringIndex;

static RoaringIndex *global_index = NULL;
static MemoryContext index_context = NULL;

/* ==================== INDEX ACCESS HELPERS ==================== */

static RoaringBitmap* get_pos_bitmap(unsigned char ch, int pos) {
    CharIndex *cidx = &global_index->pos_idx[ch];
    for (int i = 0; i < cidx->count; i++)
        if (cidx->entries[i].pos == pos)
            return cidx->entries[i].bitmap;
    return NULL;
}

static RoaringBitmap* get_neg_bitmap(unsigned char ch, int neg_pos) {
    CharIndex *cidx = &global_index->neg_idx[ch];
    for (int i = 0; i < cidx->count; i++)
        if (cidx->entries[i].pos == neg_pos)
            return cidx->entries[i].bitmap;
    return NULL;
}

static void set_pos_bitmap(unsigned char ch, int pos, RoaringBitmap *bm) {
    CharIndex *cidx = &global_index->pos_idx[ch];
    
    for (int i = 0; i < cidx->count; i++) {
        if (cidx->entries[i].pos == pos) {
            cidx->entries[i].bitmap = bm;
            return;
        }
    }
    
    if (cidx->count >= cidx->capacity) {
        int new_cap = cidx->capacity * 2;
        PosEntry *new_entries = (PosEntry *)MemoryContextAlloc(index_context, new_cap * sizeof(PosEntry));
        if (cidx->count > 0)
            memcpy(new_entries, cidx->entries, cidx->count * sizeof(PosEntry));
        cidx->entries = new_entries;
        cidx->capacity = new_cap;
    }
    
    cidx->entries[cidx->count].pos = pos;
    cidx->entries[cidx->count].bitmap = bm;
    cidx->count++;
}

static void set_neg_bitmap(unsigned char ch, int neg_pos, RoaringBitmap *bm) {
    CharIndex *cidx = &global_index->neg_idx[ch];
    
    for (int i = 0; i < cidx->count; i++) {
        if (cidx->entries[i].pos == neg_pos) {
            cidx->entries[i].bitmap = bm;
            return;
        }
    }
    
    if (cidx->count >= cidx->capacity) {
        int new_cap = cidx->capacity * 2;
        PosEntry *new_entries = (PosEntry *)MemoryContextAlloc(index_context, new_cap * sizeof(PosEntry));
        if (cidx->count > 0)
            memcpy(new_entries, cidx->entries, cidx->count * sizeof(PosEntry));
        cidx->entries = new_entries;
        cidx->capacity = new_cap;
    }
    
    cidx->entries[cidx->count].pos = neg_pos;
    cidx->entries[cidx->count].bitmap = bm;
    cidx->count++;
}

/* ==================== PATTERN ANALYSIS ==================== */

typedef struct {
    char ch;
    int pos;          /* Positive for forward, negative for backward */
    bool is_wildcard; /* true for _ or % */
    bool is_percent;  /* true for % */
} PatternToken;

typedef struct {
    PatternToken *tokens;
    int count;
    int capacity;
    
    /* Pattern characteristics */
    bool has_leading_percent;
    bool has_trailing_percent;
    bool has_internal_percent;
    int fixed_prefix_len;    /* Length of fixed prefix (before first %) */
    int fixed_suffix_len;    /* Length of fixed suffix (after last %) */
    int total_fixed_chars;   /* Total non-wildcard characters */
} PatternInfo;

static void analyze_pattern(const char *pattern, PatternInfo *info) {
    int plen = strlen(pattern);
    
    info->tokens = (PatternToken *)palloc(plen * sizeof(PatternToken));
    info->count = 0;
    info->capacity = plen;
    info->has_leading_percent = (pattern[0] == '%');
    info->has_trailing_percent = (plen > 0 && pattern[plen-1] == '%');
    info->has_internal_percent = false;
    info->fixed_prefix_len = 0;
    info->fixed_suffix_len = 0;
    info->total_fixed_chars = 0;
    
    /* Find first and last % */
    int first_percent = -1, last_percent = -1;
    for (int i = 0; i < plen; i++) {
        if (pattern[i] == '%') {
            if (first_percent == -1) first_percent = i;
            last_percent = i;
        }
    }
    
    info->has_internal_percent = (first_percent != -1 && last_percent != -1 && 
                                  first_percent < last_percent && 
                                  first_percent > 0 && last_percent < plen - 1);
    
    /* Calculate fixed prefix length (before first %) */
    if (first_percent == -1) {
        info->fixed_prefix_len = plen;  /* No % at all */
    } else {
        info->fixed_prefix_len = first_percent;
    }
    
    /* Calculate fixed suffix length (after last %) */
    if (last_percent == -1) {
        info->fixed_suffix_len = plen;  /* No % at all */
    } else {
        info->fixed_suffix_len = plen - last_percent - 1;
    }
    
    /* Tokenize pattern */
    for (int i = 0; i < plen; i++) {
        PatternToken tok;
        tok.ch = pattern[i];
        tok.is_wildcard = (pattern[i] == '_' || pattern[i] == '%');
        tok.is_percent = (pattern[i] == '%');
        tok.pos = 0;  /* Will be set based on usage */
        
        info->tokens[info->count++] = tok;
        
        if (!tok.is_wildcard)
            info->total_fixed_chars++;
    }
}

/* ==================== UNIFIED QUERY ENGINE ==================== */

/*
 * Strategy 1: Fixed prefix with wildcards (a_b%, a__c_d)
 * Use forward index only
 */
static RoaringBitmap* query_fixed_prefix(const PatternInfo *info) {
    RoaringBitmap *result = roaring_create();
    
    /* Initialize with all records */
    for (int i = 0; i < global_index->num_records; i++)
        roaring_add(result, i);
    
    /* Intersect with each non-wildcard position */
    for (int i = 0; i < info->fixed_prefix_len; i++) {
        if (info->tokens[i].is_percent) break;  /* Should not happen in fixed prefix */
        if (info->tokens[i].is_wildcard) continue;  /* Skip _ */
        
        RoaringBitmap *char_bm = get_pos_bitmap((unsigned char)info->tokens[i].ch, i);
        if (!char_bm || roaring_is_empty(char_bm)) {
            roaring_free(result);
            return roaring_create();  /* Empty result */
        }
        
        RoaringBitmap *temp = roaring_and(result, char_bm);
        roaring_free(result);
        result = temp;
        
        if (roaring_is_empty(result))
            return result;  /* Early termination */
    }
    
    return result;
}

/*
 * Strategy 2: Fixed suffix with wildcards (%a_b, %a__b)
 * Use backward index only
 */
static RoaringBitmap* query_fixed_suffix(const PatternInfo *info) {
    RoaringBitmap *result = roaring_create();
    int plen = info->count;
    
    /* Initialize with all records */
    for (int i = 0; i < global_index->num_records; i++)
        roaring_add(result, i);
    
    /* Intersect with each non-wildcard position from the end */
    for (int i = 0; i < info->fixed_suffix_len; i++) {
        int tok_idx = plen - 1 - i;
        if (info->tokens[tok_idx].is_percent) break;
        if (info->tokens[tok_idx].is_wildcard) continue;  /* Skip _ */
        
        RoaringBitmap *char_bm = get_neg_bitmap((unsigned char)info->tokens[tok_idx].ch, -1 - i);
        if (!char_bm || roaring_is_empty(char_bm)) {
            roaring_free(result);
            return roaring_create();
        }
        
        RoaringBitmap *temp = roaring_and(result, char_bm);
        roaring_free(result);
        result = temp;
        
        if (roaring_is_empty(result))
            return result;
    }
    
    return result;
}

/*
 * Strategy 3: Dual anchor (a%b, a%c_d, a_b%c_d)
 * Use both forward and backward indices
 */
static RoaringBitmap* query_dual_anchor(const PatternInfo *info) {
    RoaringBitmap *result = roaring_create();
    int plen = info->count;
    
    /* Initialize with all records */
    for (int i = 0; i < global_index->num_records; i++)
        roaring_add(result, i);
    
    /* Apply prefix constraints (forward) */
    for (int i = 0; i < info->fixed_prefix_len; i++) {
        if (info->tokens[i].is_wildcard) continue;
        
        RoaringBitmap *char_bm = get_pos_bitmap((unsigned char)info->tokens[i].ch, i);
        if (!char_bm || roaring_is_empty(char_bm)) {
            roaring_free(result);
            return roaring_create();
        }
        
        RoaringBitmap *temp = roaring_and(result, char_bm);
        roaring_free(result);
        result = temp;
        
        if (roaring_is_empty(result))
            return result;
    }
    
    /* Apply suffix constraints (backward) */
    for (int i = 0; i < info->fixed_suffix_len; i++) {
        int tok_idx = plen - 1 - i;
        if (info->tokens[tok_idx].is_wildcard) continue;
        
        RoaringBitmap *char_bm = get_neg_bitmap((unsigned char)info->tokens[tok_idx].ch, -1 - i);
        if (!char_bm || roaring_is_empty(char_bm)) {
            roaring_free(result);
            return roaring_create();
        }
        
        RoaringBitmap *temp = roaring_and(result, char_bm);
        roaring_free(result);
        result = temp;
        
        if (roaring_is_empty(result))
            return result;
    }
    
    return result;
}

/*
 * Strategy 4: Sliding window (%a_b%, %abc%)
 * Union of intersections at all valid positions
 */
static RoaringBitmap* query_sliding_window(const PatternInfo *info) {
    RoaringBitmap *result = roaring_create();
    int pattern_len = info->count - 2;  /* Remove leading and trailing % */
    
    if (pattern_len <= 0) {
        /* Pattern is just %% - match all */
        for (int i = 0; i < global_index->num_records; i++)
            roaring_add(result, i);
        return result;
    }
    
    /* For each possible starting position */
    for (int start_pos = 0; start_pos <= global_index->max_len - pattern_len; start_pos++) {
        RoaringBitmap *window_match = roaring_create();
        
        /* Initialize with all records */
        for (int i = 0; i < global_index->num_records; i++)
            roaring_add(window_match, i);
        
        /* Check each character in the pattern */
        bool valid_window = true;
        for (int i = 0; i < pattern_len; i++) {
            PatternToken tok = info->tokens[i + 1];  /* Skip leading % */
            if (tok.is_wildcard) continue;
            
            int abs_pos = start_pos + i;
            RoaringBitmap *char_bm = get_pos_bitmap((unsigned char)tok.ch, abs_pos);
            
            if (!char_bm || roaring_is_empty(char_bm)) {
                valid_window = false;
                break;
            }
            
            RoaringBitmap *temp = roaring_and(window_match, char_bm);
            roaring_free(window_match);
            window_match = temp;
            
            if (roaring_is_empty(window_match)) {
                valid_window = false;
                break;
            }
        }
        
        if (valid_window && !roaring_is_empty(window_match)) {
            RoaringBitmap *temp = roaring_or(result, window_match);
            roaring_free(result);
            result = temp;
        }
        
        roaring_free(window_match);
    }
    
    return result;
}

/*
 * Strategy 5: Contains with anchor (%a%_b, %ab%c_d)
 * Intersect anchor constraints with union of character positions
 */
static RoaringBitmap* query_contains_anchor(const PatternInfo *info) {
    RoaringBitmap *result = roaring_create();
    
    /* Start with suffix anchor (most restrictive) */
    if (info->fixed_suffix_len > 0) {
        result = query_fixed_suffix(info);
        if (roaring_is_empty(result))
            return result;
    } else {
        /* Initialize with all records */
        for (int i = 0; i < global_index->num_records; i++)
            roaring_add(result, i);
    }
    
    /* Apply character-anywhere constraints for chars between %...% */
    int start = info->has_leading_percent ? info->fixed_prefix_len + 1 : info->fixed_prefix_len;
    int end = info->has_trailing_percent ? info->count - info->fixed_suffix_len - 1 : info->count - info->fixed_suffix_len;
    
    unsigned char seen[256] = {0};
    for (int i = start; i < end; i++) {
        if (info->tokens[i].is_wildcard) continue;
        
        unsigned char ch = (unsigned char)info->tokens[i].ch;
        if (seen[ch]) continue;  /* Already processed */
        seen[ch] = 1;
        
        RoaringBitmap *char_bm = global_index->char_cache[ch];
        if (!char_bm || roaring_is_empty(char_bm)) {
            roaring_free(result);
            return roaring_create();
        }
        
        RoaringBitmap *temp = roaring_and(result, char_bm);
        roaring_free(result);
        result = temp;
        
        if (roaring_is_empty(result))
            return result;
    }
    
    return result;
}

/*
 * Extract fixed character segments from pattern (between % wildcards)
 * For %a%b%c%, returns [(a,1), (b,3), (c,5)]
 */
typedef struct {
    char ch;
    int pattern_pos;  /* Position in original pattern */
} FixedChar;

typedef struct {
    FixedChar *chars;
    int count;
} FixedCharList;

static FixedCharList extract_fixed_chars(const PatternInfo *info) {
    FixedCharList list;
    list.chars = (FixedChar *)palloc(info->count * sizeof(FixedChar));
    list.count = 0;
    
    for (int i = 0; i < info->count; i++) {
        if (!info->tokens[i].is_wildcard) {
            FixedChar fc;
            fc.ch = info->tokens[i].ch;
            fc.pattern_pos = i;
            list.chars[list.count++] = fc;
        }
    }
    
    return list;
}

/*
 * Strategy 6: Complex multi-percent pattern (%a%b%c%)
 * Union of intersections where positions maintain order: i < j < k
 */
static RoaringBitmap* query_multi_percent(const PatternInfo *info) {
    RoaringBitmap *result = roaring_create();
    
    /* Extract fixed characters that must appear in order */
    FixedCharList fixed = extract_fixed_chars(info);
    
    if (fixed.count == 0) {
        /* Only wildcards - match all */
        for (int i = 0; i < global_index->num_records; i++)
            roaring_add(result, i);
        pfree(fixed.chars);
        return result;
    }
    
    /* For each record, check if characters appear in correct order */
    for (int rec_idx = 0; rec_idx < global_index->num_records; rec_idx++) {
        char *str = global_index->data[rec_idx];
        int str_len = global_index->lengths[rec_idx];
        
        /* Try to match all fixed characters in order */
        int char_idx = 0;  /* Current character we're looking for */
        int str_pos = 0;   /* Current position in string */
        
        bool match = true;
        
        while (char_idx < fixed.count && str_pos < str_len) {
            char target = fixed.chars[char_idx].ch;
            int pattern_pos = fixed.chars[char_idx].pattern_pos;
            
            /* Check constraints based on pattern wildcards */
            bool found = false;
            
            /* Determine search range based on prefix/suffix constraints */
            int search_start = str_pos;
            int search_end = str_len;
            
            /* If we have prefix constraint for this character */
            if (char_idx == 0 && !info->has_leading_percent) {
                /* First char must be at exact position */
                if (pattern_pos < str_len && str[pattern_pos] == target) {
                    str_pos = pattern_pos + 1;
                    char_idx++;
                    continue;
                } else {
                    match = false;
                    break;
                }
            }
            
            /* If we have suffix constraint for last character */
            if (char_idx == fixed.count - 1 && !info->has_trailing_percent) {
                int expected_pos = str_len - (info->count - pattern_pos);
                if (expected_pos >= 0 && expected_pos < str_len && str[expected_pos] == target) {
                    str_pos = expected_pos + 1;
                    char_idx++;
                    continue;
                } else {
                    match = false;
                    break;
                }
            }
            
            /* Search for character starting from current position */
            for (int i = search_start; i < search_end; i++) {
                if (str[i] == target) {
                    str_pos = i + 1;  /* Next search starts after this */
                    found = true;
                    break;
                }
            }
            
            if (found) {
                char_idx++;
            } else {
                match = false;
                break;
            }
        }
        
        if (match && char_idx == fixed.count) {
            roaring_add(result, rec_idx);
        }
    }
    
    pfree(fixed.chars);
    return result;
}

/*
 * Optimized multi-percent using bitmap operations with ordering constraint
 * For pattern %a%b%c%, compute: ⋃(a[i] ∩ b[j] ∩ c[k]) where i < j < k
 */
static RoaringBitmap* query_multi_percent_optimized(const PatternInfo *info) {
    RoaringBitmap *result = roaring_create();
    
    /* Extract fixed characters */
    FixedCharList fixed = extract_fixed_chars(info);
    
    if (fixed.count == 0) {
        for (int i = 0; i < global_index->num_records; i++)
            roaring_add(result, i);
        pfree(fixed.chars);
        return result;
    }
    
    if (fixed.count == 1) {
        /* Single character - use char cache */
        RoaringBitmap *char_bm = global_index->char_cache[(unsigned char)fixed.chars[0].ch];
        if (char_bm) {
            pfree(fixed.chars);
            return roaring_copy(char_bm);
        }
        pfree(fixed.chars);
        return result;
    }
    
    /* For multiple characters with ordering constraint */
    /* We need to iterate through all valid position combinations */
    
    /* First pass: filter candidates that contain all required characters */
    RoaringBitmap *candidates = roaring_create();
    for (int i = 0; i < global_index->num_records; i++)
        roaring_add(candidates, i);
    
    for (int i = 0; i < fixed.count; i++) {
        RoaringBitmap *char_bm = global_index->char_cache[(unsigned char)fixed.chars[i].ch];
        if (!char_bm || roaring_is_empty(char_bm)) {
            roaring_free(candidates);
            pfree(fixed.chars);
            return result;
        }
        
        RoaringBitmap *temp = roaring_and(candidates, char_bm);
        roaring_free(candidates);
        candidates = temp;
        
        if (roaring_is_empty(candidates)) {
            roaring_free(candidates);
            pfree(fixed.chars);
            return result;
        }
    }
    
    /* Second pass: verify ordering constraint for candidates */
    uint64_t cand_count;
    uint32_t *cand_indices = roaring_to_array(candidates, &cand_count);
    roaring_free(candidates);
    
    if (cand_indices) {
        for (uint64_t i = 0; i < cand_count; i++) {
            uint32_t idx = cand_indices[i];
            char *str = global_index->data[idx];
            int str_len = global_index->lengths[idx];
            
            /* Check if all fixed chars appear in order */
            int str_pos = 0;
            bool valid = true;
            
            for (int c = 0; c < fixed.count; c++) {
                char target = fixed.chars[c].ch;
                bool found = false;
                
                for (int p = str_pos; p < str_len; p++) {
                    if (str[p] == target) {
                        str_pos = p + 1;  /* Next search starts after this */
                        found = true;
                        break;
                    }
                }
                
                if (!found) {
                    valid = false;
                    break;
                }
            }
            
            if (valid) {
                roaring_add(result, idx);
            }
        }
        
        pfree(cand_indices);
    }
    
    pfree(fixed.chars);
    return result;
}

/*
 * Pattern matching for verification
 */
static bool match_pattern(const char *s, const char *p) {
    int si = 0, pi = 0, star = -1, match = 0;
    int slen = strlen(s), plen = strlen(p);
    
    while (si < slen) {
        if (pi < plen && (p[pi] == s[si] || p[pi] == '_')) {
            si++; pi++;
        } else if (pi < plen && p[pi] == '%') {
            star = pi; match = si; pi++;
        } else if (star != -1) {
            pi = star + 1; match++; si = match;
        } else {
            return false;
        }
    }
    
    while (pi < plen && p[pi] == '%') pi++;
    return pi == plen;
}

/*
 * Main unified query function
 */
static uint32_t* unified_query(const char *pattern, uint64_t *result_count) {
    PatternInfo info;
    RoaringBitmap *result = NULL;
    uint32_t *final_result = NULL;
    
    /* Special case: Match all */
    if (strcmp(pattern, "%") == 0) {
        final_result = (uint32_t *)palloc(global_index->num_records * sizeof(uint32_t));
        for (int i = 0; i < global_index->num_records; i++)
            final_result[i] = i;
        *result_count = global_index->num_records;
        return final_result;
    }
    
    /* Analyze pattern */
    analyze_pattern(pattern, &info);
    
    /* Choose optimal strategy based on pattern structure */
    if (!info.has_leading_percent && !info.has_trailing_percent) {
        /* Fixed positions only: a_b_c, abc */
        result = query_fixed_prefix(&info);
        
    } else if (info.has_leading_percent && !info.has_trailing_percent && !info.has_internal_percent) {
        /* Pure suffix: %abc, %a_b */
        result = query_fixed_suffix(&info);
        
    } else if (!info.has_leading_percent && info.has_trailing_percent && !info.has_internal_percent) {
        /* Pure prefix: abc%, a_b% */
        result = query_fixed_prefix(&info);
        
    } else if (info.has_leading_percent && info.has_trailing_percent && !info.has_internal_percent &&
               info.fixed_prefix_len == 0 && info.fixed_suffix_len == 0) {
        /* Simple contains: %abc% */
        /* Use char-anywhere cache */
        result = roaring_create();
        for (int i = 0; i < global_index->num_records; i++)
            roaring_add(result, i);
        
        unsigned char seen[256] = {0};
        for (int i = 1; i < info.count - 1; i++) {
            if (info.tokens[i].is_wildcard) continue;
            
            unsigned char ch = (unsigned char)info.tokens[i].ch;
            if (seen[ch]) continue;
            seen[ch] = 1;
            
            RoaringBitmap *char_bm = global_index->char_cache[ch];
            if (!char_bm || roaring_is_empty(char_bm)) {
                roaring_free(result);
                result = roaring_create();
                break;
            }
            
            RoaringBitmap *temp = roaring_and(result, char_bm);
            roaring_free(result);
            result = temp;
            
            if (roaring_is_empty(result))
                break;
        }
        
    } else if (!info.has_internal_percent && (info.fixed_prefix_len > 0 || info.fixed_suffix_len > 0)) {
        /* Dual anchor: abc%def, a_b%c_d */
        result = query_dual_anchor(&info);
        
    } else if (info.has_leading_percent && info.has_trailing_percent && 
               info.fixed_prefix_len == 0 && info.fixed_suffix_len > 0 &&
               !info.has_internal_percent) {
        /* Suffix with contains: %a%_b, %ab%cd */
        result = query_contains_anchor(&info);
        
    } else if (info.has_leading_percent && info.has_trailing_percent &&
               info.total_fixed_chars > 0 && !info.has_internal_percent) {
        /* Sliding window: %a_b%, %abc% with wildcards */
        result = query_sliding_window(&info);
        
    } else {
        /* Complex pattern with multiple %: %a%b%c%, %a%_b%c_d */
        /* Use optimized multi-percent query with ordering constraint */
        result = query_multi_percent_optimized(&info);
    }
    
    /* Convert bitmap to array */
    if (result && !roaring_is_empty(result)) {
        uint64_t candidate_count;
        uint32_t *candidates = roaring_to_array(result, &candidate_count);
        
        /* For patterns with underscores or complex structure, verify with pattern matching */
        bool needs_verification = false;
        
        /* Check if pattern has underscores that need verification */
        for (int i = 0; i < info.count; i++) {
            if (info.tokens[i].ch == '_') {
                needs_verification = true;
                break;
            }
        }
        
        /* Also verify if we used sliding window (it's approximate) */
        if (info.has_leading_percent && info.has_trailing_percent &&
            info.total_fixed_chars > 0 && !info.has_internal_percent &&
            info.fixed_prefix_len == 0 && info.fixed_suffix_len == 0) {
            needs_verification = true;
        }
        
        if (needs_verification && candidates) {
            final_result = (uint32_t *)palloc(candidate_count * sizeof(uint32_t));
            uint64_t match_count = 0;
            
            for (uint64_t i = 0; i < candidate_count; i++) {
                uint32_t idx = candidates[i];
                if (match_pattern(global_index->data[idx], pattern)) {
                    final_result[match_count++] = idx;
                }
            }
            
            *result_count = match_count;
            pfree(candidates);
        } else {
            /* Direct bitmap result is accurate */
            final_result = candidates;
            *result_count = candidate_count;
        }
    } else {
        *result_count = 0;
    }
    
    if (result)
        roaring_free(result);
    pfree(info.tokens);
    
    return final_result;
}

/* ==================== POSTGRESQL FUNCTIONS ==================== */

PG_FUNCTION_INFO_V1(build_optimized_index);
Datum build_optimized_index(PG_FUNCTION_ARGS) {
    text *table_name = PG_GETARG_TEXT_PP(0);
    text *column_name = PG_GETARG_TEXT_PP(1);
    char *table_str = text_to_cstring(table_name);
    char *column_str = text_to_cstring(column_name);
    
    instr_time start_time, end_time;
    StringInfoData query;
    int ret, num_records;
    MemoryContext oldcontext;
    
    INSTR_TIME_SET_CURRENT(start_time);
    elog(INFO, "Building unified Roaring bitmap index...");
    
    if (SPI_connect() != SPI_OK_CONNECT)
        ereport(ERROR, (errmsg("SPI_connect failed")));
    
    initStringInfo(&query);
    appendStringInfo(&query, "SELECT %s FROM %s ORDER BY ctid",
                     quote_identifier(column_str), quote_identifier(table_str));
    
    ret = SPI_execute(query.data, true, 0);
    if (ret != SPI_OK_SELECT) {
        SPI_finish();
        ereport(ERROR, (errmsg("Query failed")));
    }
    
    num_records = SPI_processed;
    elog(INFO, "Retrieved %d rows", num_records);
    
    if (index_context)
        MemoryContextDelete(index_context);
    
    index_context = AllocSetContextCreate(TopMemoryContext,
                                         "UnifiedRoaringIndex",
                                         ALLOCSET_DEFAULT_SIZES);
    
    oldcontext = MemoryContextSwitchTo(index_context);
    
    global_index = (RoaringIndex *)MemoryContextAlloc(index_context, sizeof(RoaringIndex));
    global_index->num_records = num_records;
    global_index->max_len = 0;
    global_index->memory_used = 0;
    global_index->data = (char **)MemoryContextAlloc(index_context, num_records * sizeof(char *));
    global_index->lengths = (int *)MemoryContextAlloc(index_context, num_records * sizeof(int));
    
    /* Initialize indices */
    for (int ch_idx = 0; ch_idx < CHAR_RANGE; ch_idx++) {
        global_index->pos_idx[ch_idx].entries = 
            (PosEntry *)MemoryContextAlloc(index_context, 64 * sizeof(PosEntry));
        global_index->pos_idx[ch_idx].count = 0;
        global_index->pos_idx[ch_idx].capacity = 64;
        
        global_index->neg_idx[ch_idx].entries = 
            (PosEntry *)MemoryContextAlloc(index_context, 64 * sizeof(PosEntry));
        global_index->neg_idx[ch_idx].count = 0;
        global_index->neg_idx[ch_idx].capacity = 64;
        
        global_index->char_cache[ch_idx] = NULL;
    }
    
    elog(INFO, "Building forward and backward indices...");
    
    /* Build indices from data */
    for (int idx = 0; idx < num_records; idx++) {
        if (idx % 10000 == 0 && idx > 0)
            elog(INFO, "Processed %d/%d records", idx, num_records);
        
        HeapTuple tuple = SPI_tuptable->vals[idx];
        bool isnull;
        Datum datum = SPI_getbinval(tuple, SPI_tuptable->tupdesc, 1, &isnull);
        
        if (isnull) {
            global_index->data[idx] = MemoryContextStrdup(index_context, "");
            global_index->lengths[idx] = 0;
            continue;
        }
        
        text *txt = DatumGetTextPP(datum);
        char *str = text_to_cstring(txt);
        int len = strlen(str);
        
        if (len > MAX_POSITIONS)
            len = MAX_POSITIONS;
        
        global_index->data[idx] = MemoryContextStrdup(index_context, str);
        global_index->lengths[idx] = len;
        
        if (len > global_index->max_len)
            global_index->max_len = len;
        
        /* Build forward index: char[pos] */
        for (int pos = 0; pos < len; pos++) {
            unsigned char uch = (unsigned char)str[pos];
            
            RoaringBitmap *existing_bm = get_pos_bitmap(uch, pos);
            if (!existing_bm) {
                existing_bm = roaring_create();
                set_pos_bitmap(uch, pos, existing_bm);
            }
            roaring_add(existing_bm, (uint32_t)idx);
        }
        
        /* Build backward index: char[-pos] */
        for (int pos = 0; pos < len; pos++) {
            unsigned char uch = (unsigned char)str[len - 1 - pos];
            
            RoaringBitmap *existing_bm = get_neg_bitmap(uch, -1 - pos);
            if (!existing_bm) {
                existing_bm = roaring_create();
                set_neg_bitmap(uch, -1 - pos, existing_bm);
            }
            roaring_add(existing_bm, (uint32_t)idx);
        }
        
        pfree(str);
    }
    
    elog(INFO, "Building character-anywhere cache...");
    
    /* Build char-anywhere cache by ORing all positions */
    for (int ch_idx = 0; ch_idx < CHAR_RANGE; ch_idx++) {
        CharIndex *cidx = &global_index->pos_idx[ch_idx];
        
        if (cidx->count == 0)
            continue;
        
        RoaringBitmap *char_bm = roaring_copy(cidx->entries[0].bitmap);
        
        for (int i = 1; i < cidx->count; i++) {
            RoaringBitmap *temp = roaring_or(char_bm, cidx->entries[i].bitmap);
            roaring_free(char_bm);
            char_bm = temp;
        }
        
        global_index->char_cache[ch_idx] = char_bm;
    }
    
    /* Calculate memory usage */
    global_index->memory_used = sizeof(RoaringIndex);
    for (int ch_idx = 0; ch_idx < CHAR_RANGE; ch_idx++) {
        if (global_index->char_cache[ch_idx])
            global_index->memory_used += roaring_count(global_index->char_cache[ch_idx]) * 4;
    }
    
    MemoryContextSwitchTo(oldcontext);
    SPI_finish();
    
    INSTR_TIME_SET_CURRENT(end_time);
    INSTR_TIME_SUBTRACT(end_time, start_time);
    double ms = INSTR_TIME_GET_MILLISEC(end_time);
    
    elog(INFO, "Index built in %.0f ms", ms);
    elog(INFO, "Records: %d, Max length: %d, Memory: %zu bytes",
         num_records, global_index->max_len, global_index->memory_used);
    
    PG_RETURN_BOOL(true);
}

PG_FUNCTION_INFO_V1(optimized_like_query);
Datum optimized_like_query(PG_FUNCTION_ARGS) {
    text *pattern_text = PG_GETARG_TEXT_PP(0);
    char *pattern = text_to_cstring(pattern_text);
    uint64_t result_count = 0;
    uint32_t *results;
    
    if (!global_index) {
        elog(WARNING, "Index not built. Call build_optimized_index() first.");
        PG_RETURN_INT32(0);
    }
    
    results = unified_query(pattern, &result_count);
    
    if (results)
        pfree(results);
    
    PG_RETURN_INT32(result_count);
}

PG_FUNCTION_INFO_V1(optimized_like_query_rows);
Datum optimized_like_query_rows(PG_FUNCTION_ARGS) {
    FuncCallContext *funcctx;
    
    if (SRF_IS_FIRSTCALL()) {
        MemoryContext oldcontext;
        text *pattern_text = PG_GETARG_TEXT_PP(0);
        char *pattern = text_to_cstring(pattern_text);
        uint64_t result_count = 0;
        uint32_t *matches;
        TupleDesc tupdesc;
        
        funcctx = SRF_FIRSTCALL_INIT();
        oldcontext = MemoryContextSwitchTo(funcctx->multi_call_memory_ctx);
        
        if (!global_index) {
            MemoryContextSwitchTo(oldcontext);
            SRF_RETURN_DONE(funcctx);
        }
        
        matches = unified_query(pattern, &result_count);
        funcctx->max_calls = result_count;
        funcctx->user_fctx = (void *)matches;
        
        if (get_call_result_type(fcinfo, NULL, &tupdesc) != TYPEFUNC_COMPOSITE)
            ereport(ERROR, (errmsg("function returning record in invalid context")));
        
        funcctx->tuple_desc = BlessTupleDesc(tupdesc);
        MemoryContextSwitchTo(oldcontext);
    }
    
    funcctx = SRF_PERCALL_SETUP();
    
    if (funcctx->call_cntr < funcctx->max_calls) {
        uint32_t *matches = (uint32_t *)funcctx->user_fctx;
        uint64_t row_idx = matches[funcctx->call_cntr];
        
        Datum values[2];
        bool nulls[2] = {false, false};
        
        values[0] = Int32GetDatum((int32_t)row_idx);
        values[1] = CStringGetTextDatum(global_index->data[row_idx]);
        
        HeapTuple tuple = heap_form_tuple(funcctx->tuple_desc, values, nulls);
        Datum result = HeapTupleGetDatum(tuple);
        
        SRF_RETURN_NEXT(funcctx, result);
    }
    
    if (funcctx->user_fctx) {
        pfree(funcctx->user_fctx);
        funcctx->user_fctx = NULL;
    }
    
    SRF_RETURN_DONE(funcctx);
}

PG_FUNCTION_INFO_V1(optimized_like_status);
Datum optimized_like_status(PG_FUNCTION_ARGS) {
    StringInfoData buf;
    
    if (!global_index) {
        PG_RETURN_TEXT_P(cstring_to_text("No index loaded. Call build_optimized_index() first."));
    }
    
    initStringInfo(&buf);
    appendStringInfo(&buf, "Unified Roaring Bitmap Index Status:\n");
    appendStringInfo(&buf, "  Records: %d\n", global_index->num_records);
    appendStringInfo(&buf, "  Max length: %d\n", global_index->max_len);
    appendStringInfo(&buf, "  Memory used: %zu bytes (%.2f MB)\n", 
                     global_index->memory_used, 
                     global_index->memory_used / (1024.0 * 1024.0));
    
    /* Count active positions in forward index */
    int forward_positions = 0;
    for (int ch = 0; ch < CHAR_RANGE; ch++)
        forward_positions += global_index->pos_idx[ch].count;
    
    /* Count active positions in backward index */
    int backward_positions = 0;
    for (int ch = 0; ch < CHAR_RANGE; ch++)
        backward_positions += global_index->neg_idx[ch].count;
    
    /* Count characters in cache */
    int cached_chars = 0;
    for (int ch = 0; ch < CHAR_RANGE; ch++)
        if (global_index->char_cache[ch])
            cached_chars++;
    
    appendStringInfo(&buf, "  Forward index entries: %d\n", forward_positions);
    appendStringInfo(&buf, "  Backward index entries: %d\n", backward_positions);
    appendStringInfo(&buf, "  Cached characters: %d\n", cached_chars);
    appendStringInfo(&buf, "\nSupported patterns:\n");
    appendStringInfo(&buf, "  1. Fixed prefix: a_b%%, abc%%\n");
    appendStringInfo(&buf, "  2. Fixed suffix: %%abc, %%a_b\n");
    appendStringInfo(&buf, "  3. Dual anchor: a%%b, a%%c_d\n");
    appendStringInfo(&buf, "  4. Contains: %%abc%%, %%a%%b%%\n");
    appendStringInfo(&buf, "  5. Sliding window: %%a_b%%\n");
    appendStringInfo(&buf, "  6. Complex: %%a%%b%%c%%\n");
    
    #ifdef HAVE_ROARING
    appendStringInfo(&buf, "\nBackend: Native CRoaring library\n");
    #else
    appendStringInfo(&buf, "\nBackend: Fallback bitmap implementation\n");
    #endif
    
    PG_RETURN_TEXT_P(cstring_to_text(buf.data));
}

PG_FUNCTION_INFO_V1(test_pattern_match);
Datum test_pattern_match(PG_FUNCTION_ARGS) {
    text *str_text = PG_GETARG_TEXT_PP(0);
    text *pattern_text = PG_GETARG_TEXT_PP(1);
    char *str = text_to_cstring(str_text);
    char *pattern = text_to_cstring(pattern_text);
    bool result = match_pattern(str, pattern);
    
    pfree(str);
    pfree(pattern);
    
    PG_RETURN_BOOL(result);
}

PG_FUNCTION_INFO_V1(analyze_query_pattern);
Datum analyze_query_pattern(PG_FUNCTION_ARGS) {
    text *pattern_text = PG_GETARG_TEXT_PP(0);
    char *pattern = text_to_cstring(pattern_text);
    PatternInfo info;
    StringInfoData buf;
    
    analyze_pattern(pattern, &info);
    
    initStringInfo(&buf);
    appendStringInfo(&buf, "Pattern Analysis for: '%s'\n", pattern);
    appendStringInfo(&buf, "  Leading %%: %s\n", info.has_leading_percent ? "yes" : "no");
    appendStringInfo(&buf, "  Trailing %%: %s\n", info.has_trailing_percent ? "yes" : "no");
    appendStringInfo(&buf, "  Internal %%: %s\n", info.has_internal_percent ? "yes" : "no");
    appendStringInfo(&buf, "  Fixed prefix length: %d\n", info.fixed_prefix_len);
    appendStringInfo(&buf, "  Fixed suffix length: %d\n", info.fixed_suffix_len);
    appendStringInfo(&buf, "  Total fixed chars: %d\n", info.total_fixed_chars);
    
    /* Determine strategy */
    appendStringInfo(&buf, "\nOptimal Strategy: ");
    if (!info.has_leading_percent && !info.has_trailing_percent) {
        appendStringInfo(&buf, "Fixed Position (Forward Index Only)\n");
    } else if (info.has_leading_percent && !info.has_trailing_percent && !info.has_internal_percent) {
        appendStringInfo(&buf, "Pure Suffix (Backward Index Only)\n");
    } else if (!info.has_leading_percent && info.has_trailing_percent && !info.has_internal_percent) {
        appendStringInfo(&buf, "Pure Prefix (Forward Index Only)\n");
    } else if (!info.has_internal_percent && (info.fixed_prefix_len > 0 || info.fixed_suffix_len > 0)) {
        appendStringInfo(&buf, "Dual Anchor (Forward + Backward Index)\n");
    } else if (info.has_leading_percent && info.has_trailing_percent && 
               info.fixed_prefix_len == 0 && info.fixed_suffix_len == 0) {
        appendStringInfo(&buf, "Simple Contains (Character Cache)\n");
    } else if (info.has_leading_percent && info.has_trailing_percent) {
        appendStringInfo(&buf, "Sliding Window or Complex Pattern\n");
    } else {
        appendStringInfo(&buf, "Complex Pattern (Candidate Filtering)\n");
    }
    
    pfree(info.tokens);
    pfree(pattern);
    
    PG_RETURN_TEXT_P(cstring_to_text(buf.data));
}
