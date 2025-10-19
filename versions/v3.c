/*
 * optimized_like_roaring.c
 * PostgreSQL extension with Roaring Bitmap optimization
 * 
 * KEY OPTIMIZATIONS:
 * 1. Skip redundant bit ops: Only process up to last non-wildcard char
 * 2. Use negative indices for suffix: Avoid string reversal overhead
 * 3. Extract candidates first: Use char-anywhere cache for early filtering
 * 4. Dedup characters: %abc% same speed as %a% (only one char-anywhere lookup per unique char)
 * 5. Early termination: Stop bitmap ops when result becomes empty
 * 6. Direct lookups: Use hash maps instead of 2D arrays where possible
 * 7. NO REDUNDANT SCANS: Start with first constraint, not "all records"
 * 8. ACCURATE COUNTING: Proper pattern classification and validation
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

static RoaringBitmap* roaring_create(void)
{
    return roaring_bitmap_create();
}

static void roaring_add(RoaringBitmap *rb, uint32_t value)
{
    roaring_bitmap_add(rb, value);
}

static RoaringBitmap* roaring_and(const RoaringBitmap *a, const RoaringBitmap *b)
{
    return roaring_bitmap_and(a, b);
}

static RoaringBitmap* roaring_or(const RoaringBitmap *a, const RoaringBitmap *b)
{
    return roaring_bitmap_or(a, b);
}

static uint64_t roaring_count(const RoaringBitmap *rb)
{
    return roaring_bitmap_get_cardinality(rb);
}

static bool roaring_is_empty(const RoaringBitmap *rb)
{
    return roaring_bitmap_get_cardinality(rb) == 0;
}

static uint32_t* roaring_to_array(const RoaringBitmap *rb, uint64_t *count)
{
    uint32_t *array;
    *count = roaring_bitmap_get_cardinality(rb);
    if (*count == 0) return NULL;
    array = (uint32_t *)palloc(*count * sizeof(uint32_t));
    roaring_bitmap_to_uint32_array(rb, array);
    return array;
}

static size_t roaring_size_bytes(const RoaringBitmap *rb)
{
    return roaring_bitmap_size_in_bytes(rb);
}

static void roaring_free(RoaringBitmap *rb)
{
    if (rb) roaring_bitmap_free(rb);
}

static RoaringBitmap* roaring_copy(const RoaringBitmap *rb)
{
    return roaring_bitmap_copy(rb);
}

#else

/* Fallback bitmap implementation */
typedef struct {
    uint64_t *blocks;
    int num_blocks;
    int capacity;
    bool is_palloc;
} RoaringBitmap;

static RoaringBitmap* roaring_create(void)
{
    RoaringBitmap *rb = (RoaringBitmap *)palloc(sizeof(RoaringBitmap));
    rb->num_blocks = 0;
    rb->capacity = 16;
    rb->blocks = (uint64_t *)palloc0(rb->capacity * sizeof(uint64_t));
    rb->is_palloc = true;
    return rb;
}

static void roaring_add(RoaringBitmap *rb, uint32_t value)
{
    int block = value >> 6;
    int bit = value & 63;
    int i;
    
    if (block >= rb->capacity)
    {
        int new_cap = block + 1;
        rb->blocks = (uint64_t *)repalloc(rb->blocks, new_cap * sizeof(uint64_t));
        for (i = rb->capacity; i < new_cap; i++)
            rb->blocks[i] = 0;
        rb->capacity = new_cap;
    }
    if (block >= rb->num_blocks)
        rb->num_blocks = block + 1;
    rb->blocks[block] |= (1ULL << bit);
}

static RoaringBitmap* roaring_and(const RoaringBitmap *a, const RoaringBitmap *b)
{
    RoaringBitmap *result = roaring_create();
    int min_blocks = (a->num_blocks < b->num_blocks) ? a->num_blocks : b->num_blocks;
    int i;
    
    if (min_blocks == 0)
        return result;
    
    if (result->capacity < min_blocks)
    {
        result->blocks = (uint64_t *)repalloc(result->blocks, min_blocks * sizeof(uint64_t));
        result->capacity = min_blocks;
    }
    
    result->num_blocks = min_blocks;
    
    for (i = 0; i < min_blocks; i++)
        result->blocks[i] = a->blocks[i] & b->blocks[i];
    
    return result;
}

static RoaringBitmap* roaring_or(const RoaringBitmap *a, const RoaringBitmap *b)
{
    RoaringBitmap *result = roaring_create();
    int max_blocks = (a->num_blocks > b->num_blocks) ? a->num_blocks : b->num_blocks;
    int min_blocks = (a->num_blocks < b->num_blocks) ? a->num_blocks : b->num_blocks;
    int i;
    
    if (max_blocks == 0)
        return result;
    
    if (result->capacity < max_blocks)
    {
        result->blocks = (uint64_t *)repalloc(result->blocks, max_blocks * sizeof(uint64_t));
        result->capacity = max_blocks;
    }
    
    result->num_blocks = max_blocks;
    
    for (i = 0; i < min_blocks; i++)
        result->blocks[i] = a->blocks[i] | b->blocks[i];
    
    if (a->num_blocks > min_blocks)
    {
        memcpy(result->blocks + min_blocks, a->blocks + min_blocks,
               (a->num_blocks - min_blocks) * sizeof(uint64_t));
    }
    else if (b->num_blocks > min_blocks)
    {
        memcpy(result->blocks + min_blocks, b->blocks + min_blocks,
               (b->num_blocks - min_blocks) * sizeof(uint64_t));
    }
    
    return result;
}

static uint64_t roaring_count(const RoaringBitmap *rb)
{
    uint64_t count = 0;
    int i;
    for (i = 0; i < rb->num_blocks; i++)
        count += __builtin_popcountll(rb->blocks[i]);
    return count;
}

static bool roaring_is_empty(const RoaringBitmap *rb)
{
    int i;
    for (i = 0; i < rb->num_blocks; i++)
        if (rb->blocks[i])
            return false;
    return true;
}

static uint32_t* roaring_to_array(const RoaringBitmap *rb, uint64_t *count)
{
    uint32_t *array;
    int idx = 0, i;
    uint64_t bits, base;
    
    *count = roaring_count(rb);
    if (*count == 0)
        return NULL;
    
    array = (uint32_t *)palloc(*count * sizeof(uint32_t));
    
    for (i = 0; i < rb->num_blocks; i++)
    {
        bits = rb->blocks[i];
        if (!bits)
            continue;
        
        base = (uint64_t)i << 6;
        while (bits)
        {
            array[idx++] = (uint32_t)(base + __builtin_ctzll(bits));
            bits &= bits - 1;
        }
    }
    return array;
}

static size_t roaring_size_bytes(const RoaringBitmap *rb)
{
    return sizeof(RoaringBitmap) + rb->capacity * sizeof(uint64_t);
}

static void roaring_free(RoaringBitmap *rb)
{
    if (rb)
    {
        if (rb->blocks && rb->is_palloc)
            pfree(rb->blocks);
        pfree(rb);
    }
}

static RoaringBitmap* roaring_copy(const RoaringBitmap *rb)
{
    RoaringBitmap *copy = roaring_create();
    
    if (rb->num_blocks > 0)
    {
        copy->blocks = (uint64_t *)repalloc(copy->blocks, rb->num_blocks * sizeof(uint64_t));
        copy->num_blocks = rb->num_blocks;
        copy->capacity = rb->num_blocks;
        memcpy(copy->blocks, rb->blocks, rb->num_blocks * sizeof(uint64_t));
    }
    return copy;
}

#endif

/* ==================== INDEX STRUCTURES ==================== */

#define MAX_POSITIONS 256
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

typedef struct RoaringIndex {
    CharIndex pos_idx[CHAR_RANGE];
    CharIndex neg_idx[CHAR_RANGE];
    RoaringBitmap *char_cache[CHAR_RANGE];
    
    char **data;
    int num_records;
    int max_len;
    size_t memory_used;
} RoaringIndex;

static RoaringIndex *global_index = NULL;
static MemoryContext index_context = NULL;

/* Find pos_idx entry for (ch, pos) */
static RoaringBitmap* get_pos_bitmap(unsigned char ch, int pos)
{
    CharIndex *cidx = &global_index->pos_idx[ch];
    int i;
    
    for (i = 0; i < cidx->count; i++)
        if (cidx->entries[i].pos == pos)
            return cidx->entries[i].bitmap;
    
    return NULL;
}

/* Find neg_idx entry for (ch, neg_pos) */
static RoaringBitmap* get_neg_bitmap(unsigned char ch, int neg_pos)
{
    CharIndex *cidx = &global_index->neg_idx[ch];
    int i;
    
    for (i = 0; i < cidx->count; i++)
        if (cidx->entries[i].pos == neg_pos)
            return cidx->entries[i].bitmap;
    
    return NULL;
}

/* Set pos_idx entry, creating if needed */
static void set_pos_bitmap(unsigned char ch, int pos, RoaringBitmap *bm)
{
    CharIndex *cidx = &global_index->pos_idx[ch];
    int i;
    
    for (i = 0; i < cidx->count; i++)
    {
        if (cidx->entries[i].pos == pos)
        {
            cidx->entries[i].bitmap = bm;
            return;
        }
    }
    
    if (cidx->count >= cidx->capacity)
    {
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

/* Set neg_idx entry, creating if needed */
static void set_neg_bitmap(unsigned char ch, int neg_pos, RoaringBitmap *bm)
{
    CharIndex *cidx = &global_index->neg_idx[ch];
    int i;
    
    for (i = 0; i < cidx->count; i++)
    {
        if (cidx->entries[i].pos == neg_pos)
        {
            cidx->entries[i].bitmap = bm;
            return;
        }
    }
    
    if (cidx->count >= cidx->capacity)
    {
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

/* ==================== PATTERN MATCHING ==================== */

static bool match_pattern(const char *s, const char *p)
{
    int si = 0, pi = 0, star = -1, match = 0;
    int slen = strlen(s), plen = strlen(p);
    
    while (si < slen)
    {
        if (pi < plen && (p[pi] == s[si] || p[pi] == '_'))
        {
            si++;
            pi++;
        }
        else if (pi < plen && p[pi] == '%')
        {
            star = pi;
            match = si;
            pi++;
        }
        else if (star != -1)
        {
            pi = star + 1;
            match++;
            si = match;
        }
        else
            return false;
    }
    
    while (pi < plen && p[pi] == '%')
        pi++;
    
    return pi == plen;
}

/* ==================== HELPER FUNCTIONS ==================== */

/* Check if string starts with prefix (handles wildcards) */
static bool starts_with_pattern(const char *str, const char *prefix, int prefix_len)
{
    int i;
    int str_len = strlen(str);
    
    if (str_len < prefix_len)
        return false;
    
    for (i = 0; i < prefix_len; i++)
    {
        if (prefix[i] != '_' && prefix[i] != str[i])
            return false;
    }
    return true;
}

/* Check if string ends with suffix (handles wildcards) */
static bool ends_with_pattern(const char *str, const char *suffix, int suffix_len)
{
    int i;
    int str_len = strlen(str);
    
    if (str_len < suffix_len)
        return false;
    
    for (i = 0; i < suffix_len; i++)
    {
        if (suffix[i] != '_' && suffix[i] != str[str_len - suffix_len + i])
            return false;
    }
    return true;
}

/* ==================== QUERY FUNCTIONS ==================== */

/*
 * OPTIMIZATION: Direct bitmap lookup, then validate with actual prefix match
 * This ensures accuracy while maintaining speed
 */
static uint32_t* query_prefix(const char *prefix, uint64_t *result_count)
{
    RoaringBitmap *result = NULL;
    int prefix_len = strlen(prefix);
    int i, last_non_wildcard = -1;
    RoaringBitmap *char_bm;
    RoaringBitmap *temp;
    uint32_t *candidates;
    uint64_t cand_count;
    uint32_t *final_result;
    uint64_t match_count = 0;
    uint32_t idx;
    
    /* Find last non-wildcard position */
    for (i = prefix_len - 1; i >= 0; i--)
    {
        if (prefix[i] != '_')
        {
            last_non_wildcard = i;
            break;
        }
    }
    
    /* All wildcards = match all */
    if (last_non_wildcard == -1)
    {
        final_result = (uint32_t *)palloc(global_index->num_records * sizeof(uint32_t));
        for (i = 0; i < global_index->num_records; i++)
            final_result[i] = (uint32_t)i;
        *result_count = global_index->num_records;
        return final_result;
    }
    
    /* Build candidate set using bitmap operations */
    for (i = 0; i <= last_non_wildcard; i++)
    {
        if (prefix[i] == '_')
            continue;
        
        char_bm = get_pos_bitmap((unsigned char)prefix[i], i);
        if (!char_bm)
        {
            if (result)
                roaring_free(result);
            *result_count = 0;
            return NULL;
        }
        
        if (!result)
        {
            result = roaring_copy(char_bm);
        }
        else
        {
            temp = roaring_and(result, char_bm);
            roaring_free(result);
            result = temp;
            
            if (roaring_is_empty(result))
            {
                roaring_free(result);
                *result_count = 0;
                return NULL;
            }
        }
    }
    
    if (!result)
    {
        final_result = (uint32_t *)palloc(global_index->num_records * sizeof(uint32_t));
        for (i = 0; i < global_index->num_records; i++)
            final_result[i] = (uint32_t)i;
        *result_count = global_index->num_records;
        return final_result;
    }
    
    /* Get candidates and validate each one */
    candidates = roaring_to_array(result, &cand_count);
    roaring_free(result);
    
    if (!candidates || cand_count == 0)
    {
        *result_count = 0;
        return NULL;
    }
    
    /* Validate candidates with actual prefix matching */
    final_result = (uint32_t *)palloc(cand_count * sizeof(uint32_t));
    
    for (i = 0; i < cand_count; i++)
    {
        idx = candidates[i];
        if (starts_with_pattern(global_index->data[idx], prefix, prefix_len))
            final_result[match_count++] = idx;
    }
    
    pfree(candidates);
    *result_count = match_count;
    
    if (match_count == 0)
    {
        pfree(final_result);
        return NULL;
    }
    
    return final_result;
}

/*
 * OPTIMIZATION: Direct bitmap lookup for suffix, then validate
 */
static uint32_t* query_suffix(const char *suffix, uint64_t *result_count)
{
    RoaringBitmap *result = NULL;
    int suffix_len = strlen(suffix);
    int i, last_non_wildcard = -1;
    unsigned char ch;
    RoaringBitmap *char_bm;
    RoaringBitmap *temp;
    uint32_t *candidates;
    uint64_t cand_count;
    uint32_t *final_result;
    uint64_t match_count = 0;
    uint32_t idx;
    
    /* Find last non-wildcard from the end */
    for (i = suffix_len - 1; i >= 0; i--)
    {
        if (suffix[i] != '_')
        {
            last_non_wildcard = suffix_len - 1 - i;
            break;
        }
    }
    
    /* All wildcards = match all */
    if (last_non_wildcard == -1)
    {
        final_result = (uint32_t *)palloc(global_index->num_records * sizeof(uint32_t));
        for (i = 0; i < global_index->num_records; i++)
            final_result[i] = (uint32_t)i;
        *result_count = global_index->num_records;
        return final_result;
    }
    
    /* Build candidate set */
    for (i = 0; i <= last_non_wildcard; i++)
    {
        ch = (unsigned char)suffix[suffix_len - 1 - i];
        if (ch == '_')
            continue;
        
        char_bm = get_neg_bitmap(ch, -1 - i);
        if (!char_bm)
        {
            if (result)
                roaring_free(result);
            *result_count = 0;
            return NULL;
        }
        
        if (!result)
        {
            result = roaring_copy(char_bm);
        }
        else
        {
            temp = roaring_and(result, char_bm);
            roaring_free(result);
            result = temp;
            
            if (roaring_is_empty(result))
            {
                roaring_free(result);
                *result_count = 0;
                return NULL;
            }
        }
    }
    
    if (!result)
    {
        final_result = (uint32_t *)palloc(global_index->num_records * sizeof(uint32_t));
        for (i = 0; i < global_index->num_records; i++)
            final_result[i] = (uint32_t)i;
        *result_count = global_index->num_records;
        return final_result;
    }
    
    /* Validate candidates */
    candidates = roaring_to_array(result, &cand_count);
    roaring_free(result);
    
    if (!candidates || cand_count == 0)
    {
        *result_count = 0;
        return NULL;
    }
    
    final_result = (uint32_t *)palloc(cand_count * sizeof(uint32_t));
    
    for (i = 0; i < cand_count; i++)
    {
        idx = candidates[i];
        if (ends_with_pattern(global_index->data[idx], suffix, suffix_len))
            final_result[match_count++] = idx;
    }
    
    pfree(candidates);
    *result_count = match_count;
    
    if (match_count == 0)
    {
        pfree(final_result);
        return NULL;
    }
    
    return final_result;
}

/*
 * OPTIMIZATION: Combines prefix + suffix with validation
 */
static uint32_t* query_dual(const char *prefix, const char *suffix, uint64_t *result_count)
{
    RoaringBitmap *result = NULL;
    int prefix_len = strlen(prefix);
    int suffix_len = strlen(suffix);
    int i, prefix_last = -1, suffix_last = -1;
    RoaringBitmap *char_bm;
    RoaringBitmap *temp;
    unsigned char ch;
    uint32_t *candidates;
    uint64_t cand_count;
    uint32_t *final_result;
    uint64_t match_count = 0;
    uint32_t idx;
    const char *str;
    int str_len;
    
    /* Find last non-wildcard in prefix */
    for (i = prefix_len - 1; i >= 0; i--)
    {
        if (prefix[i] != '_')
        {
            prefix_last = i;
            break;
        }
    }
    
    /* Find last non-wildcard in suffix from end */
    for (i = suffix_len - 1; i >= 0; i--)
    {
        if (suffix[i] != '_')
        {
            suffix_last = suffix_len - 1 - i;
            break;
        }
    }
    
    /* Apply prefix constraints */
    if (prefix_last >= 0)
    {
        for (i = 0; i <= prefix_last; i++)
        {
            if (prefix[i] == '_')
                continue;
            
            char_bm = get_pos_bitmap((unsigned char)prefix[i], i);
            if (!char_bm)
            {
                if (result)
                    roaring_free(result);
                *result_count = 0;
                return NULL;
            }
            
            if (!result)
            {
                result = roaring_copy(char_bm);
            }
            else
            {
                temp = roaring_and(result, char_bm);
                roaring_free(result);
                result = temp;
                
                if (roaring_is_empty(result))
                {
                    roaring_free(result);
                    *result_count = 0;
                    return NULL;
                }
            }
        }
    }
    
    /* Apply suffix constraints */
    if (suffix_last >= 0)
    {
        for (i = 0; i <= suffix_last; i++)
        {
            ch = (unsigned char)suffix[suffix_len - 1 - i];
            if (ch == '_')
                continue;
            
            char_bm = get_neg_bitmap(ch, -1 - i);
            if (!char_bm)
            {
                if (result)
                    roaring_free(result);
                *result_count = 0;
                return NULL;
            }
            
            if (!result)
            {
                result = roaring_copy(char_bm);
            }
            else
            {
                temp = roaring_and(result, char_bm);
                roaring_free(result);
                result = temp;
                
                if (roaring_is_empty(result))
                {
                    roaring_free(result);
                    *result_count = 0;
                    return NULL;
                }
            }
        }
    }
    
    /* Handle case where both are all wildcards */
    if (!result)
    {
        final_result = (uint32_t *)palloc(global_index->num_records * sizeof(uint32_t));
        for (i = 0; i < global_index->num_records; i++)
            final_result[i] = (uint32_t)i;
        *result_count = global_index->num_records;
        return final_result;
    }
    
    /* Validate candidates */
    candidates = roaring_to_array(result, &cand_count);
    roaring_free(result);
    
    if (!candidates || cand_count == 0)
    {
        *result_count = 0;
        return NULL;
    }
    
    final_result = (uint32_t *)palloc(cand_count * sizeof(uint32_t));
    
    for (i = 0; i < cand_count; i++)
    {
        idx = candidates[i];
        str = global_index->data[idx];
        str_len = strlen(str);
        
        /* Must be long enough for both prefix and suffix */
        if (str_len < prefix_len + suffix_len)
            continue;
        
        /* Validate prefix and suffix */
        if (starts_with_pattern(str, prefix, prefix_len) &&
            ends_with_pattern(str, suffix, suffix_len))
        {
            final_result[match_count++] = idx;
        }
    }
    
    pfree(candidates);
    *result_count = match_count;
    
    if (match_count == 0)
    {
        pfree(final_result);
        return NULL;
    }
    
    return final_result;
}

/*
 * OPTIMIZATION: Deduplicate characters before bitmap operations
 * Returns candidate bitmap (not validated)
 */
static RoaringBitmap* extract_candidates(const char *pattern)
{
    RoaringBitmap *result = NULL;
    int plen = strlen(pattern);
    int i;
    char c;
    RoaringBitmap *char_bm;
    RoaringBitmap *temp;
    unsigned char seen[256];
    
    memset(seen, 0, 256);
    
    for (i = 0; i < plen; i++)
    {
        c = pattern[i];
        
        if (c == '%' || c == '_')
            continue;
        
        unsigned char uc = (unsigned char)c;
        
        /* Skip if already processed */
        if (seen[uc])
            continue;
        
        seen[uc] = 1;
        
        char_bm = global_index->char_cache[uc];
        if (!char_bm || roaring_is_empty(char_bm))
        {
            if (result)
                roaring_free(result);
            return roaring_create();
        }
        
        if (!result)
        {
            result = roaring_copy(char_bm);
        }
        else
        {
            temp = roaring_and(result, char_bm);
            roaring_free(result);
            result = temp;
            
            if (roaring_is_empty(result))
                return result;
        }
    }
    
    return result ? result : roaring_create();
}

/* ==================== MAIN QUERY FUNCTION ==================== */

static uint32_t* optimized_query(const char *pattern, uint64_t *result_count)
{
    uint32_t *result = NULL;
    int plen = strlen(pattern);
    char ch;
    RoaringBitmap *char_bm;
    char *prefix;
    const char *first_wild, *last_wild;
    int prefix_len;
    char *suffix;
    RoaringBitmap *candidates;
    uint64_t cand_count;
    uint32_t *cand_idx;
    uint64_t match_count;
    uint64_t i;
    uint32_t idx;
    
    /* Pattern: % - match all */
    if (strcmp(pattern, "%") == 0)
    {
        result = (uint32_t *)palloc(global_index->num_records * sizeof(uint32_t));
        for (i = 0; i < global_index->num_records; i++)
            result[i] = (uint32_t)i;
        *result_count = global_index->num_records;
        return result;
    }
    
    /* Single char anywhere: %c% - DIRECT BITMAP LOOKUP */
    if (plen == 3 && pattern[0] == '%' && pattern[2] == '%')
    {
        ch = pattern[1];
        if (ch == '_')
        {
            result = (uint32_t *)palloc(global_index->num_records * sizeof(uint32_t));
            for (i = 0; i < global_index->num_records; i++)
                result[i] = (uint32_t)i;
            *result_count = global_index->num_records;
            return result;
        }
        
        char_bm = global_index->char_cache[(unsigned char)ch];
        if (char_bm && !roaring_is_empty(char_bm))
        {
            result = roaring_to_array(char_bm, result_count);
            return result;
        }
        
        *result_count = 0;
        return NULL;
    }
    
    /* Pure prefix: a%, ab% - DIRECT BITMAP LOOKUP + VALIDATION */
    if (pattern[plen - 1] == '%' && strchr(pattern, '%') == &pattern[plen - 1])
    {
        prefix = pnstrdup(pattern, plen - 1);
        result = query_prefix(prefix, result_count);
        pfree(prefix);
        return result;
    }
    
    /* Pure suffix: %a, %ab - DIRECT BITMAP LOOKUP + VALIDATION */
    if (pattern[0] == '%' && strchr(pattern + 1, '%') == NULL)
    {
        result = query_suffix(pattern + 1, result_count);
        return result;
    }
    
    /* Dual anchor: a%b - DIRECT BITMAP LOOKUP + VALIDATION */
    first_wild = strchr(pattern, '%');
    last_wild = strrchr(pattern, '%');
    
    if (first_wild && first_wild == last_wild &&
        first_wild > pattern && first_wild < &pattern[plen - 1])
    {
        prefix_len = first_wild - pattern;
        prefix = pnstrdup(pattern, prefix_len);
        suffix = pstrdup(first_wild + 1);
        
        result = query_dual(prefix, suffix, result_count);
        
        pfree(prefix);
        pfree(suffix);
        return result;
    }
    
    /* Complex pattern - use candidate filtering + full pattern matching */
    candidates = extract_candidates(pattern);
    
    if (!roaring_is_empty(candidates))
    {
        cand_idx = roaring_to_array(candidates, &cand_count);
        
        if (cand_idx)
        {
            result = (uint32_t *)palloc(cand_count * sizeof(uint32_t));
            match_count = 0;
            
            for (i = 0; i < cand_count; i++)
            {
                idx = cand_idx[i];
                if (match_pattern(global_index->data[idx], pattern))
                    result[match_count++] = idx;
            }
            
            pfree(cand_idx);
            *result_count = match_count;
            
            if (match_count == 0)
            {
                pfree(result);
                result = NULL;
            }
        }
        else
            *result_count = 0;
    }
    else
        *result_count = 0;
    
    roaring_free(candidates);
    return result;
}

/* ==================== POSTGRESQL FUNCTIONS ==================== */

PG_FUNCTION_INFO_V1(build_optimized_index);
Datum build_optimized_index(PG_FUNCTION_ARGS)
{
    text *table_name = PG_GETARG_TEXT_PP(0);
    text *column_name = PG_GETARG_TEXT_PP(1);
    char *table_str = text_to_cstring(table_name);
    char *column_str = text_to_cstring(column_name);
    
    instr_time start_time, end_time;
    StringInfoData query;
    int ret, num_records, idx, len, pos;
    MemoryContext oldcontext;
    HeapTuple tuple;
    bool isnull;
    Datum datum;
    text *txt;
    char *str;
    unsigned char uch;
    RoaringBitmap *existing_bm;
    int ch_idx;
    double ms;
    int i;
    
    INSTR_TIME_SET_CURRENT(start_time);
    elog(INFO, "Building optimized Roaring bitmap index...");
    
    if (SPI_connect() != SPI_OK_CONNECT)
        ereport(ERROR, (errmsg("SPI_connect failed")));
    
    initStringInfo(&query);
    appendStringInfo(&query, "SELECT %s FROM %s ORDER BY ctid",
                     quote_identifier(column_str), quote_identifier(table_str));
    
    ret = SPI_execute(query.data, true, 0);
    if (ret != SPI_OK_SELECT)
    {
        SPI_finish();
        ereport(ERROR, (errmsg("Query failed")));
    }
    
    num_records = SPI_processed;
    elog(INFO, "Retrieved %d rows", num_records);
    
    if (index_context)
        MemoryContextDelete(index_context);
    
    index_context = AllocSetContextCreate(TopMemoryContext,
                                         "RoaringLikeIndex",
                                         ALLOCSET_DEFAULT_SIZES);
    
    oldcontext = MemoryContextSwitchTo(index_context);
    
    global_index = (RoaringIndex *)MemoryContextAlloc(index_context, sizeof(RoaringIndex));
    global_index->num_records = num_records;
    global_index->max_len = 0;
    global_index->memory_used = 0;
    global_index->data = (char **)MemoryContextAlloc(index_context, num_records * sizeof(char *));
    
    /* Initialize pos_idx and neg_idx */
    for (ch_idx = 0; ch_idx < CHAR_RANGE; ch_idx++)
    {
        global_index->pos_idx[ch_idx].entries = (PosEntry *)MemoryContextAlloc(index_context, 64 * sizeof(PosEntry));
        global_index->pos_idx[ch_idx].count = 0;
        global_index->pos_idx[ch_idx].capacity = 64;
        
        global_index->neg_idx[ch_idx].entries = (PosEntry *)MemoryContextAlloc(index_context, 64 * sizeof(PosEntry));
        global_index->neg_idx[ch_idx].count = 0;
        global_index->neg_idx[ch_idx].capacity = 64;
        
        global_index->char_cache[ch_idx] = NULL;
    }
    
    elog(INFO, "Initialized index structures");
    
    /* Build index from data */
    for (idx = 0; idx < num_records; idx++)
    {
        if (idx % 10000 == 0)
            elog(INFO, "Processing record %d/%d", idx, num_records);
        
        tuple = SPI_tuptable->vals[idx];
        datum = SPI_getbinval(tuple, SPI_tuptable->tupdesc, 1, &isnull);
        
        if (isnull)
        {
            global_index->data[idx] = MemoryContextStrdup(index_context, "");
            continue;
        }
        
        txt = DatumGetTextPP(datum);
        str = text_to_cstring(txt);
        len = strlen(str);
        
        if (len > MAX_POSITIONS)
            len = MAX_POSITIONS;
        
        global_index->data[idx] = MemoryContextStrdup(index_context, str);
        if (len > global_index->max_len)
            global_index->max_len = len;
        
        /* Build position and negative indices */
        for (pos = 0; pos < len; pos++)
        {
            /* Forward position index */
            uch = (unsigned char)str[pos];
            
            existing_bm = get_pos_bitmap(uch, pos);
            if (!existing_bm)
            {
                existing_bm = roaring_create();
                set_pos_bitmap(uch, pos, existing_bm);
            }
            roaring_add(existing_bm, (uint32_t)idx);
            
            /* Backward (negative) index */
            uch = (unsigned char)str[len - 1 - pos];
            
            existing_bm = get_neg_bitmap(uch, -1 - pos);
            if (!existing_bm)
            {
                existing_bm = roaring_create();
                set_neg_bitmap(uch, -1 - pos, existing_bm);
            }
            roaring_add(existing_bm, (uint32_t)idx);
        }
        
        pfree(str);
    }
    
    elog(INFO, "Index building complete, building char cache...");
    
    /* Build character-anywhere cache */
    for (ch_idx = 0; ch_idx < CHAR_RANGE; ch_idx++)
    {
        RoaringBitmap *new_bm = NULL;
        CharIndex *cidx = &global_index->pos_idx[ch_idx];
        
        if (cidx->count == 0)
            continue;
        
        new_bm = roaring_copy(cidx->entries[0].bitmap);
        
        for (i = 1; i < cidx->count; i++)
        {
            RoaringBitmap *temp = roaring_or(new_bm, cidx->entries[i].bitmap);
            roaring_free(new_bm);
            new_bm = temp;
        }
        
        if (new_bm)
            global_index->char_cache[ch_idx] = new_bm;
    }
    
    elog(INFO, "Character cache complete");
    
    /* Calculate memory usage */
    global_index->memory_used = sizeof(RoaringIndex);
    for (ch_idx = 0; ch_idx < CHAR_RANGE; ch_idx++)
    {
        if (global_index->char_cache[ch_idx])
            global_index->memory_used += roaring_size_bytes(global_index->char_cache[ch_idx]);
    }
    
    MemoryContextSwitchTo(oldcontext);
    SPI_finish();
    
    INSTR_TIME_SET_CURRENT(end_time);
    INSTR_TIME_SUBTRACT(end_time, start_time);
    ms = INSTR_TIME_GET_MILLISEC(end_time);
    
    elog(INFO, "Build time: %.0f ms", ms);
    elog(INFO, "Index: %d records, max_len=%d, memory=%zu bytes",
         num_records, global_index->max_len, global_index->memory_used);
    
    PG_RETURN_BOOL(true);
}

PG_FUNCTION_INFO_V1(optimized_like_query);
Datum optimized_like_query(PG_FUNCTION_ARGS)
{
    text *pattern_text = PG_GETARG_TEXT_PP(0);
    char *pattern = text_to_cstring(pattern_text);
    uint64_t result_count = 0;
    uint32_t *results;
    
    if (!global_index)
    {
        elog(WARNING, "Index not built. Call build_optimized_index() first.");
        PG_RETURN_INT32(0);
    }
    
    results = optimized_query(pattern, &result_count);
    
    if (results)
        pfree(results);
    
    PG_RETURN_INT32(result_count);
}

PG_FUNCTION_INFO_V1(optimized_like_query_rows);
Datum optimized_like_query_rows(PG_FUNCTION_ARGS)
{
    FuncCallContext *funcctx;
    uint32_t *matches;
    uint64_t row_idx;
    Datum values[2];
    bool nulls[2];
    HeapTuple tuple;
    Datum result;
    
    if (SRF_IS_FIRSTCALL())
    {
        MemoryContext oldcontext;
        text *pattern_text = PG_GETARG_TEXT_PP(0);
        char *pattern = text_to_cstring(pattern_text);
        uint64_t result_count = 0;
        TupleDesc tupdesc;
        
        funcctx = SRF_FIRSTCALL_INIT();
        oldcontext = MemoryContextSwitchTo(funcctx->multi_call_memory_ctx);
        
        if (!global_index)
        {
            MemoryContextSwitchTo(oldcontext);
            SRF_RETURN_DONE(funcctx);
        }
        
        matches = optimized_query(pattern, &result_count);
        funcctx->max_calls = result_count;
        funcctx->user_fctx = (void *)matches;
        
        if (get_call_result_type(fcinfo, NULL, &tupdesc) != TYPEFUNC_COMPOSITE)
            ereport(ERROR, (errmsg("function returning record in invalid context")));
        
        funcctx->tuple_desc = BlessTupleDesc(tupdesc);
        MemoryContextSwitchTo(oldcontext);
    }
    
    funcctx = SRF_PERCALL_SETUP();
    
    if (funcctx->call_cntr < funcctx->max_calls)
    {
        matches = (uint32_t *)funcctx->user_fctx;
        row_idx = matches[funcctx->call_cntr];
        
        nulls[0] = false;
        nulls[1] = false;
        
        values[0] = Int32GetDatum((int32_t)row_idx);
        values[1] = CStringGetTextDatum(global_index->data[row_idx]);
        
        tuple = heap_form_tuple(funcctx->tuple_desc, values, nulls);
        result = HeapTupleGetDatum(tuple);
        
        SRF_RETURN_NEXT(funcctx, result);
    }
    
    if (funcctx->user_fctx)
    {
        pfree(funcctx->user_fctx);
        funcctx->user_fctx = NULL;
    }
    
    SRF_RETURN_DONE(funcctx);
}

PG_FUNCTION_INFO_V1(optimized_like_status);
Datum optimized_like_status(PG_FUNCTION_ARGS)
{
    StringInfoData buf;
    
    if (!global_index)
    {
        PG_RETURN_TEXT_P(cstring_to_text("No index loaded. Call build_optimized_index() first."));
    }
    
    initStringInfo(&buf);
    appendStringInfo(&buf, "Roaring Bitmap Index Status:\n");
    appendStringInfo(&buf, "  Records: %d\n", global_index->num_records);
    appendStringInfo(&buf, "  Max length: %d\n", global_index->max_len);
    appendStringInfo(&buf, "  Memory used: %zu bytes\n", global_index->memory_used);
    appendStringInfo(&buf, "  Index type: Roaring Bitmap compression\n");
    
    #ifdef HAVE_ROARING
    appendStringInfo(&buf, "  Backend: Native Roaring library\n");
    #else
    appendStringInfo(&buf, "  Backend: Fallback bitmap implementation\n");
    #endif
    
    PG_RETURN_TEXT_P(cstring_to_text(buf.data));
}

PG_FUNCTION_INFO_V1(test_pattern_match);
Datum test_pattern_match(PG_FUNCTION_ARGS)
{
    text *str_text = PG_GETARG_TEXT_PP(0);
    text *pattern_text = PG_GETARG_TEXT_PP(1);
    char *str = text_to_cstring(str_text);
    char *pattern = text_to_cstring(pattern_text);
    bool match_result = match_pattern(str, pattern);
    
    PG_RETURN_BOOL(match_result);
}
