/*
 * optimized_like_roaring.c
 * PostgreSQL extension - FULLY FIXED VERSION
 * 
 * FIX: Proper underscore pattern matching with exact length constraints
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

/* ==================== OPTIMIZATION MACROS ==================== */

#ifndef likely
#define likely(x)       __builtin_expect(!!(x), 1)
#endif
#ifndef unlikely
#define unlikely(x)     __builtin_expect(!!(x), 0)
#endif
#define FORCE_INLINE    __attribute__((always_inline)) inline
#define PREFETCH(addr)  __builtin_prefetch(addr, 0, 3)
#define ALIGNED(x)      __attribute__((aligned(x)))
#define CACHE_ALIGNED   ALIGNED(64)

/* ==================== CONFIGURATION ==================== */

#define MAX_POSITIONS 256
#define CHAR_RANGE 256
#define HASH_TABLE_SIZE 4096
#define QUERY_CACHE_SIZE 512
#define BLOOM_SIZE 4096

/* ==================== BLOOM FILTER ==================== */

typedef struct {
    CACHE_ALIGNED uint64_t bits[BLOOM_SIZE / 64];
} BloomFilter;

static FORCE_INLINE void bloom_init(BloomFilter *bf)
{
    memset(bf->bits, 0, sizeof(bf->bits));
}

static FORCE_INLINE void bloom_add(BloomFilter *bf, uint32_t hash)
{
    uint32_t h1 = hash % BLOOM_SIZE;
    uint32_t h2 = (hash * 16777619) % BLOOM_SIZE;
    uint32_t h3 = (hash * 2654435761U) % BLOOM_SIZE;
    
    bf->bits[h1 >> 6] |= (1ULL << (h1 & 63));
    bf->bits[h2 >> 6] |= (1ULL << (h2 & 63));
    bf->bits[h3 >> 6] |= (1ULL << (h3 & 63));
}

static FORCE_INLINE bool bloom_check(const BloomFilter *bf, uint32_t hash)
{
    uint32_t h1 = hash % BLOOM_SIZE;
    uint32_t h2 = (hash * 16777619) % BLOOM_SIZE;
    uint32_t h3 = (hash * 2654435761U) % BLOOM_SIZE;
    
    return (bf->bits[h1 >> 6] & (1ULL << (h1 & 63))) &&
           (bf->bits[h2 >> 6] & (1ULL << (h2 & 63))) &&
           (bf->bits[h3 >> 6] & (1ULL << (h3 & 63)));
}

/* ==================== ROARING BITMAP WRAPPER ==================== */

#ifdef HAVE_ROARING

typedef roaring_bitmap_t RoaringBitmap;

static FORCE_INLINE RoaringBitmap* roaring_create(void)
{
    return roaring_bitmap_create();
}

static FORCE_INLINE void roaring_add(RoaringBitmap *rb, uint32_t value)
{
    roaring_bitmap_add(rb, value);
}

static FORCE_INLINE RoaringBitmap* roaring_and(const RoaringBitmap *a, const RoaringBitmap *b)
{
    return roaring_bitmap_and(a, b);
}

static FORCE_INLINE RoaringBitmap* roaring_or(const RoaringBitmap *a, const RoaringBitmap *b)
{
    return roaring_bitmap_or(a, b);
}

static FORCE_INLINE uint64_t roaring_count(const RoaringBitmap *rb)
{
    return roaring_bitmap_get_cardinality(rb);
}

static FORCE_INLINE bool roaring_is_empty(const RoaringBitmap *rb)
{
    return roaring_bitmap_is_empty(rb);
}

static FORCE_INLINE uint32_t* roaring_to_array(const RoaringBitmap *rb, uint64_t *count)
{
    *count = roaring_bitmap_get_cardinality(rb);
    if (unlikely(*count == 0)) return NULL;
    uint32_t *array = (uint32_t *)palloc(*count * sizeof(uint32_t));
    roaring_bitmap_to_uint32_array(rb, array);
    return array;
}

static FORCE_INLINE size_t roaring_size_bytes(const RoaringBitmap *rb)
{
    return roaring_bitmap_size_in_bytes(rb);
}

static FORCE_INLINE void roaring_free(RoaringBitmap *rb)
{
    if (likely(rb)) roaring_bitmap_free(rb);
}

static FORCE_INLINE RoaringBitmap* roaring_copy(const RoaringBitmap *rb)
{
    return roaring_bitmap_copy(rb);
}

#else

/* Optimized fallback bitmap */
typedef struct {
    CACHE_ALIGNED uint64_t *blocks;
    int num_blocks;
    int capacity;
    bool is_palloc;
} RoaringBitmap;

static FORCE_INLINE RoaringBitmap* roaring_create(void)
{
    RoaringBitmap *rb = (RoaringBitmap *)palloc(sizeof(RoaringBitmap));
    rb->num_blocks = 0;
    rb->capacity = 16;
    rb->blocks = (uint64_t *)palloc0(rb->capacity * sizeof(uint64_t));
    rb->is_palloc = true;
    return rb;
}

static FORCE_INLINE void roaring_add(RoaringBitmap *rb, uint32_t value)
{
    int block = value >> 6;
    int bit = value & 63;
    
    if (unlikely(block >= rb->capacity))
    {
        int new_cap = block + 1;
        rb->blocks = (uint64_t *)repalloc(rb->blocks, new_cap * sizeof(uint64_t));
        memset(rb->blocks + rb->capacity, 0, (new_cap - rb->capacity) * sizeof(uint64_t));
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
    
    if (unlikely(min_blocks == 0))
        return result;
    
    if (result->capacity < min_blocks)
    {
        result->blocks = (uint64_t *)repalloc(result->blocks, min_blocks * sizeof(uint64_t));
        result->capacity = min_blocks;
    }
    result->num_blocks = min_blocks;
    
    /* Unrolled loop */
    for (i = 0; i + 3 < min_blocks; i += 4)
    {
        PREFETCH(&a->blocks[i + 8]);
        PREFETCH(&b->blocks[i + 8]);
        result->blocks[i] = a->blocks[i] & b->blocks[i];
        result->blocks[i+1] = a->blocks[i+1] & b->blocks[i+1];
        result->blocks[i+2] = a->blocks[i+2] & b->blocks[i+2];
        result->blocks[i+3] = a->blocks[i+3] & b->blocks[i+3];
    }
    for (; i < min_blocks; i++)
        result->blocks[i] = a->blocks[i] & b->blocks[i];
    
    return result;
}

static RoaringBitmap* roaring_or(const RoaringBitmap *a, const RoaringBitmap *b)
{
    RoaringBitmap *result = roaring_create();
    int max_blocks = (a->num_blocks > b->num_blocks) ? a->num_blocks : b->num_blocks;
    int min_blocks = (a->num_blocks < b->num_blocks) ? a->num_blocks : b->num_blocks;
    int i;
    
    if (unlikely(max_blocks == 0))
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
        memcpy(result->blocks + min_blocks, a->blocks + min_blocks,
               (a->num_blocks - min_blocks) * sizeof(uint64_t));
    else if (b->num_blocks > min_blocks)
        memcpy(result->blocks + min_blocks, b->blocks + min_blocks,
               (b->num_blocks - min_blocks) * sizeof(uint64_t));
    
    return result;
}

static uint64_t roaring_count(const RoaringBitmap *rb)
{
    uint64_t count = 0;
    int i;
    
    for (i = 0; i + 3 < rb->num_blocks; i += 4)
    {
        count += __builtin_popcountll(rb->blocks[i]);
        count += __builtin_popcountll(rb->blocks[i+1]);
        count += __builtin_popcountll(rb->blocks[i+2]);
        count += __builtin_popcountll(rb->blocks[i+3]);
    }
    for (; i < rb->num_blocks; i++)
        count += __builtin_popcountll(rb->blocks[i]);
    
    return count;
}

static FORCE_INLINE bool roaring_is_empty(const RoaringBitmap *rb)
{
    for (int i = 0; i < rb->num_blocks; i++)
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
    if (unlikely(*count == 0))
        return NULL;
    
    array = (uint32_t *)palloc(*count * sizeof(uint32_t));
    
    for (i = 0; i < rb->num_blocks; i++)
    {
        bits = rb->blocks[i];
        if (!bits) continue;
        
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

/* ==================== HASH TABLE STRUCTURES ==================== */

typedef struct PosHashEntry {
    int pos;
    RoaringBitmap *bitmap;
    struct PosHashEntry *next;
} PosHashEntry;

typedef struct {
    CACHE_ALIGNED PosHashEntry *buckets[HASH_TABLE_SIZE];
} PosHashTable;

typedef struct {
    RoaringBitmap **length_bitmaps;
    int max_length;
} LengthIndex;

typedef struct CacheEntry {
    char *pattern;
    uint32_t *results;
    uint64_t count;
    uint64_t last_used;
    struct CacheEntry *next;
} CacheEntry;

typedef struct {
    CACHE_ALIGNED CacheEntry *entries[QUERY_CACHE_SIZE];
    uint64_t access_counter;
    BloomFilter bloom;
} QueryCache;

typedef struct RoaringIndex {
    CACHE_ALIGNED PosHashTable pos_idx[CHAR_RANGE];
    CACHE_ALIGNED PosHashTable neg_idx[CHAR_RANGE];
    CACHE_ALIGNED RoaringBitmap *char_cache[CHAR_RANGE];
    LengthIndex length_idx;
    QueryCache query_cache;
    
    char **data;
    int num_records;
    int max_len;
    size_t memory_used;
} RoaringIndex;

static RoaringIndex *global_index = NULL;
static MemoryContext index_context = NULL;

/* ==================== HASH FUNCTIONS ==================== */

static FORCE_INLINE uint32_t hash_position(int pos)
{
    return ((uint32_t)pos * 2654435761U) & (HASH_TABLE_SIZE - 1);
}

static FORCE_INLINE uint32_t hash_string(const char *str)
{
    uint32_t hash = 5381;
    int c;
    
    while ((c = *str++))
        hash = ((hash << 5) + hash) + c;
    
    return hash % QUERY_CACHE_SIZE;
}

/* ==================== POSITION BITMAP ACCESS (HASH TABLE) ==================== */

static FORCE_INLINE RoaringBitmap* get_pos_bitmap(unsigned char ch, int pos)
{
    uint32_t bucket = hash_position(pos);
    PosHashEntry *entry = global_index->pos_idx[ch].buckets[bucket];
    
    while (entry)
    {
        if (likely(entry->pos == pos))
            return entry->bitmap;
        entry = entry->next;
    }
    return NULL;
}

static FORCE_INLINE RoaringBitmap* get_neg_bitmap(unsigned char ch, int neg_offset)
{
    uint32_t bucket = hash_position(neg_offset);
    PosHashEntry *entry = global_index->neg_idx[ch].buckets[bucket];
    
    while (entry)
    {
        if (likely(entry->pos == neg_offset))
            return entry->bitmap;
        entry = entry->next;
    }
    return NULL;
}

static void set_pos_bitmap(unsigned char ch, int pos, RoaringBitmap *bm)
{
    uint32_t bucket = hash_position(pos);
    PosHashEntry *entry = global_index->pos_idx[ch].buckets[bucket];
    
    while (entry)
    {
        if (entry->pos == pos)
        {
            entry->bitmap = bm;
            return;
        }
        entry = entry->next;
    }
    
    entry = (PosHashEntry *)MemoryContextAlloc(index_context, sizeof(PosHashEntry));
    entry->pos = pos;
    entry->bitmap = bm;
    entry->next = global_index->pos_idx[ch].buckets[bucket];
    global_index->pos_idx[ch].buckets[bucket] = entry;
}

static void set_neg_bitmap(unsigned char ch, int neg_offset, RoaringBitmap *bm)
{
    uint32_t bucket = hash_position(neg_offset);
    PosHashEntry *entry = global_index->neg_idx[ch].buckets[bucket];
    
    while (entry)
    {
        if (entry->pos == neg_offset)
        {
            entry->bitmap = bm;
            return;
        }
        entry = entry->next;
    }
    
    entry = (PosHashEntry *)MemoryContextAlloc(index_context, sizeof(PosHashEntry));
    entry->pos = neg_offset;
    entry->bitmap = bm;
    entry->next = global_index->neg_idx[ch].buckets[bucket];
    global_index->neg_idx[ch].buckets[bucket] = entry;
}

/* ==================== QUERY CACHE ==================== */

static void init_query_cache(void)
{
    for (int i = 0; i < QUERY_CACHE_SIZE; i++)
        global_index->query_cache.entries[i] = NULL;
    global_index->query_cache.access_counter = 0;
    bloom_init(&global_index->query_cache.bloom);
}

static CacheEntry* cache_lookup(const char *pattern)
{
    uint32_t hash = hash_string(pattern);
    
    if (!bloom_check(&global_index->query_cache.bloom, hash))
        return NULL;
    
    CacheEntry *entry = global_index->query_cache.entries[hash];
    
    while (entry)
    {
        if (strcmp(entry->pattern, pattern) == 0)
        {
            entry->last_used = ++global_index->query_cache.access_counter;
            return entry;
        }
        entry = entry->next;
    }
    return NULL;
}

static void cache_insert(const char *pattern, uint32_t *results, uint64_t count)
{
    if (count > 50000) return;
    
    uint32_t hash = hash_string(pattern);
    CacheEntry *entry = (CacheEntry *)MemoryContextAlloc(index_context, sizeof(CacheEntry));
    
    entry->pattern = MemoryContextStrdup(index_context, pattern);
    entry->results = (uint32_t *)MemoryContextAlloc(index_context, count * sizeof(uint32_t));
    memcpy(entry->results, results, count * sizeof(uint32_t));
    entry->count = count;
    entry->last_used = ++global_index->query_cache.access_counter;
    
    entry->next = global_index->query_cache.entries[hash];
    global_index->query_cache.entries[hash] = entry;
    
    bloom_add(&global_index->query_cache.bloom, hash);
}

/* ==================== FORWARD DECLARATIONS ==================== */

static RoaringBitmap* get_length_range(int min_len, int max_len);

/* ==================== PATTERN ANALYSIS ==================== */

typedef struct {
    char **slices;
    int slice_count;
    bool starts_with_percent;
    bool ends_with_percent;
} PatternInfo;

static FORCE_INLINE int count_non_wildcard(const char *s)
{
    int count = 0;
    while (*s)
    {
        if (*s != '_')
            count++;
        s++;
    }
    return count;
}

/* Helper to count pattern length including underscores */
static FORCE_INLINE int pattern_length_with_underscores(const char *pattern)
{
    int len = 0;
    while (*pattern)
    {
        if (*pattern != '%')
            len++;
        pattern++;
    }
    return len;
}

static PatternInfo* analyze_pattern(const char *pattern)
{
    PatternInfo *info = (PatternInfo *)palloc(sizeof(PatternInfo));
    int plen = strlen(pattern);
    int slice_cap = 16;
    int slice_count = 0;
    const char *start = pattern;
    const char *p;
    int len;
    
    info->starts_with_percent = (plen > 0 && pattern[0] == '%');
    info->ends_with_percent = (plen > 0 && pattern[plen - 1] == '%');
    info->slices = (char **)palloc(slice_cap * sizeof(char *));
    
    for (p = pattern; *p; p++)
    {
        if (*p == '%')
        {
            len = p - start;
            if (len > 0)
            {
                if (slice_count >= slice_cap)
                {
                    slice_cap *= 2;
                    info->slices = (char **)repalloc(info->slices, slice_cap * sizeof(char *));
                }
                info->slices[slice_count++] = pnstrdup(start, len);
            }
            start = p + 1;
        }
    }
    
    len = p - start;
    if (len > 0)
    {
        if (slice_count >= slice_cap)
        {
            slice_cap *= 2;
            info->slices = (char **)repalloc(info->slices, slice_cap * sizeof(char *));
        }
        info->slices[slice_count++] = pnstrdup(start, len);
    }
    
    info->slice_count = slice_count;
    return info;
}

static void free_pattern_info(PatternInfo *info)
{
    for (int i = 0; i < info->slice_count; i++)
        pfree(info->slices[i]);
    pfree(info->slices);
    pfree(info);
}

/* ==================== OPTIMIZED MATCHING FUNCTIONS (FIXED) ==================== */

/* COMPLETELY FIXED: match_at_pos with proper validation */
static RoaringBitmap* match_at_pos(const char *pattern, int start_pos)
{
    RoaringBitmap *result = NULL;
    RoaringBitmap *char_bm, *temp;
    int pos = start_pos;
    int plen = strlen(pattern);
    int i;
    int min_required_length = start_pos + plen;
    bool has_non_underscore = false;
    
    /* Check if pattern has any non-underscore characters */
    for (i = 0; i < plen; i++)
    {
        if (pattern[i] != '_')
        {
            has_non_underscore = true;
            break;
        }
    }
    
    /* If pattern is all underscores, just return length-based matches */
    if (!has_non_underscore)
    {
        return get_length_range(min_required_length, -1);
    }
    
    /* Start with NULL result and intersect with each character constraint */
    for (i = 0; i < plen; i++)
    {
        if (pattern[i] == '_')
        {
            pos++;
            continue;
        }
        
        if (i + 1 < plen && pattern[i + 1] != '_')
            PREFETCH(get_pos_bitmap((unsigned char)pattern[i + 1], pos));
        
        char_bm = get_pos_bitmap((unsigned char)pattern[i], pos);
        if (unlikely(!char_bm))
        {
            if (result) roaring_free(result);
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
            
            if (unlikely(roaring_is_empty(result)))
                return result;
        }
        pos++;
    }
    
    /* Now intersect with length constraint to ensure string is long enough */
    if (result && min_required_length > 0)
    {
        temp = get_length_range(min_required_length, -1);
        RoaringBitmap *final = roaring_and(result, temp);
        roaring_free(result);
        roaring_free(temp);
        result = final;
    }
    
    return result ? result : roaring_create();
}

/* COMPLETELY FIXED: match_at_neg_pos with proper validation */
static RoaringBitmap* match_at_neg_pos(const char *pattern, int end_offset)
{
    RoaringBitmap *result = NULL;
    RoaringBitmap *char_bm, *temp;
    int plen = strlen(pattern);
    int i, pos;
    int min_required_length = plen;
    bool has_non_underscore = false;
    
    /* Check if pattern has any non-underscore characters */
    for (i = 0; i < plen; i++)
    {
        if (pattern[i] != '_')
        {
            has_non_underscore = true;
            break;
        }
    }
    
    /* If pattern is all underscores, just return length-based matches */
    if (!has_non_underscore)
    {
        return get_length_range(min_required_length, -1);
    }
    
    /* Start with NULL result and intersect with each character constraint */
    for (i = plen - 1; i >= 0; i--)
    {
        if (pattern[i] == '_')
        {
            continue;
        }
        
        pos = -(plen - i);
        
        if (i > 0 && pattern[i - 1] != '_')
            PREFETCH(get_neg_bitmap((unsigned char)pattern[i - 1], -(plen - i + 1)));
        
        char_bm = get_neg_bitmap((unsigned char)pattern[i], pos);
        if (unlikely(!char_bm))
        {
            if (result) roaring_free(result);
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
            
            if (unlikely(roaring_is_empty(result)))
                return result;
        }
    }
    
    /* Now intersect with length constraint to ensure string is long enough */
    if (result && min_required_length > 0)
    {
        temp = get_length_range(min_required_length, -1);
        RoaringBitmap *final = roaring_and(result, temp);
        roaring_free(result);
        roaring_free(temp);
        result = final;
    }
    
    return result ? result : roaring_create();
}

static RoaringBitmap* get_char_candidates(const char *pattern)
{
    RoaringBitmap *result = NULL;
    RoaringBitmap *temp;
    bool seen[CHAR_RANGE] = {false};
    int i;
    
    for (i = 0; pattern[i]; i++)
    {
        unsigned char ch = (unsigned char)pattern[i];
        if (pattern[i] != '_' && pattern[i] != '%' && !seen[ch])
        {
            seen[ch] = true;
            
            if (pattern[i + 1])
                PREFETCH(global_index->char_cache[(unsigned char)pattern[i + 1]]);
            
            if (likely(global_index->char_cache[ch]))
            {
                if (!result)
                {
                    result = roaring_copy(global_index->char_cache[ch]);
                }
                else
                {
                    temp = roaring_and(result, global_index->char_cache[ch]);
                    roaring_free(result);
                    result = temp;
                    
                    if (unlikely(roaring_is_empty(result)))
                        return result;
                }
            }
            else
            {
                if (result) roaring_free(result);
                return roaring_create();
            }
        }
    }
    
    return result;
}

/* Optimized contiguous pattern matching */
static FORCE_INLINE bool matches_at_position(const char *str, const char *pattern)
{
    const char *s = str;
    const char *p = pattern;
    
    while (*p)
    {
        if (*p == '_')
        {
            if (unlikely(!*s)) return false;
            s++;
            p++;
        }
        else if (likely(*s == *p))
        {
            s++;
            p++;
        }
        else
        {
            return false;
        }
    }
    
    return true;
}

static FORCE_INLINE const char* find_pattern(const char *str, const char *pattern)
{
    const char *s = str;
    
    while (*s)
    {
        PREFETCH(s + 64);
        if (matches_at_position(s, pattern))
            return s;
        s++;
    }
    
    return NULL;
}

static FORCE_INLINE bool contains_substring(const char *str, const char *pattern)
{
    return find_pattern(str, pattern) != NULL;
}

static RoaringBitmap* verify_multislice_pattern(RoaringBitmap *candidates, PatternInfo *info)
{
    uint64_t count, i, j;
    uint32_t *indices;
    uint32_t idx;
    const char *str;
    const char *search_start;
    const char *match_pos;
    const char *slice_ptr;
    bool all_found;
    RoaringBitmap *verified = roaring_create();
    
    indices = roaring_to_array(candidates, &count);
    
    if (!indices)
        return verified;
    
    for (i = 0; i < count; i++)
    {
        idx = indices[i];
        
        if (i + 1 < count)
            PREFETCH(global_index->data[indices[i + 1]]);
        
        str = global_index->data[idx];
        search_start = str;
        all_found = true;
        
        for (j = 0; j < info->slice_count; j++)
        {
            const char *slice = info->slices[j];
            
            match_pos = find_pattern(search_start, slice);
            
            if (unlikely(!match_pos))
            {
                all_found = false;
                break;
            }
            
            search_start = match_pos;
            slice_ptr = slice;
            while (*search_start && *slice_ptr)
            {
                if (*slice_ptr == '_' || *search_start == *slice_ptr)
                {
                    search_start++;
                    slice_ptr++;
                }
                else
                {
                    break;
                }
            }
        }
        
        if (likely(all_found))
            roaring_add(verified, idx);
    }
    
    pfree(indices);
    return verified;
}

static RoaringBitmap* get_length_range(int min_len, int max_len)
{
    RoaringBitmap *result = roaring_create();
    RoaringBitmap *temp_union;
    int len;
    
    if (max_len < 0 || max_len > global_index->length_idx.max_length)
        max_len = global_index->length_idx.max_length - 1;
    
    for (len = min_len; len <= max_len; len++)
    {
        if (global_index->length_idx.length_bitmaps[len])
        {
            temp_union = roaring_or(result, global_index->length_idx.length_bitmaps[len]);
            roaring_free(result);
            result = temp_union;
        }
    }
    
    return result;
}

/* ==================== MAIN QUERY FUNCTION (FULLY FIXED) ==================== */

static uint32_t* optimized_query(const char *pattern, uint64_t *result_count)
{
    PatternInfo *info;
    RoaringBitmap *result = NULL;
    RoaringBitmap *temp, *candidates, *temp2, *temp3;
    uint32_t *indices;
    uint32_t *cand_indices;
    uint64_t i, cand_count;
    int min_len;
    
    /* Check cache first */
    CacheEntry *cached = cache_lookup(pattern);
    if (cached)
    {
        indices = (uint32_t *)palloc(cached->count * sizeof(uint32_t));
        memcpy(indices, cached->results, cached->count * sizeof(uint32_t));
        *result_count = cached->count;
        return indices;
    }
    
    /* Pattern: % - match all */
    if (strcmp(pattern, "%") == 0)
    {
        indices = (uint32_t *)palloc(global_index->num_records * sizeof(uint32_t));
        for (i = 0; i < global_index->num_records; i++)
            indices[i] = (uint32_t)i;
        *result_count = global_index->num_records;
        return indices;
    }
    
    info = analyze_pattern(pattern);
    
    /* No slices - only % characters */
    if (info->slice_count == 0)
    {
        free_pattern_info(info);
        indices = (uint32_t *)palloc(global_index->num_records * sizeof(uint32_t));
        for (i = 0; i < global_index->num_records; i++)
            indices[i] = (uint32_t)i;
        *result_count = global_index->num_records;
        return indices;
    }
    
    /* Single slice */
    if (info->slice_count == 1)
    {
        const char *slice = info->slices[0];
        int exact_length = pattern_length_with_underscores(slice);
        
        candidates = get_char_candidates(slice);
        if (unlikely(roaring_is_empty(candidates)))
        {
            free_pattern_info(info);
            roaring_free(candidates);
            *result_count = 0;
            return NULL;
        }
        
        /* FIXED: Case: pattern (exact match - no % at all) */
        if (!info->starts_with_percent && !info->ends_with_percent)
        {
            result = match_at_pos(slice, 0);
            
            /* For exact match, string length must EXACTLY equal pattern length */
            if (exact_length < global_index->length_idx.max_length && 
                global_index->length_idx.length_bitmaps[exact_length])
            {
                temp = roaring_and(result, global_index->length_idx.length_bitmaps[exact_length]);
                roaring_free(result);
                result = temp;
            }
            else
            {
                /* No strings of this exact length exist */
                roaring_free(result);
                result = roaring_create();
            }
        }
        /* FIXED: Case: pattern% (starts at position 0, but can be longer) */
        else if (!info->starts_with_percent && info->ends_with_percent)
        {
            /* match_at_pos now only applies minimum length constraint */
            result = match_at_pos(slice, 0);
            temp = roaring_and(result, candidates);
            roaring_free(result);
            result = temp;
        }
        /* FIXED: Case: %pattern (ends at last position, but can be longer) */
        else if (info->starts_with_percent && !info->ends_with_percent)
        {
            /* match_at_neg_pos now only applies minimum length constraint */
            result = match_at_neg_pos(slice, 0);
            temp = roaring_and(result, candidates);
            roaring_free(result);
            result = temp;
        }
        /* Case: %pattern% (substring match) */
        else
        {
            result = roaring_create();
            cand_indices = roaring_to_array(candidates, &cand_count);
            
            if (cand_indices)
            {
                for (i = 0; i < cand_count; i++)
                {
                    uint32_t idx = cand_indices[i];
                    
                    if (i + 1 < cand_count)
                        PREFETCH(global_index->data[cand_indices[i + 1]]);
                    
                    const char *str = global_index->data[idx];
                    
                    if (contains_substring(str, slice))
                        roaring_add(result, idx);
                }
                pfree(cand_indices);
            }
        }
        
        roaring_free(candidates);
    }
    /* Multiple slices */
    else
    {
        /* Calculate min length */
        min_len = 0;
        for (i = 0; i < info->slice_count; i++)
            min_len += pattern_length_with_underscores(info->slices[i]);
        
        /* Get candidates with all required characters */
        candidates = NULL;
        
        for (i = 0; i < info->slice_count; i++)
        {
            temp = get_char_candidates(info->slices[i]);
            if (!candidates)
            {
                candidates = temp;
            }
            else
            {
                temp2 = roaring_and(candidates, temp);
                roaring_free(candidates);
                roaring_free(temp);
                candidates = temp2;
            }
            
            if (unlikely(roaring_is_empty(candidates)))
            {
                roaring_free(candidates);
                free_pattern_info(info);
                *result_count = 0;
                return NULL;
            }
        }
        
        /* Apply length constraint */
        temp = get_length_range(min_len, -1);
        result = roaring_and(candidates, temp);
        roaring_free(candidates);
        roaring_free(temp);
        
        if (unlikely(roaring_is_empty(result)))
        {
            roaring_free(result);
            free_pattern_info(info);
            *result_count = 0;
            return NULL;
        }
        
        /* Apply anchor constraints */
        if (!info->starts_with_percent)
        {
            temp = match_at_pos(info->slices[0], 0);
            temp3 = roaring_and(result, temp);
            roaring_free(result);
            roaring_free(temp);
            result = temp3;
            
            if (unlikely(roaring_is_empty(result)))
            {
                roaring_free(result);
                free_pattern_info(info);
                *result_count = 0;
                return NULL;
            }
        }
        
        if (!info->ends_with_percent)
        {
            temp = match_at_neg_pos(info->slices[info->slice_count - 1], 0);
            temp3 = roaring_and(result, temp);
            roaring_free(result);
            roaring_free(temp);
            result = temp3;
            
            if (unlikely(roaring_is_empty(result)))
            {
                roaring_free(result);
                free_pattern_info(info);
                *result_count = 0;
                return NULL;
            }
        }
        
        /* Verify multi-slice patterns with contiguous matching */
        RoaringBitmap *verified = verify_multislice_pattern(result, info);
        roaring_free(result);
        result = verified;
    }
    
    free_pattern_info(info);
    
    indices = roaring_to_array(result, result_count);
    roaring_free(result);
    
    /* Cache results */
    if (indices && *result_count > 0 && *result_count < 50000)
        cache_insert(pattern, indices, *result_count);
    
    return indices;
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
    int neg_offset;
    
    INSTR_TIME_SET_CURRENT(start_time);
    elog(INFO, "Building ULTIMATE optimized index (hash tables + hardware opts)...");
    
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
    
    /* Initialize hash tables */
    for (ch_idx = 0; ch_idx < CHAR_RANGE; ch_idx++)
    {
        memset(global_index->pos_idx[ch_idx].buckets, 0, sizeof(PosHashEntry*) * HASH_TABLE_SIZE);
        memset(global_index->neg_idx[ch_idx].buckets, 0, sizeof(PosHashEntry*) * HASH_TABLE_SIZE);
        global_index->char_cache[ch_idx] = NULL;
    }
    
    global_index->length_idx.max_length = 0;
    global_index->length_idx.length_bitmaps = NULL;
    init_query_cache();
    
    elog(INFO, "Initialized index structures (hash tables, cache, bloom filter)");
    
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
            neg_offset = -(1 + pos);
            uch = (unsigned char)str[len - 1 - pos];
            
            existing_bm = get_neg_bitmap(uch, neg_offset);
            if (!existing_bm)
            {
                existing_bm = roaring_create();
                set_neg_bitmap(uch, neg_offset, existing_bm);
            }
            roaring_add(existing_bm, (uint32_t)idx);
        }
        
        pfree(str);
    }
    
    elog(INFO, "Index building complete, building char cache...");
    
    /* Build character cache */
    for (ch_idx = 0; ch_idx < CHAR_RANGE; ch_idx++)
    {
        RoaringBitmap *char_bm = NULL;
        
        for (int bucket = 0; bucket < HASH_TABLE_SIZE; bucket++)
        {
            PosHashEntry *entry = global_index->pos_idx[ch_idx].buckets[bucket];
            while (entry)
            {
                if (!char_bm)
                {
                    char_bm = roaring_copy(entry->bitmap);
                }
                else
                {
                    RoaringBitmap *temp = roaring_or(char_bm, entry->bitmap);
                    roaring_free(char_bm);
                    char_bm = temp;
                }
                entry = entry->next;
            }
        }
        
        if (char_bm)
            global_index->char_cache[ch_idx] = char_bm;
    }
    
    elog(INFO, "Character cache complete");
    
    /* Build length index */
    elog(INFO, "Building length index...");
    global_index->length_idx.max_length = global_index->max_len + 1;
    global_index->length_idx.length_bitmaps = (RoaringBitmap **)MemoryContextAlloc(
        index_context, 
        global_index->length_idx.max_length * sizeof(RoaringBitmap *)
    );
    
    for (i = 0; i < global_index->length_idx.max_length; i++)
        global_index->length_idx.length_bitmaps[i] = NULL;
    
    for (idx = 0; idx < num_records; idx++)
    {
        len = strlen(global_index->data[idx]);
        if (len >= global_index->length_idx.max_length)
            continue;
        
        if (!global_index->length_idx.length_bitmaps[len])
            global_index->length_idx.length_bitmaps[len] = roaring_create();
        
        roaring_add(global_index->length_idx.length_bitmaps[len], (uint32_t)idx);
    }
    
    elog(INFO, "Length index complete");
    
    /* Calculate memory usage */
    global_index->memory_used = sizeof(RoaringIndex);
    for (ch_idx = 0; ch_idx < CHAR_RANGE; ch_idx++)
    {
        if (global_index->char_cache[ch_idx])
            global_index->memory_used += roaring_size_bytes(global_index->char_cache[ch_idx]);
    }
    for (i = 0; i < global_index->length_idx.max_length; i++)
    {
        if (global_index->length_idx.length_bitmaps[i])
            global_index->memory_used += roaring_size_bytes(global_index->length_idx.length_bitmaps[i]);
    }
    
    MemoryContextSwitchTo(oldcontext);
    SPI_finish();
    
    INSTR_TIME_SET_CURRENT(end_time);
    INSTR_TIME_SUBTRACT(end_time, start_time);
    ms = INSTR_TIME_GET_MILLISEC(end_time);
    
    elog(INFO, "Build time: %.0f ms", ms);
    elog(INFO, "Index: %d records, max_len=%d, memory=%zu bytes (%.2f MB)",
         num_records, global_index->max_len, global_index->memory_used,
         global_index->memory_used / (1024.0 * 1024.0));
    elog(INFO, "Optimizations: Hash tables (4096 buckets), prefetch, bloom filter, cache (%d slots)",
         QUERY_CACHE_SIZE);
    
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
    appendStringInfo(&buf, "ULTIMATE Roaring Bitmap Index Status:\n");
    appendStringInfo(&buf, "  Records: %d\n", global_index->num_records);
    appendStringInfo(&buf, "  Max length: %d\n", global_index->max_len);
    appendStringInfo(&buf, "  Memory used: %zu bytes (%.2f MB)\n", 
                    global_index->memory_used,
                    global_index->memory_used / (1024.0 * 1024.0));
    appendStringInfo(&buf, "\nOptimizations:\n");
    appendStringInfo(&buf, "  - Hash tables: %d buckets/char (O(1) lookup)\n", HASH_TABLE_SIZE);
    appendStringInfo(&buf, "  - Query cache: %d slots with bloom filter\n", QUERY_CACHE_SIZE);
    appendStringInfo(&buf, "  - CPU prefetching & branch hints\n");
    appendStringInfo(&buf, "  - Cache-aligned structures (64 bytes)\n");
    appendStringInfo(&buf, "  - Loop unrolling (4x)\n");
    appendStringInfo(&buf, "  - Contiguous pattern matching\n");
    appendStringInfo(&buf, "  - Hardware popcount (SIMD)\n");
    appendStringInfo(&buf, "  - FIXED: Proper length constraints for all patterns\n");
    appendStringInfo(&buf, "\nSupported: '%%' (multi-char), '_' (single-char)\n");
    
    #ifdef HAVE_ROARING
    appendStringInfo(&buf, "Backend: Native CRoaring library\n");
    #else
    appendStringInfo(&buf, "Backend: Optimized fallback bitmap\n");
    #endif
    
    PG_RETURN_TEXT_P(cstring_to_text(buf.data));
}

PG_FUNCTION_INFO_V1(optimized_like_clear_cache);
Datum optimized_like_clear_cache(PG_FUNCTION_ARGS)
{
    if (!global_index)
        PG_RETURN_TEXT_P(cstring_to_text("No index loaded."));
    
    init_query_cache();
    
    PG_RETURN_TEXT_P(cstring_to_text("Query cache cleared successfully."));
}