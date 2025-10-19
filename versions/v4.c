/*
 * optimized_like_roaring.c
 * PostgreSQL extension with Roaring Bitmap optimization
 * FIXED: Overcounting and redundant logic issues
 * 
 * KEY FIXES:
 * 1. Removed duplicate matches in moving window unions
 * 2. Added proper length constraints for all pattern types
 * 3. Eliminated redundant slice processing
 * 4. Fixed exact match logic
 * 5. Proper candidate filtering before expensive operations
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

typedef struct {
    RoaringBitmap **length_bitmaps;
    int max_length;
} LengthIndex;

typedef struct RoaringIndex {
    CharIndex pos_idx[CHAR_RANGE];
    CharIndex neg_idx[CHAR_RANGE];
    RoaringBitmap *char_cache[CHAR_RANGE];
    LengthIndex length_idx;
    
    char **data;
    int num_records;
    int max_len;
    size_t memory_used;
} RoaringIndex;

static RoaringIndex *global_index = NULL;
static MemoryContext index_context = NULL;

/* Find pos_idx bitmap for (ch, pos) */
static RoaringBitmap* get_pos_bitmap(unsigned char ch, int pos)
{
    CharIndex *cidx = &global_index->pos_idx[ch];
    int i;
    
    for (i = 0; i < cidx->count; i++)
        if (cidx->entries[i].pos == pos)
            return cidx->entries[i].bitmap;
    
    return NULL;
}

/* Find neg_idx bitmap for (ch, neg_pos) */
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

/* ==================== PATTERN ANALYSIS ==================== */

typedef struct {
    char **slices;
    int slice_count;
    bool starts_with_percent;
    bool ends_with_percent;
    int total_pattern_len;  /* Sum of all slice lengths */
} PatternInfo;

static int count_non_wildcard_chars(const char *pattern)
{
    int count = 0;
    while (*pattern)
    {
        if (*pattern != '%' && *pattern != '_')
            count++;
        pattern++;
    }
    return count;
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
    info->total_pattern_len = 0;
    
    info->slices = (char **)palloc(slice_cap * sizeof(char *));
    
    /* Split by % */
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
                info->slices[slice_count] = pnstrdup(start, len);
                info->total_pattern_len += count_non_wildcard_chars(info->slices[slice_count]);
                slice_count++;
            }
            start = p + 1;
        }
    }
    
    /* Add final slice if any */
    len = p - start;
    if (len > 0)
    {
        if (slice_count >= slice_cap)
        {
            slice_cap *= 2;
            info->slices = (char **)repalloc(info->slices, slice_cap * sizeof(char *));
        }
        info->slices[slice_count] = pnstrdup(start, len);
        info->total_pattern_len += count_non_wildcard_chars(info->slices[slice_count]);
        slice_count++;
    }
    
    info->slice_count = slice_count;
    return info;
}

static void free_pattern_info(PatternInfo *info)
{
    int i;
    for (i = 0; i < info->slice_count; i++)
        pfree(info->slices[i]);
    pfree(info->slices);
    pfree(info);
}

/* ==================== HELPER FUNCTIONS ==================== */

/* Get length constraint bitmap: strings with length >= min_len */
static RoaringBitmap* get_min_length_bitmap(int min_len)
{
    RoaringBitmap *result = roaring_create();
    int len;
    
    for (len = min_len; len < global_index->length_idx.max_length; len++)
    {
        if (global_index->length_idx.length_bitmaps[len])
        {
            RoaringBitmap *temp = roaring_or(result, global_index->length_idx.length_bitmaps[len]);
            roaring_free(result);
            result = temp;
        }
    }
    return result;
}

/* Check if string matches pattern (for verification) */
static bool string_matches_pattern(const char *str, const char *pattern)
{
    const char *s = str;
    const char *p = pattern;
    const char *star = NULL;
    const char *ss = NULL;
    
    while (*s)
    {
        if (*p == '%')
        {
            star = p++;
            ss = s;
        }
        else if (*p == '_' || *p == *s)
        {
            p++;
            s++;
        }
        else if (star)
        {
            p = star + 1;
            s = ++ss;
        }
        else
        {
            return false;
        }
    }
    
    while (*p == '%')
        p++;
    
    return *p == '\0';
}

/* ==================== CORE MATCHING FUNCTIONS ==================== */

/* Intersect pattern at positive offset, handling '_' wildcards */
static RoaringBitmap* intersect_pattern_pos(const char *pattern, int start_offset)
{
    RoaringBitmap *result = NULL;
    int offset = start_offset;
    int i, plen = strlen(pattern);
    RoaringBitmap *char_bm, *temp;
    
    for (i = 0; i < plen; i++)
    {
        if (pattern[i] == '_')
        {
            offset++;
            continue;
        }
        
        char_bm = get_pos_bitmap((unsigned char)pattern[i], offset);
        if (!char_bm)
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
        offset++;
    }
    
    return result ? result : roaring_create();
}

/* Intersect pattern at negative offset, handling '_' wildcards */
static RoaringBitmap* intersect_pattern_neg(const char *pattern, int end_offset)
{
    RoaringBitmap *result = NULL;
    int offset = end_offset - 1;
    int i, plen = strlen(pattern);
    RoaringBitmap *char_bm, *temp;
    
    for (i = plen - 1; i >= 0; i--)
    {
        if (pattern[i] == '_')
        {
            offset--;
            continue;
        }
        
        char_bm = get_neg_bitmap((unsigned char)pattern[i], offset);
        if (!char_bm)
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
        offset--;
    }
    
    return result ? result : roaring_create();
}

/* Verify candidates by actual string matching (eliminates false positives) */
static RoaringBitmap* verify_candidates(RoaringBitmap *candidates, const char *pattern)
{
    uint64_t count, i;
    uint32_t *indices = roaring_to_array(candidates, &count);
    RoaringBitmap *verified = roaring_create();
    
    if (!indices)
        return verified;
    
    for (i = 0; i < count; i++)
    {
        uint32_t idx = indices[i];
        if (string_matches_pattern(global_index->data[idx], pattern))
            roaring_add(verified, idx);
    }
    
    pfree(indices);
    return verified;
}

/* ==================== MAIN QUERY FUNCTION ==================== */

static uint32_t* optimized_query(const char *pattern, uint64_t *result_count)
{
    PatternInfo *info;
    RoaringBitmap *result = NULL;
    RoaringBitmap *temp, *verified;
    uint32_t *indices;
    int i, plen = strlen(pattern);
    int pattern_len;
    RoaringBitmap *len_constraint;
    
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
    
    /* Apply minimum length constraint */
    len_constraint = get_min_length_bitmap(info->total_pattern_len);
    
    /* Single slice */
    if (info->slice_count == 1)
    {
        const char *slice = info->slices[0];
        pattern_len = strlen(slice);
        
        /* Case: %pattern */
        if (info->starts_with_percent && !info->ends_with_percent)
        {
            result = intersect_pattern_neg(slice, 0);
            temp = roaring_and(result, len_constraint);
            roaring_free(result);
            result = temp;
        }
        /* Case: pattern% */
        else if (!info->starts_with_percent && info->ends_with_percent)
        {
            result = intersect_pattern_pos(slice, 0);
            temp = roaring_and(result, len_constraint);
            roaring_free(result);
            result = temp;
        }
        /* Case: %pattern% */
        else if (info->starts_with_percent && info->ends_with_percent)
        {
            /* Use char-anywhere cache for initial filtering */
            result = roaring_create();
            for (i = 0; i < global_index->num_records; i++)
                roaring_add(result, i);
            
            for (i = 0; i < pattern_len; i++)
            {
                if (slice[i] != '_' && global_index->char_cache[(unsigned char)slice[i]])
                {
                    temp = roaring_and(result, global_index->char_cache[(unsigned char)slice[i]]);
                    roaring_free(result);
                    result = temp;
                    
                    if (roaring_is_empty(result))
                        break;
                }
            }
            
            /* Apply length constraint */
            temp = roaring_and(result, len_constraint);
            roaring_free(result);
            result = temp;
            
            /* Verify with actual string matching */
            if (!roaring_is_empty(result))
            {
                verified = verify_candidates(result, pattern);
                roaring_free(result);
                result = verified;
            }
        }
        /* Case: pattern (exact match) */
        else
        {
            result = intersect_pattern_pos(slice, 0);
            
            /* Must match exact length */
            if (pattern_len < global_index->length_idx.max_length && 
                global_index->length_idx.length_bitmaps[pattern_len])
            {
                temp = roaring_and(result, global_index->length_idx.length_bitmaps[pattern_len]);
                roaring_free(result);
                result = temp;
            }
            else
            {
                roaring_free(result);
                result = roaring_create();
            }
        }
    }
    /* Multiple slices - always verify to avoid overcounting */
    else
    {
        /* Start with length constraint */
        result = roaring_copy(len_constraint);
        
        /* Filter by char-anywhere cache for all unique chars */
        bool seen[CHAR_RANGE] = {false};
        for (i = 0; i < info->slice_count; i++)
        {
            const char *slice = info->slices[i];
            int j;
            for (j = 0; slice[j]; j++)
            {
                unsigned char ch = (unsigned char)slice[j];
                if (slice[j] != '_' && !seen[ch] && global_index->char_cache[ch])
                {
                    seen[ch] = true;
                    temp = roaring_and(result, global_index->char_cache[ch]);
                    roaring_free(result);
                    result = temp;
                    
                    if (roaring_is_empty(result))
                        goto cleanup;
                }
            }
        }
        
        /* Apply anchor constraints */
        if (!info->starts_with_percent)
        {
            /* First slice must be at position 0 */
            temp = intersect_pattern_pos(info->slices[0], 0);
            RoaringBitmap *temp2 = roaring_and(result, temp);
            roaring_free(result);
            roaring_free(temp);
            result = temp2;
            
            if (roaring_is_empty(result))
                goto cleanup;
        }
        
        if (!info->ends_with_percent)
        {
            /* Last slice must end at string end */
            temp = intersect_pattern_neg(info->slices[info->slice_count - 1], 0);
            RoaringBitmap *temp2 = roaring_and(result, temp);
            roaring_free(result);
            roaring_free(temp);
            result = temp2;
            
            if (roaring_is_empty(result))
                goto cleanup;
        }
        
        /* Verify all candidates with actual string matching */
        verified = verify_candidates(result, pattern);
        roaring_free(result);
        result = verified;
    }
    
cleanup:
    roaring_free(len_constraint);
    free_pattern_info(info);
    
    indices = roaring_to_array(result, result_count);
    roaring_free(result);
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
    
    /* Initialize length index */
    global_index->length_idx.max_length = 0;
    global_index->length_idx.length_bitmaps = NULL;
    
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
    appendStringInfo(&buf, "  Supports: '%%' (multi-char wildcard), '_' (single-char wildcard)\n");
    
    #ifdef HAVE_ROARING
    appendStringInfo(&buf, "  Backend: Native Roaring library\n");
    #else
    appendStringInfo(&buf, "  Backend: Fallback bitmap implementation\n");
    #endif
    
    PG_RETURN_TEXT_P(cstring_to_text(buf.data));
}
