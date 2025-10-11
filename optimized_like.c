/*
 * optimized_like.c
 * PostgreSQL extension for optimized wildcard matching
 * DEBUGGED AND SYNTAX-CORRECTED VERSION
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

#ifdef PG_MODULE_MAGIC
PG_MODULE_MAGIC;
#endif

/* ==================== BITMAP IMPLEMENTATION ==================== */

typedef struct Bitmap {
    uint64_t *blocks;
    int num_blocks;
    int capacity;
} Bitmap;

static Bitmap* bitmap_create(int size)
{
    Bitmap *bm;
    
    bm = (Bitmap *)palloc(sizeof(Bitmap));
    bm->num_blocks = (size + 63) >> 6;
    bm->capacity = bm->num_blocks;
    bm->blocks = (uint64_t *)palloc0(bm->num_blocks * sizeof(uint64_t));
    return bm;
}

static void bitmap_set(Bitmap *bm, int pos)
{
    int block;
    int bit;
    int new_capacity;
    int i;
    
    block = pos >> 6;
    bit = pos & 63;
    
    if (block >= bm->capacity)
    {
        new_capacity = block + 1;
        bm->blocks = (uint64_t *)repalloc(bm->blocks, new_capacity * sizeof(uint64_t));
        for (i = bm->capacity; i < new_capacity; i++)
        {
            bm->blocks[i] = 0;
        }
        bm->capacity = new_capacity;
        bm->num_blocks = new_capacity;
    }
    bm->blocks[block] |= (1ULL << bit);
}

static Bitmap* bitmap_and(const Bitmap *a, const Bitmap *b)
{
    size_t min_size;
    Bitmap *result;
    size_t i;
    
    min_size = (a->num_blocks < b->num_blocks) ? a->num_blocks : b->num_blocks;
    if (min_size == 0)
    {
        return bitmap_create(0);
    }
    
    result = bitmap_create(min_size * 64);
    result->num_blocks = min_size;
    
    for (i = 0; i < min_size; i++)
    {
        result->blocks[i] = a->blocks[i] & b->blocks[i];
    }
    return result;
}

static Bitmap* bitmap_or(const Bitmap *a, const Bitmap *b)
{
    Bitmap *copy;
    size_t max_size;
    size_t min_size;
    Bitmap *result;
    size_t i;
    
    if (!a || a->num_blocks == 0)
    {
        copy = bitmap_create(b->num_blocks * 64);
        memcpy(copy->blocks, b->blocks, b->num_blocks * sizeof(uint64_t));
        copy->num_blocks = b->num_blocks;
        return copy;
    }
    if (!b || b->num_blocks == 0)
    {
        copy = bitmap_create(a->num_blocks * 64);
        memcpy(copy->blocks, a->blocks, a->num_blocks * sizeof(uint64_t));
        copy->num_blocks = a->num_blocks;
        return copy;
    }
    
    max_size = (a->num_blocks > b->num_blocks) ? a->num_blocks : b->num_blocks;
    min_size = (a->num_blocks < b->num_blocks) ? a->num_blocks : b->num_blocks;
    
    result = bitmap_create(max_size * 64);
    result->num_blocks = max_size;
    
    for (i = 0; i < min_size; i++)
    {
        result->blocks[i] = a->blocks[i] | b->blocks[i];
    }
    
    if (a->num_blocks > min_size)
    {
        memcpy(result->blocks + min_size, a->blocks + min_size,
               (a->num_blocks - min_size) * sizeof(uint64_t));
    }
    else if (b->num_blocks > min_size)
    {
        memcpy(result->blocks + min_size, b->blocks + min_size,
               (b->num_blocks - min_size) * sizeof(uint64_t));
    }
    
    return result;
}

static int* bitmap_to_indices(const Bitmap *bm, int *count)
{
    size_t est;
    int i;
    int *result;
    int idx;
    size_t block;
    uint64_t bits;
    int base;
    
    est = 0;
    for (i = 0; i < bm->num_blocks; i++)
    {
        est += __builtin_popcountll(bm->blocks[i]);
    }
    
    if (est == 0)
    {
        *count = 0;
        return NULL;
    }
    
    result = (int *)palloc(est * sizeof(int));
    idx = 0;
    
    for (block = 0; block < bm->num_blocks; block++)
    {
        bits = bm->blocks[block];
        if (!bits) continue;
        
        base = block << 6;
        while (bits)
        {
            result[idx++] = base + __builtin_ctzll(bits);
            bits &= bits - 1;
        }
    }
    
    *count = est;
    return result;
}

static bool bitmap_empty(const Bitmap *bm)
{
    int i;
    
    for (i = 0; i < bm->num_blocks; i++)
    {
        if (bm->blocks[i]) return false;
    }
    return true;
}

static void bitmap_set_all(Bitmap *bm, int size)
{
    int full_blocks;
    int remaining;
    int i;
    
    bm->num_blocks = (size + 63) >> 6;
    if (bm->num_blocks > bm->capacity)
    {
        bm->blocks = (uint64_t *)repalloc(bm->blocks, bm->num_blocks * sizeof(uint64_t));
        bm->capacity = bm->num_blocks;
    }
    
    full_blocks = size >> 6;
    for (i = 0; i < full_blocks; i++)
    {
        bm->blocks[i] = UINT64_MAX;
    }
    
    remaining = size & 63;
    if (remaining && full_blocks < bm->num_blocks)
    {
        bm->blocks[full_blocks] = (1ULL << remaining) - 1;
    }
}

/* ==================== INDEX STRUCTURES ==================== */

#define MAX_POSITIONS 256
#define CHAR_RANGE 256

typedef struct OptimizedIndex {
    Bitmap **pos_idx;
    Bitmap **neg_idx;
    Bitmap *char_cache;
    
    char **data;
    int num_records;
    int max_len;
} OptimizedIndex;

static OptimizedIndex *global_index = NULL;
static MemoryContext index_context = NULL;

/* Get bitmap from pos_idx */
static Bitmap* get_pos_bitmap(char ch, int pos)
{
    int idx;
    unsigned char uch;
    
    uch = (unsigned char)ch;
    if (pos < 0 || pos >= MAX_POSITIONS) return NULL;
    
    idx = uch * MAX_POSITIONS + pos;
    return global_index->pos_idx[idx];
}

/* Set bitmap in pos_idx */
static void set_pos_bitmap(char ch, int pos, Bitmap *bm)
{
    int idx;
    unsigned char uch;
    
    uch = (unsigned char)ch;
    if (pos < 0 || pos >= MAX_POSITIONS) return;
    
    idx = uch * MAX_POSITIONS + pos;
    global_index->pos_idx[idx] = bm;
}

/* Get bitmap from neg_idx */
static Bitmap* get_neg_bitmap(char ch, int neg_pos)
{
    int idx;
    unsigned char uch;
    int actual_pos;
    
    uch = (unsigned char)ch;
    actual_pos = -neg_pos - 1;
    if (actual_pos < 0 || actual_pos >= MAX_POSITIONS) return NULL;
    
    idx = uch * MAX_POSITIONS + actual_pos;
    return global_index->neg_idx[idx];
}

/* Set bitmap in neg_idx */
static void set_neg_bitmap(char ch, int neg_pos, Bitmap *bm)
{
    int idx;
    unsigned char uch;
    int actual_pos;
    
    uch = (unsigned char)ch;
    actual_pos = -neg_pos - 1;
    if (actual_pos < 0 || actual_pos >= MAX_POSITIONS) return;
    
    idx = uch * MAX_POSITIONS + actual_pos;
    global_index->neg_idx[idx] = bm;
}

/* ==================== PATTERN MATCHING ==================== */

static bool match_pattern(const char *s, const char *p)
{
    int si;
    int pi;
    int star;
    int match;
    int slen;
    int plen;
    
    si = 0;
    pi = 0;
    star = -1;
    match = 0;
    slen = strlen(s);
    plen = strlen(p);
    
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
        {
            return false;
        }
    }
    
    while (pi < plen && p[pi] == '%')
    {
        pi++;
    }
    
    return pi == plen;
}

/* ==================== QUERY FUNCTIONS ==================== */

static int* query_prefix(const char *prefix, int *result_count)
{
    Bitmap *result;
    int prefix_len;
    int i;
    Bitmap *char_bm;
    int *indices;
    
    result = bitmap_create(global_index->num_records);
    bitmap_set_all(result, global_index->num_records);
    
    prefix_len = strlen(prefix);
    for (i = 0; i < prefix_len; i++)
    {
        if (prefix[i] == '_') continue;
        
        char_bm = get_pos_bitmap(prefix[i], i);
        if (char_bm)
        {
            result = bitmap_and(result, char_bm);
            if (bitmap_empty(result))
            {
                *result_count = 0;
                return NULL;
            }
        }
        else
        {
            *result_count = 0;
            return NULL;
        }
    }
    
    indices = bitmap_to_indices(result, result_count);
    return indices;
}

static int* query_suffix(const char *suffix, int *result_count)
{
    Bitmap *result;
    int suffix_len;
    int i;
    char ch;
    Bitmap *char_bm;
    int *indices;
    
    result = bitmap_create(global_index->num_records);
    bitmap_set_all(result, global_index->num_records);
    
    suffix_len = strlen(suffix);
    for (i = 0; i < suffix_len; i++)
    {
        ch = suffix[suffix_len - 1 - i];
        if (ch == '_') continue;
        
        char_bm = get_neg_bitmap(ch, -1 - i);
        if (char_bm)
        {
            result = bitmap_and(result, char_bm);
            if (bitmap_empty(result))
            {
                *result_count = 0;
                return NULL;
            }
        }
        else
        {
            *result_count = 0;
            return NULL;
        }
    }
    
    indices = bitmap_to_indices(result, result_count);
    return indices;
}

static int* query_dual(const char *prefix, const char *suffix, int *result_count)
{
    Bitmap *result;
    int prefix_len;
    int suffix_len;
    int i;
    Bitmap *char_bm;
    char ch;
    int *indices;
    
    result = bitmap_create(global_index->num_records);
    bitmap_set_all(result, global_index->num_records);
    
    /* Apply prefix constraints */
    prefix_len = strlen(prefix);
    for (i = 0; i < prefix_len; i++)
    {
        if (prefix[i] == '_') continue;
        
        char_bm = get_pos_bitmap(prefix[i], i);
        if (char_bm)
        {
            result = bitmap_and(result, char_bm);
            if (bitmap_empty(result))
            {
                *result_count = 0;
                return NULL;
            }
        }
        else
        {
            *result_count = 0;
            return NULL;
        }
    }
    
    /* Apply suffix constraints */
    suffix_len = strlen(suffix);
    for (i = 0; i < suffix_len; i++)
    {
        ch = suffix[suffix_len - 1 - i];
        if (ch == '_') continue;
        
        char_bm = get_neg_bitmap(ch, -1 - i);
        if (char_bm)
        {
            result = bitmap_and(result, char_bm);
            if (bitmap_empty(result))
            {
                *result_count = 0;
                return NULL;
            }
        }
        else
        {
            *result_count = 0;
            return NULL;
        }
    }
    
    indices = bitmap_to_indices(result, result_count);
    return indices;
}

static Bitmap* extract_candidates(const char *pattern)
{
    Bitmap *result;
    bool first;
    int plen;
    int i;
    char c;
    unsigned char uc;
    Bitmap *char_bm;
    
    result = NULL;
    first = true;
    plen = strlen(pattern);
    
    for (i = 0; i < plen; i++)
    {
        c = pattern[i];
        if (c != '%' && c != '_')
        {
            uc = (unsigned char)c;
            char_bm = &global_index->char_cache[uc];
            
            if (char_bm && char_bm->blocks)
            {
                if (first)
                {
                    result = char_bm;
                    first = false;
                }
                else
                {
                    result = bitmap_and(result, char_bm);
                    if (bitmap_empty(result))
                    {
                        return bitmap_create(0);
                    }
                }
            }
            else
            {
                return bitmap_create(0);
            }
        }
    }
    
    return result ? result : bitmap_create(0);
}

/* ==================== MAIN QUERY FUNCTION ==================== */

static int* optimized_query(const char *pattern, int *result_count)
{
    int *result;
    int plen;
    char ch;
    unsigned char uch;
    Bitmap *char_bm;
    char *prefix;
    const char *first_wild;
    const char *last_wild;
    int prefix_len;
    char *suffix;
    Bitmap *candidates;
    int cand_count;
    int *cand_idx;
    int match_count;
    int i;
    int idx;
    
    result = NULL;
    plen = strlen(pattern);
    
    /* Pattern: % */
    if (strcmp(pattern, "%") == 0)
    {
        result = (int *)palloc(global_index->num_records * sizeof(int));
        for (i = 0; i < global_index->num_records; i++)
        {
            result[i] = i;
        }
        *result_count = global_index->num_records;
    }
    /* Single char anywhere: %c% */
    else if (plen == 3 && pattern[0] == '%' && pattern[2] == '%')
    {
        ch = pattern[1];
        if (ch == '_')
        {
            result = (int *)palloc(global_index->num_records * sizeof(int));
            for (i = 0; i < global_index->num_records; i++)
            {
                result[i] = i;
            }
            *result_count = global_index->num_records;
        }
        else
        {
            uch = (unsigned char)ch;
            char_bm = &global_index->char_cache[uch];
            if (char_bm && char_bm->blocks)
            {
                result = bitmap_to_indices(char_bm, result_count);
            }
            else
            {
                *result_count = 0;
            }
        }
    }
    /* Pure prefix: a%, ab% */
    else if (pattern[plen - 1] == '%' && strchr(pattern, '%') == &pattern[plen - 1])
    {
        prefix = pnstrdup(pattern, plen - 1);
        result = query_prefix(prefix, result_count);
        pfree(prefix);
    }
    /* Pure suffix: %a, %ab */
    else if (pattern[0] == '%' && strchr(pattern + 1, '%') == NULL)
    {
        result = query_suffix(pattern + 1, result_count);
    }
    /* Dual anchor or complex */
    else
    {
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
        }
        /* Complex pattern */
        else
        {
            candidates = extract_candidates(pattern);
            if (candidates && !bitmap_empty(candidates))
            {
                cand_idx = bitmap_to_indices(candidates, &cand_count);
                
                if (cand_idx)
                {
                    result = (int *)palloc(cand_count * sizeof(int));
                    match_count = 0;
                    
                    for (i = 0; i < cand_count; i++)
                    {
                        idx = cand_idx[i];
                        if (match_pattern(global_index->data[idx], pattern))
                        {
                            result[match_count++] = idx;
                        }
                    }
                    
                    pfree(cand_idx);
                    *result_count = match_count;
                }
                else
                {
                    *result_count = 0;
                }
            }
            else
            {
                *result_count = 0;
            }
        }
    }
    
    return result;
}

/* ==================== POSTGRESQL FUNCTIONS ==================== */

PG_FUNCTION_INFO_V1(build_optimized_index);
Datum build_optimized_index(PG_FUNCTION_ARGS)
{
    text *table_name;
    text *column_name;
    char *table_str;
    char *column_str;
    instr_time start_time, end_time;
    StringInfoData query;
    int ret;
    int num_records;
    MemoryContext oldcontext;
    int idx;
    HeapTuple tuple;
    bool isnull;
    Datum datum;
    text *txt;
    char *str;
    int len;
    int pos;
    unsigned char uch;
    int arr_idx;
    Bitmap *existing_bm;
    Bitmap *new_bm;
    int ch_idx;
    int pos_loop;
    double ms;
    
    table_name = PG_GETARG_TEXT_PP(0);
    column_name = PG_GETARG_TEXT_PP(1);
    
    table_str = text_to_cstring(table_name);
    column_str = text_to_cstring(column_name);
    
    INSTR_TIME_SET_CURRENT(start_time);
    elog(INFO, "Building optimized index...");
    
    if (SPI_connect() != SPI_OK_CONNECT)
    {
        ereport(ERROR, (errmsg("SPI_connect failed")));
    }
    
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
    
    /* Create persistent memory context */
    if (index_context)
    {
        MemoryContextDelete(index_context);
    }
    index_context = AllocSetContextCreate(TopMemoryContext,
                                         "OptimizedLikeIndex",
                                         ALLOCSET_DEFAULT_SIZES);
    
    oldcontext = MemoryContextSwitchTo(index_context);
    
    /* Initialize index */
    global_index = (OptimizedIndex *)MemoryContextAlloc(index_context, sizeof(OptimizedIndex));
    global_index->num_records = num_records;
    global_index->max_len = 0;
    global_index->data = (char **)MemoryContextAlloc(index_context, num_records * sizeof(char *));
    
    /* Initialize arrays */
    global_index->pos_idx = (Bitmap **)MemoryContextAllocZero(index_context, 
                                                               CHAR_RANGE * MAX_POSITIONS * sizeof(Bitmap *));
    global_index->neg_idx = (Bitmap **)MemoryContextAllocZero(index_context,
                                                               CHAR_RANGE * MAX_POSITIONS * sizeof(Bitmap *));
    global_index->char_cache = (Bitmap *)MemoryContextAllocZero(index_context,
                                                                 CHAR_RANGE * sizeof(Bitmap));
    
    /* Build index */
    for (idx = 0; idx < num_records; idx++)
    {
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
        
        global_index->data[idx] = MemoryContextStrdup(index_context, str);
        if (len > global_index->max_len) global_index->max_len = len;
        
        /* Build position and negative indices */
        for (pos = 0; pos < len && pos < MAX_POSITIONS; pos++)
        {
            uch = (unsigned char)str[pos];
            
            /* Position index */
            arr_idx = uch * MAX_POSITIONS + pos;
            existing_bm = global_index->pos_idx[arr_idx];
            if (!existing_bm)
            {
                existing_bm = bitmap_create(num_records);
                global_index->pos_idx[arr_idx] = existing_bm;
            }
            bitmap_set(existing_bm, idx);
            
            /* Negative index */
            uch = (unsigned char)str[len - 1 - pos];
            arr_idx = uch * MAX_POSITIONS + pos;
            existing_bm = global_index->neg_idx[arr_idx];
            if (!existing_bm)
            {
                existing_bm = bitmap_create(num_records);
                global_index->neg_idx[arr_idx] = existing_bm;
            }
            bitmap_set(existing_bm, idx);
        }
        
        pfree(str);
    }
    
    /* Build char-anywhere cache */
    for (ch_idx = 0; ch_idx < CHAR_RANGE; ch_idx++)
    {
        new_bm = NULL;
        
        for (pos_loop = 0; pos_loop < MAX_POSITIONS; pos_loop++)
        {
            arr_idx = ch_idx * MAX_POSITIONS + pos_loop;
            existing_bm = global_index->pos_idx[arr_idx];
            
            if (existing_bm)
            {
                if (!new_bm)
                {
                    new_bm = existing_bm;
                }
                else
                {
                    new_bm = bitmap_or(new_bm, existing_bm);
                }
            }
        }
        
        if (new_bm)
        {
            global_index->char_cache[ch_idx] = *new_bm;
        }
    }
    
    MemoryContextSwitchTo(oldcontext);
    SPI_finish();
    
    INSTR_TIME_SET_CURRENT(end_time);
    INSTR_TIME_SUBTRACT(end_time, start_time);
    ms = INSTR_TIME_GET_MILLISEC(end_time);
    
    elog(INFO, "Build time: %.0f ms", ms);
    elog(INFO, "Index: %d records, max_len=%d", num_records, global_index->max_len);
    
    PG_RETURN_BOOL(true);
}

PG_FUNCTION_INFO_V1(optimized_like_query);
Datum optimized_like_query(PG_FUNCTION_ARGS)
{
    text *pattern_text;
    char *pattern;
    int result_count;
    int *results;
    
    pattern_text = PG_GETARG_TEXT_PP(0);
    pattern = text_to_cstring(pattern_text);
    
    if (!global_index)
    {
        elog(WARNING, "Index not built. Call build_optimized_index() first.");
        PG_RETURN_INT32(0);
    }
    
    results = optimized_query(pattern, &result_count);
    
    if (results) pfree(results);
    PG_RETURN_INT32(result_count);
}

PG_FUNCTION_INFO_V1(optimized_like_query_rows);
Datum optimized_like_query_rows(PG_FUNCTION_ARGS)
{
    FuncCallContext *funcctx;
    int *matches;
    int row_idx;
    Datum values[2];
    bool nulls[2];
    HeapTuple tuple;
    Datum result;
    
    if (SRF_IS_FIRSTCALL())
    {
        MemoryContext oldcontext;
        text *pattern_text;
        char *pattern;
        int result_count;
        TupleDesc tupdesc;
        
        pattern_text = PG_GETARG_TEXT_PP(0);
        pattern = text_to_cstring(pattern_text);
        
        funcctx = SRF_FIRSTCALL_INIT();
        oldcontext = MemoryContextSwitchTo(funcctx->multi_call_memory_ctx);
        
        if (!global_index)
        {
            SRF_RETURN_DONE(funcctx);
        }
        
        matches = optimized_query(pattern, &result_count);
        
        funcctx->max_calls = result_count;
        funcctx->user_fctx = matches;
        
        if (get_call_result_type(fcinfo, NULL, &tupdesc) != TYPEFUNC_COMPOSITE)
        {
            ereport(ERROR, (errmsg("function returning record in invalid context")));
        }
        funcctx->tuple_desc = BlessTupleDesc(tupdesc);
        
        MemoryContextSwitchTo(oldcontext);
    }
    
    funcctx = SRF_PERCALL_SETUP();
    
    if (funcctx->call_cntr < funcctx->max_calls)
    {
        matches = (int *)funcctx->user_fctx;
        row_idx = matches[funcctx->call_cntr];
        
        nulls[0] = false;
        nulls[1] = false;
        
        values[0] = Int32GetDatum(row_idx);
        values[1] = CStringGetTextDatum(global_index->data[row_idx]);
        
        tuple = heap_form_tuple(funcctx->tuple_desc, values, nulls);
        result = HeapTupleGetDatum(tuple);
        
        SRF_RETURN_NEXT(funcctx, result);
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
    appendStringInfo(&buf, "Index Status:\n");
    appendStringInfo(&buf, "  Records: %d\n", global_index->num_records);
    appendStringInfo(&buf, "  Max length: %d\n", global_index->max_len);
    appendStringInfo(&buf, "  Index type: Array-based bitmap index\n");
    
    PG_RETURN_TEXT_P(cstring_to_text(buf.data));
}

PG_FUNCTION_INFO_V1(test_pattern_match);
Datum test_pattern_match(PG_FUNCTION_ARGS)
{
    text *str_text;
    text *pattern_text;
    char *str;
    char *pattern;
    bool match_result;
    
    str_text = PG_GETARG_TEXT_PP(0);
    pattern_text = PG_GETARG_TEXT_PP(1);
    
    str = text_to_cstring(str_text);
    pattern = text_to_cstring(pattern_text);
    
    match_result = match_pattern(str, pattern);
    
    PG_RETURN_BOOL(match_result);
}
