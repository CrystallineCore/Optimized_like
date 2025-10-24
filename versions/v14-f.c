/*
 * optimized_like_roaring.c
 * PostgreSQL extension with Roaring Bitmap optimization
 * FULLY FIXED VERSION - Correct underscore handling with length validation
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
 
 /* Find neg_idx bitmap for (ch, neg_offset) */
 static RoaringBitmap* get_neg_bitmap(unsigned char ch, int neg_offset)
 {
     CharIndex *cidx = &global_index->neg_idx[ch];
     int i;
     
     for (i = 0; i < cidx->count; i++)
         if (cidx->entries[i].pos == neg_offset)
             return cidx->entries[i].bitmap;
     
     return NULL;
 }
 
 /* Set pos_idx entry */
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
 
 /* Set neg_idx entry */
 static void set_neg_bitmap(unsigned char ch, int neg_offset, RoaringBitmap *bm)
 {
     CharIndex *cidx = &global_index->neg_idx[ch];
     int i;
     
     for (i = 0; i < cidx->count; i++)
     {
         if (cidx->entries[i].pos == neg_offset)
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
     
     cidx->entries[cidx->count].pos = neg_offset;
     cidx->entries[cidx->count].bitmap = bm;
     cidx->count++;
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
 
 static int count_non_wildcard(const char *s)
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
 
 /* FIXED: Count pattern length including underscores */
 static int pattern_length_with_underscores(const char *pattern)
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
     int i;
     for (i = 0; i < info->slice_count; i++)
         pfree(info->slices[i]);
     pfree(info->slices);
     pfree(info);
 }
 
 /* ==================== CORE MATCHING FUNCTIONS (FIXED) ==================== */
 
 /* FIXED: Match pattern at exact position with length validation */
 static RoaringBitmap* match_at_pos(const char *pattern, int start_pos)
 {
     RoaringBitmap *result = NULL;
     int pos = start_pos;
     int i, plen = strlen(pattern);
     int required_length = start_pos + plen;
     RoaringBitmap *char_bm, *temp;
     RoaringBitmap *any_char_bm;
     int ch;
     
     /* First filter by minimum required length */
     if (required_length > 0 && required_length <= global_index->length_idx.max_length)
     {
         result = get_length_range(required_length, -1);
         if (roaring_is_empty(result))
             return result;
     }
     
     for (i = 0; i < plen; i++)
     {
         if (pattern[i] == '_')
         {
             /* Underscore requires ANY character at this position */
             /* Build bitmap of all records that have ANY character at pos */
             any_char_bm = NULL;
             for (ch = 0; ch < CHAR_RANGE; ch++)
             {
                 char_bm = get_pos_bitmap((unsigned char)ch, pos);
                 if (char_bm)
                 {
                     if (!any_char_bm)
                     {
                         any_char_bm = roaring_copy(char_bm);
                     }
                     else
                     {
                         temp = roaring_or(any_char_bm, char_bm);
                         roaring_free(any_char_bm);
                         any_char_bm = temp;
                     }
                 }
             }
             
             if (any_char_bm)
             {
                 if (!result)
                 {
                     result = any_char_bm;
                 }
                 else
                 {
                     temp = roaring_and(result, any_char_bm);
                     roaring_free(result);
                     roaring_free(any_char_bm);
                     result = temp;
                     
                     if (roaring_is_empty(result))
                         return result;
                 }
             }
             else
             {
                 /* No records have any character at this position */
                 if (result)
                     roaring_free(result);
                 return roaring_create();
             }
             
             pos++;
             continue;
         }
         
         char_bm = get_pos_bitmap((unsigned char)pattern[i], pos);
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
         pos++;
     }
     
     return result ? result : roaring_create();
 }
 
 /* FIXED: Match pattern at exact position from end with length validation */
 static RoaringBitmap* match_at_neg_pos(const char *pattern, int end_offset)
 {
     RoaringBitmap *result = NULL;
     int plen = strlen(pattern);
     int required_length = plen;
     int i, pos;
     RoaringBitmap *char_bm, *temp;
     RoaringBitmap *any_char_bm;
     int ch;
     
     /* First filter by minimum required length */
     if (required_length > 0 && required_length <= global_index->length_idx.max_length)
     {
         result = get_length_range(required_length, -1);
         if (roaring_is_empty(result))
             return result;
     }
     
     for (i = plen - 1; i >= 0; i--)
     {
         /* Calculate position from end */
         pos = -(plen - i);
         
         if (pattern[i] == '_')
         {
             /* Underscore requires ANY character at this position from end */
             any_char_bm = NULL;
             for (ch = 0; ch < CHAR_RANGE; ch++)
             {
                 char_bm = get_neg_bitmap((unsigned char)ch, pos);
                 if (char_bm)
                 {
                     if (!any_char_bm)
                     {
                         any_char_bm = roaring_copy(char_bm);
                     }
                     else
                     {
                         temp = roaring_or(any_char_bm, char_bm);
                         roaring_free(any_char_bm);
                         any_char_bm = temp;
                     }
                 }
             }
             
             if (any_char_bm)
             {
                 if (!result)
                 {
                     result = any_char_bm;
                 }
                 else
                 {
                     temp = roaring_and(result, any_char_bm);
                     roaring_free(result);
                     roaring_free(any_char_bm);
                     result = temp;
                     
                     if (roaring_is_empty(result))
                         return result;
                 }
             }
             else
             {
                 if (result)
                     roaring_free(result);
                 return roaring_create();
             }
             
             continue;
         }
         
         char_bm = get_neg_bitmap((unsigned char)pattern[i], pos);
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
     }
     
     return result ? result : roaring_create();
 }
 
 /* Get candidates with required characters */
 static RoaringBitmap* get_char_candidates(const char *pattern)
 {
     RoaringBitmap *result = NULL;
     bool seen[CHAR_RANGE] = {false};
     int i;
     
     for (i = 0; pattern[i]; i++)
     {
         unsigned char ch = (unsigned char)pattern[i];
         if (pattern[i] != '_' && pattern[i] != '%' && !seen[ch])
         {
             seen[ch] = true;
             if (global_index->char_cache[ch])
             {
                 if (!result)
                 {
                     result = roaring_copy(global_index->char_cache[ch]);
                 }
                 else
                 {
                     RoaringBitmap *temp = roaring_and(result, global_index->char_cache[ch]);
                     roaring_free(result);
                     result = temp;
                     
                     if (roaring_is_empty(result))
                         return result;
                 }
             }
             else
             {
                 if (result)
                     roaring_free(result);
                 return roaring_create();
             }
         }
     }
     
     return result;
 }
 
 /* Check if pattern matches starting at current position */
 static bool matches_at_position(const char *str, const char *pattern)
 {
     const char *s = str;
     const char *p = pattern;
     
     while (*p)
     {
         if (*p == '_')
         {
             if (!*s) return false;
             s++;
             p++;
         }
         else if (*s == *p)
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
 
 /* Find next occurrence of pattern in string */
 static const char* find_pattern(const char *str, const char *pattern)
 {
     const char *s = str;
     
     while (*s)
     {
         if (matches_at_position(s, pattern))
             return s;
         s++;
     }
     
     return NULL;
 }
 
 /* Check if string contains pattern as substring */
 static bool contains_substring(const char *str, const char *pattern)
 {
     return find_pattern(str, pattern) != NULL;
 }
 
 /* Verify multi-slice pattern matches */
 static RoaringBitmap* verify_multislice_pattern(RoaringBitmap *candidates, PatternInfo *info)
 {
     uint64_t count, i, j;
     uint32_t *indices;
     uint32_t idx;
     const char *str;
     const char *search_start;
     const char *match_pos;
     bool all_found;
     RoaringBitmap *verified = roaring_create();
     
     indices = roaring_to_array(candidates, &count);
     
     if (!indices)
         return verified;
     
     for (i = 0; i < count; i++)
     {
         idx = indices[i];
         str = global_index->data[idx];
         search_start = str;
         all_found = true;
         
         for (j = 0; j < info->slice_count; j++)
         {
             const char *slice = info->slices[j];
             
             match_pos = find_pattern(search_start, slice);
             
             if (!match_pos)
             {
                 all_found = false;
                 break;
             }
             
             search_start = match_pos;
             const char *slice_ptr = slice;
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
         
         if (all_found)
         {
             roaring_add(verified, idx);
         }
     }
     
     pfree(indices);
     return verified;
 }
 
 /* Get length range bitmap */
 static RoaringBitmap* get_length_range(int min_len, int max_len)
 {
     RoaringBitmap *result = roaring_create();
     RoaringBitmap *temp_union;
     int len;
     
     if (max_len < 0 || max_len > global_index->length_idx.max_length)
         max_len = global_index->length_idx.max_length - 1;
     
     for (len = min_len; len <= max_len; len++)
     {
         if (len < global_index->length_idx.max_length && global_index->length_idx.length_bitmaps[len])
         {
             temp_union = roaring_or(result, global_index->length_idx.length_bitmaps[len]);
             roaring_free(result);
             result = temp_union;
         }
     }
     
     return result;
 }
 
 /* ==================== MAIN QUERY FUNCTION ==================== */
 
 static uint32_t* optimized_query(const char *pattern, uint64_t *result_count)
 {
     PatternInfo *info;
     RoaringBitmap *result = NULL;
     RoaringBitmap *temp, *candidates, *temp2, *temp3;
     uint32_t *indices;
     int i;
     int min_len;
     int underscore_count;
     bool has_percent;
     bool only_wildcards;
     
     /* Pattern: % - match all */
     if (strcmp(pattern, "%") == 0)
     {
         indices = (uint32_t *)palloc(global_index->num_records * sizeof(uint32_t));
         for (i = 0; i < global_index->num_records; i++)
             indices[i] = (uint32_t)i;
         *result_count = global_index->num_records;
         return indices;
     }
     
     /* OPTIMIZATION: Check if pattern contains only wildcards (_ and %) */
     only_wildcards = true;
     underscore_count = 0;
     has_percent = false;
     for (i = 0; pattern[i]; i++)
     {
         if (pattern[i] == '_')
             underscore_count++;
         else if (pattern[i] == '%')
             has_percent = true;
         else
         {
             only_wildcards = false;
             break;
         }
     }
     
     /* FAST PATH: Pattern contains only wildcards */
     if (only_wildcards)
     {
         if (!has_percent)
         {
             /* Pure underscores: ___  - exact length match */
             if (underscore_count < global_index->length_idx.max_length &&
                 global_index->length_idx.length_bitmaps[underscore_count])
             {
                 result = roaring_copy(global_index->length_idx.length_bitmaps[underscore_count]);
             }
             else
             {
                 result = roaring_create();
             }
         }
         else
         {
             /* Mixed _ and %: __%__, %___, etc. - minimum length match */
             result = get_length_range(underscore_count, -1);
         }
         
         indices = roaring_to_array(result, result_count);
         roaring_free(result);
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
         
         candidates = get_char_candidates(slice);
         if (roaring_is_empty(candidates))
         {
             free_pattern_info(info);
             roaring_free(candidates);
             *result_count = 0;
             return NULL;
         }
         
         /* FIXED: Case: pattern (exact match) */
         if (!info->starts_with_percent && !info->ends_with_percent)
         {
             int exact_length = pattern_length_with_underscores(slice);
             
             result = match_at_pos(slice, 0);
             
             /* For exact match, string length must equal pattern length */
             if (exact_length < global_index->length_idx.max_length && 
                 global_index->length_idx.length_bitmaps[exact_length])
             {
                 temp = roaring_and(result, global_index->length_idx.length_bitmaps[exact_length]);
                 roaring_free(result);
                 result = temp;
             }
             else
             {
                 roaring_free(result);
                 result = roaring_create();
             }
         }
         /* Case: pattern% */
         else if (!info->starts_with_percent && info->ends_with_percent)
         {
             result = match_at_pos(slice, 0);
             temp = roaring_and(result, candidates);
             roaring_free(result);
             result = temp;
         }
         /* Case: %pattern */
         else if (info->starts_with_percent && !info->ends_with_percent)
         {
             result = match_at_neg_pos(slice, 0);
             temp = roaring_and(result, candidates);
             roaring_free(result);
             result = temp;
         }
         /* Case: %pattern% */
         else
         {
             if (candidates)
             {
                 result = roaring_create();
                 uint64_t cand_count;
                 uint32_t *cand_indices = roaring_to_array(candidates, &cand_count);
                 uint64_t i;
                 
                 if (cand_indices)
                 {
                     for (i = 0; i < cand_count; i++)
                     {
                         uint32_t idx = cand_indices[i];
                         const char *str = global_index->data[idx];
                         
                         if (contains_substring(str, slice))
                         {
                             roaring_add(result, idx);
                         }
                     }
                     pfree(cand_indices);
                 }
                 roaring_free(candidates);
                 candidates = NULL;
             }
             else
             {
                 result = roaring_create();
             }
         }
         
         if (candidates)
             roaring_free(candidates);
     }
     /* Multiple slices */
     else
     {
         /* FIXED: Calculate min length properly */
         min_len = 0;
         for (i = 0; i < info->slice_count; i++)
             min_len += pattern_length_with_underscores(info->slices[i]);
         
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
             
             if (roaring_is_empty(candidates))
             {
                 roaring_free(candidates);
                 free_pattern_info(info);
                 *result_count = 0;
                 return NULL;
             }
         }
         
         temp = get_length_range(min_len, -1);
         result = roaring_and(candidates, temp);
         roaring_free(candidates);
         roaring_free(temp);
         
         if (roaring_is_empty(result))
         {
             roaring_free(result);
             free_pattern_info(info);
             *result_count = 0;
             return NULL;
         }
         
         if (!info->starts_with_percent)
         {
             temp = match_at_pos(info->slices[0], 0);
             temp3 = roaring_and(result, temp);
             roaring_free(result);
             roaring_free(temp);
             result = temp3;
             
             if (roaring_is_empty(result))
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
             
             if (roaring_is_empty(result))
             {
                 roaring_free(result);
                 free_pattern_info(info);
                 *result_count = 0;
                 return NULL;
             }
         }
         
         /* Verify multi-slice patterns */
         RoaringBitmap *verified = verify_multislice_pattern(result, info);
         roaring_free(result);
         result = verified;
     }
     
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
     int neg_offset;
     
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
     elog(INFO, "Index: %d records, max_len=%d, memory=%zu bytes (%.2f MB)",
          num_records, global_index->max_len, global_index->memory_used,
          global_index->memory_used / (1024.0 * 1024.0));
     elog(INFO, "FIXED: Proper underscore length validation enabled");
     
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
     appendStringInfo(&buf, "Roaring Bitmap Index Status (FIXED VERSION):\n");
     appendStringInfo(&buf, "  Records: %d\n", global_index->num_records);
     appendStringInfo(&buf, "  Max length: %d\n", global_index->max_len);
     appendStringInfo(&buf, "  Memory used: %zu bytes (%.2f MB)\n", 
                     global_index->memory_used,
                     global_index->memory_used / (1024.0 * 1024.0));
     appendStringInfo(&buf, "  Index type: Roaring Bitmap compression\n");
     appendStringInfo(&buf, "  Supports: '%%' (multi-char wildcard), '_' (single-char wildcard)\n");
     appendStringInfo(&buf, "  FIXED: Proper underscore length validation\n");
     
     #ifdef HAVE_ROARING
     appendStringInfo(&buf, "  Backend: Native Roaring library\n");
     #else
     appendStringInfo(&buf, "  Backend: Fallback bitmap implementation\n");
     #endif
     
     PG_RETURN_TEXT_P(cstring_to_text(buf.data));
 }