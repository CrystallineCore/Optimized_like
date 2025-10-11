-- complain if script is sourced in psql, rather than via CREATE EXTENSION
\echo Use "CREATE EXTENSION optimized_like" to load this file. \quit

-- Function to build the optimized index from a table column
CREATE FUNCTION build_optimized_index(
    table_name text,
    column_name text
) RETURNS boolean
AS 'MODULE_PATHNAME', 'build_optimized_index'
LANGUAGE C STRICT;

COMMENT ON FUNCTION build_optimized_index(text, text) IS 
'Build an optimized bitmap index for wildcard pattern matching on the specified table and column';

-- Function to query and return count of matches
CREATE FUNCTION optimized_like_query(
    pattern text
) RETURNS integer
AS 'MODULE_PATHNAME', 'optimized_like_query'
LANGUAGE C STRICT;

COMMENT ON FUNCTION optimized_like_query(text) IS
'Return the count of records matching the given wildcard pattern using the optimized index';

-- Function to query and return matching rows
CREATE FUNCTION optimized_like_query_rows(
    pattern text
) RETURNS TABLE(row_id integer, value text)
AS 'MODULE_PATHNAME', 'optimized_like_query_rows'
LANGUAGE C STRICT;

COMMENT ON FUNCTION optimized_like_query_rows(text) IS
'Return all records matching the given wildcard pattern using the optimized index';

-- Utility function to check index status
CREATE FUNCTION optimized_like_status()
RETURNS text
AS 'MODULE_PATHNAME', 'optimized_like_status'
LANGUAGE C STRICT;

COMMENT ON FUNCTION optimized_like_status() IS
'Display the current status of the optimized index';

-- Utility function to test pattern matching directly
CREATE FUNCTION test_pattern_match(
    str text,
    pattern text
) RETURNS boolean
AS 'MODULE_PATHNAME', 'test_pattern_match'
LANGUAGE C STRICT;

COMMENT ON FUNCTION test_pattern_match(text, text) IS
'Test if a string matches a wildcard pattern (for debugging purposes)';