-- ============================================================================
-- COMPREHENSIVE BENCHMARK: PostgreSQL LIKE vs Optimized Extension
-- Direct comparison matching meta.cpp patterns
-- ============================================================================

\timing off
SET client_min_messages TO NOTICE;

-- Drop existing tables
DROP TABLE IF EXISTS test_data CASCADE;
DROP TABLE IF EXISTS benchmark_results CASCADE;

-- ============================================================================
-- STEP 1: Generate Test Data (matching C++ random_string logic)
-- ============================================================================

\echo '========================================================================'
\echo 'STEP 1: Generating 1,000,000 random strings (6-10 chars)'
\echo '========================================================================'

CREATE TABLE test_data (
    id SERIAL PRIMARY KEY,
    value TEXT NOT NULL
);

-- Generate random strings matching C++ logic: 6 + rand() % 5
DO $$
DECLARE
    chars TEXT := 'abcdefghijklmnopqrstuvwxyz';
    i INTEGER;
    len INTEGER;
    str TEXT;
BEGIN
    FOR i IN 1..1000000 LOOP
        len := 6 + floor(random() * 5)::INTEGER;
        str := '';
        FOR j IN 1..len LOOP
            str := str || substr(chars, 1 + floor(random() * 26)::INTEGER, 1);
        END LOOP;
        INSERT INTO test_data (value) VALUES (str);
        
        IF i % 100000 = 0 THEN
            RAISE NOTICE 'Generated % rows', i;
        END IF;
    END LOOP;
END $$;

-- Create indexes for PostgreSQL
CREATE INDEX idx_test_data_value ON test_data(value);
CREATE INDEX idx_test_data_pattern ON test_data(value text_pattern_ops);
ANALYZE test_data;

\echo 'Test data generated successfully!'
\echo ''

-- ============================================================================
-- STEP 2: Build Optimized Index
-- ============================================================================

\echo '========================================================================'
\echo 'STEP 2: Building Optimized Index'
\echo '========================================================================'

-- Load extension
CREATE EXTENSION IF NOT EXISTS optimized_like;

-- Build index (matches C++ index.build())
SELECT build_optimized_index('test_data', 'value');

-- Show index status
SELECT optimized_like_status();

\echo ''

-- ============================================================================
-- STEP 3: Define Test Patterns (EXACT match to meta.cpp)
-- ============================================================================

CREATE TEMPORARY TABLE test_patterns (
    id SERIAL PRIMARY KEY,
    pattern TEXT NOT NULL,
    category TEXT NOT NULL
);

INSERT INTO test_patterns (pattern, category) VALUES
    -- Prefix-based
    ('a%', 'Prefix'),
    ('ab%', 'Prefix'),
    ('abc%', 'Prefix'),
    ('z%', 'Prefix'),
    ('xy%', 'Prefix'),
    
    -- Suffix-based
    ('%a', 'Suffix'),
    ('%b', 'Suffix'),
    ('%c', 'Suffix'),
    ('%ab', 'Suffix'),
    ('%bc', 'Suffix'),
    ('%abc', 'Suffix'),
    ('%xyz', 'Suffix'),
    
    -- Infix-based
    ('%a%', 'Infix'),
    ('%ab%', 'Infix'),
    ('%abc%', 'Infix'),
    ('%a%c%', 'Infix'),
    ('%a%b%', 'Infix'),
    ('%ab%c%', 'Infix'),
    ('%a%b%c%', 'Infix'),
    
    -- Leading underscores
    ('_a%', 'Underscore'),
    ('__a%', 'Underscore'),
    ('_ab%', 'Underscore'),
    ('__ab%', 'Underscore'),
    ('_a_b%', 'Underscore'),
    ('__a_b%', 'Underscore'),
    ('_a%b%', 'Underscore'),
    ('_%a', 'Underscore'),
    
    -- Complex hybrids
    ('%a_b%', 'Complex'),
    ('%a__b%', 'Complex'),
    ('%a%b%', 'Complex'),
    ('%a%b%c%', 'Complex'),
    ('%a%b%c%d%', 'Complex'),
    ('%ab_%c', 'Complex'),
    ('%a__b%c', 'Complex'),
    ('%a%b%c__d%', 'Complex');

-- ============================================================================
-- STEP 4: Run Benchmarks
-- ============================================================================

\echo '========================================================================'
\echo 'STEP 4: Running Benchmarks'
\echo '========================================================================'

-- Results table
CREATE TABLE benchmark_results (
    pattern TEXT NOT NULL,
    category TEXT NOT NULL,
    method TEXT NOT NULL,
    matches INTEGER NOT NULL,
    time_ms NUMERIC NOT NULL,
    avg_per_match_us NUMERIC
);

-- Function to benchmark PostgreSQL LIKE
CREATE OR REPLACE FUNCTION benchmark_pg_like(p_pattern TEXT)
RETURNS TABLE(matches BIGINT, time_us BIGINT) AS $$
DECLARE
    start_time TIMESTAMP WITH TIME ZONE;
    end_time TIMESTAMP WITH TIME ZONE;
    result_count BIGINT;
    elapsed_us BIGINT;
BEGIN
    start_time := clock_timestamp();
    
    SELECT COUNT(*) INTO result_count
    FROM test_data
    WHERE value LIKE p_pattern;
    
    end_time := clock_timestamp();
    elapsed_us := EXTRACT(EPOCH FROM (end_time - start_time)) * 1000000;
    
    RETURN QUERY SELECT result_count, elapsed_us;
END;
$$ LANGUAGE plpgsql;

-- Run benchmarks for each pattern
DO $$
DECLARE
    rec RECORD;
    pg_result RECORD;
    opt_count INTEGER;
    opt_time_us BIGINT;
    pg_time_ms NUMERIC;
    opt_time_ms NUMERIC;
    pg_avg NUMERIC;
    opt_avg NUMERIC;
BEGIN
    FOR rec IN SELECT pattern, category FROM test_patterns ORDER BY id LOOP
        RAISE NOTICE 'Testing pattern: %', rec.pattern;
        
        -- Benchmark PostgreSQL LIKE
        SELECT * INTO pg_result FROM benchmark_pg_like(rec.pattern);
        pg_time_ms := pg_result.time_us / 1000.0;
        pg_avg := CASE 
            WHEN pg_result.matches > 0 THEN pg_result.time_us::NUMERIC / pg_result.matches 
            ELSE 0 
        END;
        
        INSERT INTO benchmark_results 
        VALUES (rec.pattern, rec.category, 'PostgreSQL', 
                pg_result.matches::INTEGER, pg_time_ms, pg_avg);
        
        -- Benchmark Optimized Extension
        SELECT COUNT(*) INTO opt_count FROM optimized_like_query_rows(rec.pattern);
        
        -- Get timing from dedicated benchmark function
        SELECT time_us INTO opt_time_us FROM benchmark_optimized_query(rec.pattern);
        opt_time_ms := opt_time_us / 1000.0;
        opt_avg := CASE 
            WHEN opt_count > 0 THEN opt_time_us::NUMERIC / opt_count 
            ELSE 0 
        END;
        
        INSERT INTO benchmark_results 
        VALUES (rec.pattern, rec.category, 'Optimized', 
                opt_count, opt_time_ms, opt_avg);
        
        -- Progress update
        IF pg_result.matches != opt_count THEN
            RAISE WARNING 'MISMATCH for pattern %: PG=% vs Opt=%', 
                rec.pattern, pg_result.matches, opt_count;
        END IF;
    END LOOP;
END $$;

-- ============================================================================
-- STEP 5: Display Results
-- ============================================================================

\echo ''
\echo '========================================================================'
\echo 'BENCHMARK RESULTS'
\echo '========================================================================'
\echo ''

-- Summary by category
\echo 'Performance by Category:'
\echo '------------------------------------------------------------------------'

SELECT 
    category,
    method,
    COUNT(*) as patterns,
    ROUND(AVG(time_ms), 3) as avg_time_ms,
    ROUND(MIN(time_ms), 3) as min_time_ms,
    ROUND(MAX(time_ms), 3) as max_time_ms,
    ROUND(AVG(avg_per_match_us), 3) as avg_per_match_us
FROM benchmark_results
GROUP BY category, method
ORDER BY category, method;

\echo ''
\echo 'Speedup Analysis:'
\echo '------------------------------------------------------------------------'

WITH comparison AS (
    SELECT 
        b1.pattern,
        b1.category,
        b1.matches,
        b1.time_ms as pg_time_ms,
        b2.time_ms as opt_time_ms,
        ROUND((b1.time_ms / NULLIF(b2.time_ms, 0))::NUMERIC, 2) as speedup
    FROM benchmark_results b1
    JOIN benchmark_results b2 ON b1.pattern = b2.pattern
    WHERE b1.method = 'PostgreSQL' AND b2.method = 'Optimized'
)
SELECT 
    pattern,
    category,
    matches,
    ROUND(pg_time_ms, 3) as pg_ms,
    ROUND(opt_time_ms, 3) as opt_ms,
    speedup || 'x' as speedup
FROM comparison
ORDER BY speedup DESC;

\echo ''
\echo 'Overall Statistics:'
\echo '------------------------------------------------------------------------'

WITH comparison AS (
    SELECT 
        b1.pattern,
        b1.time_ms as pg_time,
        b2.time_ms as opt_time,
        (b1.time_ms / NULLIF(b2.time_ms, 0)) as speedup
    FROM benchmark_results b1
    JOIN benchmark_results b2 ON b1.pattern = b2.pattern
    WHERE b1.method = 'PostgreSQL' AND b2.method = 'Optimized'
)
SELECT 
    ROUND(AVG(pg_time), 3) as avg_pg_ms,
    ROUND(AVG(opt_time), 3) as avg_opt_ms,
    ROUND(AVG(speedup), 2) || 'x' as avg_speedup,
    ROUND(MAX(speedup), 2) || 'x' as max_speedup,
    ROUND(MIN(speedup), 2) || 'x' as min_speedup
FROM comparison;

-- ============================================================================
-- STEP 6: Export Results
-- ============================================================================

\echo ''
\echo '========================================================================'
\echo 'STEP 6: Exporting Results'
\echo '========================================================================'

-- Export detailed results
\copy (SELECT * FROM benchmark_results ORDER BY pattern, method) TO 'benchmark_detailed.csv' CSV HEADER

-- Export comparison
\copy (WITH comparison AS (SELECT b1.pattern, b1.category, b1.matches, b1.time_ms as pg_time_ms, b2.time_ms as opt_time_ms, ROUND((b1.time_ms / NULLIF(b2.time_ms, 0))::NUMERIC, 2) as speedup FROM benchmark_results b1 JOIN benchmark_results b2 ON b1.pattern = b2.pattern WHERE b1.method = 'PostgreSQL' AND b2.method = 'Optimized') SELECT * FROM comparison ORDER BY speedup DESC) TO 'benchmark_comparison.csv' CSV HEADER

\echo ''
\echo '✓ Results exported to:'
\echo '  - benchmark_detailed.csv'
\echo '  - benchmark_comparison.csv'
\echo ''

-- ============================================================================
-- STEP 7: Verification Tests
-- ============================================================================

\echo '========================================================================'
\echo 'STEP 7: Verification (checking result accuracy)'
\echo '========================================================================'

DO $$
DECLARE
    rec RECORD;
    pg_count BIGINT;
    opt_count INTEGER;
    mismatch_count INTEGER := 0;
BEGIN
    FOR rec IN SELECT pattern FROM test_patterns LOOP
        SELECT COUNT(*) INTO pg_count FROM test_data WHERE value LIKE rec.pattern;
        SELECT COUNT(*) INTO opt_count FROM optimized_like_query_rows(rec.pattern);
        
        IF pg_count != opt_count THEN
            RAISE WARNING 'MISMATCH: % - PG: %, Optimized: %', 
                rec.pattern, pg_count, opt_count;
            mismatch_count := mismatch_count + 1;
        END IF;
    END LOOP;
    
    IF mismatch_count = 0 THEN
        RAISE NOTICE '✓ All patterns match perfectly! No discrepancies found.';
    ELSE
        RAISE WARNING '✗ Found % mismatches!', mismatch_count;
    END IF;
END $$;

\echo ''
\echo '========================================================================'
\echo 'BENCHMARK COMPLETE!'
\echo '========================================================================'