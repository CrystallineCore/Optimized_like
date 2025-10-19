SELECT
    b.pattern,
    n.match_count AS native_count,
    ROUND(n.exec_time_ms::numeric, 2) AS native_ms,
    o.match_count AS optimized_count,
    ROUND(o.exec_time_ms::numeric, 2) AS optimized_ms,
    ROUND((n.exec_time_ms / NULLIF(o.exec_time_ms,0))::numeric, 2) AS speedup_factor,
    (o.match_count - n.match_count) AS delta
FROM benchmark_patterns b
LEFT JOIN native_results n USING(pattern)
LEFT JOIN optimized_results o USING(pattern)
ORDER BY b.pattern;
