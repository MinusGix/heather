#!/usr/bin/env python3
"""Emit the conjunction-projection-chain-cost family for --timings / perf ab.

python3 probes/conjunction_projection_chain.py > target/conjunction-chain.hthr
scripts/perf ab --file target/conjunction-chain.hthr:lib/std --samples 3
"""

print("import logic;")
print("theorem identity<A>(a: A): A { a }")
for depth in (4, 8, 16, 32, 64):
    ty = "And<A, " * depth + "A" + ">" * depth
    path = ".right" * depth
    print(f"fn bare{depth}<A>(facts: {ty}) -> A {{ facts{path} }}")
    print(f"fn alias{depth}<A>(facts: {ty}) -> A {{ let p = identity(facts); p{path} }}")
