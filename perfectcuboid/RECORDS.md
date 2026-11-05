# Perfect cuboid machines

| States | File | How | Lean theorem |
|-------:|------|-----|--------------|
| 154 | `perfectcuboid.txt` | the design, `build.py` | `TM.PerfectCuboid.halts_iff` |
| 88 | `machines/perfectcuboid_88.txt` | `minimize_clique.py` on the design (clique 87, 87 UNSAT, 88 SAT in seconds) | `TM.PerfectCuboid.M88.halts_iff` |

## How the design got there

All counts merged by `../tools/minimize_clique.py` (exact: the first SAT K is optimal).

| Design | States | Merged | Change |
|---|---:|---:|---|
| v1 | 180 | 108 | Z moves one block left at each S reset (no window counter); a failed check sets a flag in G and the tuple runs to its end; the right side (Z, G, S) rebuilt after a mirrored NEXCOM with loops |
| v2 | 171 | 105 | Z fixed at the end of the queue, a window counter W in G (a marker in three positions), an immediate abort; NEXCOM by merging blocks and cutting them at fixed offsets (no loops) |
| v3 | 165 | 99 | the next block is set up *before* the check, so the way back from S is the processing's own parser into the block's `h` (no separate parser, no re-punched `h`); the tuple starts with W = 2 and the spurious first check resets S |
| v4 | 142 | 95 | a 1-cell seed: the abort routine writes Z, G, S and, finding no queue, NEXCOM's cut chains write `(4, 4, 4)` on blank (the 35-cell seed alone had cost 17 merged states: a chain longer than about ten cells forms a clique with every state that moves the other way on 0) |
| v5 | 142 | 91 | the abort only moves S's hole home: the next tuple's first check passes and its wrap resets S |
| v6 | 154 | 88 | the bootstrap writes Z and `(4, 4, 4)` with its own chain of blank-only states, so the cut chains stay 1-only |

Ideas tried on paper and not kept: windows of 2 over `A B C` (misses `a² + b² + c²`), a bouncing
walk with subtraction (`+A +B +C −B −A +B` covers all four sums with one S but needs S to count down
and a direction flag), two or three S counters with fixed reset points, block minimum 2 (the
region's mark would have to sit on cell 0 or on the separator).
