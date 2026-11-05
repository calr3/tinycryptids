# Barker machine records

| States | Machine | How | Lean |
|-------:|---------|-----|------|
| 84 | `machines/barker_84.txt` | 102-state design (counter seed, its sentinel in the top bit's marker cell), `minimize_clique.py` (optimal: 83 UNSAT) | `TM.Barker.M84.halts_iff` |
| 86 | — | 104-state design, separate `[1 1]` sentinel | (superseded) |
| 94 | — | 112-state design, the first candidate written cell by cell (30 seed states, only 9 merged) | (superseded) |
| 101 | — | first design: agree/disagree counter with a zig-zag check, rewind after the check | — |

The core (design without a seed) merges to 71 states; the seed costs 13.
