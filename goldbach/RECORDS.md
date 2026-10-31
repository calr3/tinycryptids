# Records: Goldbach machines

All machines start on a blank tape and halt iff some even number `2n ≥ 4` is not the sum of two
primes. "Instructions" counts the defined transitions, the halting one left undefined (BBi).

| Instructions | States | Symbols | Machine | How obtained | Status |
|---:|---:|---:|---|---|---|
| **34** | **10** | 6 | `machines/goldbach_10.txt` (readable: `goldbach_10_annotated.txt`) | `minimize_clique.py goldbach.txt out 120 cadical195 e2:5` (the halting slot kept exclusive) | Proven in Lean: `TMK.Goldbach.M10.halts_iff`, `halts_iff_not` |
| 35 | 13 | 6 | `goldbach.txt` | Hand design, `build.py` | Proven in Lean: `TMK.Goldbach.halts_iff` |

For comparison, the best 2-symbol machine we know of is Google DeepMind's
[`goldbach_21`](https://github.com/google-deepmind/cryptids/tree/main/artifacts/goldbach_21)
(21 states, 41 instructions, reduced from their published 25-state machine).

## The design

Six symbols let each primality test run in place, with no copy: the divisor is a prefix of the
block, marked off by a boundary symbol, and a zigzag between the divisor and the rest marks one
cell of each per step (see `README.md`). Exits are told apart by which delimiter (0 or `s`) is
read, so one test serves both P and Q.

## The merge

Ten states is optimal for merging this design (the clique bound is 10). The merge also saves an
instruction: `inc`'s walk over 1s became `chk`'s (both are `1 → 1R`), and the growth states
`g1`, `g2` joined `rst`.
