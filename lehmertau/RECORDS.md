# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Lehmer's conjecture on
Ramanujan's τ is false (`∃ n, 1 ≤ n ∧ tau756 n = 0`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **295** | `machines/lehmertau_295.txt` (readable: `lehmertau_295_annotated.txt`) | `minimize.py` on the 481-state design (`kissat404`, one state at a time from the greedy estimate 334; `cadical195` in parallel) | Proven in Lean: `TM.LehmerTau.M295.halts_iff` |
| 481 | `machines/lehmertau_481.txt` (= `lehmertau.txt`) | `build.py`: an odometer over copies of the divisors and switchable constant blocks, two legendre/ frames, binary seed counters | Proven in Lean: `TM.LehmerTau.halts_iff` |

What stays unmerged: the seed's written word only reads 0s and merges almost entirely into
other states; the parsers and crossings are mostly pairs that merge across routines. The
odometer's carry, the copy routine and the compare keep most of their states.

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
