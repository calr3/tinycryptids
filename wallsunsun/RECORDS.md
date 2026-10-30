# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff a Wall–Sun–Sun prime exists
(`∃ p, Prime p ∧ p * p ∣ fib (wssIndex p)`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **50** | `machines/wallsunsun_50.txt` | `minimize_clique.py` (`cadical195`) on the 79-state design; 48 and 49 are unsatisfiable (optimal for the design) | Proven in Lean: `TM.WallSunSun2.M50.halts_iff` |
| 79 | `wallsunsun2.txt` | `build2.py`: every `m ≥ 2` with `m² ∣ F(m ∓ 1)` halts, no primality test | Proven in Lean: `TM.WallSunSun2.halts_iff` |

An earlier 75-state machine (118-state design) tested only primes, by trial division; without
the primality test the design shrank by 39 states.

How merged machines are proven: `minimize_clique.py` only merges states whose defined
transitions agree, so the merged machine follows the same run. The design halts by a transition
to an explicit `halt` state, which merging must keep. `gen_reduced_lean2.py` emits the merged
machine, the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
