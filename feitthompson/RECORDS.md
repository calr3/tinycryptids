# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff the Feit–Thompson conjecture is
false (`∃ p q, Prime p ∧ Prime q ∧ p ≠ q ∧ rep p q ∣ rep q p`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **106** | `machines/feitthompson_106.txt` (readable: `feitthompson_106_annotated.txt`) | `greedy_merge.py` (112) on the 149-state design, then `minimize.py` (`kissat404`) down to 106; 105 not decided | Proven in Lean: `TM.FeitThompson.M106.halts_iff` |
| 149 | `machines/feitthompson_149.txt` (= `feitthompson.txt`) | `build.py`: primes by trial division against a list kept on the tape, `rep` by Horner's rule, every divisibility test by one cyclic-hole routine CYC | Proven in Lean: `TM.FeitThompson.halts_iff` |
| 107 | (not kept) | the 150-state design, where the pair test went left to B's hole by a 3-state step-and-parser (`t1`, `TB`) instead of `t1`, `t2`; `minimize.py` (`kissat404`, `cadical195`) | was proven (`M107`) |

A first version of the design (170 states) merged to 118.

How merged machines are proven: `minimize.py` only merges states whose defined
transitions agree, so the merged machine follows the same run. `sim_run` and
`halts_iff_of_sim` (`lean/TinyCryptids/Core/Basic.lean`) turn this into a proof:
`gen_reduced_lean.py` emits the merged machine, the state map `phi`, a `compat` check and the
transferred theorem.
