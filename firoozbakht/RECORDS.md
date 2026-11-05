# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Firoozbakht's conjecture is
false (`∃ p q, Prime p ∧ Prime q ∧ p < q ∧ (∀ r, p < r → r < q → ¬ Prime r) ∧
p ^ (primeCount p + 1) ≤ q ^ primeCount p`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **117** | `machines/firoozbakht_117.txt` (readable: `firoozbakht_117_annotated.txt`) | `minimize.py` (`kissat404`; `cadical195` and `maplechrono` reached 118) on the 166-state design; 116 not decided (to resume: `MIN_SOLVER=kissat404 python3 ../tools/minimize.py firoozbakht.txt out.txt 116`) | Proven in Lean: `TM.Firoozbakht.M117.halts_iff` |
| 166 | `machines/firoozbakht_166.txt` (= `firoozbakht.txt`) | `build.py`: primes by trial division against a list kept on the tape (Feit–Thompson's CYC, mirrored), `p^(n+1)` and `q^n` by two power runs with one exponent block, a zig-zag comparison | Proven in Lean: `TM.Firoozbakht.halts_iff` |

How merged machines are proven: `minimize.py` only merges states whose defined
transitions agree, so the merged machine follows the same run. `sim_run` and
`halts_iff_of_sim` (`lean/TinyCryptids/Core/Basic.lean`) turn this into a proof:
`gen_reduced_lean.py` emits the merged machine, the state map `phi`, a `compat` check and the
transferred theorem.
