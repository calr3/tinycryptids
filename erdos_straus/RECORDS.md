# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff the Erdős–Straus conjecture is
false (`∃ n, 2 ≤ n ∧ ∀ x y z, 1 ≤ x → 1 ≤ y → 1 ≤ z → 4 * x * y * z ≠ n * (x * y + y * z + z * x)`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **128** | `machines/erdos_straus_128.txt` (readable: `erdos_straus_128_annotated.txt`) | `minimize_clique.py` (`cadical195`) on the 187-state design: clique lower bound 125, 125–127 unsatisfiable, so 128 is optimal for this design | Proven in Lean: `TM.ErdosStraus.M128.halts_iff` |
| 187 | `machines/erdos_straus_187.txt` (= `erdos_straus.txt`) | `build.py`: for each `n` and `n < 4x ≤ 3n`, the y values with `m < ay ≤ 2m + 2` (`a = 4x − n`, `m = nx`) tested for `ay − m ∣ my` by `../oddperfect`'s mod walk; everything by additions | Proven in Lean: `TM.ErdosStraus.halts_iff` |

Earlier designs (not proven; the Lean proof is for the 187-state design): a first layout with
a separate copy of `n` for the copies and the debt hole in N (241 states, clique bound 141,
at least 146 merged), and a version of the present one without the halting transition for an
`R` of 3 cells and without filling the A cursor at the stop of the y loop (182 states,
119 merged, but wrong: it halted by an undefined transition, which merging does not keep, and
left a stale cursor for the next x; the proof found both).

How merged machines are proven: `minimize_clique.py` only merges states whose defined
transitions agree, so the merged machine follows the same run. The design halts by a
transition to an explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits
the merged machine, the state map `phi`, a `compat` check and the theorem transferred by
`halts_iff_of_sim`.
