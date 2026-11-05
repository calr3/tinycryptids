# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Beal's conjecture fails
(`∃ a b c x y z, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧ Nat.gcd a b = 1 ∧ a ^ x + b ^ y = c ^ z`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **135** | `machines/beal_135.txt` (readable: `beal_135_annotated.txt`) | `minimize.py` (`kissat404`) on the 225-state design; the search for 134 was still running when this was committed (resume: `MIN_SOLVER=kissat404 python3 ../tools/minimize.py beal.txt out.txt 134`) | Proven in Lean: `TM.Beal.M135.halts_iff` |
| 225 | `machines/beal_225.txt` (= `beal.txt`) | `build.py`: Fermat's powers and compare with three exponents, NEXCOM over six blocks, the walk test for `gcd(a, b) = 1` | Proven in Lean: `TM.Beal.halts_iff` |

Earlier designs (not kept): 250 states (blocks of minimum length 5, base cursors from cell 3),
greedy merging about 162; 231 states (its own exit for pairs that are not coprime), greedy
merging 154 and `minimize.py` 142.

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
