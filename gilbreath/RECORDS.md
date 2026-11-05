# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Gilbreath's conjecture fails
(`∃ N k, 1 ≤ k ∧ k < (primesBelow N).length ∧ (gilbreathRow (primesBelow N) k).head? ≠ some 1`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **97** | `machines/gilbreath_97.txt` (readable: `gilbreath_97_annotated.txt`) | `minimize.py` (`cadical195` and `kissat404` both reached 97) on the 151-state design; searches for 96 stopped without a result (container restarts; to resume: `MIN_SOLVER=kissat404 python3 ../tools/minimize.py gilbreath.txt out.txt 96`) | Proven in Lean: `TM.Gilbreath.M97.halts_iff` |
| 151 | `machines/gilbreath_151.txt` (= `gilbreath.txt`) | `build.py`: `../legendre`'s trial division, the last diagonal (without the last prime) as a queue of unary blocks rebuilt by `|L - B|` steps at each prime | Proven in Lean: `TM.Gilbreath.halts_iff` |

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.

What does not merge (in the 97-state machine): mostly the finders, three states each, whose
found-actions differ (to G, Z, L's hole from either side, D's hole), the two walks to B, and
`../legendre`'s parsers.
