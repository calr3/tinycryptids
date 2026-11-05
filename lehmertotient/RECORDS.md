# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Lehmer's totient problem has a
counterexample (`∃ n, 2 ≤ n ∧ ¬ Prime n ∧ totient n ∣ n - 1`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **67** | `machines/lehmertotient_67.txt` (readable: `lehmertotient_67_annotated.txt`) | `minimize.py` (`kissat404`, `cadical195` and `maplechrono` all reached 67) on the 106-state design; greedy merging gave 70; the searches for 66 were stopped after an hour without a result (`maplechrono` timed out; to resume: `MIN_SOLVER=kissat404 python3 ../tools/minimize.py lehmertotient.txt out.txt 66`) | Proven in Lean: `TM.LehmerTotient.M67.halts_iff` |
| 106 | `machines/lehmertotient_106.txt` (= `lehmertotient.txt`) | `build.py`: `../carmichael`'s walk counts `φ(n)` into a pair `D 00 P`, one of `../legendre`'s mod walks tests `φ(n) ∣ n − 1 − φ(n)` | Proven in Lean: `TM.LehmerTotient.halts_iff` |

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
