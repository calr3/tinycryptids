# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Carmichael's totient
conjecture fails (`∃ m, 1 ≤ m ∧ ∀ n, n ≠ m → totient n ≠ totient m`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **80** | `machines/carmichael_80.txt` (readable: `carmichael_80_annotated.txt`) | `minimize.py` (`cadical195`) on the 117-state design (greedy merging gave 84); 79 not yet decided | Proven in Lean: `TM.Carmichael.M80.halts_iff` |
| 117 | `machines/carmichael_117.txt` (= `carmichael.txt`) | `build.py`: windows over `v`, the walk test for `gcd(k, M − k) = 1`, a count in V | Proven in Lean: `TM.Carmichael.halts_iff` |

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
