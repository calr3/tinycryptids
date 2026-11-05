# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff reverse-and-add from 196 reaches
a palindrome (`∃ k, rev10 (iterate (fun x => x + rev10 x) k 196) = iterate (fun x => x + rev10 x) k 196`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **95** | `machines/lychrel_95.txt` (readable: `lychrel_95_annotated.txt`) | `minimize.py` (`kissat404` and `cadical195`, both reached 95) on the 134-state design; searches for 94 stopped without a result (container restarts; to resume: `MIN_SOLVER=kissat404 python3 ../tools/minimize.py lychrel.txt out.txt 94`) | Proven in Lean: `TM.Lychrel.M95.halts_iff` |
| 134 | `machines/lychrel_134.txt` (= `lychrel.txt`) | `build.py`: unary numbers, a mod-10 counter D, division by a hole walk through T, multiplication by 10 through the counter, a hole walk for the compare | Proven in Lean: `TM.Lychrel.halts_iff` |

Earlier designs (not kept): 159 states (first working version: X copied to T before each round,
P and Q premade), 140 (blocks made by their first deposit; `minimize.py` 108), 136 (the compare
halts on its last position; `minimize.py` 102). The first iteration of a round now walks X itself
instead of a copy, which removed the copy phase (134).

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
