# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff the second Hardy–Littlewood
conjecture is false (`∃ x y, 2 ≤ x ∧ 2 ≤ y ∧ primeCount x + primeCount y < primeCount (x + y)`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **79** | `machines/hardylittlewood2_79.txt` (readable: `hardylittlewood2_79_annotated.txt`) | `minimize.py` on the 136-state design (`kissat404` and `cadical195` both reach 79, `maplechrono` 80); the search for 78 (three solvers for about 35 minutes, then `kissat404` and `cadical195` for about 100 more) found nothing and was stopped (resume: `MIN_SOLVER=kissat404 python3 ../tools/minimize.py hardylittlewood2.txt out.txt 78`) | Proven in Lean: `TM.HardyLittlewood2.M79.halts_iff` |
| 136 | `machines/hardylittlewood2_136.txt` (= `hardylittlewood2.txt`) | `build.py`: the gap lists B' and A, one counter E per prime, legendre/'s mod walk from d = 3 | Proven in Lean: `TM.HardyLittlewood2.halts_iff` |

What stays unmerged in the 79-state machine: the ten hole-finding parsers (most are single
states or pairs), the two trips home (adding and subtracting differ only in what they do at E
and which hole they return to), and the prime rebuild's own copy of the consolidation scan.

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
