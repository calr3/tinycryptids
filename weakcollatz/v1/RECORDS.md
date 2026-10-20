# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff the Collatz map
has a cycle other than 1 → 4 → 2 → 1
(`∃ n k, 0 < n ∧ 0 < k ∧ iterate collatz k n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **23** | `machines/weakcollatz_23.txt` (readable: `weakcollatz_23_annotated.txt`) | `minimize.py` (`cadical195`) on the 25-state design; 22 is UNSAT for merging this design | Proven in Lean: `TM.WeakCollatzV1.M23.halts_iff` |
| 25 | `machines/weakcollatz_25.txt` (= `weakcollatz.txt`) | `build.py`: one block, the value as a hole, cycle search by largest element | Proven in Lean: `TM.WeakCollatzV1.halts_iff` |

For comparison, the bbchallenge wiki's cryptid list gives a 124-state machine
(`weak_Collatz_conjecture_124_2.txt`, marked unverified) for the same conjecture.

How merged machines are proven: `minimize.py` / `greedy_merge.py` only merge states whose
defined transitions agree, so the merged machine follows the same run. `sim_run` and
`halts_iff_of_sim` (`lean/TinyCryptids/Core/Basic.lean`) turn this into a proof: `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check (one case per transition) and the transferred theorem.
