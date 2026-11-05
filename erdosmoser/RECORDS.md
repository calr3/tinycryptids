# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff the Erdős–Moser equation has a
solution with `k ≥ 2` (`∃ k m, 2 ≤ k ∧ 1 ≤ m ∧ powSum m k = m ^ k`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **71** | `machines/erdosmoser_71.txt` (readable: `erdosmoser_71_annotated.txt`) | `minimize.py` (`kissat404` and `cadical195`, both reached 71) on the 117-state design; the searches for 70 were stopped without a result (to resume: `MIN_SOLVER=kissat404 python3 ../tools/minimize.py erdosmoser.txt out.txt 70`) | Proven in Lean: `TM.ErdosMoser.M71.halts_iff` |
| 117 | `machines/erdosmoser_117.txt` (= `erdosmoser.txt`) | `build.py`: Fermat's powers, add into A and zig-zag; the bases as a marker in M; the pairs along the diagonals | Proven in Lean: `TM.ErdosMoser.halts_iff` |

Earlier designs (not kept; merged sizes by `minimize.py` when its runs were stopped):

* 125 states → 76: Fermat's zig-zag and clear, a real base cursor in M placed by every round
  end, R pushed by a scan to the end of the stack (`t1`–`t3`).
* 120 → 76: a zig-zag that erases first and then looks whether the block is empty (6 states
  instead of 9), `A = 0` as one cell.
* 117 → 76: no base hole at the start of a round (the round end no longer places one, and the
  marker step and the compare have one hole less to move); K one cell longer.
* 121 → 73: the merge into A pushes the next `R = 1 0 1` from the end of the merged block, and the
  clear writes A and R. No scan to the end of the stack is left.
* 117 → 71 (this design): the base cursor may sit on M's last cell next to the separator (two
  states fewer in the base step), now that no scan crosses M.

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
