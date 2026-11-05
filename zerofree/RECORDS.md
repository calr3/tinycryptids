# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff some power 2^n with n > 86 has
no decimal digit 0 (`∃ n, 86 < n ∧ ∀ k, 2 ^ n / 10 ^ k ≠ 0 → (2 ^ n / 10 ^ k) % 10 ≠ 0`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **44** | `machines/zerofree_44.txt` (readable: `zerofree_44_annotated.txt`) | `minimize.py` (`cadical195`) on the 55-state design; 43 timed out (1 h each with kissat404, cadical195, maplechrono), so unknown | Proven in Lean: `TM.ZeroFree.M44.halts_iff` |
| 55 | `machines/zerofree_55.txt` (= `zerofree.txt`) | `build.py`: decimal digits in two codes, a 6-bit counter of powers without a 0 | Proven in Lean: `TM.ZeroFree.halts_iff` |

How the design got here:

* **One code, with back-steps.** A first design used a single code for the digits. Its
  doubling pass wrote each digit's cells as soon as they were determined, then went back
  for the rest. It had 64 states, and exact merging brought it to about 50.
* **Two codes.** The current design uses two codes, so the pass never steps back
  (`twocode.py`, `README.md`). That gave 55 states, and 44 after merging.
* **No small single code exists.** A direct search found no decimal doubling transducer
  with at most 11 states for any 3-cell code.

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. An undefined transition would be a don't-care,
and merging can define it: an earlier merge did exactly that, and the result never halted.
`gen_reduced_lean.py` emits the merged machine, the state map `phi`, a `compat` check and the
theorem transferred by `halts_iff_of_sim`.
