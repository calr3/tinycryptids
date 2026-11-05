# The Lean proof, in plain words

Files: `../lean/TinyCryptids/Amicable/` (namespace `TM.Amicable`). Tape halves are streams
(`Core/Basic.lean`), and `Rch` is reachability for `deltaNB`, the design without its beep.

* **`Spec.lean`**: `Small x := x < properDivSum x ∧ properDivSum (properDivSum x) = x` and
  `inf_iff : InfinitelyManyAmicable ↔ ∀ N, ∃ x, N ≤ x ∧ Small x`. Going right, take an amicable
  `n ≥ N² + N + 1`. If `n < s(n)`, `n` is small. Otherwise its partner `m = s(n) < n` is
  small, and `m ≥ N`, because `n = s(m) ≤ m²` (`properDivSum_le`). Also `divSumBelow_step`
  (one more candidate divisor) and `mod_succ`.
* **`Scan.lean`**: `../OddPerfect`'s mod walk and shift (`dadv`, `mw_step`, `walk`, `shift`,
  `shift_end`, `fill_hole`), with a general stream `Z` right of R instead of a blank, because
  pass 2 has N there. The add is new. `ACC a b` is the accumulator read leftwards: `b` ones,
  the hole, then `a` ones. `add_unit` is one unit for any accumulator `ones b (F ::: V)`, giving
  `ones (b + 1) (F ::: tl V)`. `add_all` and `add_from` cover a whole D (or a whole N, for the
  copies), using `tln` (drop `k` cells) and `tln_ones`. `dstep` tests one `d`. `scan_from` and
  `scan` run the loop over `d`: `MW (F ::: ACC a b) Z 1 (x − 2) 1 0` reaches
  `RE (F ::: ACC (a − s x) (b + s x)) Z x`.
* **`Round.lean`**: `CS k` (N = `1^k`, head in `k0` right of N) and the round for `x = k + 1`:
  `start1` (N's new cells, the marker, the copy into P, P's preload, the cut), `pass1`,
  `to_hole1` (back to P's hole, filling it), `reject1`/`cleanup` (erase left of N: `CS x`),
  `start2`/`pass2` (P's 4 extra cells, the scan of `m`), `post2` (fill, the subtraction copy,
  back to the hole), `check_no`, `check_beep`, and `after_beep`, the beep step, the only
  step proved for `delta`. These combine into `round_no : ¬ Small x → Rch (CS k) (CS (k+1))`
  and `round_beep : Small x → ∃ q, Rch (CS k) (BeepCfg x q)`.
* **`Main.lean`**: `round_step` (each round takes at least one step: `CS_ne`), `reach_cs`,
  `never_halts`, and `quasihalts_iff`, shaped like `../Mersenne`. Going right, past any step
  there is a round with `Small x`, and it beeps. Going left, from the round past the last
  small `x`, `deltaNB` never halts (`not_halts_of_progress`), so `quasihalts_of_sub` applies.
* **`M55.lean`** (generated): the merged machine, the state map `phi`, `compat`, and `excl`
  (no state that reads 0 joins `H5`). `quasihalts_iff_of_sim` transfers the theorem.
