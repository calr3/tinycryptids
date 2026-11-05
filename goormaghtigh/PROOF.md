# The proof in plain words

Lean files: `../lean/TinyCryptids/Goormaghtigh/` (`Tac`, `Step`, `Base`, `Spec`, `Main`, and the
generated `Machine` and `M53`). Configurations write the cells left of the head as a stream read
leftwards, so a block to the left is `ones n (…)` just as one to the right.

## The tape between steps

`XC r d A` is the check state `X` on the cell after the hole H, with `r` ones of R and the
separator before it, and `d` ones of D after it, then blank (`d = V − r`). `A` is what lies left
of the region: `LK b E`, the separator, Vb's `b` cells right of the base hole K, K, and `E`. Left
of K is `Env k fl f`: Vb's `k` other cells, `f + 1` zeros, and F with `fl` cells. During a step
the pass cursor splits Vb's right part (`LP b1 b2 E`). `CB k b fl f` is the start of base `b`
(`r = 1`), and `KE E b n` the end of a base: the head left of K, K and the region filled.

## One step (`Step.lean`)

* `tick`: the copy cursor C moves one cell and H one cell (`TJc c u q d`: C on R's cell `c`, `u`
  cells of R after it, `q` copies, `d` cells of D). `tick_last`: C was on R's last cell; the
  pass is done. `pass`: induction on `u`, a whole pass moves H `r` cells.
* `tick_ovf`, `pass_ovf`: H is on the region's last cell when a tick needs it to move: M, C, P
  and K are filled and the machine is at the end of the base.
* `pass_next`, `pass_last`: back to P; it moves (`b2 + 1` cells right of it) or falls off Vb, and
  then M is filled (the merge) and the machine is back at `X`.
* `step_start`: H becomes M, the new H is D's first cell, P is punched on `K + 2`.
* `passes`, `passes_ovf`: induction on `b2`, the `b − 1` passes. `step_ok`: `XC (r + 1) (d + 1)`
  reaches `XC ((r + 1)(b + 2) + 1) (d − (r + 1)(b + 1))` when that fits, and `step_ovf` the end
  of the base otherwise.

## The ends (`Base.lean`)

* `hit0`, `hit1`, `hit2`: `X` reads the blank after the region (`r = V`): H is filled, the
  machine runs past K to the zeros before Vb, erases F's last cell if `f < 2` (`f` becomes
  `f + 1`, at most 2), and comes back to fill K.
* `kstep`: K moves one cell left, and the region is reset to `R = 1`, H, `D = V − 1`: the start
  of the next base.
* `vend0`, `vend1`, `vend2`, `vend_halt`: K was on Vb's cell 1. Vb grows by one cell on the
  left; F gets its `f` cells back and moves one cell left (`f = 2`: one cell, and if F is empty
  the machine halts); `vend_tail` puts K on Vb's third cell from the right and grows the region.
* `seed_reach`: the seed writes the tape of `V = 3` and runs `vend_tail`: `CB 1 2 4 0`, base 2
  of `V = 4`.

## The numbers (`Spec.lean`)

* `it b j r` is `j` steps `r ↦ r·b + 1`; `HitFrom b V r` says the walk from `r` reaches `V`, and
  `Hit b V = HitFrom b V 1`. `hit_iff`: `Hit b V ↔ ∃ m ≥ 1, rep b m = V` (`it_rep`).
* `hc V b` counts the hits among the bases `2 … b − 1`; `bad V` is `2 ≤ hc V (V − 1)`, and
  `bad_iff` says it with two bases `y < x ≤ V − 2`. `gc V` counts the bad values below `V`.
* `conj_iff`: the statement is "some bad `V` is neither 31 nor 8191" (a hit of a base
  `b ≤ V − 2` has length ≥ 3: `rep b 1 = 1`, `rep b 2 = b + 1`). `bad_31`, `bad_8191` by
  computation. `third_iff`: that holds iff some bad `V` has `gc V = 2` (a third bad value).

## Assembly (`Main.lean`)

* `walk`: strong induction on `d`. From `XC r d`, if the walk from `r` reaches `V = r + d` the
  machine reaches `XC V 0` (`step_ok` and `hitFrom_step`), otherwise the end of the base
  (`step_ovf`, `not_hitFrom_gt`).
* `base`: one base from `CB` to `KE`, with `f = fm V b = min (hc V b) 2` and `fl = 4 − g − f`
  updated by `hit_upd` when it is a hit (`fm_succ`). `bloop`: induction on `k`, all bases, with
  `kstep` between them.
* `round`: from `CV V g` (base 2 of `V`, F with `4 − g` cells), the machine halts if `V` is bad
  and `g = 2`, and otherwise reaches `CV (V + 1) (g + [bad V])` (`fm_bad`: `f = 2` iff bad).
* `halts_iff_third`: (→) with no third bad value, every `CV V (gc V)` strictly reaches the
  next one (`CV_ne`), so `not_halts_of_progress` applies; (←) `haltAt_of`: induction from
  `V = 4` (`gc_four`, `seed_reach`) up to the third bad value. `halts_iff` combines it with
  `third_iff` and `conj_iff`. `M53.halts_iff` is transferred by `halts_iff_of_sim`.
