# The proof, in plain words

This is a guided tour of the Lean proof that the machine halts if and only if Lehmer's
conjecture fails. The proof is in `../lean/TinyCryptids/LehmerTau/`; each step below names the
lemma that carries it.

## What is proved

```lean
theorem TM.LehmerTau.halts_iff : Halts delta start ↔ ∃ n, 1 ≤ n ∧ tau756 n = 0
```

The merged machine's theorem (`TM.LehmerTau.M295.halts_iff`) states the same thing for
`delta2` and is transferred from the design's (`M295.lean`). Both depend only on `propext`,
`Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

Tapes are streams seen from the head: `ones n s` is `n` ones followed by `s`, `F` a 0, `cfgL q s
R` the machine in state `q` reading the first cell of `s`. `LS a K` is the tape left of a
separator read leftward: the blocks `K` (each `pl n`, `n` plain cells, or `dg f c`, `f + 2`
cells with a hole at `c`), then the accumulator of `a + 1` cells, then blank.

The constants 65, 252, 691 are variables `kA, kB, kC ≥ 1` everywhere except in the seed.

## Part 1: frames and the divisor loop (`Walk.lean`, `Loop.lean`)

* A frame is a block X (`x + 2` cells, a hole at the residue) and a block R. `DV X B x r`: the
  walk has stopped at the divisor `x` of `x + r` (state `k1`). `RS`/`RS3`: the machine is back
  after using the divisor. `next_div`: from a resume, the next divisor `y` of `x + r`, with no
  divisor in between. `F2_UN` and `unshift`: after the last divisor the frame goes back to
  `X = 1, R = s − 1`.
* `dloopR`, `dloop'`: if an action takes `DV (Xs a) B x (N − x)` to `RS3 (Xs (a + g x)) B x
  (N − x)` at every divisor `x`, then the whole loop adds `dsum g N N = Σ_{x ∣ N} g x`
  (`dsum_gap`, `dsum_div`). The accumulator `a` may sit anywhere in the tape `Xs a`.

## Part 2: the odometer (`Trip.lean`, `Run.lean`)

* `TW a kR vs` is the whole tape word: the accumulator, the blocks `kR` (some of them active
  digits `dg f c`) and the var digits `vs` right of S0 (factor `f`, position `p`).
* `trip`, `count1`: one count, a cell at the far left (`FarL`/`FarR` over `Clean12` words, whose
  zero runs have length 1 or 2). `cv_adv`, `cv_wrap`, `VC`: the carry over the var digits;
  `k_adv`, `k_wrap`, `KSc`: the carry over the active K digits; `incV`, `incK` the counter as a
  function.
* `run`: from any position, a run adds `pV vs * pK kR` (the product of all factors) to the
  accumulator; by induction on the number of counts (`count`, with the counter's value `vV`,
  `vK` going up by one per count).

## Part 3: copies and the erase (`Copy.lean`, `Post.lean`)

* `copy1`: one copy of the source block (cursor at cell 1) to the right end, cell by cell
  (`tick`, `ticks`). `xstep`, `xloop`: the counter X makes `12 − h` copies and fills the cursor.
* `runpost`: after a run the copies are erased (`el_one`, `el_all`) and the head stops left of S0.

## Part 4: the phases (`RAct`, `RLoop`, `RStep`, `LStart`, `LAct`, `End`)

* `eact`: at a divisor `e` of `j` (R phase): fill D's hole (`ve_fill`), five copies of E, D's
  cursor (`ed_d`), five copies of D (`copies_R`), the run (`run_R`), E's hole back (`post_R`);
  P gains `d⁵ e⁵ · pK KL`.
* `dact_R`: at a divisor `d` of `i`: into E (`dd_e`), the e-loop (`dloopR` with `eact`), E
  unshifted and D's hole back (`ue_d`).
* `ud_uk`, `ri_next`: after the d-loop, the next `i` (Re gives a cell to Rd); `ri_last`: at
  `i = n − 1` the L phase starts (E', Re', M created, K252 off).
* `dact_L`: at a divisor `d` of `n`: five copies of D and the run with K691 (`copies_D`,
  `run_L`), the switches flipped (`post_L0`, `flip_1`), eleven copies and the run with K65, the
  switches back (`flip_2`); M gains `kC d⁵ + kA d¹¹`.
* `endn`: the frames reset (`en_tl`, `tl_loop`), the compare (`cm_start`, `cmp`: halt iff
  `M = P`, otherwise P is reset), K252 on and the walk on `n + 1` (`ck_next`).

## Part 5: one `n`, the seed, the theorem (`NStep`, `Seed`, `Main`)

* `nstep`: from `Sn n`, `r_iter`/`r_all` (all `i < n`), the L-phase loop, `endn`: halt iff
  `mM = rP`, else `Sn (n + 1)`.
* `Seed`: the written word (`Pat_eq`, `seed_start`), the binary decrement (`dc1`, `dc3`, `decL`,
  `vL`), a counter drained into a block (`drain_step`, `drain_all`), the next counter
  (`next_counter`), the end (`seed_end`); `seed : Rch start (Sn 65 252 691 2)`.
* `Main`: `rP_eq`, `mM_eq` (`gI_eq`: one pair is `σ₅(i) σ₅(n−i)`), `key`: `M = P ↔ tau756 n = 0`.
  (←) `haltAt_of`: from the seed and `halt_from` (`τ(1) ≠ 0`). (→) `no_halt`:
  `not_halts_of_progress` over the starts `Sn n` (`Sn_ne`: consecutive starts differ, so each step
  makes progress).
