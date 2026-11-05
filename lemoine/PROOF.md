# The proof, in plain words

This is a guided tour of the Lean proof that the machine halts if and only if Lemoine's
conjecture is false. The proof is in `../lean/TinyCryptids/Lemoine/`; each step below names the
lemma that carries it.

## What is proved

```lean
theorem TM.Lemoine.halts_iff : Halts delta start ↔
    ∃ n, 7 ≤ n ∧ n % 2 = 1 ∧ ∀ p q, Prime p → Prime q → p + 2 * q ≠ n
```

The merged machine's theorem (`TM.Lemoine.M54.halts_iff`) states the same thing for
`delta2` and is transferred from the design's (`M54.lean`). Both depend only on `propext`,
`Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

Tapes are streams seen from the head: `ones n s` is `n` ones followed by `s`, `zeros n s` the
same with 0s, `cfgL q s R` the machine in state `q` reading the first cell of `s` (the cells left
of the head are read leftwards).

## Part 1: trial division on a pair (`Test.lean`)

`../legendre`'s routines, stated for a pair anywhere on the tape: left of D's cell 0 there is a
0 and then any stream `Lx`, right of R a 0 and then any `Ry`.

* `MW Lx Ry d r c j`: the mod walk, D hole at residue `c`, R hole on cell `j`. `mw_step` advances
  both (the D hole wraps with `Dadv` from `../Core/Routines.lean`); `mw_upto` runs `j` steps.
* `mw_last_nodiv` (the hole is not back at cell 1) leads to `SH`, and `shift` to
  `SHT Lx Ry (d + 1) (r − 1)`, the start of the next trial; `tail_more` starts the walk.
* `mw_last_div`: `d ∣ r`, the composite end `CK Lx Ry d r` (state `k1b`, head two cells left of
  D). `tail_zero`: `r = 0`, the prime end `CP Lx Ry d` (state `pd`, head two cells right of R).
* `test`: by induction on `r`, from `SHT Lx Ry d r` with no divisor below `d`, the run reaches
  `CP` if `d + r` is prime and some `CK Lx Ry d' r'` with `d' + r' = d + r`, `d' ≥ 2` if not.
* `NZ Lx Rr d k`: the head on the last of `k` cells left in R (state `r1`). `norm` rewrites the
  pair as `SHT Lx Ry 2 (d + k − 4)`; `norm_halt`: if `d + k = 3` the value is 1, R has one cell and
  the test start reaches `halt`.

## Part 2: the routes (`Round.lean`)

`PL d r` is the P pair seen from its right end, then the left sentinel; `QS d r` the Q pair from
its cell 0, then the right sentinel. The checkpoint `K q dp rp dq rq` (state `PQ1`, head on the
last cell but one of Rq) has the gap `2q − 2`. `RyP` (right of P during its test) and `LxQ` (left
of Q during its test) are the gap and the other pair.

* `chk_norm`: from the checkpoint, the parser goes back to the Q hole, `z` crosses the gap and
  erases two cells of Rp: `NZ` for P.
* `nq_tail`: from Dq's cell 3, the parser finds the single 0 before the right sentinel, Rq gets a
  cell and the sentinel moves: the next checkpoint. `ParserR.zeros2` crosses the gap.
* `p_comp`: P composite (`k1b` reads the left sentinel): over P and the gap to the Q hole,
  `q + 1`. `q_comp`: Q composite (`k1b` reads the gap): the same from Q's left end.
* `p_prime`: P prime (`pd` reads the gap): to the end of Rq, `NZ` for Q.
* `q_prime`: Q prime (`pd` reads the right sentinel): Q erased, the gap filled into Rp (`fillL`),
  then `seed_tail` (the seed's last ten states and `q + 1`) writes the checkpoint
  `K 2 p (2q) 2 0` of the next `n`.

## Part 3: the theorem (`Spec.lean`, `Main.lean`)

* `Chk n q c`: `c` is a checkpoint with `dp + rp = n − 2q + 2` (two cells of Rp still to go),
  `dq + rq = q`, `dq ≥ 2`.
* `round`: from `Chk n q c` with `2q < n`: if `n − 2q = 1` the machine halts; else if `n − 2q`
  and `q` are prime it reaches `Chk (n + 2) 2`, otherwise `Chk n (q + 1)`, in at least one step
  (`reach1_of`: the run passes through `sh4`).
* `fails_iff`: `n` has no `p + 2q` iff `¬ Rep n`, where `Rep n` is a `q ≥ 2` with `2q < n` and
  `n − 2q`, `q` prime.
* `seed_reach`: the seed writes the checkpoint of `(7, 2)`.
* (←) `haltAt_of`: `halt_from`, by strong induction on `(N + 2 − n)(N + 2) + (n − 2q)`, follows
  the search up to the counterexample `N`; a smaller counterexample halts it earlier.
* (→) `not_halts_of_progress` over the checkpoints `(n, q)` with no representation below `q`:
  if every odd `n ≥ 7` has one, `n − 2q = 1` never happens.
