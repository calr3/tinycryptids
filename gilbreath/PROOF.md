# The proof, in plain words

This is a guided tour of the Lean proof that the Gilbreath machine halts if and only if
Gilbreath's conjecture fails. The proof is in `../lean/TinyCryptids/Gilbreath/`; each step below
names the lemma that carries it.

## What is proved

```lean
theorem TM.Gilbreath.halts_iff : Halts delta start ↔
    ∃ N k, 1 ≤ k ∧ k < (primesBelow N).length ∧ (gilbreathRow (primesBelow N) k).head? ≠ some 1
```

`primesBelow N` is the list of primes below `N`, `absDiffs` takes absolute differences of
neighbours and `gilbreathRow l k` is row `k` of the triangle on `l`
(`../lean/TinyCryptids/Defs.lean`). The merged machine's theorem (`TM.Gilbreath.M97.halts_iff`) states the
same thing for `delta2` and is transferred from the design's (`M97.lean`). To trust it you need
the Lean kernel, the machine model (`../lean/TinyCryptids/Core/`) and the listing of the machine.
The theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

## Part 1: the statement at list level (`Spec.lean`)

`D m` is the last diagonal of the triangle on the
primes below `m`; a prime `m` gives `D (m + 1) = ext (D m) m`, where
`ext [e0, e1, …] p = [p, |p - e0|, ||p - e0| - e1|, …]` (`row_snoc`, `D_spec`).
`fail_iff`: the conjecture fails iff some prime `m ≥ 3` has `lst (ext (D m) m) ≠ 1`.
`lst_ext_cons` drops the first entry: `lst (ext (e :: E) q) = lst (ext E |q - e|)`, which is why
the machine does not store the last prime.

## Part 2: trial division (`Trial.lean`)

The routines of `../legendre` (`mw_step`, `mw_last_nodiv`, `shift`, `tail_more`, `rebuild`, …)
are stated for any tape `X` left of D, so they are reused as they are. `cand`: a prime `m`
reaches `PX X m` (the head left of D, about to look for G), a composite one reaches some
`CP X d r` with `d + r = m`.

## Part 3: one step `Z := |L - B|` (`Walk.lean`, `Queue.lean`)

* The finders are `../Lychrel/Find.lean`'s (`FindL.cross`, `FindR.cross` over `GC` lists);
  `FindL.crossZ1` enters one in the middle of a gap. `WalkR` is the walk to B: it crosses holes and
  separators of two or three 0s (`WC` lists) and turns back at four 0s (`WalkR.cross`,
  `WalkR.find`).
* `CA z x h os ol y e Tr` is the machine on L's cursor hole (cell `h`): Z has value `z`, L value
  `x`, `mid os ol` lists the finished values, M and the old values left, B has value `y`.
  `GC.midrev` and `WC.midl` say that the finders and the walk cross `mid`.
* `p1a` (cursor advanced, `B -= 1`), `p1b` (cursor advanced, `B = 0`: `Z += 1`, via `zinc`),
  `p2a` (L exhausted: `B -= 1`, `Z += 1`), `p2b` (L exhausted, `B = 0`: B is erased, `SE`).
* `phase1`, `phase2`, `step`: from the cursor at cell 1 the step reaches `SE (ad x y) …`, Z having
  the value `|x - y|`.

## Part 4: the update and the candidates (`Update.lean`, `Main.lean`)

* `step_end`: another old value follows; L becomes a stored block, the next Z is made (`mkz`) and
  the next step starts with L = the old Z.
* `final_pre`, `final_ok`, `final_halt`: M is next; Z = 1 writes the new M and `G = H(1)` and
  goes back to D for the rebuild; otherwise the machine halts.
* `prime_start`: from D to G's hole, make Z, start the first step with L = G. `composite`:
  G += 1 and back to D.
* `upd` (induction on the old values): the whole update reaches the rebuild with the stored list
  `ext S g` if its last entry is 1, and halts otherwise.
* `RC g S e m` is the machine before testing `m`; `Inv m` says `D m = p :: S` and `g = m - p`.
  `inv_step`: a candidate with no counterexample strictly reaches `Inv (m + 1)`; a counterexample
  halts. `seed_reach`: the seed reaches `RC 1 [1] 0 4` (`D 4 = [3, 1]`).

(←) `haltAt_of`: take a counterexample prime `m` (`m ≥ 4`, since `m = 3` is fine); by strong
induction either an earlier candidate halts, or the start reaches candidate `m` (`reach_k`) and
it halts. (→) Without a counterexample every candidate strictly reaches the next, so no
candidate configuration halts (`not_halts_of_progress`); the start reaches the first, so it does
not halt either.
