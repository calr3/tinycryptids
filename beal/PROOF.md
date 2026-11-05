# The proof, in plain words

This is a guided tour of the Lean proof that the Beal machine halts if and only if Beal's
conjecture fails. The proof is in `../lean/TinyCryptids/Beal/`; each step below names the lemma
that carries it.

## What is proved

```lean
theorem TM.Beal.halts_iff :
    Halts delta start ↔ ∃ a b c x y z, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧
      Nat.gcd a b = 1 ∧ a ^ x + b ^ y = c ^ z
```

The right-hand side is a counterexample to Beal's conjecture. The merged machine's theorem
(`TM.Beal.M135.halts_iff`) states the same thing for `delta2`, and is transferred from
the design's (`M135.lean`). To trust it you need the Lean kernel, the machine model
(`../lean/TinyCryptids/Core/`) and the listing of the machine. The theorem depends only on
`propext`, `Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

## Part 1: the coprimality walk (`Walk.lean`)

`TK a b j e La Rb` is the machine at the start of a tick: H_a with `a` positions to its left
and `b` to its right in block a, H_b with `j` and `e` in block b, the head just left of H_b.

* `tick`, `tickW`: both holes move one position right; in `tickW` H_b wraps to its first position.
* `wrapC`, `wrapM`, `wrapN`: H_a wraps, and H_b's position decides: on its first position the
  pair is coprime (`CopC`, the machine goes on to the powers); on its last it is not (`NcC`);
  otherwise H_b moves on and the walk continues.
* `stride`, `strides`, `test` are those of the Carmichael machine, word for word: with
  `first_hit` (`../lean/TinyCryptids/Carmichael/Spec.lean`), the walk from both first positions
  ends in `CopC` if `gcd a b = 1` and in `NcC` otherwise (`Res`).

## Part 2: one power (`Copy.lean`, `Pow.lean`)

A base block of Beal is Fermat's with one more 1 at its start, so the copy loop and the base
loop (`copy_full`, `base_adv`, `base_loop`) are Fermat's, unchanged. New are:

* `leftOf n m E e Lx`: what lies left of the base block: a separator, the block next to it
  (`m` cells), a separator, the next exponent block (`n + 2` cells), a separator, the exponent
  block (`E + 1` cells, its cursor on cell `e`), and the rest `Lx`.
* `round_end`: the base cursor back to cell 2, Q merged into R, and back to the exponent cursor;
  when that cursor is on the block's last cell it is next to the separator, and
  `ParserL.find3` reads the three 0s as a hole.
* `e_adv` (the exponent cursor moves on, next round) and `e_done` (it wraps: it moves to cell 1
  of the next exponent block, and the machine goes to the base cursor, `nbC`).
* `pow_full`: from round 1 with R = 1, the machine reaches `nbC` with R = β^E.

## Part 3: one tuple (`Stack.lean`, `Tuple.lean`)

* `next_base`: the base cursor moves to the next block, R is added into A, a new R = 1 is pushed
  and the next power starts (Fermat's `next_base`, with the exponent block one further on).
* `compare_entry` and `zz_result` (Fermat's zig-zag): after the third power, the machine halts iff
  A = R.
* `walk_entry`: from the anchor, the holes go on a's and b's first positions. `cop_start`: in the
  coprime case R = 1 is pushed and the first power starts at H_a. `nc_exit`: in the other case
  H_a is filled and the machine goes home (`Home.goHole`, the anchor is still there) to the next
  enumeration step. `clear_home`: after an unequal compare, A is restored, the exponent cursor
  left in a is filled, and the machine goes home and puts the anchor back.
* `tuple_check`: from the walk's start, the machine halts if `gcd a b = 1` and
  `a^x + b^y = c^z`, and otherwise reaches the next enumeration step with the same tuple.

## Part 4: the enumeration and the main theorem (`Enum.lean`, `Main.lean`)

* `nxt` is NEXCOM on the six block lengths minus 4. `reached`: every tuple but `0` is reached
  from the seed `(1, 0, 0, 0, 0, 0)` (well-founded recursion: each tuple has a predecessor that
  is smaller in (total, r₆, r₅, r₄, r₃, r₂)).
* `enum_first`, `enum_mid` (after `k` minimal blocks; the transfer loop `u_loop`), `enum_last`:
  the machine's enumeration step, one lemma per case; `enum_step` puts them together.
* `seed_reach`: from the blank tape the machine writes the seed and reaches the enumeration.
* `cycle`: from one enumeration step to the next, it halts iff the next tuple is a solution.

(←) With a counterexample, `reached` gives its place in the order, and `halts_if_sol` follows the
cycles to it (`haltAt_of`).

(→) Without one, every cycle strictly reaches the next enumeration step, so none of them halts
(`not_halts_of_progress`); the start reaches the first one (`seed_reach`), so it does not halt
either.
