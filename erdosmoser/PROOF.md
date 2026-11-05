# The proof, in plain words

This is a guided tour of the Lean proof that the machine halts if and only if the Erdős–Moser
equation has a solution with `k ≥ 2`. The proof is in `../lean/TinyCryptids/ErdosMoser/`; each
step below names the lemma that carries it.

## What is proved

```lean
theorem TM.ErdosMoser.halts_iff :
    Halts delta start ↔ ∃ k m, 2 ≤ k ∧ 1 ≤ m ∧ powSum m k = m ^ k
```

The merged machine's theorem (`TM.ErdosMoser.M71.halts_iff`) states the same thing for
`delta2` and is transferred from the design's (`M71.lean`). Both depend only on `propext`,
`Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

Tapes are streams seen from the head: `ones n s` is `n` ones followed by `s`, `zeros n s` the
same with 0s, `sep s` two 0s and `s`, `cfgL q s R` the machine in state `q` reading the first cell
of `s` (the cells left of the head are read leftwards). `KL k e` is the tape left of M, read
leftwards: the separator, then K (`k + 2` cells) with its cursor on cell `e`. `rgt X r q` is the
tape right of M: `00 A 00 R 00 Q` with A's cells `X`, R of value `r` (cursor on cell 1) and `q`
cells of Q.

## Part 1: the powers (`Copy.lean`, `Pow.lean`)

The copy loop is `../fermat/`'s, verbatim (`copy_full`). The base block is the part of M right
of the marker, so the tape left of it is the marker and M's first `p` cells (`ML p k e`).

* `bAtC Lb β j b X r q`: the base cursor on cell `j` of the base block, the cell holding `b`
  (`true` only at the start of a round, when there is no hole yet; `bAt_any`).
* `base_adv`, `base_loop`: one base step makes one copy of R onto Q; from cell `j` to the last
  cell `β` Q gains `r (β − j)`. When the new cursor is on the last cell, the parser coming back
  from Q sees three 0s (`nb_back0`, with `ParserL.find3` from `../beal/`).
* `round_end`: on the last cell the round ends: back to the marker, Q merged into R, and the left
  parsers skip R's hole and the marker and find the exponent cursor (`lg_find`, which also covers a
  cursor next to the separator). `eAtC k e p β X r` is the state `eAt` on the exponent cursor.
* `e_adv`: the cursor moves on and the next round starts from the marker. `e_done`: after the
  round on K's last cell the cursor goes back to cell 1 and the head stops on the marker in state
  `N1` (`nbC`).
* `one_round`, `pow_all`, `pow_full`: from the anchor with `R = 1`, the power ends in `nbC` with
  `R = β ^ k`.

## Part 2: one pair (`Next.lean`, `Compare.lean`, `Main.lean`)

* `next_base`: marker on `p + 1 ≥ 2`: it moves left, R is added into A (`A` gains `r`) and the
  end of the merged block becomes the gap and `R = 1`. The next power starts at the anchor with
  base `β + 1`.
* `powers`: from the start of a pair `pairC k m` (marker on `m`, base 1, `A = 0`), after the power
  with base `j + 1`, A holds `sumP k j = 1^k + … + j^k`.
* `final_start`: marker on cell 1 (`R = m^k`): fill it, fill R's hole and erase R's first cell.
  The zig-zag starts with A's `1 + sumP k (m − 1)` cells against R's `m^k + 1`.
* `Z`, `zz_step`, `zz_A`, `zz_R`, `zz`: one zig-zag round erases a cell of each block. **HALT** iff
  they run out together (`HaltAt`), else the rest of A or R is erased and the head stops right of
  M (`clrC`).

## Part 3: the next pair (`End.lean`)

* `end_common`: `00 A 00 R` is written right of M (`A = 0`, `R = 1`), the marker goes on M's third
  cell from the right, and the head reads M's cell `m − 2`.
* `end_shift`: `(k, m + 2) → (k + 1, m + 1)`: the separator between K and M moves one cell right.
* `end_reset`: `(k + 2, 1) → (2, k + 2)`: the separator is filled, K grows by one cell on the left
  (the anchor moves with it) and a new separator is cut after K's fourth cell.

## Part 4: the theorem (`Main.lean`)

* `powSum_eq`: `powSum (j + 1) k = sumP k j` for `k ≥ 1` (the term `0^k` is 0).
* `cycle`: from `pairC k m`, halt iff `powSum m k = m ^ k`, else reach the next pair `nxt (k, m)`
  in at least one step (`reach1_of`: the run passes through `N1`).
* `reached`: every pair with `k ≥ 2`, `m ≥ 1` except `(2, 1)` is `itr j (2, 2)` for some `j`
  (strong induction on the diagonal `k + m`, then on `k`). `(2, 1)` is not a solution.
* `seed_reach`: the seed writes `K = 2`, `M = 1` and the end of the pair `(2, 1)` leads to
  `(2, 2)`.
* (←) `haltAt_of`: `halts_if_sol` follows the pairs to the solution. (→) `not_halts_of_progress`
  over the family `pairT t` with `t` valid.
