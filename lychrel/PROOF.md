# The proof, in plain words

This is a guided tour of the Lean proof that the 196 machine halts if and only if
reverse-and-add from 196 reaches a palindrome. The proof is in
`../lean/TinyCryptids/Lychrel/`; each step below names the lemma that carries it.

## What is proved

```lean
theorem TM.Lychrel.halts_iff : Halts delta start ↔
    ∃ k, rev10 (iterate (fun x => x + rev10 x) k 196) = iterate (fun x => x + rev10 x) k 196
```

`rev10 n = revAux n 0` with `revAux n acc = if n = 0 then acc else revAux (n / 10) (acc * 10 + n
% 10)` (`../lean/TinyCryptids/Defs.lean`). The merged machine's theorem
(`TM.Lychrel.M95.halts_iff`) states the same thing for `delta2` and is transferred from the
design's (`M95.lean`). To trust it you need the Lean kernel, the machine model
(`../lean/TinyCryptids/Core/`) and the listing of the machine. The theorem depends only on
`propext`, `Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

## Part 1: moving around (`Find.lean`, `DStep.lean`)

* The machine moves between blocks with 3-state finders (`FindL`, `FindR`): they cross runs of
  1s and runs of at least two 0s, and stop at a single 0 (a hole). `GC l` says that the list `l`
  is made of such segments; `FindL.cross` and `FindR.cross` cross any of them.
* D is 12 cells with one hole at `d(p+1)`. `fstep` and `fstep_wrap` are `p += 1` (from 9 the
  hole wraps to `d1`); `bstep` and `bstep_wrap` are `p -= 1` (from 0 it wraps to `d10`).

## Part 2: one division by 10 (`Div.lean`)

`DV cx t c p h a Q` is the machine at D's hole while T (`t + 3` cells) has its hole at cell `c`;
`cx` is what lies between D's separator and T: nothing when T is X (`CX_nil`), or X and a gap
(`CX_gap`). The structure `CX cx` gives the `GC` lists the finders cross.

* `dv_step`: `p += 1` without a wrap, then the finder goes to T's hole and moves it one cell
  right (`n_adv`, `adv_hf`).
* `dv_wrap`: `p` wraps to 0, the machine goes past T's hole to the end of the tape and appends
  a cell to Q (or makes Q with 3 cells), then back (`excursion`).
* `dv_last`: the hole reaches T's last cell; the walk is over (`WD`).
* `divide`: from `c = 1`, `p = 9` and no Q, the walk ends with Q of `t / 10 + 3` cells and
  `p = t % 10` (`dv_walk` counts the wraps with `Qk`).

## Part 3: P := 10 A + d (`Mul.lean`, `Iter.lean`)

`PL x g a q r p` is the machine at D's hole during the multiplication: X, a gap of `g`, A with
`a + 1` cells, Q with `q`, P with `r`.

* `wd_keep` (T is X: two 0s and D on its left, it stays) and `wd_erase` (otherwise T is erased)
  make P's first cell and go back to D.
* `pl_n`: `p -= 1` and one more cell of P. `pl_w`: `p` wraps to 9, A loses its first cell, one more
  cell of P. `mul_drain` and `mul_all` repeat them; `multiply` gives P with `1 + d + 10 a` cells
  and A down to one cell.
* `pl_next`: A's last cell is erased, Q and P are the new T and A, and T's hole goes on cell 1:
  the next division starts (`DV (cxg x g) …`).

## Part 4: the reversal loop and the compare (`Cmp.lean`, `Main.lean`)

* `IT x g t a` is the machine between two iterations. `iter_one`: for `t > 0` one iteration gives
  `IT x g' (t / 10) (a * 10 + t % 10)`. `rev_loop` (strong induction on `t`) reaches
  `IT x g' 0 (revAux t a)`; `rev10_eq` turns the first iteration's `revAux (x / 10) (x % 10)` into
  `rev10 x`.
* `pl_zero`: when `t = 0`, T is erased and the compare starts with X's hole on cell `x + 1`.
* `K c j G m` is the compare with X's hole at cell `c` and `j` cells right of it; `N n G m` is the
  compare after the hole is gone. `k_step` moves one cell of A to X's end and the hole one cell
  left; `k_one` fills a hole on cell 1; `n_step` moves a cell of A without a hole.
* `k_halt`: A down to one cell with the hole on cell 1: the machine halts. `k_end` and `n_end`:
  otherwise the hole is filled and the next round starts with T = X, hole on cell 1, A = 0.
* `compare`: `a = x` halts; `a ≠ x` reaches the round for `x + a`.

## Part 5: the main theorem (`Main.lean`)

* `RD x G` is the start of a round for `x`. `round_halt`: if `rev10 x = x` it halts.
  `round_next`: otherwise it strictly reaches `RD (x + rev10 x) G'`.
* `seed_reach`: from the blank tape the seed writes D, X (`x = 1`) and the multiplication for
  `T = 59`, `A = 1`; the run computes `A = 195`, adds it to `x` and reaches `RD 196 G`.
* `reach_k`: if no earlier round found a palindrome, the start reaches round `k`.

(←) `haltAt_of`: take a palindrome `iterate Fs k 196`; by strong induction either an earlier
round halts, or the start reaches round `k` (`reach_k`) and it halts (`round_halt`).

(→) Without a palindrome every round strictly reaches the next, so no round start halts
(`not_halts_of_progress`); the start reaches round 0 (`reach_k 0`), so it does not halt either.
