# The proof, in plain words

This is a guided tour of the Lean proof that the 132-state design `pillai.txt` and the
91-state machine `machines/pillai_91.txt` have a value that repeats forever iff Pillai's
conjecture is false. The proof is in `../lean/TinyCryptids/Pillai/` (`Machine` and `M91` are
generated; the rest, about 1,400 lines, is hand-written, most of it adapted from
`../fermat/` and from a machine for Beal's conjecture that is not in this repository). It uses
the shared beeping booping semantics of `../lean/TinyCryptids/Core/BeepBoop.lean`, written for
`../abc/`. Each step below names the
lemma that carries it.

## What is proved

```lean
theorem TM.Pillai.repeats_iff :
    RepeatsForever delta St.zX3 true St.zX3 false start ↔ ¬ PillaiConjecture
theorem TM.Pillai.never_halts : ¬ Halts delta start

theorem TM.Pillai.M91.repeats_iff :
    RepeatsForever delta2 St2.zX3 true St2.zX3 false start2 ↔ ¬ PillaiConjecture
theorem TM.Pillai.M91.never_halts : ¬ Halts delta2 start2
```

* `delta` is the design and `delta2` the merged machine, both generated from the text files.
  The beep is `zX3` reading 1 and the boop is `zX3` reading 0: two transitions of one state.
* `RepeatsForever δ qb bb qo bo c` (`Core/BeepBoop.lean`): some `v` is, arbitrarily late, the
  number of beep steps strictly between two consecutive boop steps.
* `PillaiConjecture` (`Defs.lean`): for every `k ≥ 1` there is an `N` such that every
  `a, b, x, y ≥ 2` with `a ^ x = b ^ y + k` has `a + b + x + y < N`.

## The semantics (`Core/BeepBoop.lean`, shared with `../abc/`)

* `Trace a es b`: from `a` to `b` by runs of `deltaQ` (the design without its beep and boop)
  joined by single beep (`true`) or boop (`false`) steps of `delta`. `Trace.evs` turns it into
  a statement about the run of `delta`: the events between the two configurations are `es`.
* `repeatsForever_of_segments`: if the run is cut into segments, each with no event or with
  `val k` beeps and then one boop (`good k`), the run repeats a value forever iff some value is
  `val k` for infinitely many good `k`.
* `repeatsForever_iff_of_sim`: the property carries over to the merged machine.

## The routines (`Rch := Reach deltaQ`)

* **Copy and power** (`Copy.lean`, `Pow.lean`, from `../fermat/`). `copy_full`: the copy loop
  appends R to Q. `base_loop`, `round_end`: a round makes `R := R · β`. `e_adv`: the exponent
  cursor moves one cell and the next round starts. New here: the left of the exponent block is
  any stream `W` (`leftOf pre k e W`), because y is not the leftmost block, and when a power is
  done the cursor moves on to cell 1 of the next block (`e_next`, which replaces Fermat's
  `e_done`). `pow_full`: from the cursor on cell 1 with `R = 1`, the machine reaches the next
  base step (`nbC`) with `R = β ^ k`, the cursor on cell 1 of the block after the exponent block.
* **Next base** (`NextBase.lean`, `next_base`, Fermat's): the marker moves to the next base,
  R is added into A, a new `R = 1` is cut, and the next power starts at the exponent cursor.
  After x's power the cursor is on y's cell 1, so the second power uses y.
* **Compare** (`Compare.lean`). `zz_step`: one zig-zag step erases A's last cell and R's first.
  `zz_A`: A runs out first, R is erased, no event. `zz_R`: R runs out first; with one cell of A
  left there is no event, with `x' + 2` cells left one is erased, then `beeps` erases `x'` cells
  with a beep each, then the boop. `zz` combines them: from A with `α` cells and R with `ρ`, the
  trace has the events `zev α ρ` (`α − ρ − 2` beeps and a boop if `ρ + 2 ≤ α`, none otherwise)
  and ends at the clear (`clrC`). `compare_entry`: from the marker step that meets M into the
  zig-zag. These are the only lemmas about `delta` itself; `Tr.pre` and `Tr.post` attach
  `deltaQ` runs to a trace.
* **One tuple** (`Tuple.lean`). `setup`: from x's anchor, over x and y, the marker goes on a's
  cell 1 and `R = 1` is added into the empty A. `clear_home`: A and R are restored, the cursor
  that y's power left on a's cell 1 is filled (`HE`, `X1`), and the machine goes home (`Home.go`,
  from `Core/Lemmas.lean`) and puts the anchor back on x's cell 1. `tuple_check` chains setup,
  `a ^ x` (`pow_full`), `next_base`, `b ^ y`, `compare_entry`, `zz` and `clear_home`:
  `Tr (suC x y a b) (zev (1 + a ^ x) (b ^ y)) (en2C x y a b)`.
* **Enumeration** (`Enum.lean`, the NEXCOM step for four blocks): `enum_first`,
  `enum_mid`, `enum_last` with the transfer loop `u_loop`.

## The main theorem (`Main.lean`)

* `nxt` is NEXCOM on `T4`, the block lengths minus 4 (`x = r₁ + 2`, …); `reached`: every tuple
  but `0` is `itr k seedT` for some `k`; `tot_mono`, `tot_big`: the totals never decrease and
  grow without bound, so late indices have large tuples.
* `seed_reach`: from the blank tape the seed loop writes `(3, 2, 2, 2)`, `M`, A and R, and the
  run reaches `en2`: 166 concrete steps (`iterate 166 (first | gRb | gLb)`), then the tape is
  compared with `en2T seedT`.
  `enum_step` and `tuple_t` give `seg_ex`: from `en2` of tuple `k` the run reaches `en2` of tuple
  `k + 1` after at least one step, with the events `evsOf (itr (k + 1) seedT)`. `TT`/`Tm` collect
  these step numbers.
* `never_halts`: the run reaches `en2` again and again. `repeats_iff`: `repeatsForever_of_segments`
  with `goodT` (`b ^ y + 2 ≤ 1 + a ^ x`, i.e. `a ^ x > b ^ y`) and `valT` (`a ^ x − b ^ y − 1`),
  then `good_iff`: a value `v` repeats for infinitely many tuples iff `a ^ x − b ^ y = v + 1` has
  arbitrarily large solutions (via `tot_big` one way, `reached` and `tot_mono` the other), iff
  Pillai's conjecture fails.
* `M91.lean` (generated): the state map, `compat`, `excl_beep`, `excl_boop` and the transfer.
