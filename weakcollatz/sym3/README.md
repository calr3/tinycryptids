# A 3-symbol Turing machine for the weak Collatz conjecture

**`machines/weakcollatz3_10.txt`, a 10-state, 3-symbol Turing machine** (named-state format,
see `../../tools/tm.py`; readable: `machines/weakcollatz3_10_annotated.txt`). Started on a
blank tape, it **halts iff the Collatz map has a cycle other than 1 → 4 → 2 → 1**. Lean proves
this (`TM3.WeakCollatz.halts_iff`, `../../lean/TinyCryptids/WeakCollatz3/`):

    Halts delta start ↔
      ∃ n k, 0 < n ∧ 0 < k ∧ iterate collatz k n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4

So knowing BB(10, 3) would settle the weak Collatz conjecture (the 2-symbol machine of `..`
gives the same for BB(14, 2)).

Standard text (bbchallenge format, `---` = unused):

    2RG0RB---_1LC1RB2LC_0LI0LD2LD_1RE1LD1LF_2RC0RB---_0RJ2RG---_1RH1RG1RH_2LI1RC1RH_0RA1LI1LI_0LI1RJ1RZ

## The algorithm

The algorithm of `../README.md`: rounds `M = 3, 4, …`; round `M` iterates the shortcut map
`T(v) = v/2` (v even), `(3v+1)/2` (v odd) from `v = M` until `v = 1` or `v ≥ M`, and halts iff
`v = M`.

**Tape** `C(M, v)`: cells `0 .. M−2` hold 1 except a **hole** (0) at cell `v − 1`, and cell
`M − 1` holds the **end mark** 2. For `v = M` the end mark is itself the hole. The head is on
cell 0 in `disp`.

The 14-state machine of `..` has the hole as the first blank at a round start, which makes
`v = M` after an odd step look exactly like a round start; it needs `toHN` and `peek` to
look at the cell after the hole. Here the third symbol marks the end of the block instead:

* **Halting test.** After the odd loop `check` runs to the hole: the end mark means the hole
  landed on cell `M − 1`, i.e. `T(v) = M`: halt. No `peek`.
* **Two markers.** The halving marker is a 0 and the odd marker a 2, so one state `back` runs
  left to either and does the right thing (`mark` or `markO`). `home` turns any 2 it passes into
  a 1, so it also fills the odd marker after an overflow (no `fill`).
* **The hole moves both ways in one state.** `newH` writes the hole one cell left in the
  halving and two cells right in the odd loop; on the end mark it leaves the 2 (the hole is on
  the end mark). When it reads the marker it ends the even case.
* **Overflow and v = 1 share one path.** `toHO` runs right to the end mark and makes it a 1;
  `hop` writes the new end mark on cell `M` (in the odd loop `hop` is also the cell the hole
  skips). For `v = 1` `disp` writes a 2 on cell 0 and takes the same path; `home` turns the 2
  into a 1. The blank tape is handled like `v = 1` and gives `C(3, 3)` (round 2 is skipped;
  no nontrivial cycle has top element 2).

| state | role | 0 | 1 | 2 |
|---|---|---|---|---|
| `disp` | dispatch on cell 0 | v = 1 | marker | – |
| `toH` | halving: run right to the hole | fill | | hole = end mark |
| `newH` | the new hole | marker: v even | new hole | on the end mark |
| `back` | run left to a marker | halving marker | | odd marker |
| `mark` | halving: marker one cell right | met the hole: v odd | marker | – |
| `markO` | odd: marker one cell left | passed cell 0 | marker | – |
| `toHO` | odd / v = 1: run right to the hole | fill | | end mark: T(v) > M |
| `hop` | odd: skip a cell / new end mark | new end mark | | T(v) > M |
| `home` | run left to cell −1 | next step | | fill a 2 |
| `check` | after the odd loop: run to the hole | T(v) < M | | **halt**: T(v) = M |

Every transition shown is used. The three unused ones are `disp`, `mark` and `markO` on 2. They
cannot be merged pairwise, because those states disagree on 0 and 1.

## The proof (`../../lean/TinyCryptids/WeakCollatz3/`)

`Core/Basic3.lean` is the Turing machine model of `Core/Basic.lean` with symbols `Sym` =
{`s0`, `s1`, `s2`} (`s0` blank) in place of `Bool`, on the same step systems (`Core/Sys.lean`).
The arithmetic is shared with the 2-symbol proof: `WeakCollatz/Spec.lean` (rounds of `T`,
`exists_top`, `round_stops`, `round_no_return`) and `WeakCollatz/Cycle.lean` (`counter_iff`:
`T`-cycles are Collatz cycles).

`Step.lean` follows the 2-symbol `Step.lean`, with `CF a r` = `a` ones, the hole, `r` ones,
the end mark, `RS M` = `M − 1` ones, the end mark, and `CS M v` either one:

* `step_one`: `CS M 1` reaches `RS (M + 1)`.
* Halving: `HL m d r` (marker on `m`, `d` ones, hole, `r` ones) and `HE m d` (the end mark as the
  hole). `hl_step` and `hl_loop` are as before. `he_step`, `he_even` and `he_odd` cover the first
  round trip when `v = M`. `step_even` is `CS M v` → `CS M (v/2)`.
* Odd loop: `OL c e s` (head on cell `c − 1` in `markO`, `e` ones, hole, `s` ones) and `OE c e`
  (hole on the end mark). The lemmas are `ol_step`, `ol_land` (the hole lands on the end mark),
  `ol_over` and `oe_over` (the next round), `ol_end` and `oe_end` (**halt**). `ol_run` sorts the
  three outcomes by comparing `s + 1` with `2c`, and `step_odd` turns them into
  `tc v < M`, `= M`, `> M`.
* `step_cases` and `round_run`: as in the 2-symbol proof.

`Main.lean`: `start_reach` (blank tape → `RS 3`), `haltAt_of_counter` (the top of a
nontrivial cycle is at least 3, since `T(2) = 1`), and `halts_iff_counter` and `halts_iff` as before.

## Files and checks

* `build.py` generates the machine (`python3 build.py weakcollatz3.txt`);
  `machines/weakcollatz3_10.txt` is a copy.
* `test_e2e.py` runs three checks:
  * every macro step from `C(M, v)` for `2 ≤ M ≤ 60`, including the halting case;
  * the run from the blank tape through rounds 3 .. 300;
  * 10⁸ steps without halting (C simulator).
* `annotate.py weakcollatz3.txt machines/weakcollatz3_10_annotated.txt` writes the readable
  listing.
* `gen_lean.py` writes `../../lean/TinyCryptids/WeakCollatz3/Machine.lean`.
* `RECORDS.md`: the searches for fewer states.
