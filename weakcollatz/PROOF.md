# The proof, in plain words

This is a guided tour of the Lean proof that the 14-state machine
`machines/weakcollatz_14.txt` halts if and only if the Collatz map has a cycle other than
1 → 4 → 2 → 1. The proof is in `../lean/TinyCryptids/WeakCollatz/`; each step below names
the lemma that carries it. It reuses the round argument of `v1/PROOF.md` (the 23-state
machine), so this tour concentrates on what is new: the shortcut map and the tape.

## What is proved

```lean
theorem TM.WeakCollatz.halts_iff :
    Halts delta start ↔
      ∃ n k, 0 < n ∧ 0 < k ∧ iterate collatz k n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4

theorem TM.WeakCollatz.halts_iff_counter :
    Halts delta start ↔ Counter     -- Counter := ∃ n k, 3 ≤ n ∧ 0 < k ∧ iterate tc k n = n
```

* `collatz x` is `x / 2` for even `x` and `3x + 1` for odd `x` (`../lean/TinyCryptids/Defs.lean`);
  `tc x` is the shortcut map, `x / 2` or `(3x + 1) / 2` (`Spec.lean`).
* `Halts δ c` means: started in `c`, the machine reaches a configuration with no transition
  (`../lean/TinyCryptids/Core/Basic.lean`).

Both theorems depend only on `propext`, `Classical.choice` and `Quot.sound`
(`../lean/Check.lean`). The machine is the design itself (no merged copy), so there is no
transfer step. `TM.WeakCollatz16.halts_iff` (`../lean/TinyCryptids/WeakCollatz16/`) is the
same proof for the given 16-state machine of `m16/`; it shares Parts 1, 2 and 4 and differs
in a few lemmas of Part 3, noted below.

## Part 1: rounds of the shortcut map (`Spec.lean`)

The machine runs rounds `M = 2, 3, …`; round `M` starts at `v = M`, applies `tc` until the
value is 1 or `≥ M` (`Cond M v`), and halts iff that value is `M`. `Spec.lean` is
`v1`'s file with `collatz` replaced by `tc`; every lemma keeps its name and proof:

* `reach_cond`, `round_stops`: without a nontrivial `tc`-cycle in `[2, n)` (`NoCyc n`), every
  round stops.
* `round_no_return`: without one in `[2, n]`, round `n` does not stop at `n`.
* `exists_top`: a counterexample gives a least `M` with a cycle in `[2, M]` through `M` and
  `NoCyc M`; round `M` halts.

Only the facts about small values change: the `tc`-orbit of 1 is `1, 2, 1, …` (`it_one`), and
a cycle with values `≥ 2` cannot pass through 2 (`tc 2 = 1`), so its first value is `≥ 3`
(`nocyc_of_not`).

## Part 2: shortcut cycles are Collatz cycles (`Cycle.lean`)

`counter_iff : Counter ↔ ∃ n k, 0 < n ∧ 0 < k ∧ iterate collatz k n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4`.

* (→) `tc x` is `collatz x` (even `x`) or `collatz (collatz x)` (odd `x`), so `k` steps of
  `tc` are `k' ≥ k` steps of `collatz` (`it_ci`), and a `tc`-cycle through `n ≥ 3` is a
  `collatz`-cycle through `n`. It is not 4: the `tc`-orbit of 4 is `4, 2, 1, 2, 1, …`.
* (←) Every positive orbit reaches an odd value (`ci_odd`, halving), so the `collatz`-cycle
  contains an odd `p`; `p ≠ 1`, or the orbit of 1 (`1, 4, 2`, `ci_one`) would contain the
  counterexample. `tc` only skips the even values `3x + 1`, so a `collatz`-path that ends at
  the odd `p` is a `tc`-path (`ci_it`, strong induction on the length): `p ≥ 3` lies on a
  `tc`-cycle.

## Part 3: the machine on the tape (`Step.lean`)

**The tape.** `CF a r` is the configuration with the head on cell 0 in `disp`, nothing to the
left, and from the head `a` ones, a 0 (the *hole*), `r` ones, then blank. The value `v` in
round `M` is `CS M v := CF (v − 1) (M − v)`, and the round start is `RS M := CS M M`: `M − 1`
ones, so the hole is the first blank.

**Going home** (`go_home`): from anywhere in the block, `home` runs left to cell −1 and steps
right into `disp`.

**v = 1** (`step_one`): `disp` reads the hole on cell 0, fills it and goes home: `CS M 1`
reaches `RS (M + 1)`. The blank tape is `CS 1 1`, so this is also the seed (`start_reach`).

**Halving.** For `v ≥ 2` the first step writes the marker on cell 0 (`disp_mark`; this is the
step that makes every macro step strict, `Rch1`). The loop invariant `HL m d r` is "the marker
on cell `m`, head on cell `m + 1` in `toH`, then `d` ones, the hole, `r` ones". One round trip
(`hl_step`): `toH` runs right and fills the hole, `stepH` writes the new hole one cell left,
`back` runs left and fills the marker, `mark` writes the marker one cell right:
`HL m (d + 2) r` reaches `HL (m + 1) d (r + 1)`; `hl_loop` iterates it.

* `d = 0` (`hl_even`): `toH` fills the hole next to the marker and `stepH` reads the marker,
  which stays as the hole: from `v = 2k + 2` this is `CS M (k + 1)` (`step_even`).
* `d = 1` (`hl_odd`): `stepH` writes the new hole where `mark` then looks for the marker:
  `mark` reads the hole. `hop2` writes the hole one cell right, `backO` fills the old one, and
  the odd loop starts.

(In `m16` the marker starts on cell 1 and the roles of the two cases are swapped: `hl_even`
ends with `cut` writing the hole left of the meeting cell.)

**Odd loop.** Invariant `OL c e s`: head on cell `c − 1` in `markO` (cells `0 .. c − 1` are
ones), then `e` ones, the hole, `s` ones. One round trip (`ol_step`): `markO` writes the marker,
`toHO` runs right and fills the hole, `hop1` steps over one cell, `hop2` writes the new hole,
`backO` runs left and fills the marker: `OL (c + 1) e (s + 2)` reaches `OL c (e + 3) s`;
`ol_loop` iterates it. Two ways out:

| situation | what the machine does | lemma |
|---|---|---|
| `s ≤ 1` with the marker still in the block | the hole runs off the end (`hop1` or `hop2` reads a blank); `fill` fills the marker and goes home: `RS (M + 1)` | `ol_over` |
| `c = 0` (the marker passed cell 0), `s = 0` | `toHN` runs to the hole, `peek` reads a blank: **halt** | `ol_end` |
| `c = 0`, `s ≥ 1` | `peek` reads a 1; `stepH` rewrites the hole and goes home: `CF e s` | `ol_end` |

(In `m16`, `fill` is followed by `grow`, a run to the end of the block, and `peek` by `cut`.)

From `v = 2k + 3` the halving ends in `OL (k + 1) 1 (r + k)` with `r = M − v`; a full odd
loop leaves the hole at cell `3k + 4 = tc v − 1`. `step_odd` sorts the three cases by
comparing `tc v = 3k + 5` with `M`.

**One step and one round** (`step_cases`, `round_run`): as in `v1`, with `tc` in place of
`collatz`. The only new case: when `tc x = 1` (so `x = 2`), the machine first reaches
`CS M 1` and then `step_one` starts the next round.

## Part 4: the main theorem (`Main.lean`)

`start_reach`: the blank tape reaches `RS 2`. `halts_iff_counter` is `v1`'s main argument with
rounds starting at 2: without a counterexample every round strictly reaches the next
(`not_halts_of_progress`); with one, take `M` from `exists_top`, every round before `M` stops
without halting or halts, and round `M` halts (`haltAt_of_counter`). Then
`halts_iff := halts_iff_counter.trans counter_iff`.

## What the proof does not cover

* It says nothing about whether a nontrivial cycle exists, and nothing about divergent orbits
  (which a halting search cannot recognise).
