# A Turing machine for the weak Collatz conjecture

**Current best: `machines/weakcollatz_14.txt`, a 14-state, 2-symbol Turing machine**
(named-state format, see `../tools/tm.py`; readable: `machines/weakcollatz_14_annotated.txt`).
Started on a blank tape, it **halts iff the Collatz map has a cycle other than
1 → 4 → 2 → 1**, i.e. iff the weak Collatz conjecture is false. Lean proves this
(`TM.WeakCollatz.halts_iff`):

    Halts delta start ↔
      ∃ n k, 0 < n ∧ 0 < k ∧ iterate collatz k n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4

where `collatz x` is `x / 2` for even `x` and `3x + 1` for odd `x`
(`TinyCryptids.collatz`, `../lean/TinyCryptids/Defs.lean`). `RECORDS.md` lists every
machine; `PROOF.md` walks through the proof in plain words.

Standard text (bbchallenge format):

    1LM0RB_1LC1RB_0LM0LD_1RE1LD_0RF0RB_0LN0LG_1LH1LG_0RK0RI_1RJ1RI_0LN1RF_0RL1RK_0RZ1LC_0RA1LM_1LM1LN

**History.** `v1/` is this repository's first design (25 states, 23 after merging). `m16/` is
the 16-state cycle detector of the release *Two exact binary Collatz Turing machines*, which
introduced the shortcut map, the halving by a marker meeting the hole, and the odd step that
reuses the marker. The 14-state machine is that machine with two states removed (see below).
`sym3/` is a 10-state machine with 3 symbols (BB(10, 3)): the same algorithm with the end of
the block marked by a 2.

## The search

The machine looks for each cycle at its **largest element**, iterating the **shortcut map**
`T(v) = v/2` (v even), `(3v+1)/2` (v odd):

    for M = 2, 3, 4, ...:
        v := M
        repeat v := T(v) until v = 1 or v >= M
        if v = M: HALT

* If a nontrivial cycle exists, take the one whose largest element `M` is smallest. From `M`
  the orbit stays in `[2, M]` and returns to `M`, so round `M` halts.
* A round can only run forever if its orbit stays in `[2, M−1]`, i.e. falls into a nontrivial
  cycle with a smaller largest element, whose round already halted.
* `T` has a cycle through some `n ≥ 3` iff `collatz` has a cycle other than 1 → 4 → 2 → 1
  (`counter_iff` in `Cycle.lean`): a `T`-orbit is a `collatz`-orbit with the even values
  `3x + 1` skipped, and a `collatz`-cycle contains an odd value, which `T` never skips.

## How it works

`C(M, v)`, `1 ≤ v ≤ M`: cells `0 .. M−1` hold 1 except a **hole** at cell `v − 1`; all other
cells are 0, and the head is on cell 0 in `disp`. For `v = M` the block is just `M − 1`
ones and the hole is the first blank. The blank tape is `C(1, 1)`.

* **v = 1** (`disp` reads 0): fill cell 0 and go home. The tape is now `M` ones, the first
  blank is the hole: `C(M+1, M+1)`.
* **Halving.** `disp` writes a second hole, the **marker**, on cell 0. Per round trip `toH`
  runs right and fills the hole, `stepH` writes it one cell further left, `back` runs left and
  fills the marker, and `mark` writes it one cell further right. They meet in the middle:
  * on **neighbouring cells** (`stepH` reads the marker, `v = 2k`): the marker sits on cell
    `k − 1`, which is exactly the result hole: go home, `C(M, k)`.
  * on the **same cell** (`mark` reads the hole, `v = 2k+1`): the hole is on cell `k`.
  The parity of `v` is never computed separately.
* **Odd.** `hop2` moves the hole to `k + 1` and `backO` puts the marker back, `markO` moving it
  to `k − 1`. Per round trip the marker moves left one cell and the hole right two (`toHO`,
  `hop1`, `hop2`), so when the marker passes cell 0 (`markO` reads 0) the hole is at
  `k + 1 + 2k = 3k + 1 = T(v) − 1`. `toHN` runs to it and `peek` looks at the next cell: blank
  means `T(v) = M`, **halt**; otherwise `stepH` rewrites the hole and goes home: `C(M, T(v))`.
  If the hole runs past the block first (`hop1`/`hop2` read 0: `T(v) > M`), `fill` fills the
  marker and goes home: `C(M+1, M+1)`.
* **Home**: run left over 1s to cell −1, step right.

The two states saved against `m16/`:

* **No `grow`.** After the hole runs off the block, `m16`'s machine fills the marker and then
  runs right to the end of the block before going home. But the tape is already `C(M+1, M+1)`
  once the marker is filled, so `fill` goes straight home (and so does `disp` for `v = 1`).
* **No `cut`.** `m16` starts the marker on cell 1, so for even `v` the marker and the hole meet
  on one cell and `cut` must write the result hole one cell to the left. Starting the marker on
  cell 0 swaps the two meeting cases: for even `v` the marker itself is the result hole, and
  for odd `v` `mark` reads the hole and `hop2`/`backO` set up the odd loop with no new state.
  `peek` restores the hole through `stepH` instead of `cut`.

Every transition except `peek`'s halt is used by the run and no two states agree, so merging
cannot shrink it (`greedy_merge.py`: 14). A search for a 13-state machine near this one found
nothing; see `RECORDS.md`.

## Files and checks

* `build.py` generates the machine (`python3 build.py weakcollatz.txt`);
  `machines/weakcollatz_14.txt` is a copy.
* `test_e2e.py`: every macro step from `C(M, v)` for `2 ≤ M ≤ 60`, `1 ≤ v ≤ M` (1,829
  cases, including the halting case `T(v) = M`, which the real run never meets) against the
  reference; the run from the blank tape at every macro step for rounds 2 .. 300; and 10⁸
  steps without halting (C simulator).
* `annotate.py weakcollatz.txt machines/weakcollatz_14_annotated.txt`: the readable listing.
* `gen_lean.py` writes `../lean/TinyCryptids/WeakCollatz/Machine.lean`.
* The proof: `../lean/TinyCryptids/WeakCollatz/` (see `PROOF.md` and `../lean/README.md`).
* `m16/`: the given 16-state machine, with its own proof (`TM.WeakCollatz16.halts_iff`).
* `v1/`: the earlier 25-state design and its 23-state merge, with their own proof
  (`../lean/TinyCryptids/WeakCollatzV1/`).
* `sym3/`: a 10-state, 3-symbol machine, with its own proof (`TM3.WeakCollatz.halts_iff`,
  `../lean/TinyCryptids/WeakCollatz3/`).
