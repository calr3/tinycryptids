# The proof, in plain words

This is a guided tour of the Lean proof that the 15-state machine `machines/erdos_15.txt`
halts if and only if some power 2^n with n > 8 has no digit 2 in base 3. The proof is about
400 lines in `../lean/TinyCryptids/Erdos/`; each step below names the lemma that carries it.

## What is proved

```lean
theorem TM.Erdos.halts_iff :
    Halts delta start ↔ ∃ n, 8 < n ∧ 2 ∉ digits3 (2 ^ n)
```

* `digits3 n` is the list of base-3 digits of `n`, least significant first
  (`../lean/TinyCryptids/Defs.lean`). For example, `digits3 256 = [1, 1, 1, 0, 0, 1]`.
* `Halts δ c`: started in configuration `c`, the machine reaches a configuration with no
  transition (`../lean/TinyCryptids/Core/Basic.lean`, the model shared by every machine in the
  repository).
* `delta` is the machine, generated from `machines/erdos_15.txt` (`Machine.lean`). `start`
  is state `A` on a blank tape.

To trust the result you need to trust the Lean kernel, `digits3`, the model and the listing
of the machine. The theorem depends only on `propext`, `Classical.choice` and `Quot.sound`
(`../lean/Check.lean`).

## Part 1: doubling digit by digit (`Spec.lean`)

The machine never stores 2^n as a number, only as digits. `Dig` has the three digits
`z, o, t` (0, 1, 2). `dbl c ds` doubles a digit list, least significant first, with an
incoming carry `c`: digit `d` becomes `(2d + c) mod 3` and the carry `(2d + c) / 3`. If a
carry is left at the end, it becomes a new digit 1. `pw n` is `[o]` doubled `n` times.

* `dbl_val`: if `ds` are the digits of `m`, then `dbl c ds` are the digits of `2m + c`
  (induction on the list).
* `pw_eq`: `pw n` are the digits of `2 ^ n`.
* `two_mem`: `2 ∈ digits3 (2 ^ n) ↔ t ∈ pw n`.

## Part 2: one round on the tape (`Round.lean`)

A digit takes two cells: `z` is `01`, `o` is `10`, `t` is `11` (`ca`, `cb`). A list of
digits is written to the left of the head by `pushL` (last digit nearest) and to the right
by `putR` (first digit nearest). Left of the digits sit the separator `00` and the counter
`c` (`ctr c`: the cells `y x` with `c = 2x + y`). The **round start** is

    S c ds = ⟨E, pushL ds (ctr c), blank⟩

with the head just right of the top digit in state `E`.

* `pass`: the doubling pass. From the first cell of `rest` with carry `c` (state `C` for carry
  0, `A` for carry 1), the machine writes `dbl c rest` and stops in `E` right of it, which is
  the next round start. Induction on `rest`, one case per digit and carry. The case of a 1
  with carry 1 needs one step back (`O` writes `11`, `M` turns the first cell to 0).
* `scan_cross`: with no `t` in a list, the scan (`F`, `E`, `G`) crosses it unchanged.
  `kn_cross`: the walk after a 2 (`K`, `N`, `I`) crosses any list.
* `round_two`: if `t ∈ ds`, then `S c ds` strictly reaches `S c (dbl false ds)`. The list
  splits at its last `t` (`split_last`). The scan crosses the digits above it and finds it,
  the walk crosses those below, and the pass starts at the separator (`to_pass`).
* `round_no2`: if `t ∉ ds` and `c < 3`, then `S c ds` strictly reaches
  `S (c + 1) (dbl false ds)`: the scan reaches the separator and `H` (with `L`, `M` when `y`
  is 1) adds 1 to the counter.
* `round_halt`: if `t ∉ ds`, then `S 3 ds` halts: `H` clears `y`, and `L` reads `x = 1`,
  where the machine has no transition.

## Part 3: the main theorem (`Main.lean`)

* `start_reach`: the blank tape is `ctr 0` with an empty number, and `A` is the pass with
  carry 1. So the start reaches `S 0 (pw 0)`.
* `early`: rounds 0 to 8, one lemma each, with `decide` checking which `pw k` contain a `t`.
  Only `pw 0`, `pw 2` and `pw 8` do not, so the machine reaches `S 3 (pw 9)`.
* `later`: from `S 3 (pw 9)`, the machine halts or reaches `S 3 (pw (9 + k))`, for every `k`.

(←) Given a counterexample `n > 8`, `later (n - 9)` reaches round `n` (or halts earlier).
`round_halt` halts there.

(→) If there is no counterexample, every `pw n` with `n ≥ 9` contains a `t`. Then every
configuration `S 3 (pw n)` strictly reaches `S 3 (pw (n + 1))` (`round_two`), so none of
them halts (`not_halts_of_progress`). The start reaches `S 3 (pw 9)`, and the machine is
deterministic, so it does not halt either.
