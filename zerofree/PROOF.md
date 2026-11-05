# The proof, in plain words

This is a guided tour of the Lean proof that the zero-free machine halts if and only if
some power 2^n with n > 86 has no decimal digit 0. The proof is in
`../lean/TinyCryptids/ZeroFree/`; each step below names the lemma that carries it.

## What is proved

```lean
theorem TM.ZeroFree.halts_iff :
    Halts delta start ↔ ∃ n, 86 < n ∧ ∀ k, 2 ^ n / 10 ^ k ≠ 0 → (2 ^ n / 10 ^ k) % 10 ≠ 0
```

The right-hand side says: some 2^n with n > 86 has no digit 0. `2 ^ n / 10 ^ k % 10` is its digit
k, and `2 ^ n / 10 ^ k ≠ 0` says that digit is not a leading zero. The merged machine's
theorem (`TM.ZeroFree.M<k>.halts_iff`) states the same thing for `delta2`, and is transferred
from the design's (`M<k>.lean`).

To trust it you need the Lean kernel, the machine model (`../lean/TinyCryptids/Core/`) and
the listing of the machine. The theorem depends only on `propext`, `Classical.choice` and
`Quot.sound` (`../lean/Check.lean`).

## Part 1: decimal doubling (`Spec.lean`)

`D` has the ten digits `d0 … d9`. `dbl c ds` doubles a digit list (least significant
first) with carry `c`: digit `d` becomes `dd c d = (2d + c) mod 10`, the carry `hi d = [d ≥ 5]`,
and a carry left over becomes a new digit 1. `pw n` is `[d1]` doubled `n` times.

* `num_dbl`, `pw_num`: `pw n` stands for `2 ^ n`.
* `canon_pw`: `pw n` has no leading zero.
* `zero_free_iff`: the right-hand side's condition for `n` holds iff `d0 ∉ pw n`.

## Part 2: one round on the tape (`Round.lean`)

A digit takes four cells: its parity, then three cells for `a = d / 2`. Between rounds the
three cells are in code A (`ax`, `ay`, `az`, generated from `build.py` into `Codes.lean`).
`S c ds` is the round start: the counter `c` and the separator to the left
(`ctr c`), the digits `ds` in code A to the right, the head on the first parity cell.

* `pass`: the pass from the first digit with carry `c`. Each digit takes four steps
  right (`pass_digit`). It writes the carry into the parity cell and the three cells of
  code B for the old digit (`qx`, `qy`, `qz`); the groups it leaves are `trace c ds`, pairs
  (carry, old digit). The blank group after the number ends the pass (`pass_end0`), or
  first becomes the digit 1 with a carry (`pass_end1`). The new digits are
  `(trace c ds).map nd = dbl c ds` (`trace_nd`).
* `scan_cross`: the scan, right to left, takes four steps per group and rewrites each
  group into code A of its new digit, while that digit is not 0. `found_cross` does the
  same after a 0 was found, and `zero_group` is the switch.
* `scan_found`: with a digit 0, the scan reaches the separator in found mode, and the
  next pass starts with the counter unchanged. The list is split at its last 0
  (`split_last`, `map_split`).
* `inc`: from the counter's first guard, a counter `c` with `c + 1 < 2^k` becomes `c + 1`,
  and the return parser starts the next pass. It is proved by induction on the bits,
  carrying the `0 1` pairs already reset (`zp`, `zpL`). `overflow`: the full counter
  reaches the halting state.
* `round_no0`, `round_0`, `round_halt`: from `S c ds`, the machine reaches
  `S (c + 1) (dbl false ds)` if the new number has no 0 (and `c < 63`), `S c (dbl false ds)`
  if it has one, and halts if it has none and `c = 63`. The first two take at least one
  step (`pass1`).

## Part 3: the main theorem (`Main.lean`)

* `seed`, `first`: the seed writes the counter 27 and the separator. The first pass
  writes 2^0 = 1, which has no 0, so it reaches `S 28 (pw 0)`.
* `st n` computes the counter and digits after the scan of 2^n. `early`: for `n ≤ 86`
  the machine reaches `S (st n).1 (pw n)`. `decide` checks the counter never passes
  63 (`st_le`) and is exactly 63 at `n = 86` (`st_86`): there are 36 powers without a 0 up
  to 2^86.
* `later`: from `S 63 (pw 86)`, for every `j`, the machine reaches the halting state or
  `S 63 (pw (86 + j))`.

(←) A counterexample `n > 86`: `later` reaches round `n − 1` or halts earlier, and
`round_halt` halts there (`haltAt_of`).

(→) Without a counterexample every `pw n` with `n > 86` has a 0. So each `S 63 (pw n)`,
`n ≥ 86`, strictly reaches `S 63 (pw (n + 1))` (`round_S`), and none of them halts
(`not_halts_of_progress`). The start reaches `S 63 (pw 86)`, and the machine is
deterministic, so it does not halt either.
