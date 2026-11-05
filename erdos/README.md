# Erdős: powers of 2 in base 3

Erdős conjectured (1979) that for every n > 8 the base-3 representation of 2^n
contains at least one digit 2. The only known exceptions are
2^0 = 1, 2^2 = 11 and 2^8 = 100111 (base 3).

`machines/erdos_15.txt` is a 15-state, 2-symbol machine that, started on a blank
tape, halts iff the conjecture is false:

    1RB1RO_0RC0RC_0RD1RJ_0LE1RC_0LF1LK_0LG1LE_0LH1LF_1RI0LL_0RB1LK_1RC0RA_0LI1LN_1RM---_0RI0RO_0LK1LK_1LM1RA

It is not designed here: this is the machine as it was given to us. Stérin and Woods
built a 15-state machine for this conjecture in
[*On the hardness of knowing busy beaver values BB(15) and BB(5,4)*](https://arxiv.org/abs/2107.12475)
(2021). What this folder adds is a Lean proof of exactly that claim:

```lean
theorem TM.Erdos.halts_iff :
    Halts delta start ↔ ∃ n, 8 < n ∧ 2 ∉ digits3 (2 ^ n)
```

`digits3 n` is the list of base-3 digits of `n` (`../lean/TinyCryptids/Defs.lean`). The
theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## How the machine works

Each base-3 digit takes two cells: 0 is `01`, 1 is `10`, 2 is `11`, least significant
digit first. A `00` pair at cells -2, -1 separates the number from a 2-bit counter
(cells -4, -3) of the powers seen so far that had no digit 2.

    x y 0 0 | a0 b0 a1 b1 ... ak bk | blank

Round n starts with 2^n on the tape and the head just right of its top digit:

1. **Scan** (`E F G`): move left, top digit first, looking for a `11`.
2. **Found a 2** (`K N I`): walk on left to the separator.
   **No 2** (`H L M`): add 1 to the counter. If it was already 3, `L` reads a 1 and halts.
   This undefined transition is the machine's only one.
3. **Double** (`C D J` with carry 0, `A B O M` with carry 1): one pass right, least
   significant digit first. If the carry is left over at the end, it becomes a new top
   digit 1. The pass ends when it reads `00`, and the next round starts.

The very first step is already part of a pass: `A` (carry 1) on an empty number writes
2^0 = 1. Below n = 9 only n = 0, 2, 8 have no 2, so the counter is 3 from round 9 on, and the
4th power without a 2 (a counterexample) halts the machine.

`machines/erdos_15_annotated.txt` describes every transition.

## Files

| File | Contents |
|------|----------|
| `machines/erdos_15.txt` | The machine (named-state format, states named after the standard-text letters) |
| `machines/erdos_15_annotated.txt` | The same machine, every transition explained |
| `test_tape.py` | Runs the machine and checks the invariant of the proof at each round start: the tape holds the counter and the digits of 2^n (`python3 test_tape.py 300`) |
| `gen_lean.py` | Emits `../lean/TinyCryptids/Erdos/Machine.lean` |
| `PROOF.md` | The proof in plain words |
| `RECORDS.md` | State count, and why merging does not shrink it |

## Running it

`gcc -O2 -o ../tools/sim ../tools/sim.c`; the machine runs for 10^10 steps (about 85,000
rounds, n up to about 85,000) without halting. As expected, it reaches no counterexample.
