# Records: twin prime machines with more than 2 symbols

All machines are beeping machines that start on a blank tape, never halt, and beep infinitely
often iff the twin prime conjecture is true. "Instructions" counts the defined transitions
(BBBi).

| Instructions | States | Symbols | Machine | How obtained | Status |
|---:|---:|---:|---|---|---|
| **27** | 10 | 4 | `machines/twinprimes4_10.txt` (= `twinprimes4.txt`; readable: `twinprimes4_10_annotated.txt`) | Local search around the 28-instruction machine (below) | Proven in Lean: `TMK.TwinPrimes4.quasihalts_iff`, `never_halts`, `beeps_forever_iff` |
| 28 | 10 | 4 | not kept | Local search around the 29-instruction design | Simulated: beeps at exactly the lesser twin primes 3, 5, 11, … (the first 12) |
| 29 | 10 | 4 | not kept | Hand design (below) | Simulated: beeps at exactly the first 15 lesser twin primes |

For comparison, the 2-symbol machine of `..` has 18 states and 34 instructions (`../RECORDS.md`).

## From 34 to 29: the hand design

The algorithm of `..` with D's cells written 3 and R's cells 1, a marker 2 in D and a cursor 2
in R, and no separator:

* The scanners stop at a 2, so they need no second state to count zeros. Each one passes 1s
  and 3s.
* `cur` reads D's last cell itself when the walk is over, which makes it the first check
  (`X1` is gone). `grow` writes the new marker straight onto R's cell 0 (`G1` is gone).
* `toR` also runs to R's end at the start of the walk (`SC` is gone), and `wrap` also runs to
  the marker after a passed check (`H0` is gone). The rebuild's last state is `grow`.
* The cost: `adv` must wrap on both a 1 and the cursor (R's cell 0 holds the cursor in the
  walk's last step), and the start needs one transition of its own (`grow` reading 0).

A first draft with 28 instructions had `adv` wrap only on a 1. It failed at the first walk
(`d = 2`, `m = 3`), where R's cell 0 is the cursor.

The FAIL from `cur` went right to a state `F`. `F` reading a 1 (R's cell 0) went left into the
rebuild, and `F` reading 0 (R empty: `d = m`) was the beep. A design that keeps a separator symbol
between D and R was estimated at 32 and not built.

## From 29 to 27: local search

Search (C, OpenMP, about a minute each on 24 threads): from the current machine, every machine
with one instruction fewer obtained by

* removing one instruction and changing up to two others (any write, move and next state, or
  undefined), with any start state, or
* removing two instructions and setting one slot to any action, with any start state.

A candidate passed if its first five beeps came by steps 400, 2 000, 20 000, 80 000 and
400 000, with the 4th and 5th beeps at or after steps 1 000 and 5 000. The survivors (8 202
around 29, 5 900 around 28, 7 042 around 27) were run for up to 3·10⁸ steps, and the
nonblank cells were counted at their first 12 beeps. Most of them beep for primes, powers of 2
or other sequences.

* Around the 29-instruction design (742 million candidates), three machines beep at the
  lesser twin primes. One of them is the **28-instruction** machine: `chk3`'s FAIL goes to
  `reb`, and `reb` converts a 3 by `3 → 1 R` followed by `1 → 1 L`, a zigzag. That handles
  the D cells right of the marker, so `F`'s `3 → 1 R F` is no longer needed.
* Around 28 (665 million candidates), three machines beep at every lesser twin prime except
  5, plus once at step 2. One of them is the **27-instruction** machine. `F` loses its
  1-transition: `cur`'s FAIL goes to `reb` directly, and `reb`'s 0-transition (the blank right
  of D) leads to the beep through `grow`'s 0-transition, which was the start's own
  transition. The beep path then adds two cells, so the next candidate is `m + 3`.
* Around 27 (595 million candidates), **no** machine passed. This is not a proof that 26 is
  impossible: a different tape layout could do better.
