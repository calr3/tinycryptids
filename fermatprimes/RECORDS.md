# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff some Fermat number
`2^(2^n) + 1` with `n ≥ 5` is prime (`∃ n, 5 ≤ n ∧ Prime (2 ^ 2 ^ n + 1)`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **25** | `machines/fermatprimes_25.txt` (readable: `fermatprimes_25_annotated.txt`) | `minimize_clique.py` on the 27-state design: the start's last two states join `E` and `W2`. The clique bound is 25, so this is optimal for the design | Proven in Lean: `TM.FermatPrimes.M25.halts_iff` |
| 27 | `machines/fermatprimes_27.txt` (= `fermatprimes.txt`) | `build.py`: trial division of odd `m` and `m − 1` by odd `d` (one mod walk per `d`), a counter of 6 cells for the passes 3, 5, 17, 257, 65537, a start that writes it | Proven in Lean: `TM.FermatPrimes.halts_iff` |

## Earlier designs (not kept)

| Design | Merged | Difference to the next one |
|-------:|-------:|----------------------------|
| 27 | 25 | `d + r = m − 3`, so that `d ∣ m` and `d ∣ m − 1` put the hole on D's cells `d − 3` and `d − 2`; three check states and a separate refill for FAIL; the passes from `m = 5` on (a counter of 5 cells) |

## Where the states go, and what to try next

Minimization stopped at 25 states: the 25-state machine is the result. Most of the threshold's
cost is the counter path `P1`, `P2`, `P3` and the five start states that write the counter.
The SAT searches below use scripts like `../tools/synth_round.py`.
These are leads for later:

* **A shorter start (SAT, not built).** A start of 2 new states reaches the walk for `m = 5`
  with the counter in place. It reuses the free 0-transitions of `E` and `W2`. 1 new state is
  UNSAT within 60 steps. The new start would replace the five start states left after
  merging. If the merge holds, that is about 22 states, but this has not been checked.
* **A smaller round end (stopped, no answer).** The check, shift, pass and rebuild were
  synthesised with the walk fixed (`../tools/synth_round.py`). The reference was the design's rounds
  up to `m = 31` together with the halting round of a 3-cell counter, and each round could be
  at most 4 steps longer. The searches with 9, 10 and 11 free states ran for 3 hours with
  `kissat404` without an answer. 12 free states, the design's own round end and so certainly
  SAT, gave no answer in 2 hours even with the rounds cut to `m ≤ 21`. The encoding (the long
  trips out to the counter) should be checked or made smaller before its answers are trusted.
