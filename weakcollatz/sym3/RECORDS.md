# Records: 3-symbol weak Collatz machines

| States | Symbols | Machine | How obtained | Status |
|---:|---:|---|---|---|
| **10** | 3 | `machines/weakcollatz3_10.txt` (= `weakcollatz3.txt`; readable: `weakcollatz3_10_annotated.txt`) | `build.py`: the algorithm of the 14-state machine, with the end of the block marked by a 2 | Proven in Lean: `TM3.WeakCollatz.halts_iff` |

For comparison, the best 2-symbol machine is the 14-state machine of `..` (`../RECORDS.md`).

## Searches for 9 states

The 10-state machine uses 26 transitions plus the halt, i.e. exactly the 27 slots of a 9-state
machine. Its only states with a free slot (`disp`, `mark`, `markO`, each unused on 2) disagree
on both 0 and 1, so none of them merge: a 9-state machine needs a different design.

The search below kept the tape layout and the macro step: from `C(M, v)` (head on cell 0 in
the start state), the first return to the start state on cell 0 must have the tape of the
reference's next `C(M', v')`, or the machine must halt where the reference halts.

* **Local search** around the 10-state machine. It deleted each state `X ≠ disp`, redirected its
  incoming transitions to each other state `Y`, and changed up to two further transitions (any
  write, move, next state, or halt). Each candidate was tested on every macro step with `M ≤ 9`
  and on the blank tape: 83 million candidates, **none** passed.

This is not a proof that 9 states is impossible: another tape layout or round structure could
do better.
