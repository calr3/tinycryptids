# Best machines so far

All machines are 2-symbol beeping machines that start on a blank tape, never halt, and beep
(state `H5` reading 0) once for each smaller number of an amicable pair. So they quasihalt iff
there are only finitely many amicable numbers.

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **55** | `machines/amicable_55.txt` (readable: `amicable_55_annotated.txt`) | `../tools/minimize_clique.py` on the 69-state design: optimal for this design (the clique bound is 55) | Proven in Lean: `TM.Amicable.M55.quasihalts_iff` |
| 69 | `machines/amicable_69.txt` (= `amicable.txt`) | `build.py` | Proven in Lean: `TM.Amicable.quasihalts_iff` |

## How the design got smaller (merged size in brackets)

* 82 (67): the first working design. Both passes used fresh accumulators. Pass 2's
  accumulator needed a 4-cell seed so that the subtraction lands on `a = 1`. The cleanup
  walked to the far left and erased rightwards.
* 73 (59): N stays `1^x` after pass 1 (its four 0s are blank), so the subtraction copies `x`
  units and no seed is needed. The four cells move to the round start, where N is extended
  anyway.
* 71 (57): the checks fill the hole they find, so the junk left of N is one block. It is
  erased in one leftward sweep from its right end (`x1`, `er`, `bk`).
* 69 (55): the copy into P takes `x + 3` units, and N's last new cell is written after it
  (`CE1`). P's preload is then exactly `x + 1`, and "grown" is a single test (`G4`).

Ideas not (yet) carried out: share the abundance check (`G0 … G4`) with the beep check
(`H0 … H5`). They differ only at their ends, but there they disagree on what a hole at the
far end means. Reuse the junk of a pass-1 reject, which has exactly `x + 2` cells, as the
next round's P instead of copying N again.
