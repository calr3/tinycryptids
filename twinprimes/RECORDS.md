# Best machines so far

All machines are 2-symbol beeping machines that start on a blank tape, never halt, and take
their beep transition (state `G2` reading 0 in the design; `N` reading 0 in the standard text
of the 18-state machine) exactly once per lesser twin prime `p ≥ 3`. They quasihalt (beep
finitely often) iff the twin prime conjecture is false: `QuasiHalts … ↔ ¬ TwinPrimeConjecture`.

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **18** | `machines/twinprimes_18.txt` (readable: `twinprimes_18_annotated.txt`) | `minimize_clique.py twinprimes.txt out 600 cadical195 G2:0` on the 19-state design: the wrap's last state joins the D step. The clique bound is 18, so this is optimal for the design | Proven in Lean: `TM.TwinPrimes.M18.quasihalts_iff`, `M18.never_halts` |
| 19 | `machines/twinprimes_19.txt` (= `twinprimes.txt`) | `build.py`: trial division of `m = 3, 4, …` with one mod walk per `d` for both `m` and `m + 2`, zero-counting scanners, a beep when R runs out | Proven in Lean: `TM.TwinPrimes.quasihalts_iff`, `never_halts`, `beeps_forever_iff` |

Earlier designs (not kept), each merged with the same tool:

| Design | Merged | Difference to the next one |
|-------:|-------:|----------------------------|
| 31 | 25 | `D 00 R` with the 2-state parsers of `Core/Lemmas.lean` (a hole needs a 1 on both sides; the step back from one past the hole); D with a permanent cell 0; the walk ended by `R`'s length check with three states |
| 24 | 23 | single-0 separator and zero-counting scanners; the rebuild grew the tape at the right end and walked back |
| 20 | 19 | the rebuild grows the tape at the left end, where it writes the new D; D lost its permanent cell 0 (the wrap and the rebuild each one state shorter) |
| 19 | 18 | the rebuild's last state (write the separator) is the shift's `G1` (this design) |

A variant whose R hole moves right also merges to 18. The walk then starts right after the
shift with no trip to R's end, but the check needs a trip back from R's end to the separator.

How the merged machine is proven: `minimize_clique.py` merges only states whose defined
transitions agree, and with `G2:0` no state with a defined 0-transition joins `G2`'s class.
`gen_reduced_lean.py` emits the merged machine, the state map `phi`, `compat` and `excl` (the
merged beep state plays only `G2` on symbol 0), and transfers both theorems with
`quasihalts_iff_of_sim` and `not_halts_of_sim` (`../lean/TinyCryptids/Core/Beep.lean`). The
design never halts, so the merged machine beeps at exactly the same steps.
