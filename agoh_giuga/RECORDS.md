# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff the Agoh–Giuga conjecture is
false (`∃ n, 2 ≤ n ∧ ¬ Prime n ∧ n ∣ powSum n (n - 1) + 1`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **100** | `machines/agoh_giuga_100.txt` (readable: `agoh_giuga_100_annotated.txt`) | `minimize.py` (`kissat404` and `cadical195` both reached 100) on the 167-state design; searches for 99 (`kissat404`, `cadical195`, `maplechrono`) were stopped without a result | Proven in Lean: `TM.AgohGiuga.M100.halts_iff` |
| 167 | `machines/agoh_giuga_167.txt` (= `agoh_giuga.txt`) | `build.py`: for each `n`, the bases `i = n − 1 … 2`: `i^(n−1)` by `../firoozbakht`'s Horner run, `B += i^(n−1) − 1` into a cyclic hole mod `n`, a flag at the first nonzero `B` (composite, by Fermat), halt at the end of a round if the flag is set and `B = 0` | Proven in Lean: `TM.AgohGiuga.halts_iff` |
| 103 | (not kept) | The same design with the second states of two left parsers (`HE2`, `PN2`) defined on 0, as `../firoozbakht`'s parser lemma needs; they never read a 0 there, and leaving them undefined (`ParserL1` in `Horner.lean`) gave the merger room for 100 | — |
| 101 | (not kept) | `minimize.py` on an earlier 174-state design (`N 00 J 00 I 00 x 00 K 00 S 00 R`: the base shrunk at its left end, a separate dead block next to the flag, S grown on its right with R moved); not proven | — |

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
