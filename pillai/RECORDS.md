# Best machines so far

All machines are 2-symbol Beeping Booping machines (Bram Cohen's definition). They start on a
blank tape and never halt. Their beep is state `zX3` reading 1 and their boop is `zX3` reading 0
(design names). Some beep count between consecutive boops repeats forever iff Pillai's
conjecture is false: `RepeatsForever … ↔ ¬ PillaiConjecture`.

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **91** | `machines/pillai_91.txt` (readable: `pillai_91_annotated.txt`) | `minimize_clique.py pillai.txt out 3600 cadical195 zX3:1,zX3:0`: clique bound 89, 89 and 90 unsatisfiable, 91 found in under a minute; optimal for this design | Proven in Lean: `TM.Pillai.M91.repeats_iff`, `M91.never_halts` |
| 132 | `pillai.txt` | `build.py`: Fermat's powers with two exponent blocks, a four-block NEXCOM enumeration, the shared home routine, a zig-zag that beeps, a looping seed | Proven in Lean: `TM.Pillai.repeats_iff`, `never_halts` |

## History

| Design | Merged | Change |
|-------:|-------:|--------|
| 138 | 97 (optimal) | First design: a 26-cell straight-line seed `10111 00 1111 00 1111 00 1111 00 1` |
| 132 | **91** (optimal) | A looping seed: the hole in x counts the blocks still to write, each round appends `00 1111`, the last one `M` |

* Merging the 138-state design without its seed gave 80 states, so the straight-line seed
  cost 17 merged states: a straight-line seed only reads blank cells, so its 26 states are 26
  distinct merged states, and only 9 of them found partners among the other routines. The loop
  seed (20 states) costs about 11.
* A first loop seed that refilled the counter hole and punched the anchor back (3 states, like
  Fermat's `eD1`–`eD3`) had lower bound 91 and greedy 97; leaving the hole on x's last cell for
  the home routine to fill saved those states.
* Rejected: the exponent cursor reset to cell 1 of its own block with y left of x (Fermat's
  `eD`, no home scan): it needs the wraps of x and y told apart by a scan past the block and saves
  at most one design state.

## Where the states go

59 of the 91 merged states play a single design role. They are the two-state parsers (`CP`,
`HE`, `HL`, `HS`, `HU`, `LF`, `LG`, `MB`, `MC`, `MM`, `MN`, `MQ`, `NB`, and the seed's `PL`), the
copy loop `c1`–`c6`, the zig-zag (`zH1`, `zA1`, `zG1`, `zZ1`, `zK1`, `zX1`, `zX2`), the home scan
`H1`–`H4`, the seed's scans `R1`–`R3`, `T1`, `T2`, and a few enumeration states. The beep/boop
state `zX3` reads both symbols, so it can never share a class.
