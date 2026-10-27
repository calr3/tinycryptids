# Best machines so far

All machines are 2-symbol beeping machines that start on a blank tape, never halt, and take
their beep transition (state `G0` reading 0 in the design; `P` reading 0 in the standard text
of the 16-state machine) exactly once per Fermat prime. They quasihalt (beep finitely often)
iff there are only finitely many Fermat primes:
`QuasiHalts … ↔ ¬ InfinitelyManyFermatPrimes`.

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **16** | `machines/fermatprimesinf_16.txt` (readable: `fermatprimesinf_16_annotated.txt`) | `minimize_clique.py fermatprimesinf.txt out 600 cadical195 G0:0` on the 17-state design: the wrap's last state joins the D step. The clique bound is 16, so this is optimal for the design | Proven in Lean: `TM.FermatPrimesInf.M16.quasihalts_iff`, `M16.never_halts` |
| 17 | `machines/fermatprimesinf_17.txt` (= `fermatprimesinf.txt`) | `build.py`: `../fermatprimes`'s design without the counter and its start; the pass beeps and goes straight to the rebuild, and the run starts in `C4` | Proven in Lean: `TM.FermatPrimesInf.quasihalts_iff`, `never_halts`, `beeps_forever_iff` |

## Where the states go

Walk 7 (after merging), end of the walk and check 6 (`E`, `V`, `X1`, `X`, `Q`, `HF`), shift,
beep and rebuild 3 (`H1`, `G0`, `C4`). A Mersenne prime search (testing `m` and `m + 1`)
with the same walk has a round end of 7 states: its two FAIL cases are D's last two cells
(`d ∣ m`, `d ∣ m + 1`), found by one erase-to-the-hole pass. Here they are D's two ends (`d ∣ m`: cell `d − 1`; `d ∣ m − 1`:
cell 0), so the check needs `X1` for the last cell and `Q`, `HF` for the first.

## The synthesis

`../tools/synth_round.py` searched for a smaller round end. It kept the
walk's 7 states fixed and gave `k` free states. The reference was the first 33 rounds of the
17-state design (every `(m, d)` with `m ≤ 39` and the first of `m = 41`, including the beep at
17), each at most 4 steps
longer than in the design:

    python3 ../tools/synth_round.py fermatprimesinf.txt out.txt --fixed B2,Y1,Y2,A2,W1,Z1,Z2 \
        --merge W2:A2 --leave B2:0 --enter B2:1 --k 8 --beep G0:0 --solver kissat404

| `k` | Total | Result |
|----:|------:|--------|
| 9 | 16 | SAT in 77 min (`kissat404`): the sanity check, the size of the design's own round end |
| 8 | 15 | no answer in 12 h (`kissat404`, `cadical195`); `maplechrono` timed out at 11 h |
| 7 | 14 | no answer in 12 h (`kissat404`, `cadical195`); `maplechrono`, `glucose4` timed out at 11 h |
| 6 | 13 | UNSAT in 53 min (`kissat404`) and 85 min (`cadical195`) |

So with this walk and these tape conventions, no round end of 6 states works within those step
bounds: 13 states would need a different walk or layout. 14 and 15 are open. These instances
are much harder than those for the Mersenne round end, whose `k = 8` took 66 s and whose
`k = 6` UNSAT took about 500 s.
