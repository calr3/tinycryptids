# Best machines so far

All machines are 2-symbol beeping machines that start on a blank tape, never halt, and take
their beep transition (state `G0` reading 0 in the design; `Q` reading 0 in the standard text
of the 17-state machine) exactly once per Sophie Germain prime `p ≥ 3`. They quasihalt (beep
finitely often) iff there are only finitely many Sophie Germain primes:
`QuasiHalts … ↔ FinitelyManySophieGermainPrimes`.

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **17** | `machines/sophiegermain_17.txt` (= `sophiegermain.txt`) | `synth_round.py` with the 9-state double-step walk fixed and `k = 8` free states, reference: the 20-state design. `minimize_clique.py` merges nothing (clique bound 17) | Proven in Lean: `TM.SophieGermain.quasihalts_iff`, `never_halts`, `beeps_forever_iff`; `M17.quasihalts_iff`, `M17.never_halts` |
| 20 | `machines/sophiegermain_20.txt` (= `sophiegermain_ref.txt`, `build.py` variant `ref`) | By hand: `../mersenne`'s tape and walk with D's hole moving two cells per step; a plain check (scan to the separator, read three cells, scan to the hole) and a separate rebuild. Merges to nothing | Tested (`test_e2e.py`), not proven |

## The arithmetic

`../mersenne` tests `m` and `m + 1` with D's hole moving one cell per R cell and ending on
`(m − 1) mod d`. Moving it **two** cells per R cell makes it end on `(2n − 2) mod d`, which
for odd `d` is `d − 2` iff `d ∣ n` and `d − 3` iff `d ∣ 2n + 1`. Other placements were
considered and set aside:

* D's hole home on D's last cell (`../twinprimes`), which ends on `(2n − 1) mod d`, so the
  failing cells would be `d − 1`, `d − 2` as in `../mersenne`'s check. But D would no longer
  grow for free on its left, and the shift needs `G0` and one more state to check for an
  empty R.
* The hole moving left with its home on the blank: the failing cells are `d − 1`, `d − 2`
  for `n = r − 1` (with `d + r = n + 1`). But then R still holds one cell when every divisor
  has passed, and the beep would need a test for a one-cell R.
* R holding `2n`-ish cells with the one-cell walk: `d + r` would no longer be fixed per
  candidate, and the rebuild could not recover `n`.

## The synthesis

    python3 ../tools/synth_round.py sophiegermain_ref.txt out.txt \
        --fixed B2,Y1,Y2,A2,A3,W1,W3,Z1,Z2 --leave B2:0 --enter B2:1 --k K --beep G0:0 \
        [--rounds 40] [--slack 4|-1] [--solver kissat404]

| `k` | Total | Rounds, slack | Result |
|----:|------:|---------------|--------|
| 8 | 17 | 40, 4 | SAT in 22 min (`kissat404`: this design; `cadical195` found another 8-state round end a minute later) |
| 7 | 16 | 22, 4 | UNSAT in about 2 hours (`kissat404`); so also UNSAT for 30 and 40 rounds (more constraints), whose runs were stopped |
| 7 | 16 | 22, −1 (`2 n + 10` steps per round) | no answer after 2 h 10 min (`cadical195`, stopped) |
| 6 | 15 | 40, 4 | UNSAT in 13–15 min (`kissat404`, `cadical195`) |

So with this walk and these tape conventions, no round end of 7 states (16 in all)
reproduces the reference's rounds (those up to `n = 11`) within 4 extra steps per round: 17 is
optimal in that sense. A 16-state machine would need longer rounds (the open `--slack -1`
search), another walk, or other tape conventions.

The synthesized round end checks by **reading forward from the hole**: `X` fills the hole and
`K1`, `K2`, `K3` look for the separator on the next three cells. The walk end erases R's last
cell by bouncing between `E` and `B2`, and the rebuild is the same check run on the blank cells
left of the block: `X` and `K1` write `1 1` there.
