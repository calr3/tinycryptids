# Best machines so far

All machines are 2-symbol beeping machines that start on a blank tape, never halt, and take
their beep transition (state `G0` reading 0 in the design; `N` reading 0 in the standard text
of the 14-state machine) exactly once per Mersenne prime. They quasihalt (beep finitely often)
iff the Mersenne prime conjecture is false: `QuasiHalts … ↔ ¬ MersennePrimeConjecture`.

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **14** | `machines/mersenne_14.txt` (readable: `mersenne_14_annotated.txt`) | `minimize_clique.py mersenne.txt out 600 cadical195 G0:0` on the 15-state design: the wrap's last state joins the D step. The clique bound is 14, so this is optimal for the design | Proven in Lean: `TM.Mersenne.M14.quasihalts_iff`, `M14.never_halts` |
| 15 | `machines/mersenne_15.txt` (= `mersenne.txt`) | `build.py`: trial division of odd `m = 5, 7, …` by odd `d = 3, 5, …`, one mod walk per `d` for both `m` and `m + 1`; the round end found by SAT synthesis (`k = 7`, below) | Proven in Lean: `TM.Mersenne.quasihalts_iff`, `never_halts`, `beeps_forever_iff` |

## Earlier designs (not kept)

Each was merged with the same tool. "Merged" is optimal for the design (it equals the clique
bound).

| Design | Merged | What changed in the next one |
|-------:|-------:|------------------------------|
| 19 | 17 | `../twinprimes`'s machine with odd `d` (the shift writes `1 0 0`: `d := d + 2`) and `m := m + 2`; D's hole on D's last cell; the walk's R hole moving left; a separate beep state `G2`. A variant with the D hole moving left and its home on the old separator also merged to 17 |
| 18 | 16 | the hole's home is the **blank left of D** (D grows by one cell there for free, so the shift only fills the old separator and writes a new one); the R hole **moves right**, starting right after the shift; each walk ends by erasing R's last cell (`d + r = m − 1`), so `G0` reads a blank exactly when every divisor has passed: the beep state is the shift's own state |
| 16 | 15 | found by SAT synthesis (`k = 8`): the scan back to the separator fills it, the check erases the cells it reads, and the way back refills them, so FAIL needs no trip to the separator |
| 15 | 14 | this design (SAT synthesis, `k = 7`): `X1`/`X2` alternate to erase all the way to the hole (no separate scan to the hole); `C4` tells FAIL from OK by what it reads after the hole is filled |

A design that tests only `m = 2^k − 1` (so only `d ∣ m`) was considered and set aside. Its
per-round machinery is one state smaller, but the doubling `m := 2m + 1` needs a loop of about
six states.

## The synthesis

`../tools/synth_round.py` encodes as SAT a table with the walk's 7 states fixed (`B2`'s
0-transition free) and `k` free states, and one run per round of a reference design: from
the end of a walk to the start of the next one, with the tape before and after given. The
reference was the 18-state design of the table above, and its first 33 rounds (every
`(m, d)` with `m ≤ 31`). Each run may be at most 4 steps longer than the reference's. The
beep must be free state `N0` reading 0, taken exactly once in the round of the last divisor
of a Mersenne prime and never otherwise. Free states are first visited in index order
(symmetry breaking). Solvers: `kissat404`, `cadical195` (python-sat). For example, `k = 8`:

    python3 ../tools/synth_round.py design.txt out.txt --fixed B2,Y1,Y2,A2,W1,Z1,Z2 \
        --merge W2:A2 --leave B2:0 --enter B2:1 --k 8 --beep G0:0

| `k` | Total | Result |
|----:|------:|--------|
| 8 | 15 | SAT in 66 s; written out as the 16-state design above |
| 7 | 14 | SAT in 34 min (`kissat404`), 42 min (`cadical195`); this design |
| 6 | 13 | UNSAT in about 500 s (three solvers) with each run at most 4 steps longer than the reference design's |

So with this walk and these tape conventions, no round end of 6 states works within those
step bounds.

## Open: 13 states

Two longer searches for 13 states were run and stopped without an answer. Neither result
rules out 13 states, so this is worth trying again:

* **The `k = 6` search above with `--slack -1`.** Each run may take up to `2n + 10` steps,
  where `n` is the reference run's length. It ran with five solvers (`kissat404`,
  `cadical195`, `cadical153`, `maplechrono`, `glucose4`) for about 7 hours and none
  answered.
* **Only the scanners fixed.** `Y1`, `Y2`, `Z1` and `Z2` were fixed, and `B2`, `A2`, the beep
  state and six more states were free, 13 in all. The reference was the 15-state design, with
  every walk step up to `m = 13` and every round end up to `m = 31`, each at most 4 steps longer
  than in the design. The same five solvers ran for about 7 hours and none answered.
  `synth_round.py` fixes the whole walk, so this search would need it extended. The scratch
  script it used was not kept.

Other ideas:

* split the search into cubes (for example, by the free states' first transitions);
* other tape conventions for the walk;
* a reference design other than the 18-state one.

How the merged machine is proven: `minimize_clique.py` merges only states whose defined
transitions agree, and with `G0:0` no state with a defined 0-transition joins `G0`'s class.
`gen_reduced_lean.py` emits the merged machine, the state map `phi`, `compat` and `excl` (the
merged beep state plays only `G0` on symbol 0), and transfers both theorems with
`quasihalts_iff_of_sim` and `not_halts_of_sim` (`../lean/TinyCryptids/Core/Beep.lean`). The
design never halts, so the merged machine beeps at exactly the same steps.
