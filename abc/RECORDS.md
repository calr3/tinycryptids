# Best machines so far

All machines are 2-symbol Beeping Booping machines (Bram Cohen's definition). They start on a
blank tape and never halt. Their beep is state `xe3` reading 0 and their boop is `xq6` reading 0
(design names). Some beep count between consecutive boops repeats forever iff the abc
conjecture is false: `RepeatsForever … ↔ ¬ ABCConjecture`.

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **235** | `machines/abc_235.txt` (readable: `abc_235_annotated.txt`) | `greedy_merge_par.py abc.txt out 184 23 xe3:0,xq6:0 5000` (randomised greedy merging on 23 processes, the beep and the boop kept exclusive), stopped after about 3.5 hours; 235 came from seed 5014 at restart 22,813. Not proven optimal (below) | Proven in Lean: `TM.ABC.M235.repeats_iff`, `M235.never_halts` |
| 368 | `abc.txt` | `build.py`: the factor loop (`GCD(D, X)` by lockstep holes, `R := R·d`), the pre-test, the power loop (`P := P·c` mirrored, `Q := Q·R`, a shared compare), the pair end | Proven in Lean: `TM.ABC.repeats_iff`, `never_halts` |

## Merging

* `greedy_merge.py` (randomised, without the exclusivity constraint): 252 states with 2,000
  restarts (a longer run reached 244 but was cut off before writing its result). The 252-state
  merge happens to keep the beep and the boop exclusive.
* `greedy_merge_par.py` (the same merging on many processes, refusing merges that break the
  exclusivity, writing each new best at once): with 23 processes, 244 within a minute, 242
  seconds later, then 241, 240, 238, 237 and 236 within 30 minutes, 235 after about 1.5 hours
  (restart 22,813 of one process), and nothing better in the 2.5 hours after that. Greedy merging
  seems to level off near 235.
* `minimize_clique.py abc.txt out 3600 cadical195 xe3:0,xq6:0`: the clique lower bound is 179.
  `K` = 179 … 183 are unsatisfiable, which bounds this design's merges from below.
  `K` = 184 and above were not settled (each `K` is a CNF of tens of millions of clauses), and the
  search was stopped, so the optimum for this design lies somewhere in 184 … 235.

## Where the states go

The design's 368 states:

| Part | States |
|------|-------:|
| Seed | 26 |
| `GCD(D, X)` and its four entries and exits (pass, hit, the `R` test) | 76 |
| `d += 1`, the last divisor, the pre-test | 25 |
| Compare (shared by the pre-test and the loop) | 26 |
| Power init | 18 |
| `R := R·d` and `Q := Q·R` (one copy of the multiplication), the way back | 42 |
| After the beep, `P := P·c` (the mirrored copy), the way to `Q := Q·R` | 64 |
| Pair end: erase, `a += 1` or `c += 1`, `R := 1`, `d := 2` | 91 |

Ideas for a smaller machine:

* The two multiplications (right and mirrored) are 30 states each. With `P` grown on the right,
  past `Q`, one copy would serve all three products, at the cost of longer walks.
* The seed (26 states) could be a pseudo-pair that the pair end turns into `(1, 1)`, as in
  `../sierpinski` and `../twinprimes`.
