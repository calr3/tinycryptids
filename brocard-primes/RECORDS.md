# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Brocard's conjecture is false
(`∃ p q, 3 ≤ p ∧ Prime p ∧ Prime q ∧ p < q ∧ (∀ r, p < r → r < q → ¬ Prime r) ∧
primeCount (q ^ 2) - primeCount (p ^ 2) < 4`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **72** | `machines/brocard_primes_72.txt` (readable: `brocard_primes_72_annotated.txt`) | `minimize.py` (`kissat404`; `cadical195` also reaches 72) on the 108-state design; the searches for 71 (`kissat404`, `cadical195`, `maplechrono`) were stopped without a result (to resume: `MIN_SOLVER=kissat404 python3 ../tools/minimize.py brocard_primes.txt out.txt 71`) | Proven in Lean: `TM.BrocardPrimes.M72.halts_iff` |
| 108 | `machines/brocard_primes_108.txt` (= `brocard_primes.txt`) | `build.py`: `../legendre-sieve`'s sieve with a marker before the primes whose square is passed and a counter of the primes since the last prime square | Proven in Lean: `TM.BrocardPrimes.halts_iff` |

Other designs (not kept, see `README.md`): a cheaper marker move (107 states → 73), K in front
of S (103 → 74; proven in Lean along the way, then replaced), S swept as an ordinary block
(102 → 76).

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
