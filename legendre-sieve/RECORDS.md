# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Legendre's
conjecture is false: for some `n >= 1` there is no prime `p` with `n^2 < p < (n+1)^2`.

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **45** | `machines/legendre_45.txt` | `minimize.py` (kissat) on the 68-state design; 44 unresolved (kissat and cadical each timed out after ~2 h) | Proven in Lean: `TM.LegendreSieve.M45.halts_iff` |
| 68 | `machines/legendre_68.txt` (= `legendre.txt`) | `build.py`: incremental sieve | Proven in Lean: `TM.LegendreSieve.halts_iff` |
