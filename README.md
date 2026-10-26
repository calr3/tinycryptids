# Small Turing machines for open problems, proven in Lean

Each folder holds a Turing machine that refers to a notable mathematical conjecture. Each machine is designed so that whether it halts implies something about a notable mathematical conjecture. For example, for problems in [class Π₁](https://en.wikipedia.org/wiki/Arithmetical_hierarchy), the machine halts iff the conjecture is false; for Σ₁, it halts iff the conjecture is true, and so on. See the [BusyBeaverWiki](https://wiki.bbchallenge.org/wiki/Cryptids#Larger_Cryptids) for many other interesting examples!

Each machine comes with a formalized proof in Lean 4 (core library only, no Mathlib); run
`cd lean && lake build && lake env lean Check.lean` to check them all.

## Machines

| Folder | Conjecture | [Class](https://en.wikipedia.org/wiki/Arithmetical_hierarchy) | Condition | [Result](https://wiki.bbchallenge.org/wiki/Busy_Beaver_Functions) |  Theorem |
|--------|------------|:-----:|-----------|-----:|----------|
| [`weakcollatz/`](https://github.com/calr3/tinycryptids/tree/main/weakcollatz) | [Weak Collatz conjecture](https://en.wikipedia.org/wiki/Collatz_conjecture) | Π₁ | Halts iff the Collatz sequence has a cycle other than 1 → 4 → 2 → 1 | BB(14) | `TM.WeakCollatz.halts_iff` |
| [`weakcollatz/sym3/`](https://github.com/calr3/tinycryptids/tree/main/weakcollatz/sym3) | [Weak Collatz conjecture](https://en.wikipedia.org/wiki/Collatz_conjecture) | Π₁ | Halts iff the Collatz sequence has a cycle other than 1 → 4 → 2 → 1 | BB(10,3) | `TM3.WeakCollatz.halts_iff` |
| [`twinprimes/`](https://github.com/calr3/tinycryptids/tree/main/twinprimes) | [Twin prime conjecture](https://en.wikipedia.org/wiki/Twin_prime) | Π₂ | Quasihalts iff there are only finitely many twin primes (the beep: state N reading 0) | BBB(18) ‡ | `TM.TwinPrimes.M18.quasihalts_iff` |
| [`oddperfect/`](https://github.com/calr3/tinycryptids/tree/main/oddperfect) | [No odd perfect numbers](https://en.wikipedia.org/wiki/Perfect_number#Odd_perfect_numbers) | Π₁ | Halts iff an odd perfect number exists | BB(37) | `TM.OddPerfect.M37.halts_iff` |
| [`kurepa/`](https://github.com/calr3/tinycryptids/tree/main/kurepa) | [Kurepa's conjecture](https://oeis.org/A049782) | Π₁ | Halts iff some odd prime `p` divides `!p = 0! + 1! + … + (p−1)!` | BB(38) | `TM.Kurepa.M38.halts_iff` |
| [`sierpinski/`](https://github.com/calr3/tinycryptids/tree/main/sierpinski) | [Sierpiński problem](https://en.wikipedia.org/wiki/Sierpiński_number#Smallest_Sierpiński_number) | Σ₁ | Halts iff 78557 is the smallest Sierpiński number | BB(60) | `TM.Sierpinski.M60.halts_iff` |
| [`riesel/`](https://github.com/calr3/tinycryptids/tree/main/riesel) | [Riesel problem](https://en.wikipedia.org/wiki/Riesel_number) | Σ₁ | Halts iff 509203 is the smallest Riesel number | BB(76) | `TM.Riesel.M76.halts_iff` |
| [`fermat/`](https://github.com/calr3/tinycryptids/tree/main/fermat) | [Fermat's Last Theorem](https://en.wikipedia.org/wiki/Fermat's_Last_Theorem) † | Π₁ | Halts iff there's a non-trivial solution to `x^n + y^n = z^n` for some `n ≥ 3` | BB(90) | `TM.Fermat.M90.halts_iff` |

The symbol count is the number of unique symbols that the machine can print. The state count is the number of states required by the smallest known machine, as given by the output of the fully minimized machine (`minimize.py` or `minimize_clique.py`) from the design given in the folder's `build.py`.
Each folder's `RECORDS.md` lists every machine, `README.md` explains the algorithm and gives the machine in bbchallenge standard text, `PROOF.md` walks through the proof in plain words, and `machines/*_annotated.txt` describes every state.

† Fermat's Last Theorem is of course a theorem since Wiles, so any non-halting machine would do. This more direct machine is included as a historical curiosity, because James Randels' dissertation *Studies in Turing Machines* (1965) estimated
that fewer than 400 states would suffice for a Fermat counterexample searcher, but didn't provide the full description. This machine (and its proof) do not use Wiles's result.

‡ A beeping machine never halts. It has one designated beep transition (here state N reading 0), and it *quasihalts* if it takes that transition only finitely often; this one takes it once for every twin prime pair (p, p + 2), p ≥ 3. A Π₂ statement such as the twin prime conjecture has no finite counterexample for a halting machine to find, but a beeping machine has a last beep iff it is false. The Lean definitions are in `lean/TinyCryptids/Core/Beep.lean`. BBB(18) here counts 18-state machines with a beep transition; with a beep *state* (Aaronson's definition) the same machine needs at most one more state.

## Layout

| Path | Contents |
|------|----------|
| `<conjecture>/` | One hand-designed machine: `build.py`, tests, `machines/`, `README.md`, `RECORDS.md`, and `gen_lean.py`/`gen_reduced_lean.py`/`annotate.py` |
| `lean/` | **All proofs**, one Lake project: `TinyCryptids/Core/` (the shared machine model), `TinyCryptids/Defs.lean` (every definition used in a statement), `TinyCryptids/<Machine>/` (namespace `TM.<Machine>`), `Check.lean`. See `lean/README.md` |
| `tools/` | Shared Python tools: `tm.py` (format, standard text), `sim.c` (`gcc -O2 -o tools/sim tools/sim.c`), `same_run.py`, `minimize.py`, `minimize_clique.py`, `minimize_dimacs.py`, `greedy_merge.py`, `leangen.py` |
