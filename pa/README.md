# Peano arithmetic: a machine that halts iff a PA-equivalent theory is inconsistent

**Statement.** The machine halts iff it finds a proof of `v0 e. v0` in the theory **T** = Tarski's
system S2 of first-order logic with `=` and `e.` (axioms B1–B8 below, rules modus ponens and
generalisation) plus one set-theoretic axiom scheme from H. Friedman, *Issues in the Foundations of
Mathematics* (2002), p. 10. T proves `¬ ∀v0 v0 e. v0` (it has an empty set), so it proves
`v0 e. v0` iff it is inconsistent, and T is equiconsistent with PA (it is mutually interpretable
with PA: separation for every formula gives induction, and PA interprets the hereditarily finite
sets). So the machine halts iff PA is inconsistent, and its halting is independent of PA (if PA is
consistent).

**Proven in Lean** for the 309-state machine (`../lean/TinyCryptids/PA/`, `PROOF.md`):

```
TM.PA.M309.halts_iff : Halts delta2 start2 ↔ TinyCryptids.Wff.Provable (TinyCryptids.Wff.el 0 0)
```

with T defined in `../lean/TinyCryptids/Defs.lean` (`Wff`, `Wff.Axiom`, `Wff.Provable`) exactly
as below, in the standard forms (axioms: `propext`, `Classical.choice`, `Quot.sound`). The step
from T to PA (equiconsistency) is Friedman's and is not formalised.

| Machine | States | |
|---------|-------:|---|
| `machines/pa_372.txt` | 372 | LegionMammal978's `pa.py` (baseline, rebuilt exactly by `baseline.py`) |
| `machines/pa_309.txt` | 309 | this folder: `program.py` + `tmbuilder.py` (`build.py`); proven in Lean (`TM.PA.M309.halts_iff`) |

`RECORDS.md` lists every step from 372 down.

## The baseline (372 states)

[LegionMammal978/turing_machine_explorer](https://github.com/LegionMammal978/turing_machine_explorer)
`pa.py` (commit `c3d265a`, 2026-02-15), a modification of A. J. Wade's `zf2.py` (ZF, 432 states),
which ports sorear's NQL `zf2.nql` (metamath-turing-machines). The sources are in `legion/`
(MIT No Attribution, `legion/LICENSE`).

* **Framework** (95 states): a register machine on the tape. A program counter (PC) at the left
  is a path in a binary *decision DAG*; dispatch walks the PC from its start through DAG states,
  one state per DAG node, to a leaf `3.R.inc` / `3.R.decnz`; the leaf marks the PC and extends a
  "-1 register" over the gap to the register file, dispatch runs again, and the leaf now goes down
  a chain of states (`2b.reg.N.*`, one per register) that counts registers, performs the
  operation, and returns; `6.break.*` / `6.continue.*` update the PC (next sibling, leave a loop,
  restart a loop). Registers are unary blocks; there are 11.
* **Program** (277 DAG states): an RPN proof checker. A stack of theorems `wffstack` / `topwff`
  (wffs coded by Cantor pairing: `x = y` is `pair(pair(x, y), 0)`, then `e.` 1, `->` 2, `-.`
  3 as `pair(ph, 3)`, `A.` 4; variables are numbers, so `v0 e. v0` is 1). Each iteration reads a
  step `(axiomcode, p1, p2, p3)` from the proof code `prooflist` (and moves on to the next code,
  `nextproof`, when it runs out: every finite sequence of steps is eventually run), pushes the last
  theorem, computes *every* candidate — each axiom instance with parameters `p1, p2, p3`,
  generalisation, modus ponens on the top theorems — keeps candidate number `axiomcode`, and halts
  if the kept wff is `v0 e. v0`.

The axioms (wffs over `p1, p2, p3`; B6a needs `p3` distinct from `p1`, `p2`):

```
B1  (p1 -> p2) -> ((p2 -> p3) -> (p1 -> p3))        B2  (-. p1 -> p1) -> p1
B3  p1 -> (-. p1 -> p2)                              B4  A.p1 (p2 -> p3) -> (A.p1 p2 -> A.p1 p3)
B6a (p1 = p2 -> A.p3 p1 = p2) /\ (p1 e. p2 -> A.p3 p1 e. p2)
B6b A.p1 A.p2 p3 -> A.p2 A.p1 p3                     B6c E.p1 A.p1 p2 -> p2
B7  E.p1 p1 = p2                                     B8a p1 = p2 -> (p1 = p3 -> p2 = p3)
B8b p1 = p2 -> (p1 e. p3 -> p2 e. p3)                B8c p1 = p2 -> (p3 e. p1 -> p3 e. p2)
E   E.v1 A.v0 (((-. v0 e. v2 -> v0 = v3) -> (A.v1 P -> v0 e. v1)) /\ (v0 e. v1 -> A.v1 P))
    with P = p1   (Friedman: the set {v0 in v2 u {v3} : P} exists, up to the A.v1 trick)
```

## What changed (309 states)

The theory is the same; the candidates, the library routines and the compiler changed.
`ref.py` states the new iteration exactly (`iterate_tail`; `iterate_original` is pa.py's).

Compiler (`tmbuilder.py`, both switches off reproduce pa.tm exactly):

* `dispatch_reset`: dispatch counts *consecutive* zeros, resetting on a 1. The PC never holds
  more zeros in a row than the longest run of car-descents in the DAG, so `run + 1` counting states
  suffice instead of `(zeros on a path) + 3` (14 → 11 states here).
* `merge_equal`: states with identical behaviour are merged (`2b.reg.-2.inc` = `inc.shift_2`).
* (in `program.py`, `shallow`) `pair`, `unpair` and `if_eq` are re-nested so that no continue
  erases more than two PC bits and no break skips more than one level: the framework then needs
  only `6.break.0/1` and `6.continue.0/1`.
* `breakers`: a node `(_break.0, X)` replaces the references to `X` (here `pushwff`). Its car
  rewrites its own 0 bit to 1 and re-dispatches, so `X` is entered through a 1 and no run of
  zeros on a PC path continues into it: one state, and the longest run (hence dispatch) shrinks
  by more. `max_zero_run` now counts only the bits that are on the tape when dispatch scans (a
  break/continue/halt leaf's own bit never is).

Program (`program.py`):

* The duplicate B6b and B8b candidates are dropped, and the axioms are reordered (the order
  decides which subsequences the builder can share).
* Each axiom's parameters are relabelled (`VARIANTS`: B8a(p2, p3, p1) is the same schema as
  B8a(p1, p2, p3)), and the non-propositional axioms (B4, B8a–c, B6a, E) may be written in a
  tautologically equivalent form (`FORMS`: antecedents swapped, conjuncts commuted, inside E
  `-. v0 e. v2 -> v0 = v3` as `-. v0 = v3 -> v0 e. v2`); B1–B3, the propositional base, are only
  relabelled. Order, relabellings and forms were searched together (`search_variants.py`).
* B6a, GEN and DET come last, so they may destroy parameters instead of copying them: B6a's two
  distinctness tests share one `if_eq` with DET, and `scratch3` is gone (10 registers).
* GEN and DET are computed only when kept (each is one test of `axiomcode`, `cascade`). GEN pops
  the top theorem `q`; DET then pops the next one `M` and keeps `p1` if `M = (q -> p1)`, else
  `v0 = v0`. DET's comparison is B6a's `if_eq` (the body `topwff := param1`, with `p1` parked while
  B6a tests). (pa.py popped both premises inside DET, testing `axiomcode == 1` for each rule.)
* The stack is `pair(rest, top)` and proof codes are read as `pair(rest, component)`, so every pop
  is one `unpair` instance and `cons` reuses `pushwff`'s `pair` instance (wff codes are unchanged);
  `select` is an if/else on `axiomcode` instead of a second `unpair`.
* Smaller things: the reload of `prooflist` and B6a's tests reuse existing loops; `v_3`, `v_4` are
  built as `v_1`, `v_2` plus two increments (one zero less on the longest DAG path, so one
  dispatch state less).

Why the changes keep the halting condition: the set of wffs a step can produce is the same as in
pa.py up to tautological equivalence — every axiom instance for every `p1, p2, p3` (B6a only when `p3` is distinct from `p1`,
`p2`), generalisation of the top theorem, modus ponens on two theorems of the stack — and every
kept wff is an axiom instance, a rule application, or `v0 = v0` (code 0, which T proves). Proofs
are trees evaluated in RPN; the stack only grows by theorems; pops only drop theorems. A step
coded past the last candidate keeps the last one (DET), as pa.py keeps its last (E). DET reads
its premises "minor on top, major below", which any proof tree can be arranged to give (when DET
is kept, GEN has popped the minor premise just before). A proof code can always make a
step's unused parameters harmless (B6a's test failing only matters if B6a is kept). The proof enumeration (`prooflist` decremented each step, reloaded from
`nextproof`) still runs every finite step sequence: decoding `pair(rest, c)` only changes which
code stands for which sequence.

## The Lean proof

`PROOF.md` walks through it. In outline:

* `Machine.lean` defines the machine TMBuilder compiles from *any* decision DAG. `M309.lean`
  checks, state by state, that `machines/pa_309.txt` is that machine for the program's DAG
  (`Dag.lean`, generated by `gen_lean.py`) with two equal states merged.
* `Frame.lean` proves, for any DAG meeting `DagOK` (leaf kinds, zero runs of at most 6, depth),
  that the tape follows the DAG's big-step semantics (`Sem.lean`): dispatch, the walk, both
  phases of every register operation, the program counter updates. `DagCheck.lean` checks
  `DagOK` by `decide`.
* `Nodes.lean` (generated by `gen_nodes.py`) gives every node's effect on the registers.
  `Clean.lean` and `Abs.lean` turn the subroutines into stack operations, and `Iter.lean`
  (generated by `gen_iter.py`) proves main computes one iteration of the proof search.
* `Search.lean` proves the search keeps `v0 e. v0` iff T proves it. Every candidate is a
  theorem; every axiom of T derives from the candidates (E and B4 are in a form with two
  antecedents swapped, rewritten with permutation from `Luk.lean`, derivations found by
  `cd_search.py`); derivations are replayed in reverse Polish notation; the enumeration reaches
  every proof code.
* `Boot1.lean` proves the 5-state counter's 2,133,492 steps by sweeps (seven rounds); `Boot2.lean`
  the 1908 inc/decnz pairs that build the register file.

## Tests

The machine cannot be run to any interesting point: one iteration builds every axiom instance,
and a single cons squares a number, so the first iteration already handles numbers of ~10^5 bits
(in unary). The tests check the three layers separately.

* `test_model.py`: `dagsim.py` runs the compiled machine's *own* decision-DAG, root, break and
  continue transitions on the PC, with registers as integers (loops and pair/unpair accelerated),
  and is compared with `ref.py` iteration by iteration: the run from the blank start and 400
  random steps (every axiom code, random parameters and stacks, DET applicable or not, B6a's side
  condition hit). Also run on the baseline (`original`) against `ref.iterate_original`.
* `check_accel.py`: every subroutine node of the DAG, run from small random registers with and
  without the accelerations: same registers.
* `test_forms.py`: every form of every axiom, as postfix in `program.py`, equals the
  hand-written formula in `ref.py`, and forms other than the first are tautologically
  equivalent to it (all truth assignments; for E, the matrix under `E.v1 A.v0`).
* `test_proofs.py`: proofs fed in as proof codes from the blank start (B3, B2 and modus ponens;
  generalisation), checking the machine's theorem after each step, and a step that keeps
  `v0 e. v0`, which must halt.
* `tm_events.py`: the real machine (`tools/evsim.c`) for 10^11 steps: its first 300,000 register
  operations after the boot are the same as `dagsim`'s, and so are the register values decoded from
  the tape. This covers the boot, dispatch, the register chains and the returns.

`gmpy2` makes `test_model.py` about 30× faster (`dagsim.py` uses it if present).

## Files

```
legion/         LegionMammal978's pa.py, A. J. Wade's TMBuilder.py and tm.py, pa.tm (MIT-0)
baseline.py     rebuild pa.tm with tmbuilder.py (all switches off) and check it is identical
tmbuilder.py    the fork of TMBuilder.py (switches: dispatch_reset, merge_equal, breakers, grammar_seed)
program.py      the improved program (switches for each change); build.py writes machines/
ref.py          reference semantics of one iteration (both programs)
dagsim.py       abstract interpreter of a compiled machine (registers as integers)
gen_lean.py     writes ../lean/TinyCryptids/PA/Dag.lean and M309.lean (checks machines/pa_309.txt)
gen_nodes.py    writes Nodes.lean (every node's effect);  gen_iter.py  Iter.lean (main's operations)
gen_cand.py     writes Cand.lean (the candidates' codes);  gen_logic.py  Luk.lean from cd_proofs.txt
cd_search.py    condensed-detachment search for the propositional laws (writes cd_proofs.txt)
PROOF.md        the Lean proof in plain words
test_model.py   dagsim vs ref;   test_proofs.py  proofs end to end;   test_forms.py  axiom forms
check_accel.py  accelerations vs plain execution
tm_events.py    real machine vs dagsim (tools/evsim.c: gcc -O2 -o tools/evsim tools/evsim.c)
search_variants.py  annealing over order, relabellings and forms (search_order.py: order only)
search_breakers.py  greedy breaker placement;  zerorun.py  longest DAG zero runs
```
