# Records: PA (halts iff PA is inconsistent)

| States | Machine | How |
|-------:|---------|-----|
| 372 | `machines/pa_372.txt` | LegionMammal978, `legion/pa.py` (turing_machine_explorer `c3d265a`, 2026-02-15); A. J. Wade's TMBuilder |
| 309 | `machines/pa_309.txt` | `program.py` + `tmbuilder.py`, `build.py` (this folder) |

The 309-state machine is proven in Lean (`TM.PA.M309.halts_iff`: it halts iff T proves `v0 e. v0`;
`PROOF.md`); the 372-state baseline is not.

## From 372 to 309

Each line adds one change to the previous (the program is `program.py` with its switches; the
first lines are the program restructuring, measured with the experimental builds that preceded it).

| States | Change |
|-------:|--------|
| 372 | pa.py as published |
| 369 | drop the second copies of B6b and B8b (they are candidates twice) |
| 349 | reorder the axioms (annealing over the order, `search_order.py`); B6a, GEN, DET last, destroying parameters instead of copying them; `scratch3` removed; GEN/DET pop when `axiomcode != 0` |
| 345 | `dispatch_reset`: dispatch counts consecutive zeros only (11 counting states instead of 14) |
| 344 | `merge_equal`: identical states merged (`2b.reg.-2.inc` = `2b.reg.inc.shift_2`) |
| 330 | `stack_rev`: stack `pair(rest, top)`, proof codes `pair(rest, c)`: one `unpair` for every pop, `cons` shares `pushwff`'s `pair`, `select` without its own `unpair` |
| 329 | `reload2`: the `nextproof` copy goes through `scratch1`/`scratch2` loops that exist anyway |
| 325 | `b6a2`: B6a's two distinctness tests rebuilt from existing loops |
| 320 | `shared_eq`: DET compares with B6a's `if_eq` instance (`eqbody`: topwff := param1, with p1 parked during B6a); DET pops only the major premise (GEN has popped the minor one) |
| 319 | `cascade`: GEN and DET are computed only when kept (one `axiomcode` test each, `drop` instead of `select`) |
| 318 | `vchain`: `v_3 = v_1 + 2`, `v_4 = v_2 + 2` (the longest zero run on a DAG path 10 → 9, one dispatch state less) |
| 316 | `shallow`: `pair`, `unpair`, `if_eq` re-nested so that no loop's continue erases more than two PC bits and no break skips more than one level: `6.continue.2`, `6.continue.3`, `6.break.2` are gone (`pair` +1 node) |
| 315 | `breakers`: `pushwff` is entered through a node `(_break.0, body)` that rewrites its 0 bit to 1 and re-dispatches, so no run of zeros on a PC path goes through it; the longest run drops 9 → 7 (−2 dispatch states, +1 node) |
| 309 | `variants`: each axiom's parameters relabelled (B8a(p2, p3, p1) is the same schema as B8a(p1, p2, p3)) and the non-propositional axioms written in tautologically equivalent forms (antecedents swapped, conjuncts commuted, inside E too), searched together with the order (`search_variants.py`); the longest zero run is now 6 |

The order of the axioms matters by a few states (every search ends with E first); the lines up
to 316 use the 316 order. With the 309 configuration, the breaker is worth 2 states (311 without)
and the relabellings and forms 6 (315 with the breaker but the 316 order and plain forms).

What did not help: conjunction candidates (`X+Y`, one candidate `X /\ Y`; the search found
309s with them, but none below); conjoining B8a, B8b, B8c into one axiom (the builder already shares their common
prefix; +1 to +4 states); randomised subsequence factoring (`grammar_seed`, at most −1 on some
builds); flattening the `v_k` chain (the factoring pass re-nests it). One rule for GEN and DET
(`gendet`: pop `q` and `M`, keep `p1` if `M = (q -> p1)`, else `A.p1 q`) built to 315 states, but
it was wrong: it parks the comparison value in `scratch2` while building `A.p1 q`, and `cons`
uses `scratch2`. `test_proofs.py` and the random steps of `test_model.py` both catch it (dagsim
now refuses an `unpair` entered with nonzero outputs instead of running it plainly forever); the
correct versions cost as much as they save.
