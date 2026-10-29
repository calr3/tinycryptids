# The proof for the 10-symbol machine, in plain words

The Lean files are in `../lean/TinyCryptids/PAK/` (namespace `TMK.PA`), with the multi-symbol
machine model in `../lean/TinyCryptids/Core/Multi.lean` (namespace `TMK`). The main theorem is

```
TMK.PA.M10.halts_iff : TMK.Halts delta2 start2 ↔ TinyCryptids.Wff.Provable (TinyCryptids.Wff.el 0 0)
```

for the 122-state, 10-symbol machine `machines/pa_10sym_470.txt` (470 instructions), where
`delta2` is that file's table and `Wff.Provable` is provability in the theory T of `../pa/README.md`
(`../lean/TinyCryptids/Defs.lean`). It is the statement of `TM.PA.M309.halts_iff` for the 2-symbol
machine. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

The program is `../pa/program.py`'s, with this machine's axiom order and forms (`configs.py`,
`D = 8`); the proof reuses the 2-symbol proof's abstract layers (the registers between
subroutines `TM.PA.A`, Cantor pairing, formula codes, the logic) and redoes the machine-level
ones. `gen_klean.py` writes the generated files (`Tree`, `Nodes`, `Comp`, `Cand`, `M10`).

## 1. The machine (`Core/Multi.lean`, `Tree.lean`, `Machine.lean`, `M10.lean`)

* `Core/Multi.lean`: Turing machines over the symbols `Nat` (0 is the blank): tapes are streams
  `Nat → Nat`, `step`, `Halts` (via `Sys`), and `halts_iff_of_sim`, as `Core/Basic.lean` for two
  symbols.
* `Tree.lean` (generated): `kary.py`'s program tree, 87 nodes (node 0 is main): each node's slots
  (`Sl`: a child, `inc r`, `dec r`, a break or continue with the number of cells it erases, a jump
  to a slot of the node, the end of an inlined loop, halt), the value its cell holds when each
  slot runs (`vals`), the value each slot's transition writes (`wrs`), the skip values, subtree
  heights, the break and continue levels a node can end with, the erase / advance / return
  tables and the register numbering (`mpos`, the order of first use).
* `Machine.lean`: `St` and `delta`, `kary.py`'s `emit` for this tree: the node states, `scan`,
  `adv`, the erase states, the chains `cinc j` / `cdec j`, the shifts, the returns and the boot.
* `M10.lean` (generated from the machine file): the file's table `delta2`, the state map `phi`,
  `compat` (by `decide`: every defined transition of `delta` is the file's), and `halts_iff` via
  `halts_iff_of_sim`.

## 2. The tape (`Sem.lean`, `Tape.lean`, `Ops.lean`, `Frame.lean`)

* `Sem.lean`: `Run i j s o t`, node `i` run from its slot `j` on registers `s` (`TM.PA.R`) ends
  with outcome `o` (`brk k`, `cnt k`, `halt`) and registers `t`. A child's break or continue past
  its parent carries the premise that the erase state reads the parent's cell.
* `Tape.lean`: the register file `regs` (blocks `9 1^v`), moves over runs of `1` and `9`, the
  chain to a register (`chain_regs`) or to the blank after the last (`chain_new`: the register is
  created), the inc's shift right (`shift_ret`) and the decnz's shift left (`dscan_ret`), and the
  return to the node's cell (`ret_back`).
* `Ops.lean`: the four cases of a register operation on lists (`inc_list`, `inc_new`, `dec_pos`,
  `dec_zero`, `dec_new`), and on the registers `R` with nine or ten registers present (`LV`: only
  `param2`, the last, may be missing, and is then zero): `op_inc`, `op_dec`.
* `Frame.lean`: a node at depth `d` with its ancestors' values left of its cell (`pcL`, `atNode`);
  `dispatch` (`scan` to the blank, then the walk down the path, `WalkOK`); `nodeOK` lists what the
  simulation needs of each slot (which value follows which, the transitions of the advance, the
  returns and the erase states, the subtree's depth), checked for all nodes by `decide`
  (`allOK`). `sim`: by induction on `Run`, every outcome is reached on the tape (`Ends`).

## 3. The program (`Shape.lean`, `Nodes.lean`, `Abs.lean`, `Comp.lean`)

* `Shape.lean`: `runS` runs a list of slots (operations, children with a known denotation `ch c g`,
  a tail proven apart), ending with an outcome or back at a slot of the node; `runS_sound` (when
  the list is the node's slots, `SMatch`). `outcomes` and `ctlOK` (by `decide`) give the erase
  premises. `straight_sound` for nodes without loops; `loop_sound` (a measure and a closed form),
  `while_sound`, and the closed forms `zero_sound`, `xfer_sound`, `xfer2_sound`.
* `Nodes.lean` (generated): for every node its denotation `d<i>` (outcome and registers) and the
  proof `e<i>`: 54 straight nodes, 24 zeroing and moving loops, 5 nodes ending in an inlined
  moving loop, and four loops proven with `loop_sound`: the two `unpair` loops (one step of
  Cantor's order per unit, `TM.PA.nextN`), `pair` (`scratch1 += T(topwff)`) and `if_eq`'s lockstep.
* `Abs.lean`: the subroutines on `TM.PA.A` (`PA/Abs.lean`'s abstract registers: scratch zero,
  `wffstack` a stack): `push_emb`, `par1_emb` … `cons_emb`, `select_emb`, `drop_emb`,
  `reload_emb`, the zeroing and decoding steps, `if_eq` in closed form, B6a's check in two parts
  (`b6pre`, which ends one of main's chunks, and its last loop), DET's comparison, the halt test.
* `Comp.lean` (generated): every node made of subroutines computes a chain of `A` operations
  (`k<i>_emb`, by rewriting with `run_ch`); GEN and DET; main: `k0_emb`, main computes `k0` and
  halts iff its `topwff` is 1.

## 4. The search (`Cand.lean`, `Step.lean`)

* `Cand.lean` (generated): each candidate axiom in this machine's form and relabelling as a code
  (`axB2` … `axB6a`), its chain of operations (`kc<X>`) and `kc<X>_eq`; main's chain grouped into
  the decoding, `v_0`, the twelve candidates in this machine's order, GEN and DET (`iterK`;
  `k0_eq` by `rfl`).
* `Step.lean`: `stepK`, one iteration of `../pa/ref.py`'s `iterate_tail` with these candidates
  (`iterK_eq`); soundness (`cand_sound`: B4 and B8b with antecedents swapped by `perm_r`, E by
  `e_swap`), completeness (`axiom_M`, `rpn`, `run_code`, `reach_code`), and `search_iff`, as
  `PA/Search.lean`.

## 5. The run (`Boot.lean`, `Run.lean`)

* `Boot.lean`: the boot and main's first operations create the register file one register at a
  time, which `sim` (nine or ten registers) does not cover. The first 853 steps from the blank tape
  are run as a computation on finite tapes (`lrun`, by `decide`, about a second): they end in
  main's second chunk (node 17) at its slot 5, with nine registers.
* `Run.lean`: `pass`, a pass through main from `mainCfg σ` (the registers of an iteration) is one
  `stepK`, or halts iff the kept theorem is 1; `first_pass`, from the blank tape, the computation
  and then the rest of the first pass by `sim`; `halts_iff` for `delta`: (→) by
  `not_halts_of_progress` over the starts of the passes, (←) by running to the first iteration
  that keeps `v0 e. v0`; `haltAt_of` for the transfer to `M10`.

## Regenerating

`python3 gen_klean.py` rewrites `Tree`, `Nodes`, `Comp`, `Cand` and `M10` from `kbuild.build(8)` and
the machine file. The hand-written files name node numbers and slots of this tree (`Abs`, `Run`,
the templates in `gen_klean.py`) and the 853-step computation's end (`Boot`); if the program or
`configs.py`'s entry for `D = 8` changes, regenerate and fix them.
