# Peano arithmetic with more symbols: fewer instructions

The machine of `../pa` (halts iff the theory T proves `v0 e. v0`; T is equiconsistent with PA,
see `../pa/README.md`) compiled for more than two symbols, to lower the **instruction count**
(BBi: the number of defined transitions, the halting one included). The program, i.e. the proof
search, is `../pa/program.py`'s; only the compiler and the register-machine framework are new.

**The 10-symbol machine is proven in Lean**: `TMK.PA.M10.halts_iff` (`../lean/TinyCryptids/PAK/`,
see `PROOF.md`) states that `machines/pa_10sym_470.txt` halts iff T proves `v0 e. v0`, the same
statement as `TM.PA.M309.halts_iff` for the 2-symbol machine; axioms `propext`,
`Classical.choice`, `Quot.sound`. The other symbol counts are tested, not proven.

| Symbols | States | Instructions | Machine |
|-----:|-----:|-----:|---------|
| 2 | 309 | 617 | `../pa/machines/pa_309.txt` (proven in Lean) |
| 5 | 208 | 521 | `machines/pa_5sym_521.txt` |
| 6 | 160 | 493 | `machines/pa_6sym_493.txt` |
| 7 | 141 | 480 | `machines/pa_7sym_480.txt` |
| 8 | 132 | 475 | `machines/pa_8sym_475.txt` |
| 9 | 126 | 471 | `machines/pa_9sym_471.txt` |
| 10 | 122 | **470** | `machines/pa_10sym_470.txt` (proven in Lean) |
| 11 | 121 | 470 | `machines/pa_11sym_470.txt` |
| 12 | 119 | 472 | `machines/pa_12sym_472.txt` |
| 14 | 116 | 470 | `machines/pa_14sym_470.txt` |

With 10 symbols the count drops from 617 to **470** (−24%). Beyond about 10 symbols nothing
more is gained: nodes cost about one instruction per slot either way, and the two states that
read every digit (`scan`, `adv`) grow by one each per symbol. These are the best programs found by
search for each symbol count, not proven minima. A machine with `k` symbols uses `D = k − 2`
digit values (`kbuild.py`, `configs.py`).

## How it works (`kary.py`)

TMBuilder's machine (`../pa`) keeps a program counter (PC) on the tape: a path through a binary
decision DAG, one bit per node, re-walked from the root before every register operation. With
`D` digit values a node can have up to `D` children, so a sequence of `m` steps is one node with
`m` transitions instead of `m − 1` binary nodes with two transitions each. The machines here use
`D + 2` symbols: blank, the digits `1 … D` (digit value `v` is the symbol `v + 1`), and the
register separator `S = D + 1`.

```
0 [d0 d1 … dh] 1 1 … 1 [S 1^v0] [S 1^v1] … [S 1^v9] 0 0 …
   PC (cell 0 = root)  gap   register file (blocks S 1^v, unary)
```

* **Nodes.** A node is one state; its cell on the PC holds the slot being run, and its children
  are right of it. `1` (digit 0) is also the gap symbol, so a fresh cell means "first slot" and
  the PC needs no length.
* **Advancing.** When a child finishes, `adv` writes `v + 1` on the parent's cell. A node's
  last slot leaves `T = D − 1` on its cell, so `adv` erases `T` cells (writes `1`) and carries
  left: the parent is done too. Slots run at `0, 1, 2, …`; a node with `m < D` slots whose last
  slot is a node reads `m − 1` once and jumps to `T` (one more transition). Nodes that contain
  a register op avoid that: the op finishes within one dispatch, so its transition may write any
  value, and it writes the one after which the remaining slots count up to `T`.
* **Dispatch.** `scan` runs left to the blank before cell 0 and enters the root; the walk goes
  right through the nodes (`D + 1` transitions for `scan`, against 8 dispatch states and 2 root
  states with two symbols).
* **Register operations.** An op is a node's transition straight into a chain state: it writes
  a nonzero digit on its own cell and moves right into the gap. The chain (`cinc<j>`, `cdec<j>`:
  two transitions each) counts `j` separators to the register (the gap is `1`s, crossed like a
  register's unary content), `carry1`/`carryS` shift the rest right for an inc, `dstart`,
  `dscan`, `dput`, `dlast` shift it left for a successful decnz. The return (`retok`, `retfail`)
  runs left over `1`s and separators to the first other symbol, which is the op's node cell,
  and advances it (a failed decnz erases it instead: the node is done). There are no leaf
  states, no marker, no "-1 register" and no prep/cleanup phases.
* **Lazy register file.** Registers are numbered in the order of their first operation in a
  run from the start (`ksim.first_use`), so when register `r` is first used, registers
  `0 … r − 1` exist and `r` is the first missing one: the last chain state writes its separator
  on the blank after the file. The boot only has to write the gap.
* **break / continue** of a label from a node `h` levels below it erase `h + 1` cells
  (`ebrk<h>`, `ecnt<h>`, one transition per digit value that can be there), then `adv` or
  `scan`. A loop used only as the last slot of its parents, and continued only by its own slots,
  is inlined into them: its continue rewrites the parent's cell to the loop's first slot and
  dispatches (`_jmp`), its break finishes the parent (`_done`).
* **Boot.** A searched 3-state machine (`tools/bootsearch.c`) writes the gap and enters `scan`:
  7 instructions leave 12 ones, 8 instructions leave 39 (no 7-instruction machine with three
  states and three symbols, or two states and four, that exits within 10^5 steps leaves more
  than 12). The gap must hold every PC cell: 7 instructions when the PC has at most 12 cells.

The compiler flattens the program's sequences into nodes, factors repeated runs of slots into
shared nodes and inlines small shared nodes where the instruction count drops (`factor`,
`inline`), splits nodes that do not fit into `D` values into trees (`split`: the bottom chunks
by dynamic programming, so that main's 100-odd slots cost few extra nodes), and inlines tail
loops (`inline_loops`). `search_k.py`
then searches the axiom order, each axiom's parameter relabelling and equivalent form (as
`../pa/search_variants.py` did for two symbols), `v_k`'s construction and a seed for the
factoring, for each `D`.

Where the instructions go:

| Part | 2 symbols (`pa_309`) | 10 symbols (`pa_10sym_470`) |
|------|-----:|-----:|
| program (DAG nodes / nodes) | 458 (229 binary nodes) | 371 (87 nodes, 351 slots) |
| boot | 20 (boot1, boot2, root) | 7 |
| dispatch | 16 | 9 (`scan`) |
| advancing, break, continue | 8 | 12 (`adv` 9, erase states 3) |
| register leaves | 40 | 0 |
| prep and cleanup of the -1 register | 7 | 0 |
| register chains | 48 | 42 |
| register operations and returns | 20 | 29 |
| **total** | **617** | **470** |

## Tests

The machines cannot run to any interesting point (one iteration already handles numbers of
millions of bits in unary), so, as in `../pa`, the layers are tested separately:

* `test_ref.py D [N] [R]`: `ksim.py` runs the compiled machine's own node, `adv`, `scan` and
  erase transitions on the PC, with registers as integers (loops and pair/unpair accelerated),
  against `../pa/ref.py` iteration by iteration: the run from the blank start, and random steps
  (every axiom code, random parameters and stacks, DET applicable, B6a's side condition, and
  steps where modus ponens derives `v0 e. v0`, which must halt).
* `check_kaccel.py D`: every pair/unpair node entered afresh from small random registers, with
  and without the acceleration: same registers.
* `kevents.py D [E]`: the real machine (`tools/kevsim.c`) from the blank tape, including the
  boot: its first `E` register operations are those of `ksim` without accelerations, and the
  registers decoded from the tape are equal.
* `test_regs.py D`: the register framework on the real machine (`../tools/sim`): every operation
  on every register from a node's transition, on random register files, including each
  register's creation; the registers, the node's cell and the state the return leaves in.

All nine machines pass: `kbuild.py check` (the files are what the compiler writes),
`test_regs.py D 20` (400 operations), `check_kaccel.py D 20`, `kevents.py D 100000` (about
2·10^9 steps of the real machine), and `test_ref.py D 3 200` (3 iterations from the start,
about 2^200000 register operations or more, and 200 random steps, 16 of which halt as the model
says). The 10-symbol machine also passes `kevents.py 8 300000` (1.7·10^10 steps) and
`test_ref.py 8 6 500` (34 halting steps).

## Files

```
ir.py           ../pa/program.py's program with symbolic labels (break/continue unresolved)
kary.py         the compiler: nodes, factoring, splitting, digit values, the machine
ksim.py         abstract interpreter (registers as integers, accelerations)
configs.py      the program found by search_k.py for each D;  kbuild.py writes machines/
search_k.py     annealing over order, relabellings, forms, switches and a factoring seed
gen_klean.py    the generated parts of the Lean proof of the 10-symbol machine (PROOF.md)
test_ref.py     ksim vs ../pa/ref.py;   check_kaccel.py  accelerations vs plain execution
kevents.py      real machine vs ksim (tools/kevsim.c);   test_regs.py  the register framework
tools/          kevsim.c, bootsearch.c (gcc -O2 -o tools/kevsim tools/kevsim.c, likewise)
machines/       pa_<symbols>sym_<instructions>.txt
```
