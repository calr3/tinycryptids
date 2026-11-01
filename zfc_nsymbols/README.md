# ZFC with more symbols: a machine that halts iff ZFC is inconsistent

E. Glazer's K215 ([elliotglazer/k215-pa](https://github.com/elliotglazer/k215-pa)) is a 2-symbol
Turing machine with 215 states and 430 instructions, with a Metamath Zero proof (in PA) of

```
theorem K215_halts_iff_ZFC_inconsistent: $ k215LiteralHalts <-> zfcInconsistent $;
```

K215 runs a register program, `k215P` in that proof (`k215_literal_runtime_program.mm0`: 4751
entries over 9 registers, starting at pc 0 with r0 = 4), and the proof shows separately that
K215 halts iff k215P halts and that k215P halts iff ZFC is inconsistent. The machines here
run the same program k215P, step for step, compiled for more symbols.

| Symbols | States | Instructions | Machine |
|-----:|-----:|-----:|---------|
| 2 | 215 | 430 | K215 (Glazer) |
| 5 | | 550 | (search only) |
| 6 | | 441 | (search only) |
| 7 | 152 | 417 | `machines/zfc_7sym_417.txt` |
| 8 | 152 | 411 | `machines/zfc_8sym_411.txt` |
| 9 | 152 | 409 | `machines/zfc_9sym_409.txt` |
| 10 | 143 | 402 | `machines/zfc_10sym_402.txt` |
| 11 | 143 | 402 | `machines/zfc_11sym_402.txt` |
| 12 | 136 | 402 | `machines/zfc_12sym_402.txt` |
| 12 | 117 | **376** | `machines/zfc_12sym_376.txt` (11 digits, the separator shares a digit's symbol) |
| 14 | 135 | 400 | `machines/zfc_14sym_400.txt` |
| 16 | 135 | 402 | `machines/zfc_16sym_402.txt` |

Instructions are defined transitions, the halting one included, so the best machine is BBi(375).
The counts are the best merge sets found, not proven minima. The 376 uses every compiler option
below (`configs/11.json`); the other rows are the first version's (13 symbols gave 398 there).
Beyond about 11 digits nothing more is gained: the nodes keep shrinking, but `scan` and `adv`
read every digit and grow by one each per symbol.

## How it works

* **The program** (`program.py`). `extract.py` reads k215P's table out of Glazer's
  `k215_literal_runtime_program.mm0`. Its entries are the leaves of a binary trie (each entry
  has a path), and every break, continue and failed-decnz target is an ancestor of its leaf.
  The program is rebuilt as a binary DAG with *relative* control leaves ("finish / restart the
  node k levels up"), hash-consed: 182 nodes, about Glazer's 179. Four decnz leaves finish a
  grandparent rather than their parent. Each is rewritten as `X = (Z, break -> A)`,
  `Z = (decnz r, break -> X)`. A prologue of `inc r0` slots (4, or 3 when the boot does one)
  precedes the program, which is wrapped as `L = (k215P, continue L)` so that restarting the
  main loop skips the prologue.
* **The machine** (`compiler.py`), in the style of `../pa_nsymbols/kary.py`. Tape:
  `0 [PC digits] 1^(39-depth) [S 1^r] [S 1^r] ...`. The PC holds one digit per DAG node on the
  path from the root, and a node is one state. Single-parent nodes are merged into their parent,
  giving D-ary nodes with up to D slots. `scan` runs left to the blank and enters the root, and
  the walk goes right through the nodes. A register op is a node's transition straight into
  a chain state. It writes the node's next slot value on its cell, so the return is `scan`
  itself; a failed decnz returns through `retfail`, which erases the cell and advances the
  parent. Break and continue are relative: they erase h cells, then `adv`, `scan`, or rewrite
  the holding node's cell (when the target is merged into it).
* **Slot values.** `adv` carries (the node is done) on the values 1 and T = D − 1, and
  otherwise writes v + 1. Two-slot nodes, the most common kind, therefore need no extra
  transition. Every node's slot values are chosen optimally for that rule (`assign`).
* **Registers** are created lazily, in the order of first use from the start (r0, the
  prologue's, then k215P's 8, 6, 7, 3, 1, 2, 5, 4). All 9 exist after 327 k215P steps.
* **Boot**: a searched 3-state machine (8 instructions) leaves 39 ones, then exits into
  register 1's inc chain (r0 = 1), so the prologue has 3 incs.

### Options used by the best machine (`compiler.py` flags, set in `configs/11.json`)

* **Virtual gotos** (`VIRT`). A control slot need not exist when the machine can reach its target
  anyway: after an inc or decnz the op's marker is the target slot's value (a restart or a jump
  inside the node), and after a child the child's inside value is the target slot's value − 1
  (`adv` then writes it). The dropped goto's k215P pc has no configuration of its own; in the
  proof it is related to the configuration one step before the root (`scan` on the blank, with
  the target's tape), so every k215P step still takes at least one machine step and the halting
  argument is unchanged. 240 of the 4751 pcs are virtual.
* **Shared erase states** (`UNICTL`): one erase chain per height; the target cell's value picks
  the action (restart, exit or jump).
* **Failed decnz** (`DECJUMP`): `retfail` reads the op's marker, so a failed decnz may also jump
  inside its node.
* **Separator symbol** (`sepval`): the separator is a digit's symbol (never a dec marker). Only
  `scan` reads both digits and separators, and it treats them alike, so it needs one transition
  fewer and the machine has 12 symbols.
* **Alternative value orders** (`alts`): when two nodes' values give one cell value two meanings
  (an erase action or a failed-decnz action), a node's slot values are re-chosen in another
  order. This unblocks merges; the merge set comes from an iterated local search.
* `adv` never reads the blank (the prologue's loop means the root never finishes).
* **Pre-written separators** (`presep`, not used yet): a boot that also writes all 9 separators
  and a dummy one makes lazy creation unnecessary and `carry1`, `dstart` never read the blank
  (4 transitions fewer). The generators and the proof support it (checked with a hand-written
  test boot), but no boot short enough has been found: with the merge set found for it
  (361 transitions without the boot), a 10-instruction boot writing `1^G S 1 1 S^9` would give
  BBi(370). Exhaustive searches found none of 8 instructions (2–4 states, 3–5 symbols) or of 9
  (3 states, 3 symbols).

## Tests

* `test_pcs.py D [trials]`: from every pc and random registers, the machine reaches the
  configuration of k215P's next state.
* `test_e2e.py D [steps]`: the real machine from the blank tape (boot, prologue, lazy
  registers) against k215P from its initial state.
* `build.py check`: the machine files are what the compiler writes.

All machines pass `test_pcs.py D 2` (virtual gotos are skipped: they have no configuration). The
best machine also passes `test_e2e.py 11 1e7` (11,243 k215P steps).

## Proof

**Checked in Metamath Zero** (`mm0/`, see `mm0/PROOF.md`), for the 12-symbol machine `zfc_12sym_376.txt`:

```
theorem kz_halts_iff_program: $ kzHalts <-> k215PInitialHalts $;

theorem kz_halts_iff_ZFC_inconsistent
  (hK215: $ k215LiteralHalts <-> zfcInconsistent $)
  (hProgram: $ k215PNativeLaw -> (k215LiteralHalts <-> k215PInitialHalts) $)
  (hNative: $ k215PNativeLaw $):
  $ kzHalts <-> zfcInconsistent $;
```

`kzHalts` is the machine's transition table run from the blank tape (`mm0/kz_tm.mm0`). The first
theorem has no hypotheses: the machine halts iff Glazer's program k215P halts. The three
hypotheses of the second are, verbatim, theorems checked by Glazer's receipt (his main theorem and
the two that connect K215 to k215P), so together the two checks give: the machine halts iff ZFC
is inconsistent. The definitions are Glazer's unmodified `.mm0` files (all 440 used have the
receipt's hashes) and the joined spec has only peano's 26 axioms. `mm0/check.sh` compiles and
checks the whole proof in about 2 minutes (36 GB), and checks that mm0-c rejects a false
conclusion.
