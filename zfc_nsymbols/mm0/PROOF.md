# The Metamath Zero proof

`kz_final.mm0` states, about the 13-symbol machine `../machines/zfc_13sym_398.txt` (its transition
table is `kz_tm.mm0`, generated from the machine file by `gen_spec.py`):

```
theorem kz_halts_iff_program: $ kzHalts <-> k215PInitialHalts $;

theorem kz_halts_iff_ZFC_inconsistent
  (hK215: $ k215LiteralHalts <-> zfcInconsistent $)
  (hProgram: $ k215PNativeLaw -> (k215LiteralHalts <-> k215PInitialHalts) $)
  (hNative: $ k215PNativeLaw $):
  $ kzHalts <-> zfcInconsistent $;
```

* `kzHalts` (`kz_tm.mm0`): the machine, run from the blank tape (`kzState 0 0 0`), reaches the
  halt label. Tapes are numbers in base 13 (head cell lowest). Undefined transitions go to the halt
  label.
* `k215PInitialHalts` (Glazer's `k215_literal_runtime_program.mm0`): his register program k215P,
  run from `k215PInitial` (pc 0, r0 = 4), reaches an entry with tag 4.
* The three hypotheses are, verbatim, theorems of
  [elliotglazer/k215-pa](https://github.com/elliotglazer/k215-pa), checked by its receipt
  (`receipt/thm1`):
  * `K215_halts_iff_ZFC_inconsistent_final` (`k215_final_thm1.mm0`): `k215LiteralHalts <-> zfcInconsistent`;
  * `k215LiteralHalts_iff_program_given_native_law` (`k215_literal_runtime_conditional.mm0`);
  * `k215PActualNativeLaw` (`k215_literal_runtime_native_assembled_full.mm0`).

  So the two checks together give "the machine halts iff ZFC is inconsistent". Discharging the
  hypotheses inside one check would mean compiling Glazer's whole development (459 GB peak in his
  run). Here only `kz_halts_iff_program` is new, and it is checked with no hypotheses.

The definitions behind the statement are `kz_tm.mm0` and Glazer's `.mm0` files, unmodified: all
440 of his files in the build have the sha256 his receipt lists. The joined spec contains only the
26 axioms of `peano.mm0`.

## Checking

```
git clone https://github.com/elliotglazer/k215-pa      # commit 992b76d
(cd k215-pa && sh scripts/fetch_large_inputs.sh)        # release inputs (1.5 GB)
# tools: mm0-rs and mm0-c from github.com/digama0/mm0 at 0d414c0b, mm0-c patched with
# k215-pa/checker/mm0-c-capacity.patch (mm0-rs needs a Rust toolchain with edition 2024)
MM0RS=.../mm0-rs MM0C=.../mm0-c sh check.sh            # with k215-pa/ in this directory
```

`check.sh` flattens `kz_final.mm1` (post-order imports, as k215-pa's `check.py` does: compiling
Glazer's modules one by one fails on missing equality theorems). It compiles the result with mm0-rs
and writes the spec in the same module order (`join_flat.py`: `peano.mm0`, then every module's
`.mm0` without its imports). It checks with mm0-c, then checks that mm0-c rejects the same binary
when the last theorem concludes `F.`. On a 24-core machine with 49 GB it takes 2 minutes, 36 GB
peak. Last run: spec `kz_final.mm0` sha256 `d4bea036…`, joined spec `2e002fb3…` (`out/`, not
committed; the binary's hash depends on the checkout's paths).

## How the proof goes

The machine runs k215P step for step (`../README.md`). For every k215P state s it has a
configuration `kzConf`: state = the root node, head on PC cell 0, left of it a blank, then the PC
digits, the gap `1^(39 − depth)`, and the register file `S 1^r` × 9. Trailing zero digits are
folded into the gap, so each configuration has one canonical form.

1. **Library** (`kz_lib.mm1`, by hand). Steps `kzSR`/`kzSL` from an action lemma; `kzRunAdd`; runs
   `kzRep 1 n`; the right and left loops `kzLoopR`, `kzLoopL`, `kzLoopLS` (induction with the other
   tape generalised); `kzReach` and `kzReachP` (≥ 1 step). The inc carry treats the pending
   symbol as the top of a virtual left tape (`kzPend`), so crossing a register block needs no case
   split on whether a register is empty (`kzPend_step1/S`, `kzPend_loop`, `kzPend_block`,
   `kzPend_end`). Also the dec shift (`kzDec_block`, `kzDec_end`) and a chain crossing a block
   (`kzChain`).
2. **Transitions** (`gen_act.py` → `kz_act.mm1`): `kzAction q b = (w, d, t)` for each of the 398
   transitions, and the digit and state bounds.
3. **Register macros** (`gen_sim.py` → `kz_mac.mm1`). Each takes the op from its chain state across
   the gap and the file, for inc, decnz > 0 and decnz = 0, for every register and every file size
   0–9 (lazy creation included). Each is generic in the left tape, the gap and the register values.
4. **Steps** (`gen_pcs.py` → `kz_p000…013.mm1`). For each (pc, canonical tape) and each branch, the
   configuration reaches (`kzReachP`) the next state's configuration. The generator executes the
   machine symbolically and emits the proof: walk, leaf transition, macro, scan back, and follow-on
   cycles for prologue and rewritten-decnz slots. There are 6600 lemmas: the prologue and the first
   328 k215P steps with a partial register file, then every state reachable over both branches of
   every decnz with all 9 registers (4912 states).
5. **Relation** (`gen_rel.py` → `kz_rel.mm1`). `kzRel s c` is a balanced disjunction of
   `kzD<i> s c`: s has state i's pc and c is state i's configuration with s's registers.
   `gen_glue.py` → `kz_s*.mm1` proves `kzD<i> s c -> kzGood s c` for each state, from Glazer's
   lookup lemmas (`k215PLookupNorm…`), his `k215PAtCI/CD/CB/CC` and vector lemmas, and step 4.
   `kzGood` says: c is not halted; if s has halted, the machine halts from c; otherwise c reaches,
   in at least one step, a configuration related to `k215PStep s`. `kzSimAll` combines them over
   the tree.
6. **Halting** (`kz_halt.mm1`, by hand). Forward, by induction along k215P's run: c reaches a
   configuration related to `k215PIter n s`. Backward: in at least n steps, so a halt at time T
   would make a configuration related to a running state halted. Together these give
   `kzEquiv: kzRel s c -> (k215PHaltsFrom s <-> kzHaltsFrom c)`.
7. **Start** (`gen_boot.py` → `kz_boot.mm1`, `gen_prefix.py` → `kz_prefix.mm1`). The boot's 3180
   steps; the prologue and the 328 prefix steps chained with concrete registers;
   `k215PIter 328 k215PInitial` computed; `kzRel` at that state. `kz_final.mm1` shifts halting
   along both runs and concludes.

Regenerate (in order): `gen_spec.py 11`, `gen_act.py 11`, `gen_sim.py 11 0 1 2 3 4 5 6 7 8 9`,
`gen_pcs.py 11`, `gen_boot.py 11`, `gen_rel.py 11`, `gen_glue.py 11`, `gen_prefix.py 11`,
`gen_final.py` (the `lookups.json` map of Glazer's lookup lemmas is written by the snippet in
`gen_lookups.py`).
