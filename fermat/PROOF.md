# The proof, in plain words

This is a guided tour of the Lean proof that the Turing machine `fermat.txt` (the
127-state design) and its merged version `machines/fermat_90.txt` halt if and only if
Fermat's Last Theorem is false. The proof is about 1,260 hand-written lines in
`../lean/TinyCryptids/Fermat/` (plus the generated `Machine.lean` and `M90.lean`); each step
below names the lemma that carries it.

## What is proved

```lean
theorem TM.Fermat.halts_iff :
    Halts delta start ↔ ∃ E x y z : Nat, 3 ≤ E ∧ 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧ x ^ E + y ^ E = z ^ E

theorem TM.Fermat.M90.halts_iff :
    Halts delta2 start2 ↔ ∃ E x y z : Nat, 3 ≤ E ∧ 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧ x ^ E + y ^ E = z ^ E
```

* `delta` is the transition table of the 127-state design, `start` is its state `seed0` on a
  blank tape (`../lean/TinyCryptids/Fermat/Machine.lean`, generated from `fermat.txt` by
  `gen_lean.py`). `delta2`/`start2` in `M90.lean` are the merged 90-state table, generated
  from `machines/fermat_90.txt` by `gen_reduced_lean.py`.
* `Halts δ c` means: started in configuration `c`, the machine reaches a configuration with
  no transition (`../lean/TinyCryptids/Core/Basic.lean`, the model shared by every machine in the
  repository: 2 symbols, a two-way infinite tape stored as two streams `Nat → Bool`, the head
  always moves). An undefined entry in the table counts as halting, so the theorem also says
  that the run never hits an undefined entry unless a counterexample exists.
* The right-hand side is the negation of Fermat's Last Theorem, written with `^` and `+` on
  `Nat` from Lean's core library. No custom definition enters the statement.

The design halts by moving into an extra state `halt` that has no transitions
(`zX2` on 0 goes to `halt`); `halt` is not counted among the 127 states (in the
bbchallenge text format it is the halting transition).

To trust the result you need to trust the Lean kernel, the statement above and the
transcription of the machine listings into `Machine.lean` and `M90.lean`. Nothing else: the
theorems depend only on `propext`, `Classical.choice` and `Quot.sound` (`../lean/Check.lean`
prints this). The proof does not use Wiles' theorem.

The proof has five parts: tape vocabulary and the shared parser lemmas (`Core/`, `Blk`,
`Tac`), the power computation (`Copy`, `Pow`), the rest of one tuple check (`NextBase`,
`Compare`, `Tuple`), the enumeration (`Enum`, `Nexcom`), and the main theorem with its
transfer to the merged machine (`Main`, `M90`).

## The idea

The machine enumerates all tuples `(E, x, y, z)` with `E ≥ 3` and `x, y, z ≥ 1` and checks
each one:

    t := (4, 1, 1, 1)
    loop:
      t := nxt(t)                         (next tuple in NEXCOM order)
      A := 1 + x^E + y^E;  R := z^E       (unary, by repeated copying)
      if A = R + 1: HALT                  (otherwise clear and loop)

Numbers are blocks of 1s separated by `00`. Powers are computed by a nested loop whose
counters are single 0s ("holes") inside blocks: a hole in the exponent block counts rounds,
a hole in the base block counts copies (next to a second hole, the marker, that says which
block is the base), a hole in the `R` block counts cells being copied, and the single 0 before
R is the hole by which every trip to R finds it.
The comparison erases one cell from each side alternately and halts iff R runs out with
exactly one cell of A left. The search order `nxt` steps through the compositions of each total in
NEXCOM order (Nijenhuis–Wilf), one total after another; a separate, purely arithmetic
argument shows it visits every tuple. Both directions then follow the usual pattern: no
counterexample means the machine strictly moves from one checkpoint to the next forever;
a counterexample is reached after finitely many checkpoints and the check of it halts.

## Part 1: tape vocabulary (`Core/`, `Blk.lean`, `Tac.lean`)

**Tapes.** A configuration `⟨q, L, R⟩` has the state, the tape left of the head (nearest
cell first) and the tape from the head on. `ones n s` is `n` cells of 1 followed by `s`,
`zeros n s` the same with 0s, `app w s` puts a finite list `w` in front of `s`, and
`cfgL q s R` is the configuration whose head reads the first cell of `s`, used for leftward
moves (`Core/Basic.lean`, `Core/Lemmas.lean`). `Reach`/`Reach1` are reachability in any /
at least one step (`Core/Sys.lean`); in the Fermat files they are abbreviated `Rch`/`Rch1`.

**Single steps and scans.** `stepR`, `stepL`, `scanR`, `scanL` (and the 0-versions `scanR0`,
`scanL0`, the erasers `eraseR`, `eraseL`) are one step and a run over `n` equal cells.
`Tac.lean` wraps them as tactics `gR`, `gL`, `sRn`, `zRn`, `eRn`, … that check each
transition against `delta` by `rfl`. Most routine lemmas are proved by a literal list of
these steps.

**Clean segments and parsers.** A list is `Clean` if every run of 0s in it has length
exactly two and is followed by a 1 — i.e. it consists of block cells and `00` separators
but no hole. A *right parser* is a pair of states `p1, p2` with transitions
`p1: 1 → R p1, 0 → R p2` and `p2: 0 → R p1` (`ParserR`; `ParserL` mirrored).

**Lemma 1 (parsers find the next hole, `ParserR.find`, `ParserL.find`).** A parser crosses
any clean segment and stops on the first 1 after the first isolated 0. *Proof:* induction on
`Clean` (`ParserR.cross`): a 1 is skipped by `p1`; a separator `001` is read as `p1→p2→p1`.
Only then a single 0 followed by 1 sends `p2` on to its "found" action. A hole next to a
separator is a run of three 0s, which the parser (counting 0s modulo 2) also reads as a hole:
`ParserL.find3` (`Pow.lean`).

Fourteen parsers in the design (`MC`, `NB`, `MM`, `LE`, `LF`, `LG`, `MB`, `MN`, `MQ`, `CP`,
`HE`, `HS`, `HU`, `HL`; each name is the prefix of two states, e.g. `MC1`/`MC2`) are
instances, each established by `⟨rfl, rfl, rfl⟩` (`PMC`, `PNB`, …). `Blk l` says `l` is a list of nonempty blocks separated by `00`; `Blk.clean_append`,
`Blk.join`, `Blk.reverse` let the proofs feed whole stretches of the tape to a parser.

## The tape

At each checkpoint the tape is (`chk E a b c`, `Tuple.lean`; `tailL` is the part after B1):

    B1 = 1 0 1^E    00  B2 = 1^(a+2)  00  B3 = 1^(b+2)  00  B4 = 1^(c+2)  00  M = 1  00 0  R = 1

with the head on the 0 of B1 in state `en1`, everything else blank. So:

* B1 holds the exponent `E` as a block of `E + 2` cells with a **permanent hole**: the
  exponent cursor, on cell 1 (the anchor) between powers, on cells `1 .. E + 1` during one.
* B2, B3, B4 hold `x = a`, `y = b`, `z = c` as blocks of `value + 2` cells.
* `M` is a one-cell block. A, between M's separator and a single 0, is empty (it gets `α`
  cells, meaning `α − 1`). R, after that single 0, is `r` cells for the value `r`; the single
  0 is R's hole (with A empty it is the third 0 of a run of three, which parsers also read as
  a hole).

During a power computation `Q` (scratch, `q` cells meaning `q`) follows R after another single
0 (`rgt X r q` in `Pow.lean`: `00 X 0 R 0 Q`, where X ends with A), and the current base block
carries the **marker** on its cell 1 and, during a round, a cursor on cells `3 .. β + 1`
(`bA2C`, `BL`). The cursors of B1 and of the base may sit on the last cell of their block, next
to the separator; every other hole has 1s on both sides, so every stretch between the head and
a target hole is clean and Lemma 1 (or `find3`) applies.

## Part 2: powers (`Copy.lean`, `Pow.lean`)

**Lemma 2 (copy, `copy_one`, `copy_last`, `copy_all`, `copy_full`).** The `MC` parser stops at
R's hole and punches a copy cursor on R's first cell (`mc_cross`). With the cursor on R's
cell `c` (`cpyS c r q`, state `c1` right of it), one pass (`c1`–`c4`, `c5`) appends one cell to
Q and moves the cursor to `c + 1`; it may reach R's last cell, since only the copy loop's own
scans ever look for it. When `c5` reads the 0 after R, the copy is done: `c6` runs back over
R to R's hole and enters the `NB` parser (`cpyDone`). So a full copy adds `r` cells to Q and
leaves R unchanged.

**Lemma 3 (base loop, `base_adv`, `base_loop`).** The base block has `β + 2` cells: cell 0,
the marker on cell 1, and the cursor cells `1 .. β` (cells `2 .. β + 1`). In state `bA2` on
cursor cell `j + 1` (`bA2C`): if `j < β` the machine punches a hole there, the `MC` parser
finds R and a full copy runs, and the `NB` parser returns (`nb_back`, or `nb_back0` with
`find3` when the hole is on the last cell); `bAt` fills the hole, and the machine is in `bA2`
one cell further: `q := q + r`. Iterated from `j = 1` to `j = β`: `q := q + r(β − 1)`.

**Lemma 4 (end of a round, `round_end`).** In `bA2` on the separator after the base block
(`j = β`): the `MM` parser, entered on that separator, finds R; `m1`–`m3` fill the 0 between R
and Q and erase Q's last cell, so `R := r + q`; `m4` runs back over R to its hole, and two
left parsers (`LF` skips the marker, `LG` finds the exponent hole, `lg_find`) bring the head to
the exponent cursor (`eAtC`). `PreOK` describes what may lie between B1 and the base block
(just `00`, or more blocks), so the same lemma serves all three bases. Together with Lemma 3:
one round turns `R = r` into `R = rβ` (`one_round`).

**Lemma 5 (exponent loop, `e_adv`, `e_done`, `pow_all`, `pow_full`).** At the exponent cursor
`e` (state `eAt`): if `e ≤ E` it moves to `e + 1` and the `MB` parser finds the marker and
lands on cursor cell 1, so the next round starts in `bA2` with no base hole (`e_adv`); if
`e = E + 1` (the last cell) the cursor is reset to cell 1 and the `MN` parser goes to the
marker in state `nb0` (`nbC`, `e_done`). By induction on `E + 1 − e`, starting from `R = 1`
and the anchor `e = 1`, the machine reaches `nb0` with `R = β^E` (`pow_full`; `Q` is empty
again).

| routine | states | effect |
|---|---|---|
| copy | `MC`, `c1`–`c6` | `Q += r` |
| base step | `bAt`, `bA2` | base cursor `+1`, then copy |
| round end | `MM`, `m1`–`m4`, `LF`, `LG` | `R := R + Q`, back to exponent cursor |
| exponent step | `eAt`, `eA2`, `MB`, `eD1`–`eD3`, `MN` | next round, or done |

## Part 3: one tuple (`NextBase.lean`, `Compare.lean`, `Tuple.lean`)

**Lemma 6 (next base, `next_base`).** From `nb0` with `R = r`: fill the marker, step to the
next block and put the marker into its cell 1 (`nb4` sees a 1 there, so it is not `M`); then
the `MQ` parser finds R's hole, `q0` fills it (A and R are one block), `q1` writes a 1 past
R's end and `q2` erases the cell before it: A grows by exactly `r` cells, and a fresh `R = 1`
follows after a single 0. `LF` skips the new marker and `LG` finds the anchor: the next power
starts (`eAtC` with the new base). So after base `x` the next power starts on base `y` with
`A = 1 + x^E`, and after `y` on `z` with `A = 1 + x^E + y^E`.

**Lemma 7 (setup, `setup`).** From state `su0` on the anchor (`suC E a b c`): `su0` steps
right into the next-base routine as if the anchor were a marker (it is left in place): the
marker goes on B2's cell 1, and the add-into-A part turns the empty A and `R = 1` into `A = 1`
and a fresh `R = 1`; the `MQ` parser finds R's hole as a run of three 0s (`ParserR.find3`).
Then `LF`, `LG`: the starting configuration of `pow_full` for base `x`.

**Lemma 8 (compare, `compare_entry`, `zz_step`, `zz`).** After `z^E`, `nb4` reads the 0 after
the one-cell block M and enters the `CP` parser instead, which stops at R's hole and starts the
zig-zag there, with A of `x = 1 + a^E + b^E` cells and R of `y = c^E` cells. The zig-zag
`Z LA i j x y` (states `zH1`, `zA1`, `zG1`, `zZ1`) erases the last cell of A and then the first
cell of R, each time looking at the next cell to see whether the block is now empty; the gap
between them only grows (`zz_step`). By induction on `x`:

| A and R left | what the machine does | lemma |
|---|---|---|
| both ≥ 2 | erase one cell of each, repeat | `zz_step` |
| A = 1 | A runs out first (`x ≤ y`): `zK1`, `cr1` erase R, reach the clearing point `clrC` | `zz_A` |
| A ≥ 2, R = 1 | R runs out: `zX1` erases one more cell of A; `zX2` reads 0 iff A is now empty (`x = 2`): **halt**; else `zX3` erases the rest of A, reach `clrC` | `zz_R` |

So the zig-zag halts iff `x = y + 1`. `HaltAt c` means `c` reaches the state `halt`
(`Compare.lean`); `HaltAt.halts` turns it into `Halts`.

**Lemma 9 (clear and return, `clear_home`).** From `clrC` (head right of M, blank to the
right) `cr4`–`cr7` write `00 0 1` (A empty, `R = 1`), and the `HE` parser, entered on R's
hole, returns to the anchor in state `en1`: the checkpoint `chk E a b c`, with the same tuple.

**Lemma 10 (one tuple, `tuple_check`).** For `E, a, b, c ≥ 1`, from `suC E a b c`:
if `a^E + b^E = c^E` the machine reaches `halt`; otherwise it reaches `chk E a b c`.
*Proof:* chain Lemmas 7, 5, 6, 5, 6, 5, 8 (three powers, positive by `pow_pos'`), then
Lemma 8 with `1 + a^E + b^E = c^E + 1 ↔ a^E + b^E = c^E`, then Lemma 9.

## Part 4: the enumeration (`Enum.lean`, `Nexcom.lean`)

**The order (`nxt`, `Nexcom.lean`).** On tuples `(E, a, b, c)`:

| case | `nxt (E, a, b, c)` | in blocks |
|---|---|---|
| `E ≥ 4` | `(E − 1, a + 1, b, c)` | one unit from B1 to B2 |
| `E = 3`, `a ≥ 2` | `(a + 1, 1, b + 1, c)` | one unit from B2 to B3, the rest of B2's excess to B1 |
| `E = 3`, `a = 1`, `b ≥ 2` | `(b + 1, 1, 1, c + 1)` | one unit from B3 to B4, the rest to B1 |
| `E = 3`, `a = b = 1`, `c ≥ 2` | `(c + 3, 1, 1, 1)` | next total: B1 grows by one, B4's excess to B1 |
| `(3, 1, 1, 1)` | `(4, 1, 1, 1)` | (never used by the machine) |

In terms of the nonnegative parts `(E − 3, a − 1, b − 1, c − 1)` this is NEXCOM: find the
first nonzero part `h`; move one unit to part `h + 1` and the remaining units of part `h` to
part 1; after the last composition `(0, 0, 0, n)` start the first one of total `n + 1`.

**Lemma 11 (validity, `nxt_valid`, `nxt_ne_seed`).** `nxt` keeps `Valid` (`E ≥ 3`, `a, b, c ≥ 1`)
and never returns `seedT = (3, 1, 1, 1)`.

**Lemma 12 (coverage, `reached`).** Every valid tuple is `itr k seedT` for some `k`.
*Proof*, by well-founded recursion on `(E + a + b + c, c, b, a)` in lexicographic order, by
naming a valid predecessor: if `a ≥ 2`, it is `(E + 1, a − 1, b, c)` (same total, smaller
`a`); else if `b ≥ 2`, `(3, E − 1, b − 1, c)` (smaller `b`); else if `c ≥ 2`,
`(3, 1, E − 1, c − 1)` (smaller `c`); else if `E ≥ 5`, `(3, 1, 1, E − 3)` (total one less);
`(4, 1, 1, 1)` is `itr 1` and `(3, 1, 1, 1)` is `itr 0`. In each case one checks that
`nxt` of the predecessor is the tuple.

**Lemma 13 (the machine follows `nxt`, `enum_step`).** For a valid tuple `t ≠ seedT`, from the
checkpoint `chk t` the machine reaches `suC (nxt t)` (state `su0` on the anchor). The first step (`chk_step`) leaves
`en1`; `en2`–`en5` read B1 and branch:

| case | path | lemma |
|---|---|---|
| `E ≥ 4` | `e6`–`e9`: the separator after B1 moves one cell left; `HS` back to the cursor | `enum_E` |
| `E = 3`, `a = 2` | `f1`–`f5` find B2 non-minimal; `k1`–`k4`, `n2`–`n9` move the separator after B2 left; B2 is now minimal, `HS` | `enum_B2a` |
| `E = 3`, `a ≥ 3` | as above, then the transfer loop moves `a − 2` units from B2 to B1 | `enum_B2b` |
| `E = 3`, `a = 1`, `b = 2` / `b ≥ 3` | the same one block further right | `enum_B3a`, `enum_B3b` |
| `E = 3`, `a = b = 1`, `c ≥ 2` (B4 non-minimal) | `k4` sees the marker; `HL` to the cursor, `g1`–`g3` grow B1 at its free left end, then the transfer loop moves `c − 1` units from B4 to B1 | `enum_last` |

**Lemma 14 (transfer loop, `u_unit_more`, `u_unit_last`, `u_loop`).** One unit from block B_h
to B1, with `k` minimal blocks `111` in between (`UE`, `minc`): from `uh` on the exponent
cursor, B1 gains a cell at its right end, each minimal block in between shifts one cell right
(`uchain`), and B_h loses its first cell. If B_h is still longer than minimal, `HU` returns to
`uh` and the loop repeats; if it is now minimal (3 cells), `HS` returns in state `su0` (`SU`).
By induction, a block of length `m + 4` gives all `m + 1` surplus units to B1.

## Part 5: the main theorem (`Main.lean`)

**Lemma 15 (seed, `seed_reach`).** From the blank tape, `seed0`–`seed23` write
`1 0 1111 00 111 00 111 00 111 00 1` and end in `cr4` right of M, which is the clearing point
of Lemma 9: the machine reaches the checkpoint `chkT (4, 1, 1, 1)` (`seedT4 = nxt seedT`). The tuple
`(4, 1, 1, 1)` itself is never checked, which is harmless since `1 + 1 ≠ 1`.

**Lemma 16 (one cycle, `cycle`).** For valid `t ≠ seedT`: if `Sol (nxt t)` then `chkT t`
reaches `halt`; otherwise `chkT t` strictly reaches `chkT (nxt t)`. *Proof:* Lemma 13 then
Lemma 10 for `nxt t`; the step out of `en1` makes it strict.

**No counterexample ⇒ no halt.** The family `{chkT t : t valid, t ≠ seedT}` is closed under
strict progress by Lemmas 11 and 16. `not_halts_of_progress` (`Core/Sys.lean`) says no member
halts; the start reaches a member (Lemma 15), and halting is inherited along a deterministic
run (`halts_det`), so the start does not halt.

**Counterexample ⇒ halt (`haltAt_of_sol`, `halts_if_sol`).** Lemma 12 gives `k` with
`itr k seedT` the counterexample; `k ≥ 2` because neither `(3, 1, 1, 1)` nor `(4, 1, 1, 1)`
is a solution. `halts_if_sol` (induction on `k`, applying Lemma 16 until the solution is the
next tuple) shows `chkT seedT4` reaches `halt`, and Lemma 15 prepends the seed.

This is `TM.Fermat.halts_iff`.

## Part 6: the merged machine (`M90.lean`)

`M90` is obtained from the design by `minimize.py`, which merges states that never disagree
on a transition the design defines. `M90.lean`, generated by `gen_reduced_lean.py`, gives the
merged table `delta2` (on `St2`, 90 states plus `halt2`), a map `phi : St → St2` with
`phi seed0 = seed0` and `phi halt = halt2`, and `compat`: for every state and symbol,
`Compat phi (delta q b) (delta2 (phi q) b)` — wherever `delta` is defined, `delta2` does the
same thing on the image state (one case per transition, closed by `rfl`).

**Lemma 17 (`sim_run`, `halts_iff_of_sim`, `Core/Basic.lean`).** Under `compat`, every run of
the design maps step by step to a run of the merged machine. So if the design never halts,
neither does the merged machine; and if the design reaches a configuration whose image has
no transition, the merged machine halts. The second condition is supplied by
`haltAt_of_sol`: the design reaches state `halt`, and `delta2 halt2 _ = none`. Hence
`TM.Fermat.M90.halts_iff`.

## What the proof does not cover

* It says nothing about whether a counterexample exists. By Wiles' theorem none does, so
  the machines in fact run forever; the Lean proof shows only the equivalence and does not
  use or reprove Wiles.
* The correspondence between the text listings (`fermat.txt`, `machines/fermat_90.txt`) and
  the Lean tables is by the generators `gen_lean.py`, `gen_reduced_lean.py`
  (`../tools/leangen.py`), not by a Lean proof. The bbchallenge standard-text line, the
  annotated listings (`annotate.py`) and the Python tests (`test_*.py`, `same_run.py`) are
  outside the proof.
* The theorems are about runs from the blank tape only (`start`, `start2`).
