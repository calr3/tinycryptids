# A Beeping Booping Turing machine for Pillai's conjecture

**Current best: `machines/pillai_91.txt`, a 91-state, 2-symbol Beeping Booping Turing machine.**
Started on a blank tape, it never halts. Its output is the sequence of beep counts between
consecutive boops. **Some value occurs infinitely often in that output iff Pillai's conjecture
is false.**

[Pillai's conjecture](https://en.wikipedia.org/wiki/Pillai%27s_conjecture) says that for every
`k ≥ 1` the equation `a^x − b^y = k` has only finitely many solutions with `a, b, x, y ≥ 2`.
That is Π₃ (for every `k` there is a bound `N` such that every solution is below `N`), so "Pillai's
conjecture fails" is Σ₃, the class of Bram Cohen's
[Beeping Booping Busy Beavers](https://bramcohen.com/p/beeping-booping-busy-beavers), like
`../abc/` (the abc conjecture implies Pillai's conjecture). For `k = 1` the statement is
Catalan's conjecture, proved by Mihăilescu (`3^2 − 2^3` is the only solution); for every other
`k` it is open.

**The beep is the transition of state `83` reading 1; the boop is `83` reading 0**
(`zX3` in the design and the Lean files: one state, its two transitions).

## What is proved

Lean (`../lean/TinyCryptids/Pillai/`, core Lean 4.15.0, no Mathlib):

    theorem TM.Pillai.M91.repeats_iff :
        RepeatsForever delta2 St2.zX3 true St2.zX3 false start2 ↔ ¬ PillaiConjecture
    theorem TM.Pillai.M91.never_halts : ¬ Halts delta2 start2

with (`../lean/TinyCryptids/Core/BeepBoop.lean`, `../lean/TinyCryptids/Defs.lean`)

    def RepeatsForever δ qb bb qo bo c := ∃ v, ∀ N, ∃ i j, N ≤ i ∧ i < j ∧
        BeepsAt δ qo bo c i ∧ BeepsAt δ qo bo c j ∧ (∀ k, i < k → k < j → ¬ BeepsAt δ qo bo c k) ∧
        beepsBetween δ qb bb c i j = v
    def PillaiConjecture := ∀ k, 1 ≤ k → ∃ N, ∀ a b x y, 2 ≤ a → 2 ≤ b → 2 ≤ x → 2 ≤ y →
        a ^ x = b ^ y + k → a + b + x + y < N

A bound on `a + b + x + y` stands in for "finitely many". The 132-state design has the same two
theorems (`TM.Pillai.repeats_iff`, `TM.Pillai.never_halts`). All of them depend only on
`propext`, `Classical.choice` and `Quot.sound` (`../lean/Check.lean`). `PROOF.md` walks through
the proof, and `RECORDS.md` lists the machines.

## How it works

For every tuple `(x, y, a, b)` with `x, y, a, b ≥ 2`, in NEXCOM order of the block lengths (which
reaches every tuple, once):

* `A := 1 + a^x`, `R := b^y` (Fermat's power routine, `../fermat/`, with two exponent blocks).
* **Compare.** Erase A's last cell and R's first cell in turn. If A runs out first or they run out
  together (`a^x ≤ b^y`), there is no event. If R runs out first, A has `1 + a^x − b^y` cells left:
  the next one is erased, and if more are left (`a^x > b^y`), the next one is erased too and each
  further one with a **beep**: `a^x − b^y − 1` beeps, then the **boop**.

So the output is the sequence of `a^x − b^y − 1` over the tuples with `a^x > b^y`, in order, and
a value `v` repeats forever iff `a^x − b^y = v + 1` has infinitely many solutions. Tuples with
`a^x = b^y` (infinitely many, e.g. `a = b`, `x = y`) give no event, so 0 is not a value that
repeats for free. No pigeonhole argument is needed, unlike `../abc/`.

The first tuples are `(x, y, a, b) = (2, 3, 2, 2)` (no event), `(2, 2, 3, 2)` (`9 − 4 = 5`: 4
beeps and a boop, at step 1,885), `(4, 2, 2, 2)` (`16 − 4`: 11 beeps), …; 10⁹ steps give 151
boops.

### Tape

Unary blocks of 1s, separated by `00`; a single 0 inside a block is a **hole** (a cursor):

    x 00 y 00 a 00 b 00 M 00 A 0 R 0 Q

* `x`, `y` (exponents): `E + 2` cells; the exponent cursor runs over cells `1 … E + 1` (on the
  last one it sits next to the separator, a run of three 0s that the parsers still read as a
  hole). Between tuples `x` holds the anchor on cell 1. When x's power is done the cursor moves
  on to cell 1 of `y`, and when y's is done, to cell 1 of `a`.
* `a`, `b` (bases): `v + 2` cells; the base being powered has a marker hole on cell 1 and,
  during a round, a cursor on cells `3 … v + 1`. So every block of the tuple has at least 4 cells.
* `M`: one cell. `A`: `1 + a^x` after the first power, empty between tuples. `R`: the running
  power, after a single 0 that is its hole. `Q`: scratch for copies of `R`.

### Routines

* **Enumeration**: the NEXCOM step (four blocks of minimum length 4).
* **Setup**: from the anchor over `x` and `y`, then Fermat's next-base step puts the marker on `a`
  and adds `R = 1` into the empty `A` (hence `A = 1 + a^x`).
* **Powers**: Fermat's: `E` rounds of `R := R · β` (copy `R` onto `Q` `β − 1` times, merge), the
  marker moves to the next base and `R` is added into `A`.
* **Compare and clear**: Fermat's zig-zag, with its halt replaced by "no event" and its last
  clear by the beep loop (`zX3`). Then `A` and `R` are restored, the cursor left on `a`'s cell 1
  is filled, and the machine goes home (`H1 … H5`, the `Home` routine of `Core/Lemmas.lean`) and puts the anchor back.
* **Seed**: writes `x = 3` with a hole on cell 1, which counts the blocks still to write: each round
  moves it one cell right and appends `00 1111` (`y = a = b = 2`); when it was on x's last cell,
  `M` is appended and `A`, `R` follow. The hole is then filled by the routine that ends every
  tuple. This loop (20 states) replaced a 26-cell straight-line seed and saved 6 merged states.

The design (`pillai.txt`, from `build.py`) has 132 states; `../tools/minimize_clique.py pillai.txt
out 3600 cadical195 zX3:1,zX3:0` finds 91 and proves 89 and 90 unsatisfiable (the clique bound is
89), so 91 is optimal for this design. The beep and the boop stay exclusive: no other state joins
`zX3`'s class.

## Standard text (bbchallenge format, 91 states)

    1R1,1R45_0R2,0R21_1R3,0R43_1R4,0L61_1L5,1R0_0L6,1L5_0L5,1R7_0R8,1R28_0R14,0L9_1R10,1L32_0R11,0R38_0R12,1R11_0R13,1R11_1R2,1R11_0R15,1R14_0R16,1R14_1R66,1R14_0L86,1R18_1L87,1R19_0R25,1R20_0L1,1R20_0R22,1R31_1L23,1R72_0L24,1L23_0L23,1R27_0R26,1R33_1L17,1R24_0R46,1R7_0R25,1R29_0R30,1R29_0R21,1R30_0L37,1L9_1L33,1L34_0L8,0R69_0R73,1L35_1R38,1L36_0L24,1L39_0L31,1L37_1L41,1R38_0L40,1L39_0L39,1R41_0R42,0L62_1R1,1R42_0L58,1R44_1R47,1R4_0L23,1L39_0R29,1R46_0R51,0R48_0R49,1R48_0R48,0R52_0R51,1R50_0R50,1R59_0R53,1R52_1L54,1R53_0L55,1L54_1R56,1L55_0L57,0R52_0L58,1L57_0L43,1L58_1R60,1R59_0L3,1R60_0L62,1L61_0L63,1L62_0L62,1L64_0L65,1L64_0L64,1R16_0R19,0R67_0R68,1R67_0R67,1R47_0R70,1R69_0R69,1L71_1R30,0R17_0R75,0R73_0R34,1R73_0R75,1R74_0R74,1L76_0L76,0L77_0R80,1R78_0R78,0R79_0L81,1L76_0R80,0R84_0L81,0L82_0L85,0L83_0L85,0L83_0L85,0R84_0L85,1R66_0L17,1L86_0L88,1L87_0L89,1L87_0R90,1L87_0R90,1R71

States are listed in order (`_` between states), and the first is the start state. **Beep:
`83` reading 1. Boop: `83` reading 0.**

## Files and checks

| File | Contents |
|------|----------|
| `build.py` | The generator of the design (variant `halt`: the boop replaced by a halt) |
| `pillai.txt` | The 132-state design |
| `machines/pillai_91.txt`, `_annotated.txt` | The merged machine, and the same machine with each state's roles and the beep and boop marked |
| `ref.py` | The reference model: the tuples in order and the events of each |
| `test_tuple.py` | Tuples placed on the tape, run from the setup: the events of `ref.py` and the tuple restored at the next enumeration step |
| `test_enum.py` | From a blank tape, the tuples reaching the setup are the NEXCOM successors of the seed, in order, each once |
| `test_e2e.py` | The events of the first 10⁹ steps against `ref.py`; the variant halts at the first boop after 4 beeps; 10⁸ steps without halting; with a merged machine as argument, the same events |
| `gen_lean.py`, `gen_reduced_lean.py`, `annotate.py` | `Machine.lean` (`delta`, and `deltaQ`, the design without its beep and boop), `M91.lean`, the annotated listing |
