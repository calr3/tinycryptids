# A Beeping Booping Turing machine for the abc conjecture

The [abc conjecture](https://en.wikipedia.org/wiki/Abc_conjecture) is a major conjecture in number theory. Informally, it states that for given any coprime `a`, `b`, and `c` with `a + b = c` it should rarely occur that `rad(abc)` is much smaller than `c` (where `rad(n)` is the product of `n`'s prime factors). To state this formally, we need three alternating quantifiers:

`∀ε∈ℚ ∃K∈ℚ ∀a,b,c∈ℕ. c < K · rad(abc)^(1+ϵ)`.

This puts the abc conjecture in the Σ₃ class of the [arithmetic hierarchy](https://en.wikipedia.org/wiki/Arithmetical_hierarchy), which is beyond even the ability of a [Beeping Busy Beaver machine](https://wiki.bbchallenge.org/wiki/Beeping_Busy_Beaver) to address. However, it can be tackled with a [Beeping _Booping_ Busy Beaver](https://wiki.bbchallenge.org/wiki/Beeping_Busy_Beaver#Beeping_Booping_Busy_Beavers) and the machine given here follows Bram Cohen's convention for these: the machine "pseudoquasihalts" iff the abc conjecture is false.

**Current best machine: `machines/abc_235.txt`, a 235-state, 2-symbol Beeping Booping Turing machine.**

The beep is the transition of state `117` reading 0; the boop is `121` reading 0
(`xe3` and `xq6` in the design and the Lean files).

## What is proved

Lean (`../lean/TinyCryptids/ABC/`, core Lean 4.15.0, no Mathlib):

    theorem TM.ABC.M235.repeats_iff :
        RepeatsForever delta2 St2.xe3 false St2.xq6 false start2 ↔ ¬ ABCConjecture
    theorem TM.ABC.M235.never_halts : ¬ Halts delta2 start2

with (`../lean/TinyCryptids/Core/BeepBoop.lean`, `../lean/TinyCryptids/Defs.lean`)

    def RepeatsForever δ qb bb qo bo c := ∃ v, ∀ N, ∃ i j, N ≤ i ∧ i < j ∧
        BeepsAt δ qo bo c i ∧ BeepsAt δ qo bo c j ∧ (∀ k, i < k → k < j → ¬ BeepsAt δ qo bo c k) ∧
        beepsBetween δ qb bb c i j = v
    def ABCConjecture := ∀ n, 1 ≤ n → ∃ N, ∀ a b, 1 ≤ a → 1 ≤ b → Nat.gcd a b = 1 → N ≤ a + b →
        (a + b) ^ n ≤ rad (a * b * (a + b)) ^ (n + 1)

`BeepsAt δ q b c n` says that step `n + 1` of the run from `c` is the transition of `q`
reading `b` (`Core/Beep.lean`). So `RepeatsForever` says: there is a `v` such that,
arbitrarily late, two consecutive boops have exactly `v` beeps between them.
`beepsBetween δ qb bb c i j` counts the beep steps strictly between steps `i` and `j`.
`rad n` is the product of the distinct primes dividing `n`. `ABCConjecture` is the abc
conjecture with `ε = 1/n`: for each `n`, only finitely many coprime triples
`a + b = c` have `c > rad(abc)^(1 + 1/n)`. A bound on `c` stands in for "finitely many".
The 368-state design has the same two theorems (`TM.ABC.repeats_iff`, `TM.ABC.never_halts`).
All of them depend only on `propext`, `Classical.choice` and `Quot.sound`
(`../lean/Check.lean`).

`RECORDS.md` lists the machines. `PROOF.md` walks through the proof in plain words.

## How it works

For each pair `(a, b)`, `c = a + b`, in the order `c = 2, 3, …`, `a = 1, …, c − 1`:

* **Factor phase.** `R := 1`. For the trial divisors `d = 2, …, c`: `d` **hits** if it shares a
  factor with `a`, `b` or `c` (tested in that order, stopping at the first hit). A hit with
  `gcd(d, R) = 1` does `R := R · d`. Afterwards `R = rad(abc)`. A prime `d` dividing `abc` hits
  and is coprime to `R`. A composite `d` that hits shares a smaller prime with `abc`, and that
  prime already divides `R`. At `d = c`, a hit on `a` means `gcd(a, b) = gcd(a, c) > 1`, and
  the pair is skipped.
* **Pre-test.** If `c ≤ R`, the pair is skipped: then `c^n ≤ R^n < R^(n+1)` for every `n`.
* **Powers.** `P := 1`, `Q := R`. Repeat: compare `P` with `Q`. If `P ≤ Q`: **beep**,
  `P := P · c`, `Q := Q · R`. If `P > Q`: **boop**, next pair. The compares are
  `(1, R), (c, R²), …, (c^n, R^(n+1))`, so a pair that passes beeps exactly `v` times and
  then boops, where `v` is the least `n` with `c^n > R^(n+1)`.

A skipped pair beeps and boops nothing. So the output is the sequence of values `v` of the
passing pairs (coprime, `c > rad(abc)`), in order. If abc fails for some `n`, infinitely
many triples have `v ≤ n`, and by pigeonhole some value repeats forever. Conversely, a value
`v` that repeats forever gives infinitely many triples with `c^v > rad^(v+1)`, so abc fails
at `n = v`. There is no other way for a given value to be repeatedly infinitely often. Therefore
the machine pseudoquasihalts iff the abc conjecture is false.

The first passing pairs are `1 + 8 = 9` and `8 + 1 = 9` (`rad = 6`, `v = 5`: `9^5 > 6^6`,
`9^4 ≤ 6^5`). Next come `5 + 27 = 32` and `27 + 5 = 32` (`rad = 30`, `v = 53`). The powers
are in unary, so the first boop is at step 9.45·10⁹.

### Tape encoding

Numbers are in unary. A block of `v + 2` cells holds `v`. Cells `1 … v` are the positions of
a **hole** (a single 0, a cursor), and cells `0` and `v + 1` are guards. Blocks are separated
by `00`:

    [P 00] K 00 D 00 A 00 B 00 C 00 M 00 R [00 Q]

* `K`: `c − d + 1` cells and no hole, the countdown for `d`. `d += 1` moves the `K|D` separator
  one cell left.
* `D`: the trial divisor. Its hole is the counter of the gcd test.
* `A`, `B`, `C`: `a`, `b`, `c`. The block being tested carries a marker hole on cell 1.
* `M`: one cell. No other block has fewer than three, so finders stop at `M`.
* `R`: the radical so far.
* `P` and `Q` exist only in the power phase. `P` grows to the left (a mirrored copy of the
  multiplication) and `Q` to the right.

### Routines

* **`GCD(D, X)`, lockstep holes.** `D`'s hole (positions `1 … d`) and `X`'s hole (positions
  `1 … x`) start on position 1. One round moves `X`'s hole once around `X`, and `D`'s hole
  `x` times. After round `j`, `D`'s hole is on `(j·x mod d) + 1`. If position 1 comes up first
  (`j·x ≡ 0`, `j < d`), then `gcd > 1`; if position 2 comes first (`j·x ≡ 1`), then `gcd = 1`.
* **`Z := Z · base`.** Each non-wrapping advance of the base hole appends a copy of `Z` after
  `Z`'s separator (a copy loop driven by `Z`'s own hole). The wrap merges the copies into `Z`.
  The same 30 states serve `R := R · d` (`Z = R`, base `D`) and `Q := Q · R` (`Z = Q`, base
  `R`). A mirrored copy does `P := P · c`.
* **Compare.** `X`'s cursor moves left from `X`'s last position and `Y`'s moves right from
  position 1, in turn. `Y` runs out first iff `x > y`. The same states compare `C` with `R`
  (the pre-test) and `P` with `Q` (the loop). The exits tell the two apart by the cell left of
  `X`.
* **Pair end.** Erase `R` and `Q`, then do `a += 1, b −= 1` (the `A|B` separator moves one cell
  right) or, when `b = 1`, `c += 1, a := 1, b := c`. Then `R := 1`, `d := 2`, and `K` gets
  `c − 1` cells.

The design (`abc.txt`, from `build.py`) has 368 states. A randomised greedy merge
(`../tools/greedy_merge_par.py`, on 23 processes, with the beep and the boop kept exclusive)
gives 235 states. Both special
transitions stay exclusive: no state that reads 0 shares the beep or the boop state's class,
which `gen_reduced_lean.py` checks. The exact search (`../tools/minimize_clique.py abc.txt
out 3600 cadical195 xe3:0,xq6:0`) has a clique lower bound of 179 and proves 179–183
unsatisfiable. Larger `K` is still open, so 235 is not known to be optimal.

## Standard text (bbchallenge format, 235 states)

    1R1,1R135_0R2,1R204_0R3,1R143_1R4,0R109_1R5,1L174_1R6,0R145_1R7,0L65_0R8,0R31_0R9,1L161_1R10,0R147_1R11,1L118_1R12,0L116_0R13,1L213_0R14,1L103_1R15,1R87_1R16,1R33_1R17,1R208_0R18,1L17_0R19,1R6_1R20,0R47_1R21,1L77_1R22,1R42_1R23,1L220_0R24,0R96_0R25,1R153_1R204,1R16_1R27,1R26_1L219,1R28_0L29,1L7_0R30,1L29_0R207,1R7_0R32,1R31_0R31,1L14_0L35,1L34_1L59,0L38_0R36,1L35_1R186,1R37_0R135,0L40_0L39,1L38_0L38,1R26_0L41,1L40_0L40,1R42_0L43,0R154_0L173,1L44_0R67,1L45_0R46,1R26_0L90,1R19_1R48,---_0R49,1R48_0R48,1R50_0R51,1R50_0R52,1L185_0L61,1R53_0L57,0L54_0L55,1L54_0L54,1R56_1L38,0L179_0L58,1L57_0L57,1R34_0L60,1L59_0L59,1R90_0L62,1R2_0L63,1R2_0L64,1L63_0L63,1L65_0L66,1L65_0L65,1R142_1L120,1R68_0R69,1L22_0R70,1R69_0R69,1R71_0R72,1R71_0R73,1R83_0L86,1R74_0L54,1L75_0L76,1L75_0L75,1R77_1L78,0R96_0L79,1L78_0L78,1L80_0L81,1R209_0L82,1L93_1L46,1L83_0R202,1R84_0R85,1R84_0R84,1L26_0L87,1L108_0L88,0L38_0L89,1L88_0L88,1L59_1L91,0L27_0R208,1L92_0L80,1R204_0R97,1R94_0L121,0R95_0R22,---_0R13,1R96_0R98,1R97_0R97,1L99_0L100,0L114_0R30,1L101_0L102,---_0L13,0R169_0L104,1L234_0L105,1L20_1L124,1L106_1L194,1L86_1L86,---_0L116,1R3_0R110,1R109_0R109,1L111_1R112,1R111_1R156,1R113_0L10,1L99_0L115,1L114_0L114,1R107_0L117,1L42_0R165,1R122_0L119,1L118_0L118,1R67_0L94,1L120_0R100,1L126_0R123,1R122_0R122,1L105_0L125,1L124_0L80,1R11_0L127,1L126_0L128,1L126_1L129,1L126_0L130,1R129_1R131,1L162_0R132,1L188_0R133,1R132_0R134,1R132_1R37,1R132_1L136,0R195_0L137,1R218_0L219,1L138_0L139,---_0L140,1R91_0R141,1L140_1L114,1R62_1R2,0L151_0L144,1L5_0R21,1L144_0R146,1R145_0R145,1R147_0R148,1R147_0R149,---_1L150,1R149_0L151,1L150_0L152,0L157_1R24,1L152_0L17,1L9_0R155,1R154_0R154,1R111_0L142,1R156_0L158,1L157_0L157,1L159_0L160,1L178_0L8,---_0L162,1L163_0L59,0L191_0L164,1L163_0L163,1R141_0R166,1R201_0R167,1R25_0L168,1R167_0L4,1L102_0R170,1R169_0R169,1L171_1L172,---_0R125,1L172_0L168,1L173_0L175,1L12_0L176,1L175_0L181,1L158_1L159,---_0R129,1R56_0L180,1L179_0L179,1L175_1R182,1L181_0R183,1R182_0R184,1R0_1L51,1R184_0R187,1R186_0R215,0L175_0L131,1R187_0R139,0R189_0R190,1R189_0R189,1L177_0L192,1L191_0L191,1L193_1L106,1L193_0R135,1L194_0R135,0R196_0R197,1R196_0R196,1R198_0R199,1R198_0R198,1L200_1R165,---_0R71,---_0R203,1R202_0R166,1R61_0R205,1R204_0R206,1R204_1R228,1R92_0R188,0R207_0R1,1R103_0R210,0R209_0R211,0R209_0L212,0R209_0L212,1L42_0L137,1L214_0L36,1L214_0R83,0R216_0R217,1R216_0R136,1R216_0R205,1R216_1L214,1L68_0L222,1R183_0L222,1L221_0L223,1L221_0R224,1L221_0R225,---_1R226,---_0R227,1R226_0R228,1R226_0R230,1R229_0R82,1R226_1L231,0R166_0L232,1L231_0L233,1L231_0R215,1L231_0L206,1L234

States are listed in order, and the first is the start state. **Beep: `117` reading 0.
Boop: `121` reading 0.**

## Files and checks

| File | Contents |
|------|----------|
| `build.py` | The generator of the design (variant `halt`: the boop replaced by a halt) |
| `abc.txt` | The 368-state design |
| `machines/abc_235.txt`, `_annotated.txt` | The merged machine, and the same machine with each state's roles and the beep and boop marked |
| `ref.py` | The reference model: the pairs in order, their `rad`, their values `v`, the event string |
| `test_e2e.py` | The events of the first 2·10¹⁰ steps against `ref.py` (`1 + 8` and `8 + 1`, 5 beeps each, then into `5 + 27`); the variant halts at the first boop after 5 beeps; 10⁸ steps without halting; with a merged machine as argument, the same events |
| `gen_lean.py`, `gen_reduced_lean.py`, `annotate.py` | `Machine.lean` (`delta`, and `deltaQ`, the design without its beep and boop), `M235.lean`, the annotated listing |

Shared tools: `../tools/sim.c` and `../tools/tm.py` report beeps and boops
(`tm.run(…, beep=('xe3', 0), boop=('xq6', 0), notape=True)`). `../tools/minimize_clique.py`
and `../tools/greedy_merge_par.py` take several exclusive transitions (`xe3:0,xq6:0`). `../tools/leangen.py`
(`reduced_beepboop_lean`) writes the transfer to a merged machine.
