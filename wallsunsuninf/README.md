# A beeping Turing machine for infinitely many Wall–Sun–Sun primes

**Current best: `machines/wallsunsuninf_48.txt`, a 48-state, 2-symbol
[beeping](https://wiki.bbchallenge.org/wiki/Beeping_Busy_Beaver) Turing machine** (94
instructions, BBBi). Started on a blank tape, it takes its beep transition once for m = 1 and
then once for every m ≥ 2 with

    m² ∣ F(m − 1)  if m ≡ ±1 (mod 5),     m² ∣ F(m + 1)  otherwise

(`F` the Fibonacci numbers). So it **quasihalts iff there are finitely many Wall–Sun–Sun
primes** (primes `p` with `p² ∣ F(p − (p/5))`): it beeps infinitely often iff there are
infinitely many. None is known, and they are conjectured to be infinitely many.

Lean proves it (`TM.WallSunSunInf.M48.quasihalts_iff`, with `never_halts`):

    QuasiHalts M48.delta2 M48.St2.q9 false M48.start2 ↔ ¬ InfinitelyManyWallSunSunPrimes

where `InfinitelyManyWallSunSunPrimes` is `∀ n, ∃ p, n ≤ p ∧ Prime p ∧ p * p ∣ fib (wssIndex p)`
(`../lean/TinyCryptids/Defs.lean`); `beeps_forever_iff` states the converse form.

The beep is state `38` reading 0 in the standard text below (`q9` reading 0 in the design and
in the merged machine's file). The machine never halts. Its first and so far only beep is the
check of m = 1, at step 110.

    1R25,0L4_0L2,1L1_0L3,0L29_0R24,1L0_0R15,1L5_0L9,1L6_0R15,1L7_0R15,1L8_0L9,1L4_0L10,0R15_0R11,1L10_1L13,1R9_1L12,1L11_0R14,1L11_1R47,0R34_0R16,1R15_0R15,1L17_1R18,0L1_1R13,1R19_0L21,1L20_0L39,0L31_0R22,1L21_---,1R23_---,0R24_0R3,1R24_0R46,1R26_0L27,1L2_0R28,1L27_1R43,1R2_0L30,1L29_0L29,1L31_0L32,1L31_0L33,0L42_1L12,1L12_0R35,1R34_0R34,1R36_0R37,1R39_0R37,1R38_0L19,1L19_0L40,1R39_1L41,1L40_0L32,1L40_1L28,1L42_0R44,1R43_0R43,1L45_1R46,1R17_1L47,1R46_0R45,1L47

## Why the beeps count Wall–Sun–Sun primes

Write `z(q)` for the rank of apparition of a prime `q` (the least `k ≥ 1` with `q ∣ F(k)`), and
`ε(m) = 1` if m ≡ ±1 (mod 5), `−1` otherwise. Three standard facts: `q^j ∣ F(k)` iff
`z(q^j) ∣ k`; `z(q) ∣ q − (q/5)` for q ≠ 5, with `(q/5) = ε(q)`; and `z(q²)` is `z(q)` or
`q·z(q)`.

* Every Wall–Sun–Sun prime p passes: p ≠ 5 (25 ∤ F(5)), and m − ε(m) is p − (p/5).
* If m ≥ 2 passes and q is a prime factor of m, then q does not divide m − ε(m) = m ∓ 1. So
  `z(q²) ∣ m − ε(m)` leaves `z(q²) = z(q)`, which divides q − (q/5): q is a Wall–Sun–Sun prime
  (this rules out q = 2 and q = 5, since z(4) = 6 = 2·z(2) and z(25) = 25 = 5·z(5)).
* The exponent of q in m is bounded. For odd q and `z(q) ∣ n`,
  `v_q(F(n)) = v_q(F(z(q))) + v_q(n / z(q))`. If q^a ∥ m, then q^(2a) ∣ F(m − ε(m)), and q does
  not divide m − ε(m), so 2a ≤ e_q := v_q(F(z(q))).
  So if there are finitely many Wall–Sun–Sun primes, finitely many m pass, and the beeps stop.

So the machine needs no primality test.

## How it works

It is `../wallsunsun`'s machine with the halt made a beep. The tape at the start of round m
(blocks of 1s, separators `00`, a hole is a single 0):

    B 00 E 00 D

* **B** (`m + 1` cells, no hole): the Zeckendorf odometer, its `m − 1` inner cells the bits
  of a binary string without two adjacent 1s.
* **E** (`m + 2` cells): the low base-m digit, a hole cycling through cells `1 … m`.
* **D** (`m + 2` cells, its hole on cell 1): the high base-m digit.

E's hole is put on cell m (the counter is `m − 1`). Counting the m cells left of it mod 5
decides the first string (`10…0` if m ≡ ±1, else `0…0`), and the odometer then advances
the counter once per string: `F(m − ε(m))` times in all. The check reads E's cell m and D's
cell 1. Both are holes iff the counter is back at `m − 1` mod m², i.e. iff `m² ∣ F(m − ε(m))`,
and that transition (`q9` reading 0) is the **beep**. The round end then fills E's hole and
grows E by a cell on the left (B gives its last cell and gets two on the left), fills D's hole,
appends a cell to D and makes D's cell 1 the hole.

Round 1 (B with no inner cells) is not a real round: its mod-5 count makes B's last cell a
hole, and `r3` reading 0 (otherwise unused) fills it again. Round 1 then ends in the exact
start of round 2. That makes round 1 a cheap entry point for the seed.

## Smaller machine

* `wallsunsuninf.txt` (= `machines/wallsunsuninf_79.txt`) is the 79-state design: 64 states of
  rounds plus a plain 15-state seed that writes round 2.
* The seed costs nothing in the merged machine. `minimize_clique.py` on the seedless design
  `wallsunsuninf_noseed.txt` (64 states) gives `machines/wallsunsuninf_noseed_48.txt`. That is
  48 states, the clique bound, so optimal for these rounds, with the beep kept exclusive.
  It leaves six transitions undefined. `seedfit.py` (search in `seedfit.c`) then tries every
  start state and branches on each undefined transition the blank-tape run meets. It finds
  ten seeds that use three of them, and none that use fewer. The one kept starts in `w` and
  sets `b2`, `a2` and `ov` reading 0 to `0R f2`, `1R nb2` and `1R f3`. The run reaches the
  exact start of round 1 (`build.canon(1)` in `e1`, the head on D's cell 0) at step 45 and
  follows the design from there.
* The full 79-state design with the 15-state seed did not settle K = 48 in 30 minutes of
  `minimize_clique.py`.

## Files

| File | Contents |
|------|----------|
| `build.py` | Generator of the design `wallsunsuninf.txt` and of `wallsunsuninf_noseed.txt`. Variants: `extra` cells in B, other residues `holes` for `10…0`, the round `m0` the seed writes. `q7` reading 0 is taken iff E's hole is on cell m (`m ∣ N`), a second beep for tests |
| `machines/wallsunsuninf_48.txt` | The best machine: `machines/wallsunsuninf_noseed_48.txt` with the seed fitted by `seedfit.py` |
| `unroll_seed.py`, `wallsunsuninf_seeded.txt` | The Lean design: the seedless design plus the 48-state machine's seed run as 45 seed states |
| `gen_lean.py`, `gen_reduced_lean.py` | `../lean/TinyCryptids/WallSunSunInf/Machine.lean` (`delta`, `deltaNB`) and `M48.lean` |
| `seedfit.py`, `seedfit.c` | The seed search: `python3 seedfit.py machines/wallsunsuninf_noseed_48.txt machines/wallsunsuninf_48.txt` |
| `test_e2e.py [machine]` | The design's checks m = 2…24 against the Fibonacci model (B clean, E's and D's holes as the base-m digits of `m − 1 + N`), its round starts m = 2…26, and variants that beep exactly where the model says (low digit only: every prime but 5 up to 31; `extra` 3, 8, 5 with all residues, 1, 11: the beeps at m = 2, 3, 2, none, 12). The merged machine has the same tape and head as the design with m0 = 1, at 10³…10⁸ steps after round 1 starts, and the same beeps (only m = 1) in 2·10⁸ steps |

## The Lean proof (`../lean/TinyCryptids/WallSunSunInf/`)

The 48-state machine's seed is not the design's, so the proof is for
`wallsunsuninf_seeded.txt` (109 states): the seedless design plus the 48-state machine's seed
run (45 steps to round 1) unrolled into one state per step (`unroll_seed.py`). The 48-state
machine is a merge of it, and `gen_reduced_lean.py` transfers the theorems
(`quasihalts_iff_of_sim`, the beep kept exclusive).
`Odo`, `Round` are `../lean/TinyCryptids/WallSunSun2/`'s (the 50-state Wall–Sun–Sun machine's)
routines for `deltaNB` (the design without its beep); `check` beeps where that machine halts.
`Main`: `round` (every `m ≥ 2`: the beep iff `m² ∣ F (m ∓ 1)`, then round `m + 1`), `round1`
(round 1, 65 + 1 + 34 concrete steps, one beep), `seed_reach`, `reach_rs`, `never_halts` and
`quasihalts_iff`, with `TM.WallSunSun2.inf_bridge` for the number theory (`../wallsunsun/PROOF.md`).

    python3 build.py && python3 test_e2e.py
    cd ../tools && python3 minimize_clique.py ../wallsunsuninf/wallsunsuninf_noseed.txt ../wallsunsuninf/machines/wallsunsuninf_noseed_48.txt 300 cadical195 q9:0
