# The proof, in plain words

This is a guided tour of the Lean proof that the 368-state design `abc.txt` and the
235-state machine `machines/abc_235.txt` have a value that repeats forever iff the abc
conjecture is false. The proof is in `../lean/TinyCryptids/ABC/` (`Machine` and `M235` are
generated; the rest, about 3,300 lines, is hand-written). It sits on two shared files:
`../lean/TinyCryptids/Core/BeepBoop.lean` (the beeping booping semantics, for any machine)
and `../lean/TinyCryptids/Core/Mirror.lean` (running a machine on the mirrored tape), about 560
lines between them. Each step below names the lemma that carries it.

## What is proved

```lean
theorem TM.ABC.repeats_iff :
    RepeatsForever delta St.xe3 false St.xq6 false start ↔ ¬ ABCConjecture
theorem TM.ABC.never_halts : ¬ Halts delta start

theorem TM.ABC.M235.repeats_iff :
    RepeatsForever delta2 St2.xe3 false St2.xq6 false start2 ↔ ¬ ABCConjecture
theorem TM.ABC.M235.never_halts : ¬ Halts delta2 start2
```

* `delta` is the design and `delta2` the merged machine, both generated from the text files.
  The model (`Core/Basic.lean`) has 2 symbols, a two-way infinite tape, and a head that always
  moves.
* `RepeatsForever δ qb bb qo bo c` (`Core/BeepBoop.lean`): some `v` is, arbitrarily late, the
  number of beep steps (`qb` reading `bb`) strictly between two consecutive boop steps (`qo`
  reading `bo`).
* `ABCConjecture` (`Defs.lean`): for every `n ≥ 1` there is an `N` such that every coprime
  `a, b ≥ 1` with `a + b ≥ N` has `(a + b)^n ≤ rad(ab(a + b))^(n+1)`. `rad n = radBelow n (n + 1)`,
  where `radBelow n k` is the product of the primes `p < k` dividing `n`.

## Layer 1: the semantics (`Core/BeepBoop.lean`)

* `repeatsForever_of_segments`. Cut a run into segments `[T k, T (k+1))` with `T` strictly
  increasing and no event before `T 0`. Suppose every segment has either no event, or `val k`
  beeps followed by one boop (`good k`). Then the run repeats a value forever iff some value
  `v` is `val k` for infinitely many good `k`. The proof locates each boop in its segment
  (`hwhere`). It shows that two consecutive boops are the boops of two good segments with only
  quiet segments in between (`hquiet`), and that the beeps between them are exactly the second
  segment's (`cnt_beep`, `evs_append`).
* `Trace a es b`: from `a` to `b` by runs of `δ0` (the machine without its beep and boop),
  joined by single beep (`true`) or boop (`false`) steps of `δ`, in the order `es`.
  `Trace.evs` turns a trace into a statement about the run of `δ`: from step `n` at `a`, it
  reaches `b` at some `n + m`, and the events in `[n, n + m)` are exactly `es`.
* `repeatsForever_iff_of_sim`. The property carries over to a machine that simulates the
  original under a state map `φ`, provided the original never halts and the simulator's beep
  and boop states stand in for the original's only on the special symbol. That is how the
  merged machine inherits the theorem.

## Layer 2: the routines on the tape

All lemmas are about `Rch := Reach deltaQ`, where `deltaQ` is the design without its two
special transitions (`Tac.lean`). Streams `ones n s`, `b ::: s` and `app l s` describe the tape;
`cfgL q s R` is the configuration with the head on `s`'s first cell. Lists of 1s and `00`
separators that a parser crosses are `Clean`; the parsers are `pRR`, `pRL`, `pLR`, `pLL`
(`Nav.lean`).

* **The multiplication** (`Mult.lean`). It is proved once, on a 30-state template machine
  `mdelta` (`mult`). Embedding it by a compatible state map gives `multR` (the right copy, used
  for `R := R·d` and `Q := Q·R`). The mirror (`Core/Mirror.lean`: `Reach.mir`, `Reach.embed`)
  gives `multL` (`P := P·c`, built leftwards).
* **The gcd test** (`Gcd.lean`). `gcd_run`: from the start of `GCD(D, X)`, if `gcd(x, d) = 1`
  the run reaches the "pass" exit (`E1`), otherwise the "hit" exit (`H1`). The proof is
  the coprimality walk (`Walk.lean`: `first_hit`): after round `j`, `D`'s hole is on
  `(j·x mod d) + 1`.
* **One divisor** (`Factor.lean`, `Round.lean`). The configurations `stA`, `stB`, `stC`, `stR`
  (testing `A`, `B`, `C`, `R`) and `dpC` (after the tests). `pass_A`, `pass_B`, `pass_C` move
  to the next test, and `hit_A`, `hit_B`, `hit_C` jump to the `R` test. `new_R` (`gcd = 1`:
  `R := R·d`, `zd_factor` back to `D`) and `notnew_R` end at `dpC`. `next_d` does `d += 1`
  while `K` has at least two cells. `last_d` goes to the pre-test when `K` has one.
* **The pair end** (`PairEnd.lean`). `pe_erase` erases everything right of `M`. `next_ab`
  (`b ≥ 2`: the `A|B` separator one cell right) and `next_c` (`b = 1`: `a := 1`, `K += 1`,
  `C += 1`, `B := c`, `a_loop`, `fk_go`) both end in `wr_go`, which writes `R := 1` with
  `d := 2`. `hitA_nc` and `hitB_nc` are the not-coprime exits at `d = c`.
* **The compare** (`Compare.lean`). `compare`: in `cmpA`, `x ≤ y` reaches `xe2` and `y < x`
  reaches `xq6`, by induction on the rounds (`cmp_round`, `cmp_rounds`, `cmp_xexh`,
  `cmp_yexh`).
* **The powers** (`Power.lean`). `pre_entry`, `pre_skip` (`c ≤ r`) and `pre_pass` (`r < c`:
  `P := 1`, `Q := 1`, at `qE`). `q_mult`: `Q := Q·R`, back to the compare (`loopA`).
  `loop_beep`/`loop_boop` give the two outcomes (`beepC`, `boopC`). `beep_step`: after the
  beep, `Q`'s cursor goes back to cell 1, then `P := P·c` (`multL`), then into `Q := Q·R`.
  `boop_end`: erase `P`, then to `M`.

## Layer 3: the arithmetic (`Spec.lean`)

* `rstep a b c r d`: the machine's update of `R` at `d`. `rstep_rad`: on
  `R = radBelow(abc) d`, it gives `radBelow(abc) (d + 1)`. If `d` is prime, it hits iff
  `d ∣ abc` (`prime_gcd`, Euclid's lemma `prime_dvd_mul`), and it is coprime to `R`
  (`prime_dvd_radBelow`). If `d` is not prime, a hit has a prime factor `p < d` of `abc`
  (`gcd_prime`), which divides `R` (`dvd_radBelow`), so `gcd(R, d) ≠ 1`. `rfrom_rad`: from
  `R = 1` at `d = 2`, the updates up to `d = c` give `rad(abc)`, because no prime factor of
  `abc` exceeds `c` (`radBelow_const`).
* `gcd_ac`, `gcd_bc`: `gcd(a, c) = gcd(b, c) = gcd(a, b)` for `c = a + b`.
* `val c r`: the least `n` with `c^n > r^(n+1)`, found by a bounded search (`vAux`). It exists
  when `r < c`, since `c^(r²) > r^(r²+1)` by Bernoulli's inequality (`bern`, `pow_beat`).
  `val_spec` states this.
* `pairAt k`: the `k`-th pair. `pairAt_spec` gives `2k + 3c = c² + 2a`, so `c` grows with `k`.
  `pairAt_onto`: every pair occurs. `pairAt_c_le`: `c ≤ k + 2`.
* `good_iff`: some value of `val` occurs for infinitely many `Good` pairs (coprime,
  `rad < c`) iff `¬ ABCConjecture`. For one direction, the repeated value `v` contradicts the
  conjecture at `n = v`, for pairs with large enough `c`. For the other, the conjecture fails
  at some `n`. Every failing triple is good with `val ≤ n`, and a uniform bound over the values
  `≤ n` (`bound_all`) gives the pigeonhole.

## Layer 4: the run (`Main.lean`)

* `factor_loop`: `fround` (one divisor, `K ≥ 2`) and `dp_next`, by induction from `d = 2` to
  `d = c`. `last_cop` (coprime: `pass_A`, `pass_B`, `hit_C`, then the `R` test and `last_d`)
  or `hitA_nc`.
* `power`: by induction on the beeps left, with `P = c^n` and `Q = r^n` at `qE`. It is a
  `Trace` with `replicate (val c r) true ++ [false]` to the pair end. The beep and boop steps
  of `delta` are checked by `rfl`.
* `pair_trace`: one `Trace` per pair, from `pS a c` (the pair's start) to the next pair's
  start. Its events are `evsOf a c`: `[]` if the pair is skipped, otherwise `val` beeps and a
  boop.
* `seed`: from the blank tape to `pS 1 2`. `TT`/`Tm` define the segment starts recursively from
  `Trace.evs`. `Tm_lt` holds because consecutive pair starts differ (`pS_ne`). `never_halts`
  follows from `Tm_ge`.
* `repeats_iff`: `repeatsForever_of_segments` with `good k := Good (pairAt k)`, then
  `good_iff`.
* `deltaQ_sub`: `deltaQ` is `delta` without the two special transitions (`deltaQ_eq`, a case
  split over the 368 states).

## The merged machine (`M235.lean`, generated)

`gen_reduced_lean.py` writes `delta2`, the state map `phi`, `compat` (every design transition
is simulated), and `excl_beep`/`excl_boop` (the merged beep and boop states stand in for the
design's only on symbol 0). `repeatsForever_iff_of_sim` then transfers `repeats_iff`, and
`not_halts_of_sim` transfers `never_halts`.
