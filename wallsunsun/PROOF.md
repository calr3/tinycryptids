# The proof, in plain words

This is a guided tour of the Lean proof that the machine halts if and only if a Wall–Sun–Sun
prime exists. The proof is in `../lean/TinyCryptids/WallSunSun2/`; each step below names the
lemma that carries it.

## What is proved

```lean
theorem TM.WallSunSun2.halts_iff :
    Halts delta start ↔ ∃ p, Prime p ∧ p * p ∣ fib (wssIndex p)
```

`wssIndex p` is `p` if `p % 5 = 0`, `p − 1` if `p % 5 ∈ {1, 4}` and `p + 1` otherwise
(`p − (p/5)` with the Legendre symbol; `../lean/TinyCryptids/Defs.lean`). The merged machine's
theorem (`TM.WallSunSun2.M50.halts_iff`) states the same thing for `delta2` and is transferred
from the design's (`M50.lean`). Both depend only on `propext`, `Classical.choice` and
`Quot.sound` (`../lean/Check.lean`). The number theory is in core Lean too: `Fermat.lean`
(Euclid's lemma, `p ∣ choose p k`, the binomial theorem, Fermat's little theorem) is the base.

Tapes are streams seen from the head: `ones n s` is `n` ones followed by `s`, `cfgL q s R` the
machine in state `q` reading the first cell of `s` (the cells left of the head are read
leftwards).

## Part 1: the odometer on lists (`Spec.lean`, namespace `TM.Zeckendorf`)

B's inner cells are a bit string without two adjacent 1s, a `List Bool` with the least
significant bit first (`Valid`). `inc` is the machine's increment step by step: clear 1-bits;
at the first 0-bit (`cand`) look at the next bit: if it is 0, set the candidate; if it is 1,
clear it and make the bit after it the candidate. Past the end of the list there is no
candidate: the last string. `val k l` is the Zeckendorf value with weights `fib (k + 2)`,
`fib (k + 3)`, …

* `cand_spec`: a step of `cand` at weight offset `k` adds `fib (k + 2)` to `val k`. Clearing the
  bit of weight `fib (k + 3)` and setting the one of weight `fib (k + 4)` adds `fib (k + 2)` too,
  which is the whole induction.
* `inc_spec`: `inc` adds 1 to `val 0` and keeps the string valid and its length.
* `inc_none`, `cand_none`: when there is no next string, `val 0 l + 1 = fib (n + 2)` (`n` the
  length).
* `val_lt`: a valid string has `val 0 l < fib (n + 2)` (so the loop ends).
* `val_replicate`, `val_msb`: the first strings `0…0` (value 0) and `10…0` (value `fib (n + 1)`).

So from `0…0` there are `fib (n + 2)` strings and from `10…0` there are `fib n`.

## Part 2: the odometer and the counter on the tape (`Odo.lean`)

* `BL l`: B from the head leftwards (a 1-bit is a hole), then B's left marker. `SC l k X`: state
  `sc` on the first bit with `k` cleared cells to its right; `NB`, `QE`, `OV`: the candidate test,
  a set candidate about to tick, the last string passed (the head on B's left marker).
* `nb_spec`, `sc_spec`: by induction along `cand` and `inc`, the machine from `SC l k X` reaches
  `QE` with the new string written (`replicate k' false ++ true :: r'`), or `OV` when `inc l` is
  `none`. `overflow` is the last string: one cell left of B is written and restored.
* `EV p V`: E and D as the two base-`m` digits of the counter `V` (E's hole on cell `V % p + 1`,
  D's on `V / p % p + 1`). `tick0`, `tick`: from `QE` (or from E's cell 0) the
  machine parses to E's hole, moves it (`DadvL.nowrap` of `../lean/TinyCryptids/Core/Routines.lean`);
  on a wrap (`DW.wrap`) it parses on to D's hole and moves that one too; back to `sc`: `EV p (V + 1)`.
  `div_succ`, `div_succ'` give `(V + 1) / p`.
* `loop`: from string `l` and counter `V`, after `t = fib (n + 2) − 1 − val 0 l` rounds the machine
  is in `OV` with the counter `V + t` (induction on `t` with `sc_spec`, `tick`, `inc_spec`).

## Part 3: the rounds and the theorem (`Round.lean`, `Main.lean`)

`Round.lean`: `RS m` is the start of round `m` (D `= 1 0 1^m`, the head on D's cell
0), `init` and `check` as before. The round end is `to_next`: `next_hole` (E and B grow),
then `rebuild` (PF to D's hole) and `fill` (fill the hole, append a cell, make cell 1 the hole).
`Main.lean`: `round` (every `m ≥ 2`: halt iff `m² ∣ N m`, else `RS (m + 1)`), `seed_reach`
(21 concrete steps), and `halts_iff_idx`: the design halts iff some `m ≥ 2` has
`m² ∣ fib (idx m)` (`idx m = m ∓ 1` by `m mod 5`). `bridge` turns that into the statement.

## Part 4: the number theory (`Fib`, `Gauss`, `Recip`, `Bridge`, `InfBridge`)

* `Fib.lean`: the addition formula `fib_add`, `fib_dvd_mul` (`F m ∣ F (m t)`),
  `fib_succ_coprime` (no prime divides two consecutive Fibonacci numbers). `Rank q z`: `z` is the
  least `z ≥ 1` with `q ∣ F z`, and `rank_dvd`: `q ∣ F n → z ∣ n`. `lift`: with `a = F z`,
  `b = F (z − 1)`, `F (z (t + 1)) ≡ (t + 1) a b^t (mod a²)` (and `F (z (t + 1) − 1) ≡ b^(t + 1)
  (mod a)`), by induction on `t` with the addition formula. So `sq_of_sq`: `q² ∣ F k` with
  `q ∤ k` gives `q² ∣ F z`, because `q ∤ t + 1`, and `q ∤ b`.
* `Gauss.lean`: Gauss's lemma for 5. For an odd prime `q = 2h + 1 ≠ 5`, `r5 k` folds `5k mod q`
  into `[1, h]`, `5k ≡ ±r5 k` (`r5_cong`), `r5` is injective (`r5_inj`), so `∏ r5 k = h!`
  (`perm_prod`: an injective self-map of `[1, n]` has product `n!`, with the pigeonhole in the
  same induction). Hence `5^h h! ≡ (−1)^μ h!` and `gauss`: `q ∣ 5^h − (−1)^μ`. `mu_formula`
  counts `μ` by floors (`5k mod q > h` iff `5k ∈ (h, q) ∪ (q + h, 2q)`), and `mu_parity`:
  `μ` is even iff `q ≡ ±1 (mod 5)` (`omega`, split on `h mod 5`).
* `Recip.lean`: `S n = Σ C(n, 2j+1) 5^j` and `T n = Σ C(n, 2j) 5^j` (`(1 + √5)^n = T n + S n √5`)
  satisfy `2 S n = 2^n F n` and `2 T n + 2^n F n = 2^(n+1) F (n + 1)` (`ST_fib`, from Pascal's
  rule: `S_succ`, `T_succ`). Modulo an odd prime `q`, every binomial coefficient but the first or
  last is a multiple of `q` (`S_mod`, `T_mod`), so with Fermat `F q ≡ 5^h` and
  `2 + 2 F q ≡ 4 F (q + 1)`. With `gauss`: `prime_dvd_fib_wss`, `q ∣ F (wssIndex q)` for every
  prime `q` (`2` and `5` by `decide`).
* `Bridge.lean`: `bridge`. A prime `p` with `p² ∣ F (wssIndex p)` is not 5, so `idx p =
  wssIndex p`. Conversely a prime factor `q` of a passing `m` does not divide `idx m = m ∓ 1`,
  so `sq_of_sq` gives `q² ∣ F z`, and `z ∣ wssIndex q` by `rank_dvd` and `prime_dvd_fib_wss`.

`InfBridge.lean` is used by `../wallsunsuninf`'s proof: `pow_of_pow` (`q^j ∣ F k`, `q ∤ k` gives
`q^j ∣ F z`), `dvd_of_prime_pows` (`m ∣ X` if every prime power dividing `m` does), and
`pass_dvd`: with all Wall–Sun–Sun primes below `N`, every passing `m` divides `F (N!)`. So
`inf_bridge`: infinitely many `m` pass iff there are infinitely many Wall–Sun–Sun primes.
