# The proof, in plain words

This is a guided tour of the Lean proof that the 23-state machine
`machines/weakcollatz_23.txt` halts if and only if the Collatz map has a cycle
other than 1 → 4 → 2 → 1. The proof is about 900 lines in
`../lean/TinyCryptids/WeakCollatz/`; each step below names the lemma that carries it.

## What is proved

```lean
theorem TM.WeakCollatz.M23.halts_iff :
    Halts M23.delta2 M23.start2 ↔
      ∃ n k, 0 < n ∧ 0 < k ∧ iterate collatz k n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4
```

* `collatz x` is `x / 2` for even `x` and `3x + 1` for odd `x`; `iterate collatz k n` applies
  it `k` times (`../lean/TinyCryptids/Defs.lean`).
* `Halts δ c` means: started in configuration `c`, the machine reaches a configuration with
  no transition (`../lean/TinyCryptids/Core/Basic.lean`, the model shared by every machine in the
  repository: 2 symbols, a two-way infinite tape, the head always moves).
* So the right-hand side says: some `n` other than 1, 2, 4 returns to itself — a nontrivial
  cycle. (The trivial cycle is exactly {1, 2, 4}, so this is the weak Collatz conjecture's
  negation.)

To trust the result you need to trust the Lean kernel, the three definitions above, and the
listing of the machine. Nothing else: the theorem depends only on Lean's standard axioms
`propext`, `Classical.choice` and `Quot.sound` (`../lean/Check.lean` prints this).

The proof has four parts: arithmetic about Collatz orbits (`Spec.lean`), the machine's
behaviour on the tape (`Step.lean`), the main theorem for the readable 25-state design
(`Main.lean`), and the transfer to the 23-state machine (`M23.lean`).

## The idea

The machine runs **rounds** `n = 1, 2, 3, …`. In round `n` it starts from `x = n` and applies
the Collatz map until the value is either 1 or at least `n`:

    x := n
    repeat x := collatz(x) until x = 1 or x ≥ n
    if x = n: HALT            (otherwise go on to round n + 1)

A cycle is found **at its largest element**. If a nontrivial cycle has largest element `M`,
then from `M` the orbit stays inside the cycle, below or at `M` and never 1, so round `M`
comes back to exactly `M` and halts. The delicate point is the other direction of time: a
round must not get stuck forever before the machine reaches round `M`. A round is stuck only
if its orbit stays in `[2, n − 1]` forever — and that, it turns out, forces a nontrivial cycle
*below* `n`, whose own round came earlier.

## Part 1: arithmetic (`Spec.lean`)

Write `Cᵏ(x)` for `iterate collatz k x` (`it k x` in the file). Two definitions:

* `Cond n v` — the round for `n` stops at value `v`: `v = 1` or `v ≥ n`.
* `NoCyc n` — there is no cycle all of whose values lie in `[2, n)`: no `c` and `k > 0` with
  `Cᵏ(c) = c` and `2 ≤ Cʲ(c) < n` for all `j ≤ k`.

`NoCyc` gets weaker as `n` grows: `NoCyc n` implies `NoCyc m` for `m ≤ n` (`NoCyc.mono`).

**Lemma 1 (first hitting time, `first_index`).** If some `i` satisfies a property `P`, there is
a least one. (Proved by induction on a bound; Lean's core library does not provide it
directly.)

**Lemma 2 (orbits escape, `reach_cond`).** If `NoCyc n`, then every orbit starting in
`[1, n)` eventually takes a value that is 1 or `≥ n`.

*Proof*, by induction on `n`. For `n = 0` there is nothing to show. Assume the statement for
`n` and assume `NoCyc (n + 1)` (which gives `NoCyc n`). We show every orbit from `[1, n]`
reaches 1 or `[n + 1, ∞)`.

* *Start at `n` itself.* If `n = 1` we are already at 1. Otherwise let `y = C(n)`. If `y` is 1
  or `≥ n + 1`, done. If not, `y < n` (it cannot equal `n`: `C(n) ≠ n` for `n > 0`). By the
  induction hypothesis the orbit of `y` reaches 1 or `[n, ∞)`; take the *first* such moment
  `j` (Lemma 1). If the value there is 1 or `≥ n + 1`, done. Otherwise it is exactly `n`:
  then `n → y → … → n` is a cycle, and by the choice of the first moment all its values lie
  in `[2, n]`. That contradicts `NoCyc (n + 1)`.
* *Start at `x < n`.* By the induction hypothesis the orbit reaches 1 (done), a value
  `≥ n + 1` (done), or exactly `n`, and from `n` the previous case applies.

No pigeonhole argument is needed: the cycle is produced directly from a first return.

**Lemma 3 (rounds stop, `round_stops`).** If `NoCyc n` and `n ≥ 1`, some `i` has
`Cond n (Cⁱ⁺¹(n))`. *Proof:* if `C(n)` already satisfies `Cond n`, take `i = 0`; otherwise
`1 ≤ C(n) < n` and Lemma 2 applies to `C(n)`.

**Lemma 4 (no false alarm, `round_no_return`).** If `NoCyc (n + 1)`, the round for `n` does
not stop at `n`: if `i` is the first index with `Cond n (Cⁱ⁺¹(n))`, then `Cⁱ⁺¹(n) ≠ n`.
*Proof:* otherwise `n` lies on a cycle whose values before the return are, by minimality, in
`[2, n − 1]` — a cycle in `[2, n]`. (For `n = 1` directly: `C(1) = 4 ≥ 1`, value `4 ≠ 1`.)

**Lemma 5 (`nocyc_of_not`).** If there is no counterexample, then `NoCyc n` for every `n`:
a cycle with values `≥ 2` cannot contain 2 (`C(2) = 1`) or 4 (`C²(4) = 1`), so its first
value is a counterexample.

**Lemma 6 (a cycle has a well-placed top, `exists_top`).** If a counterexample exists, there
is an `M ≥ 2` such that `NoCyc M` holds and `M` lies on a cycle with all values in `[2, M]`.

*Proof.* Take the counterexample `n₀` with `Cᵏ⁰(n₀) = n₀`. Its orbit never reaches 1 (from 1
the orbit is 1, 4, 2, 1, … (`it_one`), and it would have to come back to `n₀ ∉ {1, 2, 4}`).
Its values are bounded (`bnd`, `le_bnd`), so `NoCyc` fails for some bound; let `m₀` be the
least `m` with `¬ NoCyc m` (Lemma 1) and `M = m₀ − 1`. Then `NoCyc M` holds, and there is a
cycle with values in `[2, M]`. Not all of its values are `< M` (that would contradict
`NoCyc M`), so the cycle passes through `M` — and the orbit of `M`, running around the same
cycle (`it_mod`), stays in `[2, M]` and returns to `M`.

## Part 2: the machine on the tape (`Step.lean`)

**The tape.** During round `n` the whole tape is one block of `n + 2` cells, numbered
`0 … n + 1`, all 1 except a single 0, the *hole* `H`, at cell `x` (`1 ≤ x ≤ n`); everything
else is blank. Cells 0 and `n + 1` are always 1 between steps. So `n` is the length of the
block and `x` a position in it. In Lean, a configuration is a state with the tape to the left
of the head and the tape from the head on, each as a stream of cells; `ones k s` is `k` cells
of 1 followed by `s`. The two checkpoints are:

* `PB n x` — the *parity branch*: the head on the hole at cell `x`, in state `p0` if `x` is
  even and `p1` if odd. Left of the head: `x` ones. From the head: `0`, then `n + 1 − x` ones.
* `RS n` — the *round start*: hole at cell `n`, head one cell to its left in state `gl`.

**Lemma 7 (parity walk, `parity`, `home`, `rs_pb`).** From state `gl` anywhere left of the
hole, the machine runs left to cell 0 and back right over the ones, alternating `p0`/`p1`, and
reaches `PB n x`. In particular `RS n` reaches `PB n n`, in at least one step.

**Lemma 8 (even step, `even_step`, loop `el_step`/`el_loop`).** From `PB n x` with `x` even:
a second hole `G` walks from `x − 1` to the left end two cells per round trip while `H` walks
left one cell per round trip. The loop invariant `EL a d r` is "head on cell `a`, then `d`
ones, then `H`, then `r` ones"; one round trip turns `EL (a + 2) d r` into `EL a (d + 1) (r + 1)`.
Starting from `EL (x − 2) 1 (·)`, after `x/2 − 1` trips `H` sits at `x/2`. Then the machine
reads cell 1: if `x/2 = 1` it grows the block and reaches `RS (n + 1)` (`grow`); otherwise it
continues the parity walk and reaches `PB n (x/2)`.

**Lemma 9 (odd step, `odd_step`, loop `ol_step`/`ol_loop`).** From `PB n x` with `x` odd: the
old hole becomes `G`, and `H` is re-created at `x + 1`. `G` walks to the left end one cell per
round trip while `H` moves right two cells. Invariant `OL g d r` ("`G` just left cell `g`, then
`d` ones, `H`, `r` ones"); one trip turns `OL (g + 1) d (r + 2)` into `OL g (d + 3) r`. After
`x` trips `G` falls off the left end and `H` is at `x + 1 + 2x = 3x + 1`. Three outcomes:

| `3x + 1` compared with `n` | what the machine does | lemma |
|---|---|---|
| `3x + 1 > n + 1` | `H` runs off the block mid-loop; `G` is filled, the block grows: `RS (n + 1)` | `ol_over` |
| `3x + 1 = n + 1` | `H` lands on the end cell; the block grows: `RS (n + 1)` | `ol_end` (`r = 0`) |
| `3x + 1 = n` | `H` lands on cell `n`: **the machine halts** | `ol_end` (`r = 1`) |
| `3x + 1 < n` | back to the parity walk: `PB n (3x + 1)` | `ol_end` (`r ≥ 2`) |

**Lemma 10 (one step, `step_cases`).** Combining the two, from `PB n x` (`1 ≤ x ≤ n`):
if `C(x) = n` the machine halts; if `Cond n (C(x))` but `C(x) ≠ n` it reaches `RS (n + 1)`;
otherwise it reaches `PB n (C(x))`. (An even step never lands on `n` or above, and an odd step
never lands on 1, so the machine needs only the checks shown above.)

**Lemma 11 (a round, `round_run`, `round`).** If `i` is the first index with
`Cond n (Cⁱ⁺¹(n))`: when `Cⁱ⁺¹(n) = n` the machine halts from `RS n`; otherwise it strictly
reaches `RS (n + 1)`. *Proof:* induction on `i`, one `step_cases` per Collatz step; minimality
of `i` says every intermediate value is in `[2, n − 1]`, so every intermediate step is of the
third kind.

## Part 3: the main theorem for the design (`Main.lean`)

The seed (one state) writes the tape of round 1: `start` reaches `RS 1` (`start_reach`).

**Halting gives a cycle.** Suppose no counterexample exists. By Lemma 5, `NoCyc n` holds for
every `n`. Then for each round `n`, Lemma 3 gives a stopping index, Lemma 4 says the round does
not stop at `n`, and Lemma 11 says `RS n` strictly reaches `RS (n + 1)`. A machine that keeps
strictly moving from one `RS` to the next never halts (`not_halts_of_progress`) — contradiction.

**A cycle makes it halt** (`haltAt_of_cycle`). Take `M` from Lemma 6. Round `M` halts: the
orbit of `M` stays in `[2, M]` and returns to `M`, so its first stopping value is `M` itself,
and Lemma 11 applies. Every earlier round `m < M` has `NoCyc m`, so by Lemma 3 it stops; it
either halts (fine) or passes to round `m + 1`. By induction on `M − m`, the machine halts from
`RS 1`, hence from `start`.

This is `TM.WeakCollatz.halts_iff`, for the 25-state design `weakcollatz.txt`.

## Part 4: the 23-state machine (`M23.lean`)

`M23` is obtained from the design by merging states that never disagree on a transition the
run uses. `M23.lean` is generated by `gen_reduced_lean.py`: it gives the merged table
`delta2`, a map `phi` from design states to merged states, and a check `compat` (one case per
transition, closed by computation) that `delta2 (phi q) b` does what `delta q b` does wherever
the latter is defined. The generic lemma `halts_iff_of_sim` (`Core/Basic.lean`) then shows the
merged machine follows the design's run step for step, halts exactly when it does, and inherits
the theorem.

## What the proof does not cover

* It says nothing about whether a nontrivial cycle exists — that is the open problem. If the
  weak Collatz conjecture is true, the machine runs forever, and the proof shows exactly that.
* The full Collatz conjecture also excludes divergent orbits. A machine searching for a
  divergent orbit cannot recognise one in finite time, so that half is not captured here.
* The bbchallenge standard-text line in `README.md` and the annotated listing are printed from
  the same machine file; `annotate.py` checks the listing is the same machine.
