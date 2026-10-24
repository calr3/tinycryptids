# The proof, in plain words

The proof in `../lean/TinyCryptids/Riesel/` is the proof of the earlier 110-state Sierpiński
design (whose routines `../sierpinski/PROOF.md` describes in their current form) with these changes:

```lean
theorem TM.Riesel.halts_iff :
    Halts delta start ↔ ∀ k, k % 2 = 1 → k < 509203 → ∃ n, 1 ≤ n ∧ Prime (k * 2 ^ n - 1)
```

* `Spec.lean`: `Good k` uses `k·2^n − 1`; `cand_odd`, `cand_ge` (at least 9 for `k ≥ 5`) and
  `cand_succ`: `k·2^(n+1) − 1 = 2(k·2^n − 1) + 1`. `good_one` (n = 2) and `good_three` (n = 1)
  cover the two `k` the machine skips.
* `Cycle.lean`: `comp_end` keeps every cell (R gets `P − 1` cells), so `dfin` gives the walk for
  `2P + 1`.
* `Counter.lean`: the counter is `Cg g v`, `g` groups; `cg_dec` and `cg_zero` are inductions
  on `g` (a group 0 borrows and the next group is decremented), used with `g = 5`.
* `Main.lean`: `XK k v` has `k + 7` cells of K, `KL k v` `k + 5`; `seed_reach` writes
  `Cs 254599` (`cs_c0`: its top group is `grp 3`, whose two 0 bits are blank) and reaches
  `KL 5 254599`; `reach_i` runs over `k = 5 + 2i`; `halts_iff` treats `k = 1, 3` by `good_one`
  and `good_three`.
