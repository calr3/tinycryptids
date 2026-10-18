import TinyCryptids.Defs

/-!
# The statement and the arithmetic of a round

The machine runs rounds `n = 1, 2, 3, …`: from `x = n` it applies `collatz`
until the value `v` satisfies `Cond n v` (`v = 1` or `v ≥ n`), and halts iff
then `v = n`.

* `reach_cond`: if no nontrivial cycle lies in `[2, n)` (`NoCyc n`), every
  orbit from `x ∈ [1, n)` reaches a value `1` or `≥ n`. So rounds end.
* `round_no_return`: with no nontrivial cycle in `[2, n]`, a round does not
  return to `n`: it does not halt.
* `exists_top`: a nontrivial cycle gives a least `M` with a cycle in `[2, M]`
  through `M`; `NoCyc M` holds, so all earlier rounds end, and round `M` halts.
-/

namespace TM.WeakCollatz

open TinyCryptids

abbrev it (k x : Nat) : Nat := iterate collatz k x

theorem it_zero (x : Nat) : it 0 x = x := rfl

theorem it_succ (k x : Nat) : it (k + 1) x = collatz (it k x) := rfl

theorem it_add (a b x : Nat) : it (a + b) x = it a (it b x) := by
  induction a with
  | zero => simp [it_zero]
  | succ a ih => rw [Nat.add_right_comm, it_succ, it_succ, ih]

theorem it_succ' (k x : Nat) : it (k + 1) x = it k (collatz x) := by
  rw [it_add]; rfl

theorem collatz_pos (x : Nat) (h : 0 < x) : 0 < collatz x := by
  unfold collatz; split <;> omega

theorem it_pos (k x : Nat) (h : 0 < x) : 0 < it k x := by
  induction k with
  | zero => exact h
  | succ k ih => rw [it_succ]; exact collatz_pos _ ih

theorem collatz_ne_self (x : Nat) (h : 0 < x) : collatz x ≠ x := by
  unfold collatz; split <;> omega

theorem collatz_even (x : Nat) (h : x % 2 = 0) : collatz x = x / 2 := by
  unfold collatz; rw [if_pos h]

theorem collatz_odd (x : Nat) (h : x % 2 = 1) : collatz x = 3 * x + 1 := by
  unfold collatz; rw [if_neg (by omega)]

/-- the orbit of 1 is `1, 4, 2, 1, …` -/
theorem it_one (t : Nat) : it t 1 = 1 ∨ it t 1 = 2 ∨ it t 1 = 4 := by
  induction t with
  | zero => exact Or.inl rfl
  | succ t ih =>
    rw [it_succ]
    rcases ih with h | h | h <;> rw [h] <;> decide

/-- the stopping condition of the round for `n` -/
def Cond (n v : Nat) : Prop := v = 1 ∨ n ≤ v

/-- no cycle with all its values in `[2, n)` -/
def NoCyc (n : Nat) : Prop :=
  ¬ ∃ c k, 0 < k ∧ it k c = c ∧ ∀ j, j ≤ k → 2 ≤ it j c ∧ it j c < n

theorem NoCyc.mono {m n : Nat} (h : NoCyc n) (hmn : m ≤ n) : NoCyc m := by
  rintro ⟨c, k, hk, hc, hv⟩
  exact h ⟨c, k, hk, hc, fun j hj => let ⟨a, b⟩ := hv j hj; ⟨a, by omega⟩⟩

theorem first_index {P : Nat → Prop} (h : ∃ i, P i) : ∃ i, P i ∧ ∀ j, j < i → ¬ P j := by
  obtain ⟨i, hi⟩ := h
  suffices H : ∀ N i, i ≤ N → P i → ∃ i, P i ∧ ∀ j, j < i → ¬ P j from H i i (Nat.le_refl _) hi
  intro N
  induction N with
  | zero =>
    intro i hi hp
    obtain rfl : i = 0 := by omega
    exact ⟨0, hp, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ N ih =>
    intro i hi hp
    rcases Classical.em (∃ j, j < i ∧ P j) with ⟨j, hj, hpj⟩ | hm
    · exact ih j (by omega) hpj
    · exact ⟨i, hp, fun j hj hpj => hm ⟨j, hj, hpj⟩⟩

/-- Without a nontrivial cycle in `[2, n)`, every orbit from `[1, n)` reaches 1 or `[n, ∞)`. -/
theorem reach_cond : ∀ n, NoCyc n → ∀ x, 1 ≤ x → x < n → ∃ i, Cond n (it i x) := by
  intro n
  induction n with
  | zero => intro _ x _ h; omega
  | succ n ih =>
    intro hc
    have ih' := ih (hc.mono (Nat.le_succ n))
    -- from `n` itself
    have top : 1 ≤ n → ∃ i, Cond (n + 1) (it i n) := by
      intro hn1
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · exact ⟨0, Or.inl (by rw [it_zero]; omega)⟩
      rcases Classical.em (Cond (n + 1) (collatz n)) with hy | hy
      · exact ⟨1, hy⟩
      have hy1 : 1 ≤ collatz n := collatz_pos n (by omega)
      have hyn : collatz n < n := by
        have := collatz_ne_self n (by omega); unfold Cond at hy; omega
      obtain ⟨j, hj, hfirst⟩ := first_index (ih' (collatz n) hy1 hyn)
      rcases hj with hj | hj
      · exact ⟨j + 1, Or.inl (by rw [it_succ']; exact hj)⟩
      rcases Nat.lt_or_ge n (it j (collatz n)) with hj2 | hj2
      · exact ⟨j + 1, Or.inr (by rw [it_succ']; exact hj2)⟩
      exfalso
      have heq : it j (collatz n) = n := by omega
      apply hc
      refine ⟨n, j + 1, by omega, by rw [it_succ']; exact heq, ?_⟩
      intro t ht
      rcases t with _ | t
      · rw [it_zero]; omega
      · rw [it_succ']
        rcases Nat.lt_or_ge t j with htj | htj
        · have h1 := hfirst t htj
          have h2 := it_pos t (collatz n) hy1
          unfold Cond at h1; omega
        · obtain rfl : t = j := by omega
          omega
    intro x hx1 hxn
    rcases Nat.lt_or_ge x n with hlt | hge
    · obtain ⟨i, hi⟩ := ih' x hx1 hlt
      rcases hi with hi | hi
      · exact ⟨i, Or.inl hi⟩
      rcases Nat.lt_or_ge n (it i x) with h3 | h3
      · exact ⟨i, Or.inr h3⟩
      have hix : it i x = n := by omega
      obtain ⟨i', hi'⟩ := top (by omega)
      exact ⟨i' + i, by rw [it_add, hix]; exact hi'⟩
    · obtain rfl : x = n := by omega
      exact top hx1

/-! ## rounds -/

/-- Without a nontrivial cycle in `[2, n)`, the round for `n` stops. -/
theorem round_stops (n : Nat) (hn : 1 ≤ n) (hc : NoCyc n) : ∃ i, Cond n (it (i + 1) n) := by
  rcases Classical.em (Cond n (collatz n)) with hy | hy
  · exact ⟨0, hy⟩
  have hy1 : 1 ≤ collatz n := collatz_pos n (by omega)
  have hyn : collatz n < n := by unfold Cond at hy; omega
  obtain ⟨i, hi⟩ := reach_cond n hc (collatz n) hy1 hyn
  exact ⟨i, by rw [it_succ']; exact hi⟩

/-- Without a nontrivial cycle in `[2, n]`, the round for `n` stops elsewhere than at `n`. -/
theorem round_no_return (n : Nat) (hn : 1 ≤ n) (hc : NoCyc (n + 1)) (i : Nat)
    (hfirst : ∀ j, j < i → ¬ Cond n (it (j + 1) n)) : it (i + 1) n ≠ n := by
  intro heq
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · obtain rfl : n = 1 := by omega
    rcases i with _ | i
    · exact absurd heq (by decide)
    · exact hfirst 0 (by omega) (Or.inr (by decide))
  apply hc
  refine ⟨n, i + 1, by omega, heq, ?_⟩
  intro t ht
  rcases t with _ | t
  · rw [it_zero]; omega
  · rcases Nat.lt_or_ge t i with hti | hti
    · have h1 := hfirst t hti
      have h3 := it_pos (t + 1) n (by omega)
      unfold Cond at h1; omega
    · obtain rfl : t = i := by omega
      omega

/-- The weak Collatz conjecture fails: some `n ∉ {1, 2, 4}` lies on a cycle. -/
def Counter : Prop := ∃ n k, 0 < n ∧ 0 < k ∧ it k n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4

/-- A cycle in `[2, n)` is a counterexample. -/
theorem nocyc_of_not (h : ¬ Counter) (n : Nat) : NoCyc n := by
  rintro ⟨c, k, hk, hc, hv⟩
  have h0 := hv 0 (Nat.zero_le _)
  have h1 := hv 1 hk
  rw [it_zero] at h0
  apply h ⟨c, k, by omega, hk, hc, by omega, ?_, ?_⟩
  · rintro rfl; exact absurd h1.1 (by decide)
  · rintro rfl
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      exact absurd hc (by decide)
    · exact absurd (hv 2 hk2).1 (by decide)

/-- `bnd x k` bounds the first `k + 1` values of the orbit of `x`. -/
def bnd (x : Nat) : Nat → Nat
  | 0 => x
  | k + 1 => max (bnd x k) (it (k + 1) x)

theorem le_bnd (x : Nat) : ∀ k t, t ≤ k → it t x ≤ bnd x k := by
  intro k
  induction k with
  | zero =>
    intro t ht
    obtain rfl : t = 0 := by omega
    exact Nat.le_refl _
  | succ k ih =>
    intro t ht
    show it t x ≤ max (bnd x k) (it (k + 1) x)
    rcases Nat.lt_or_ge t (k + 1) with h | h
    · exact Nat.le_trans (ih t (by omega)) (Nat.le_max_left _ _)
    · obtain rfl : t = k + 1 := by omega
      exact Nat.le_max_right _ _

/-- the orbit of a point of a cycle repeats with the cycle -/
theorem it_mod (c k : Nat) (hc : it k c = c) : ∀ s, it (s + k) c = it s c := by
  intro s; rw [it_add, hc]

/-- A counterexample gives `M` with no nontrivial cycle in `[2, M)` and a cycle in
`[2, M]` through `M`. -/
theorem exists_top (h : Counter) :
    ∃ M, 2 ≤ M ∧ NoCyc M ∧ ∃ k, 0 < k ∧ it k M = M ∧ ∀ t, t ≤ k → 2 ≤ it t M ∧ it t M ≤ M := by
  obtain ⟨n0, k0, hn0, hk0, hc0, h1, h2, h4⟩ := h
  -- the orbit of `n0` avoids 1
  have hne1 : ∀ j, it j n0 ≠ 1 := by
    intro j hj
    have hj' : it (j % k0) n0 = 1 := by
      have := Nat.mod_add_div j k0
      have e : ∀ q, it (j % k0 + k0 * q) n0 = it (j % k0) n0 := by
        intro q
        induction q with
        | zero => rfl
        | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, it_mod n0 k0 hc0, ih]
      rw [← e (j / k0), this]; exact hj
    have hl := Nat.mod_lt j hk0
    have : it (k0 - j % k0) (it (j % k0) n0) = n0 := by
      rw [← it_add, show k0 - j % k0 + j % k0 = k0 by omega, hc0]
    rw [hj'] at this
    rcases it_one (k0 - j % k0) with e | e | e <;> rw [e] at this <;> omega
  have hbad : ¬ NoCyc (bnd n0 k0 + 1) := fun hn => hn ⟨n0, k0, hk0, hc0, fun j hj =>
    ⟨by have := it_pos j n0 hn0; have := hne1 j; omega, by have := le_bnd n0 k0 j hj; omega⟩⟩
  obtain ⟨m0, hm0, hmin⟩ := first_index (P := fun m => ¬ NoCyc m) ⟨_, hbad⟩
  have hm0' : ∃ c k, 0 < k ∧ it k c = c ∧ ∀ j, j ≤ k → 2 ≤ it j c ∧ it j c < m0 :=
    Classical.byContradiction hm0
  obtain ⟨c, k, hk, hc, hv⟩ := hm0'
  have hm2 : 3 ≤ m0 := by have := hv 0 (Nat.zero_le _); rw [it_zero] at this; omega
  have hM : NoCyc (m0 - 1) := Classical.byContradiction (hmin (m0 - 1) (by omega))
  -- some point of the cycle is `m0 - 1`
  have hj : ∃ j, j ≤ k ∧ it j c = m0 - 1 := by
    apply Classical.byContradiction
    intro hno
    exact hM ⟨c, k, hk, hc, fun j hj =>
      let ⟨a, b⟩ := hv j hj
      have hne : it j c ≠ m0 - 1 := fun e => hno ⟨j, hj, e⟩
      ⟨a, by omega⟩⟩
  obtain ⟨j, hjk, hjc⟩ := hj
  refine ⟨m0 - 1, by omega, hM, k, hk, ?_, ?_⟩
  · rw [← hjc, ← it_add, Nat.add_comm, it_add, hc]
  · intro t ht
    rw [← hjc, ← it_add]
    rcases Nat.lt_or_ge k (t + j) with h | h
    · have e : it (t + j) c = it (t + j - k) c := by
        rw [← it_mod c k hc (t + j - k), show t + j - k + k = t + j by omega]
      rw [e]
      have := hv (t + j - k) (by omega); omega
    · have := hv (t + j) h; omega

end TM.WeakCollatz
