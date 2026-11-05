import TinyCryptids.AgohGiuga.Fermat

/-!
# The arithmetic of the search

Round `n` takes the bases `i = n - 1, n - 2, …, 2`; after `k` of them the counter holds
`gsum n k % n`, where `gsum n k = Σ (i ^ (n - 1) - 1)` over those bases, and the flag says
whether one of `gsum n 1, …, gsum n k` was nonzero mod `n` (`fl n k`).  The machine halts at the
end of round `n` iff `fl n (n - 2)` and `gsum n (n - 2) % n = 0`, which holds iff `n` is a
composite with `n ∣ powSum n (n - 1) + 1` (`bad_iff`).
-/

namespace TM.AgohGiuga
open TinyCryptids

/-- the next position of a cyclic hole with positions `1..c` -/
def nx (c i : Nat) : Nat := if i < c then i + 1 else 1

def nxs (c : Nat) : Nat → Nat → Nat
  | i, 0 => i
  | i, n + 1 => nxs c (nx c i) n

/-- from position `m % c + 1`, `k` advances lead to `(m + k) % c + 1` -/
theorem nxs_mod (c : Nat) (hc : 1 ≤ c) : ∀ k m, nxs c (m % c + 1) k = (m + k) % c + 1 := by
  intro k
  induction k with
  | zero => intro m; rfl
  | succ k ih =>
    intro m
    show nxs c (nx c (m % c + 1)) k = _
    have e : nx c (m % c + 1) = (m + 1) % c + 1 := by
      unfold nx
      have hlt := Nat.mod_lt m (show 0 < c by omega)
      have hd := Nat.mod_add_div m c
      split
      · have : (m + 1) % c = m % c + 1 := by
          rw [show m + 1 = (m % c + 1) + c * (m / c) by omega, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt (by omega)]
        omega
      · have : (m + 1) % c = 0 := by
          rw [show m + 1 = c * (m / c + 1) by rw [Nat.mul_add, Nat.mul_one]; omega,
            Nat.mul_mod_right]
        omega
    rw [e, ih (m + 1)]; congr 2; omega

/-- `Σ (i ^ (n - 1) - 1)` over the first `k` bases `i = n - 1, …, n - k` -/
def gsum (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => gsum n k + ((n - (k + 1)) ^ (n - 1) - 1)

/-- the flag after `k` bases: some `gsum n j`, `1 ≤ j ≤ k`, is nonzero mod `n` -/
def fl (n : Nat) : Nat → Bool
  | 0 => false
  | k + 1 => fl n k || gsum n (k + 1) % n != 0

theorem fl_iff (n : Nat) : ∀ k, fl n k = true ↔ ∃ j, 1 ≤ j ∧ j ≤ k ∧ gsum n j % n ≠ 0
  | 0 => by simp [fl]; intro j h1 h2; omega
  | k + 1 => by
    simp only [fl, Bool.or_eq_true, bne_iff_ne, ne_eq, fl_iff n k]
    constructor
    · rintro (⟨j, h1, h2, h3⟩ | h)
      · exact ⟨j, h1, by omega, h3⟩
      · exact ⟨k + 1, by omega, Nat.le_refl _, h⟩
    · rintro ⟨j, h1, h2, h3⟩
      by_cases hj : j = k + 1
      · subst hj; exact Or.inr h3
      · exact Or.inl ⟨j, h1, by omega, h3⟩

theorem powSum_gsum {n : Nat} (hn : 2 ≤ n) : ∀ k, k ≤ n - 2 →
    powSum n (n - 1) = powSum (n - k) (n - 1) + gsum n k + k
  | 0, _ => by simp [gsum]
  | k + 1, hk => by
    have ih := powSum_gsum hn k (by omega)
    have e : powSum (n - k) (n - 1) = powSum (n - (k + 1)) (n - 1) + (n - (k + 1)) ^ (n - 1) := by
      rw [show n - k = (n - (k + 1)) + 1 by omega]; rfl
    have hp : 1 ≤ (n - (k + 1)) ^ (n - 1) := Nat.pos_pow_of_pos _ (by omega)
    show _ = _ + (gsum n k + ((n - (k + 1)) ^ (n - 1) - 1)) + (k + 1)
    omega

/-- the counter at the end of the round: `n ∣ powSum n (n - 1) + 1` iff it is 0 -/
theorem gsum_last {n : Nat} (hn : 2 ≤ n) : powSum n (n - 1) + 1 = gsum n (n - 2) + n := by
  have h := powSum_gsum hn (n - 2) (Nat.le_refl _)
  rw [show n - (n - 2) = 2 by omega] at h
  have h2 : powSum 2 (n - 1) = 1 := by
    show powSum 0 (n - 1) + 0 ^ (n - 1) + 1 ^ (n - 1) = 1
    rw [Nat.zero_pow (by omega), Nat.one_pow]; rfl
  omega

theorem dvd_iff_gsum {n : Nat} (hn : 2 ≤ n) : n ∣ powSum n (n - 1) + 1 ↔ gsum n (n - 2) % n = 0 := by
  rw [gsum_last hn]
  constructor
  · intro h
    have := (Nat.dvd_add_iff_left (Nat.dvd_refl n)).2 h
    exact Nat.mod_eq_zero_of_dvd this
  · intro h
    exact (Nat.dvd_add_iff_left (Nat.dvd_refl n)).1 (Nat.dvd_of_mod_eq_zero h)

/-- a prime never sets the flag (Fermat) -/
theorem gsum_prime {n : Nat} (hp : Prime n) : ∀ k, k ≤ n - 2 → gsum n k % n = 0
  | 0, _ => by simp [gsum]
  | k + 1, hk => by
    have h2 := hp.1
    have ih := gsum_prime hp k (by omega)
    have hf := fermat hp (a := n - (k + 1)) (by omega) (by omega)
    have hp1 : 1 ≤ (n - (k + 1)) ^ (n - 1) := Nat.pos_pow_of_pos _ (by omega)
    show (gsum n k + ((n - (k + 1)) ^ (n - 1) - 1)) % n = 0
    rw [Nat.add_mod, ih, Nat.zero_add, Nat.mod_mod]
    have h1 := Nat.mod_add_div ((n - (k + 1)) ^ (n - 1)) n
    rw [hf] at h1
    rw [show (n - (k + 1)) ^ (n - 1) - 1 = n * ((n - (k + 1)) ^ (n - 1) / n) by omega,
      Nat.mul_mod_right]

/-- a composite sets the flag: at its divisor `d`, `d ^ (n - 1) ≢ 1` -/
theorem fl_comp {n : Nat} (h3 : 3 ≤ n) (hc : ¬ Prime n) : fl n (n - 2) = true := by
  rw [fl_iff]
  have : ∃ d, d < n ∧ 2 ≤ d ∧ n % d = 0 := by
    exact Classical.byContradiction fun hno => hc ⟨by omega, fun d h1 h2 h3 => hno ⟨d, h1, h2, h3⟩⟩
  obtain ⟨d, hdn, hd2, hdd⟩ := this
  refine Classical.byContradiction fun hno => ?_
  have hz : ∀ j, 1 ≤ j → j ≤ n - 2 → gsum n j % n = 0 := fun j h1 h2 =>
    Classical.byContradiction fun h => hno ⟨j, h1, h2, h⟩
  -- the step `j = n - d` adds `d ^ (n - 1) - 1`
  have hj := hz (n - d) (by omega) (by omega)
  have hj0 : gsum n (n - d - 1) % n = 0 := by
    by_cases h0 : n - d - 1 = 0
    · rw [h0]; rfl
    · exact hz _ (by omega) (by omega)
  have e : gsum n (n - d) = gsum n (n - d - 1) + (d ^ (n - 1) - 1) := by
    rw [show n - d = (n - d - 1) + 1 by omega]
    show gsum n (n - d - 1) + ((n - (n - d - 1 + 1)) ^ (n - 1) - 1) = _
    rw [show n - (n - d - 1 + 1) = d by omega, Nat.add_sub_cancel]
  have hm : (d ^ (n - 1) - 1) % n = 0 := by
    rw [e, Nat.add_mod, hj0, Nat.zero_add, Nat.mod_mod] at hj; exact hj
  have hdvd : d ∣ d ^ (n - 1) - 1 :=
    Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hdd) (Nat.dvd_of_mod_eq_zero hm)
  have hdp : d ∣ d ^ (n - 1) := by
    rw [show n - 1 = (n - 2) + 1 by omega, Nat.pow_succ]; exact Nat.dvd_mul_left d _
  have hp1 : 1 ≤ d ^ (n - 1) := Nat.pos_pow_of_pos _ (by omega)
  have h1 : d ∣ 1 := by
    have := Nat.dvd_sub (by omega) hdp hdvd
    rwa [show d ^ (n - 1) - (d ^ (n - 1) - 1) = 1 by omega] at this
  have := Nat.le_of_dvd (by omega) h1
  omega

theorem fl_prime {n : Nat} (hp : Prime n) : fl n (n - 2) = false := by
  cases h : fl n (n - 2)
  · rfl
  · obtain ⟨j, h1, h2, h3⟩ := (fl_iff n (n - 2)).1 h
    exact absurd (gsum_prime hp j h2) h3

/-- the stop condition of round `n` -/
def Bad (n : Nat) : Prop := fl n (n - 2) = true ∧ gsum n (n - 2) % n = 0

theorem bad_iff' {n : Nat} (h3 : 3 ≤ n) : Bad n ↔ ¬ Prime n ∧ n ∣ powSum n (n - 1) + 1 := by
  unfold Bad
  rw [dvd_iff_gsum (by omega)]
  constructor
  · rintro ⟨hf, hg⟩
    refine ⟨fun hp => ?_, hg⟩
    rw [fl_prime hp] at hf; exact Bool.false_ne_true hf
  · rintro ⟨hc, hg⟩; exact ⟨fl_comp h3 hc, hg⟩

/-- 2 and 3 are prime: the search can start at `n = 4` -/
theorem bad_iff : (∃ n, 4 ≤ n ∧ Bad n) ↔ ∃ n, 2 ≤ n ∧ ¬ Prime n ∧ n ∣ powSum n (n - 1) + 1 := by
  constructor
  · rintro ⟨n, h4, hb⟩
    exact ⟨n, by omega, (bad_iff' (by omega)).1 hb⟩
  · rintro ⟨n, h2, hc, hd⟩
    have h4 : 4 ≤ n := by
      refine Classical.byContradiction fun h => hc ?_
      have : n = 2 ∨ n = 3 := by omega
      rcases this with rfl | rfl <;> exact ⟨by omega, by decide⟩
    exact ⟨n, h4, (bad_iff' (by omega)).2 ⟨hc, hd⟩⟩

end TM.AgohGiuga
