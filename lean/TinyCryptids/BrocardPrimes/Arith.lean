import TinyCryptids.Defs

/-! # Arithmetic for the Brocard machine: primes in divisor form, the descending list of
primes, the split of that list at the marker, and the prime counter. -/

namespace TM.BrocardPrimes

/-- Divisor form of primality (equivalent to `TinyCryptids.Prime`, `primeDvd_iff`). -/
def PrimeDvd (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

theorem primeDvd_iff (p : Nat) : PrimeDvd p ↔ TinyCryptids.Prime p := (TinyCryptids.prime_iff_dvd p).symm

theorem exists_prime_dvd : ∀ n, 2 ≤ n → ∃ p, PrimeDvd p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases hp : PrimeDvd n
    · exact ⟨n, hp, Nat.dvd_refl n⟩
    · have : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
        apply Classical.byContradiction; intro hc
        apply hp; refine ⟨hn, fun d hd => ?_⟩
        apply Classical.byContradiction; intro h2
        exact hc ⟨d, hd, fun e => h2 (Or.inl e), fun e => h2 (Or.inr e)⟩
      obtain ⟨d, hd, h1, hdn⟩ := this
      have hd0 : d ≠ 0 := by rintro rfl; rw [Nat.zero_dvd] at hd; omega
      have hle : d ≤ n := Nat.le_of_dvd (by omega) hd
      obtain ⟨p, hp, hpd⟩ := ih d (by omega) (by omega)
      exact ⟨p, hp, Nat.dvd_trans hpd hd⟩

/-- For `m ≥ 1`: `m+1` is composite iff some prime `p ≤ m` divides it. -/
theorem not_prime_iff (m : Nat) (hm : 1 ≤ m) :
    ¬ PrimeDvd (m+1) ↔ ∃ p, PrimeDvd p ∧ p ≤ m ∧ (m+1) % p = 0 := by
  constructor
  · intro h
    have : ∃ d, d ∣ (m+1) ∧ d ≠ 1 ∧ d ≠ m+1 := by
      apply Classical.byContradiction; intro hc
      apply h; refine ⟨by omega, fun d hd => ?_⟩
      apply Classical.byContradiction; intro h2
      exact hc ⟨d, hd, fun e => h2 (Or.inl e), fun e => h2 (Or.inr e)⟩
    obtain ⟨d, hd, h1, hdn⟩ := this
    have hd0 : d ≠ 0 := by rintro rfl; rw [Nat.zero_dvd] at hd; omega
    have hle : d ≤ m+1 := Nat.le_of_dvd (by omega) hd
    obtain ⟨p, hp, hpd⟩ := exists_prime_dvd d (by omega)
    have hpd' : p ≤ d := Nat.le_of_dvd (by omega) hpd
    exact ⟨p, hp, by omega, Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hpd hd)⟩
  · rintro ⟨p, ⟨hp2, _⟩, hpm, hmod⟩ ⟨_, h⟩
    rcases h p (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega

theorem sq_succ (n : Nat) : (n+1)*(n+1) = n*n + 2*n + 1 := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega

theorem sq_not_prime (n : Nat) (hn : 1 ≤ n) : ¬ PrimeDvd ((n+1)*(n+1)) := by
  rintro ⟨_, h⟩
  have h1 := sq_succ n
  have : n * n ≥ 1 := Nat.mul_le_mul hn hn
  rcases h (n+1) (Nat.dvd_mul_right _ _) with h | h <;> omega

/-- A prime dividing a square `k * k` divides `k`, so it is at most `k`. -/
theorem prime_dvd_sq {p k : Nat} (hp : PrimeDvd p) (hk : 1 ≤ k) (h : (k * k) % p = 0) : p ≤ k := by
  apply Classical.byContradiction; intro hlt
  have hp2 := hp.1
  -- k ≡ k (mod p) with 0 < k < p, and p ∣ k * k: impossible for a prime
  have hd : p ∣ k * k := Nat.dvd_of_mod_eq_zero h
  -- gcd p k = 1 since p prime and p ∤ k
  have hg : Nat.gcd p k = 1 := by
    rcases hp.2 _ (Nat.gcd_dvd_left p k) with h1 | h1
    · exact h1
    · have : p ∣ k := h1 ▸ Nat.gcd_dvd_right p k
      have := Nat.le_of_dvd (by omega) this; omega
  have h1 : p ∣ Nat.gcd (p * k) (k * k) := Nat.dvd_gcd (Nat.dvd_mul_right p k) hd
  rw [Nat.gcd_mul_right, hg, Nat.one_mul] at h1
  have := Nat.le_of_dvd (by omega) h1; omega

/-! ## The list of primes `≤ m`, largest first -/

open Classical in
noncomputable def primesDesc : Nat → List Nat
  | 0 => []
  | k + 1 => if PrimeDvd (k+1) then (k+1) :: primesDesc k else primesDesc k

theorem mem_primesDesc (p : Nat) : ∀ m, p ∈ primesDesc m ↔ PrimeDvd p ∧ p ≤ m := by
  intro m
  induction m with
  | zero =>
    simp only [primesDesc, List.not_mem_nil, false_iff]; rintro ⟨⟨h, _⟩, h'⟩; omega
  | succ k ih =>
    unfold primesDesc
    split
    · rename_i hk
      simp only [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨h1, h2⟩); exact ⟨hk, Nat.le_refl _⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge p (k+1) with h | h
        · exact Or.inr ⟨h1, by omega⟩
        · exact Or.inl (by omega)
    · rename_i hk
      rw [ih]; constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rcases Nat.lt_or_ge p (k+1) with h | h
        · omega
        · obtain rfl : p = k+1 := by omega
          exact absurd h1 hk

theorem primesDesc_prime (m : Nat) (h : PrimeDvd (m+1)) : primesDesc (m+1) = (m+1) :: primesDesc m := by
  simp [primesDesc, h]

theorem primesDesc_comp (m : Nat) (h : ¬ PrimeDvd (m+1)) : primesDesc (m+1) = primesDesc m := by
  simp [primesDesc, h]

/-- Cutting the descending list at `t ≥ s`: the primes above `t`, then those in `(s, t]`. -/
theorem filter_split (s t : Nat) (hst : s ≤ t) : ∀ m,
    (primesDesc m).filter (fun p => decide (s < p)) =
      (primesDesc m).filter (fun p => decide (t < p)) ++
        (primesDesc m).filter (fun p => decide (s < p ∧ p ≤ t)) := by
  intro m
  induction m with
  | zero => rfl
  | succ k ih =>
    by_cases hk : PrimeDvd (k+1)
    · rw [primesDesc_prime k hk]
      by_cases ht : t < k + 1
      · have h1 : decide (s < k + 1) = true := by simp; omega
        have h2 : decide (t < k + 1) = true := by simp; omega
        have h3 : decide (s < k + 1 ∧ k + 1 ≤ t) = false := by simp; omega
        simp only [List.filter_cons, h1, h2, h3, if_true, ih, List.cons_append]; rfl
      · have hall : ∀ p ∈ primesDesc k, ¬ t < p := fun p hp => by
          have := ((mem_primesDesc p k).1 hp).2; omega
        have e1 : (primesDesc k).filter (fun p => decide (t < p)) = [] :=
          List.filter_eq_nil_iff.2 (fun p hp => by simpa using hall p hp)
        rw [e1] at ih
        have h2 : decide (t < k + 1) = false := by simp; omega
        simp only [List.filter_cons, h2, ih, e1, List.nil_append]
        by_cases hs : s < k + 1
        · have h1 : decide (s < k + 1) = true := by simp; omega
          have h3 : decide (s < k + 1 ∧ k + 1 ≤ t) = true := by simp; omega
          simp only [h1, h3, if_true, Bool.false_eq_true, if_false]; rfl
        · have h1 : decide (s < k + 1) = false := by simp; omega
          have h3 : decide (s < k + 1 ∧ k + 1 ≤ t) = false := by simp; omega
          simp only [h1, h3, Bool.false_eq_true, if_false]; rfl
    · rw [primesDesc_comp k hk]; exact ih

/-- Likewise for the primes at most `t`: those in `(s, t]`, then those at most `s`. -/
theorem filter_split_le (s t : Nat) (hst : s ≤ t) : ∀ m,
    (primesDesc m).filter (fun p => decide (p ≤ t)) =
      (primesDesc m).filter (fun p => decide (s < p ∧ p ≤ t)) ++
        (primesDesc m).filter (fun p => decide (p ≤ s)) := by
  intro m
  induction m with
  | zero => rfl
  | succ k ih =>
    by_cases hk : PrimeDvd (k+1)
    · rw [primesDesc_prime k hk]
      by_cases ht : k + 1 ≤ t
      · have h1 : decide (k + 1 ≤ t) = true := by simp; omega
        simp only [List.filter_cons, h1, if_true, ih]
        by_cases hs : k + 1 ≤ s
        · have h2 : decide (s < k + 1 ∧ k + 1 ≤ t) = false := by simp; omega
          have h3 : decide (k + 1 ≤ s) = true := by simp; omega
          have hall : ∀ p ∈ primesDesc k, ¬ (s < p ∧ p ≤ t) := fun p hp => by
            have := ((mem_primesDesc p k).1 hp).2; omega
          have e1 : (primesDesc k).filter (fun p => decide (s < p ∧ p ≤ t)) = [] :=
            List.filter_eq_nil_iff.2 (fun p hp => by simpa using hall p hp)
          simp only [h2, h3, e1, Bool.false_eq_true, if_false, if_true, List.nil_append]
        · have h2 : decide (s < k + 1 ∧ k + 1 ≤ t) = true := by simp; omega
          have h3 : decide (k + 1 ≤ s) = false := by simp; omega
          simp only [h2, h3, Bool.false_eq_true, if_false, if_true, List.cons_append]
      · have h1 : decide (k + 1 ≤ t) = false := by simp; omega
        have h2 : decide (s < k + 1 ∧ k + 1 ≤ t) = false := by simp; omega
        have h3 : decide (k + 1 ≤ s) = false := by simp; omega
        simp only [List.filter_cons, h1, h2, h3, Bool.false_eq_true, if_false, ih]
    · rw [primesDesc_comp k hk]; exact ih

theorem filter_nil_of {m : Nat} {P : Nat → Bool} (h : ∀ p, PrimeDvd p → p ≤ m → P p = false) :
    (primesDesc m).filter P = [] :=
  List.filter_eq_nil_iff.2 (fun p hp => by
    have := (mem_primesDesc p m).1 hp; simp [h p this.1 this.2])

theorem filter_congr' {m : Nat} {P Q : Nat → Bool} (h : ∀ p, PrimeDvd p → p ≤ m → P p = Q p) :
    (primesDesc m).filter P = (primesDesc m).filter Q :=
  List.filter_congr (fun p hp => by have := (mem_primesDesc p m).1 hp; exact h p this.1 this.2)

/-- The only prime in `(t - 1, t]` below `m` is `t` itself, if it is prime. -/
theorem filter_single {m t : Nat} (ht : PrimeDvd t) (htm : t ≤ m) :
    (primesDesc m).filter (fun p => decide (t - 1 < p ∧ p ≤ t)) = [t] := by
  induction m with
  | zero => have := ht.1; omega
  | succ k ih =>
    by_cases hk : PrimeDvd (k+1)
    · rw [primesDesc_prime k hk]
      by_cases he : k + 1 = t
      · subst he
        have h1 : decide (k + 1 - 1 < k + 1 ∧ k + 1 ≤ k + 1) = true := by simp
        simp only [List.filter_cons, h1, if_true]
        rw [filter_nil_of (fun p _ hp => by simp; omega)]
      · have h1 : decide (t - 1 < k + 1 ∧ k + 1 ≤ t) = false := by simp; omega
        simp only [List.filter_cons, h1, Bool.false_eq_true, if_false]
        exact ih (by omega)
    · rw [primesDesc_comp k hk]
      have : t ≠ k + 1 := fun e => hk (e ▸ ht)
      exact ih (by omega)

/-! ## Counting primes -/

/-- the number of primes `≤ x` -/
noncomputable def pc (x : Nat) : Nat := (primesDesc x).length

open Classical in
theorem pc_succ (x : Nat) : pc (x+1) = pc x + (if PrimeDvd (x+1) then 1 else 0) := by
  unfold pc
  by_cases h : PrimeDvd (x+1)
  · rw [primesDesc_prime x h, if_pos h]; rfl
  · rw [primesDesc_comp x h, if_neg h]; rfl

theorem pc_mono (a : Nat) : ∀ j, pc a ≤ pc (a + j)
  | 0 => Nat.le_refl _
  | j + 1 => by
    have := pc_mono a j
    rw [← Nat.add_assoc, pc_succ]; omega

theorem pc_le {a b : Nat} (h : a ≤ b) : pc a ≤ pc b := by
  have := pc_mono a (b - a); rwa [show a + (b - a) = b by omega] at this

theorem pc_eq_primeCount : ∀ x, pc x = TinyCryptids.primeCount x
  | 0 => by
    show (0 : Nat) = TinyCryptids.primeCount 0; decide
  | x + 1 => by
    rw [pc_succ, pc_eq_primeCount x]
    show _ = ((List.range (x + 1 + 1)).filter (fun p => decide (TinyCryptids.Prime p))).length
    rw [List.range_succ (x+1), List.filter_append, List.length_append]
    by_cases h : TinyCryptids.Prime (x + 1)
    · have h' : PrimeDvd (x+1) := (primeDvd_iff _).2 h
      simp [h, h', TinyCryptids.primeCount]
    · have h' : ¬ PrimeDvd (x+1) := fun e => h ((primeDvd_iff _).1 e)
      simp [h, h', TinyCryptids.primeCount]

/-! ## The prime below the current square root, and the counter's base -/

/-- the largest prime `≤ n` (0 if none) -/
noncomputable def lp (n : Nat) : Nat := (primesDesc n).headD 0

open Classical in
theorem lp_succ (n : Nat) : lp (n+1) = if PrimeDvd (n+1) then n+1 else lp n := by
  unfold lp
  by_cases h : PrimeDvd (n+1)
  · rw [primesDesc_prime n h, if_pos h]; rfl
  · rw [primesDesc_comp n h, if_neg h]

theorem lp_spec : ∀ n, 2 ≤ n → PrimeDvd (lp n) ∧ lp n ≤ n ∧ ∀ r, lp n < r → r ≤ n → ¬ PrimeDvd r
  | 0, h | 1, h => absurd h (by omega)
  | n + 1, h => by
    rw [lp_succ]
    by_cases hp : PrimeDvd (n+1)
    · rw [if_pos hp]; exact ⟨hp, Nat.le_refl _, fun r h1 h2 => by omega⟩
    · rw [if_neg hp]
      by_cases h2 : 2 ≤ n
      · obtain ⟨a, b, c⟩ := lp_spec n h2
        refine ⟨a, by omega, fun r h1 h3 => ?_⟩
        rcases Nat.lt_or_ge r (n+1) with hl | hl
        · exact c r h1 (by omega)
        · obtain rfl : r = n + 1 := by omega
          exact hp
      · obtain rfl : n = 1 := by omega
        exact absurd ⟨by omega, fun d hd => by
          have := Nat.le_of_dvd (by omega) hd
          rcases d with _ | _ | _ | d
          · simp at hd
          · exact Or.inl rfl
          · exact Or.inr rfl
          · omega⟩ hp

theorem lp_one : lp 1 = 0 := by
  rw [show (1 : Nat) = 0 + 1 from rfl, lp_succ, if_neg (fun h => by have := h.1; omega)]; rfl

/-- the counter counts the primes above `base n`: the square of the last prime `≥ 3` passed -/
noncomputable def base (n : Nat) : Nat := if 3 ≤ lp n then lp n * lp n else 1

theorem base_le (n : Nat) (hn : 1 ≤ n) : base n ≤ n * n := by
  unfold base
  split
  · rename_i h
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      rw [lp_one] at h; omega
    · have := (lp_spec n h2).2.1; exact Nat.mul_le_mul this this
  · exact Nat.mul_le_mul hn hn

end TM.BrocardPrimes
