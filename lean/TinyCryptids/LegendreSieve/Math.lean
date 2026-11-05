import TinyCryptids.LegendreSieve.Sweep
import TinyCryptids.Defs
namespace TM.LegendreSieve

/-! ## Elementary number theory (core Lean only) -/

/-- Divisor form of primality, used inside this proof: at least 2, and the only
divisors are 1 and itself. Equivalent to `TinyCryptids.Prime` (`primeDvd_iff`). -/
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

/-! ## The list of primes `≤ m`, largest first, and the blocks of the sieve -/

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

/-- the block of prime `p` at checkpoint `m`: hole index `p-1-(m % p)`, `m % p` cells after it -/
def pb (m p : Nat) : Nat × Nat := (p - 1 - m % p, m % p)

noncomputable def blocks (m : Nat) : List (Nat × Nat) := (primesDesc m).map (pb m)

theorem prime_two_le {p : Nat} (h : PrimeDvd p) : 2 ≤ p := h.1

theorem stp_pb (m p : Nat) (hp : 2 ≤ p) : stp (pb m p) = pb (m+1) p := by
  have hlt := Nat.mod_lt m (show p > 0 by omega)
  unfold pb
  by_cases h : m % p = p - 1
  · have h1 : (m + 1) % p = 0 := by
      rw [Nat.add_mod, h, Nat.mod_eq_of_lt (show 1 < p by omega)]
      rw [show p - 1 + 1 = p by omega, Nat.mod_self]
    rw [h1, h, show p - 1 - (p - 1) = 0 by omega]; rfl
  · have h1 : (m + 1) % p = m % p + 1 := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < p by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1]
    obtain ⟨a, ha⟩ : ∃ a, p - 1 - m % p = a + 1 := ⟨p - 2 - m % p, by omega⟩
    rw [ha]; show (a, m % p + 1) = _; congr 1; omega

theorem map_stp (m : Nat) (l : List Nat) (hl : ∀ p ∈ l, 2 ≤ p) :
    (l.map (pb m)).map stp = l.map (pb (m+1)) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.mem_cons] at hl ⊢
    rw [stp_pb m p (hl p (Or.inl rfl)), ih (fun q hq => hl q (Or.inr hq))]

theorem blocks_map (m : Nat) : (blocks m).map stp = (primesDesc m).map (pb (m+1)) :=
  map_stp m _ (fun p hp => ((mem_primesDesc p m).1 hp).1.1)

theorem wraps_pb (m : Nat) (l : List Nat) (hl : ∀ p ∈ l, 2 ≤ p) :
    wraps (l.map (pb m)) = true ↔ ∃ p ∈ l, (m+1) % p = 0 := by
  induction l with
  | nil => simp [wraps]
  | cons p l ih =>
    simp only [List.map_cons, wraps, pb, Bool.or_eq_true, beq_iff_eq, List.mem_cons] at hl ⊢
    rw [ih (fun q hq => hl q (Or.inr hq))]
    have hp := hl p (Or.inl rfl)
    have hlt := Nat.mod_lt m (show p > 0 by omega)
    have key : p - 1 - m % p = 0 ↔ (m + 1) % p = 0 := by
      constructor
      · intro h
        have h' : m % p = p - 1 := by omega
        rw [Nat.add_mod, h', Nat.mod_eq_of_lt (show 1 < p by omega), show p - 1 + 1 = p by omega,
          Nat.mod_self]
      · intro h
        apply Classical.byContradiction; intro hne
        have : (m + 1) % p = m % p + 1 := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < p by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        omega
    rw [key]
    constructor
    · rintro (h | ⟨q, hq, h⟩); exact ⟨p, Or.inl rfl, h⟩; exact ⟨q, Or.inr hq, h⟩
    · rintro ⟨q, rfl | hq, h⟩; exact Or.inl h; exact Or.inr ⟨q, hq, h⟩

/-- the sweep at checkpoint `m` ends in composite mode iff `m+1` is not prime -/
theorem wraps_blocks (m : Nat) (hm : 1 ≤ m) : wraps (blocks m) = true ↔ ¬ PrimeDvd (m+1) := by
  rw [blocks, wraps_pb m _ (fun p hp => ((mem_primesDesc p m).1 hp).1.1), not_prime_iff m hm]
  constructor
  · rintro ⟨p, hp, h⟩; exact ⟨p, ((mem_primesDesc p m).1 hp).1, ((mem_primesDesc p m).1 hp).2, h⟩
  · rintro ⟨p, h1, h2, h⟩; exact ⟨p, (mem_primesDesc p m).2 ⟨h1, h2⟩, h⟩

theorem blocks_succ_prime (m : Nat) (h : PrimeDvd (m+1)) :
    blocks (m+1) = (m, 0) :: (blocks m).map stp := by
  rw [blocks_map, blocks]
  simp only [primesDesc, if_pos h, List.map_cons, pb, Nat.mod_self]
  congr 1

theorem blocks_succ_comp (m : Nat) (h : ¬ PrimeDvd (m+1)) :
    blocks (m+1) = (blocks m).map stp := by
  rw [blocks_map, blocks]
  simp only [primesDesc, if_neg h]

end TM.LegendreSieve
