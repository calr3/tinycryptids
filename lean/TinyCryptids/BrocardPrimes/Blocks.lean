import TinyCryptids.BrocardPrimes.Sweep
import TinyCryptids.BrocardPrimes.Arith
namespace TM.BrocardPrimes

/-! # The blocks of the sieve, split at the marker -/

/-- the block of prime `p` at checkpoint `m`: hole index `p-1-(m % p)`, `m % p` cells after it -/
def pb (m p : Nat) : Nat × Nat := (p - 1 - m % p, m % p)

/-- the marker stands right of the primes above `sv n` (for `n ≥ 2`: those whose square
is above `m`) -/
def sv (n : Nat) : Nat := max n 2

noncomputable def up (m n : Nat) : List Nat := (primesDesc m).filter (fun p => decide (sv n < p))
noncomputable def lo (m n : Nat) : List Nat := (primesDesc m).filter (fun p => decide (p ≤ sv n))

theorem two_le_of_mem {m p : Nat} {P : Nat → Bool} (h : p ∈ (primesDesc m).filter P) : 2 ≤ p :=
  ((mem_primesDesc p m).1 (List.mem_filter.1 h).1).1.1

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

theorem map_stp' (m : Nat) (P : Nat → Bool) :
    (((primesDesc m).filter P).map (pb m)).map stp = ((primesDesc m).filter P).map (pb (m+1)) :=
  map_stp m _ (fun _ hp => two_le_of_mem hp)

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

theorem wraps_append (l l' : List (Nat × Nat)) : wraps (l ++ l') = (wraps l || wraps l') := by
  induction l with
  | nil => simp [wraps]
  | cons x l ih => obtain ⟨a, b⟩ := x; simp [wraps, ih, Bool.or_assoc]

/-- the sweep at checkpoint `m` ends in composite mode iff `m+1` is not prime -/
theorem wraps_blocks (m n : Nat) (hm : 1 ≤ m) :
    (wraps ((up m n).map (pb m)) || wraps ((lo m n).map (pb m))) = true ↔ ¬ PrimeDvd (m+1) := by
  rw [Bool.or_eq_true, up, lo, wraps_pb m _ (fun _ hp => two_le_of_mem hp),
    wraps_pb m _ (fun _ hp => two_le_of_mem hp), not_prime_iff m hm]
  constructor
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩) <;>
    · have := (mem_primesDesc p m).1 (List.mem_filter.1 hp).1
      exact ⟨p, this.1, this.2, h⟩
  · rintro ⟨p, h1, h2, h⟩
    have hm : p ∈ primesDesc m := (mem_primesDesc p m).2 ⟨h1, h2⟩
    by_cases hs : sv n < p
    · exact Or.inl ⟨p, List.mem_filter.2 ⟨hm, by simpa using hs⟩, h⟩
    · exact Or.inr ⟨p, List.mem_filter.2 ⟨hm, by simp; omega⟩, h⟩

/-! ## How the lists change -/

theorem up_prime (m n : Nat) (hm : sv n < m + 1) (h : PrimeDvd (m+1)) :
    up (m+1) n = (m+1) :: up m n := by
  unfold up; rw [primesDesc_prime m h]; simp [hm]

theorem lo_prime (m n : Nat) (hm : sv n < m + 1) (h : PrimeDvd (m+1)) :
    lo (m+1) n = lo m n := by
  unfold lo; rw [primesDesc_prime m h, List.filter_cons, if_neg (by simp; omega)]

theorem up_comp (m n : Nat) (h : ¬ PrimeDvd (m+1)) : up (m+1) n = up m n := by
  unfold up; rw [primesDesc_comp m h]

theorem lo_comp (m n : Nat) (h : ¬ PrimeDvd (m+1)) : lo (m+1) n = lo m n := by
  unfold lo; rw [primesDesc_comp m h]

/-- passing a square `(n+1)^2` whose root is not a prime `≥ 3` leaves the split unchanged -/
theorem up_sq (m n : Nat) (h : ¬ (PrimeDvd (n+1) ∧ 2 ≤ n)) : up m (n+1) = up m n := by
  unfold up
  refine filter_congr' (fun p hp _ => ?_)
  simp only [sv, decide_eq_decide]
  by_cases h2 : 2 ≤ n
  · have : p ≠ n + 1 := fun e => h ⟨e ▸ hp, h2⟩
    omega
  · omega

theorem lo_sq (m n : Nat) (h : ¬ (PrimeDvd (n+1) ∧ 2 ≤ n)) : lo m (n+1) = lo m n := by
  unfold lo
  refine filter_congr' (fun p hp _ => ?_)
  simp only [sv, decide_eq_decide]
  by_cases h2 : 2 ≤ n
  · have : p ≠ n + 1 := fun e => h ⟨e ▸ hp, h2⟩
    omega
  · omega

/-- at the square of the prime `n+1 ≥ 3` it moves from the end of `up` to the front of `lo` -/
theorem up_bd (m n : Nat) (hp : PrimeDvd (n+1)) (h2 : 2 ≤ n) (hm : n + 1 ≤ m) :
    up m n = up m (n+1) ++ [n+1] := by
  unfold up
  have e1 : sv n = n := by unfold sv; omega
  have e2 : sv (n+1) = n + 1 := by unfold sv; omega
  rw [e1, e2, filter_split n (n+1) (by omega) m]
  congr 1
  have := filter_single (m := m) hp hm
  simp only [Nat.add_sub_cancel] at this
  exact this

theorem lo_bd (m n : Nat) (hp : PrimeDvd (n+1)) (h2 : 2 ≤ n) (hm : n + 1 ≤ m) :
    lo m (n+1) = (n+1) :: lo m n := by
  unfold lo
  have e1 : sv n = n := by unfold sv; omega
  have e2 : sv (n+1) = n + 1 := by unfold sv; omega
  rw [e1, e2, filter_split_le n (n+1) (by omega) m]
  have := filter_single (m := m) hp hm
  simp only [Nat.add_sub_cancel] at this
  rw [this]; rfl

/-- at a square `(n+1)^2 = m+1` whose root is not a prime `≥ 3`, no prime above the marker
divides `m+1` -/
theorem up_not_dvd (m n : Nat) (hn : 1 ≤ n) (hsq : m + 1 = (n+1)*(n+1))
    (h : ¬ (PrimeDvd (n+1) ∧ 2 ≤ n)) : ∀ p ∈ up m n, (m+1) % p ≠ 0 := by
  intro p hp hd
  have hm := (mem_primesDesc p m).1 (List.mem_filter.1 hp).1
  have hs : sv n < p := by simpa using (List.mem_filter.1 hp).2
  rw [hsq] at hd
  have := prime_dvd_sq hm.1 (by omega) hd
  unfold sv at hs
  have hpn : p = n + 1 := by omega
  subst hpn
  exact h ⟨hm.1, by omega⟩

end TM.BrocardPrimes
