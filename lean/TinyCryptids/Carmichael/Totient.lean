import TinyCryptids.Carmichael.Gcd
import TinyCryptids.Carmichael.ListAux

/-!
# Euler's totient: multiplicativity and the bound `n ≤ 2 φ(n)²`
-/

namespace TinyCryptids

theorem totient_eq (n : Nat) : totient n = ((List.range n).filter (fun k => Nat.gcd k n == 1)).length := rfl

theorem totient_one : totient 1 = 1 := rfl

theorem totient_mul {a b : Nat} (h : Nat.gcd a b = 1) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    totient (a * b) = totient a * totient b := by
  let f : Nat → Nat × Nat := fun k => (k % a, k % b)
  let S := (List.range (a * b)).filter (fun k => Nat.gcd k (a * b) == 1)
  let T := (prodList a b).filter (fun xy => (Nat.gcd xy.1 a == 1) && (Nat.gcd xy.2 b == 1))
  have hT : T.length = totient a * totient b :=
    filter_prodList a b (fun x => Nat.gcd x a == 1) (fun y => Nat.gcd y b == 1)
  have hinj : ∀ x ∈ List.range (a * b), ∀ y ∈ List.range (a * b), f x = f y → x = y := by
    intro x hx y hy e
    simp only [f, Prod.mk.injEq] at e
    exact crt_inj h (List.mem_range.mp hx) (List.mem_range.mp hy) e.1 e.2
  have hSnd : (S.map f).Nodup :=
    nodup_map_of_inj ((List.nodup_range _).filter _) (fun x hx y hy => hinj x
      (List.mem_filter.mp hx).1 y (List.mem_filter.mp hy).1)
  have hTnd : T.Nodup := (nodup_prodList a b).filter _
  -- surjectivity of `f` onto the box
  have hsurj : ∀ x ∈ prodList a b, x ∈ (List.range (a * b)).map f := by
    refine sub_of_length _ _ (nodup_map_of_inj (List.nodup_range _) hinj) (fun x hx => ?_) ?_
    · rw [List.mem_map] at hx
      obtain ⟨k, _, rfl⟩ := hx
      exact mem_prodList.mpr ⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega)⟩
    · rw [List.length_map, List.length_range, length_prodList]; exact Nat.le_refl _
  have h1 : S.length ≤ T.length := by
    rw [← List.length_map S f]
    refine length_le_of_sub _ _ hSnd (fun x hx => ?_)
    rw [List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [List.mem_filter, List.mem_range, beq_iff_eq, gcd_mul_eq_one_iff] at hk
    rw [List.mem_filter]
    refine ⟨mem_prodList.mpr ⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega)⟩, ?_⟩
    simp only [f, gcd_mod_left, hk.2.1, hk.2.2, beq_self_eq_true, Bool.and_self]
  have h2 : T.length ≤ S.length := by
    rw [← List.length_map S f]
    refine length_le_of_sub _ _ hTnd (fun x hx => ?_)
    rw [List.mem_filter] at hx
    obtain ⟨hx, hc⟩ := hx
    have := hsurj x hx
    rw [List.mem_map] at this ⊢
    obtain ⟨k, hk, rfl⟩ := this
    refine ⟨k, ?_, rfl⟩
    rw [List.mem_filter, beq_iff_eq, gcd_mul_eq_one_iff]
    simp only [f, gcd_mod_left, Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hk, hc⟩
  show S.length = _
  omega

theorem totient_prime {p : Nat} (hp : Prime p) : totient p = p - 1 := by
  have h2 := hp.two_le
  rw [totient_eq, show p = 1 + (p - 1) by omega, range_add, List.filter_append, List.length_append]
  rw [show 1 + (p - 1) - 1 = p - 1 by omega]
  have e1 : (List.filter (fun k => Nat.gcd k (1 + (p - 1)) == 1) (List.range 1)).length = 0 := by
    simp; omega
  have e2 : (List.filter (fun k => Nat.gcd k (1 + (p - 1)) == 1)
      ((List.range (p - 1)).map (1 + ·))).length = p - 1 := by
    rw [List.filter_map, List.length_map, show 1 + (p - 1) = p by omega]
    rw [List.filter_eq_self.mpr, List.length_range]
    intro j hj
    rw [List.mem_range] at hj
    simp only [Function.comp, beq_iff_eq]
    rw [gcd_prime_eq_one hp]
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  rw [e1, e2, Nat.zero_add]

theorem count_blocks (m : Nat) : ∀ j,
    ((List.range (j * m)).filter (fun k => Nat.gcd k m == 1)).length = j * totient m := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.succ_mul, range_add, List.filter_append, List.length_append, ih, List.filter_map,
      List.length_map, Nat.succ_mul]
    congr 1
    rw [totient_eq]
    congr 2
    funext k
    simp only [Function.comp, Nat.add_comm (j * m) k, gcd_add_mul_left]

theorem totient_mul_of_dvd {p m : Nat} (hp : Prime p) (hm : p ∣ m) : totient (p * m) = p * totient m := by
  rw [totient_eq, ← count_blocks m p]
  suffices e : (fun k => Nat.gcd k (p * m) == 1) = (fun k => Nat.gcd k m == 1) by rw [e]
  funext k
  have : Nat.gcd k (p * m) = 1 ↔ Nat.gcd k m = 1 := by
    constructor
    · intro h; exact gcd_eq_one_of_dvd h (Nat.dvd_mul_left m p)
    · intro h
      refine (gcd_mul_eq_one_iff k p m).mpr ⟨(gcd_prime_eq_one hp).mpr fun hk => ?_, h⟩
      have := Nat.dvd_gcd hk hm
      rw [h] at this
      have := Nat.le_of_dvd (by decide) this; have := hp.two_le; omega
  by_cases hk : Nat.gcd k m = 1
  · rw [hk, this.mpr hk]
  · have h' : Nat.gcd k (p * m) ≠ 1 := fun e => hk (this.mp e)
    rw [beq_false_of_ne h', beq_false_of_ne hk]

theorem exists_prime_dvd : ∀ n, 2 ≤ n → ∃ p, Prime p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h2
    by_cases hp : Prime n
    · exact ⟨n, hp, Nat.dvd_refl n⟩
    · have : ∃ d, d < n ∧ 2 ≤ d ∧ n % d = 0 := by
        exact Classical.byContradiction fun hne => hp ⟨h2, fun d hd h2d hm => hne ⟨d, hd, h2d, hm⟩⟩
      obtain ⟨d, hd, h2d, hm⟩ := this
      obtain ⟨p, hpr, hpd⟩ := ih d hd h2d
      exact ⟨p, hpr, Nat.dvd_trans hpd (Nat.dvd_of_mod_eq_zero hm)⟩

theorem le_sq_sub (p : Nat) (hp : 3 ≤ p) : p ≤ (p - 1) * (p - 1) := by
  have : 2 * (p - 1) ≤ (p - 1) * (p - 1) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **`n ≤ 2 φ(n)²`**, and `n ≤ φ(n)²` for odd `n`. -/
theorem totient_bound : ∀ n, 1 ≤ n →
    n ≤ 2 * (totient n * totient n) ∧ (n % 2 = 1 → n ≤ totient n * totient n) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst h1; rw [totient_one]; omega
    obtain ⟨p, hp, hpn⟩ := exists_prime_dvd n (by omega)
    have hp2 := hp.two_le
    obtain ⟨n', rfl⟩ := hpn
    have hn' : 1 ≤ n' := by rcases n' with _ | n' <;> simp_all
    have hlt : n' < p * n' := by
      have : 2 * n' ≤ p * n' := Nat.mul_le_mul_right _ hp2
      omega
    obtain ⟨ihA, ihB⟩ := ih n' hlt hn'
    generalize ht : totient n' = t at ihA ihB
    have hodd : p * n' % 2 = 1 → n' % 2 = 1 := by
      intro h; rcases Nat.mod_two_eq_zero_or_one n' with e | e
      · have : p * n' % 2 = 0 := by rw [Nat.mul_mod, e, Nat.mul_zero]
        omega
      · exact e
    by_cases hd : p ∣ n'
    · rw [totient_mul_of_dvd hp hd, ht]
      constructor
      · have : p * n' ≤ p * (2 * (t * t)) := Nat.mul_le_mul_left p ihA
        have : p * (2 * (t * t)) ≤ p * (p * (2 * (t * t))) := Nat.le_mul_of_pos_left _ (by omega)
        have e : 2 * (p * t * (p * t)) = p * (p * (2 * (t * t))) := by
          simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        omega
      · intro ho
        have := ihB (hodd ho)
        have : p * n' ≤ p * (t * t) := Nat.mul_le_mul_left p this
        have : p * (t * t) ≤ p * (p * (t * t)) := Nat.le_mul_of_pos_left _ (by omega)
        have e : p * t * (p * t) = p * (p * (t * t)) := by
          simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        omega
    · have hc : Nat.gcd p n' = 1 := by
        rw [Nat.gcd_comm]; exact (gcd_prime_eq_one hp).mpr hd
      rw [totient_mul hc (by omega) hn', totient_prime hp, ht]
      rcases Nat.lt_or_ge p 3 with hp3 | hp3
      · have hp2' : p = 2 := by omega
        subst hp2'
        have hno : n' % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one n' with e | e
          · exact absurd (Nat.dvd_of_mod_eq_zero e) hd
          · exact e
        have := ihB hno
        refine ⟨by simp only [show 2 - 1 = 1 from rfl, Nat.one_mul]; omega, fun ho => ?_⟩
        have : 2 * n' % 2 = 0 := by simp
        omega
      · have hsq := le_sq_sub p hp3
        constructor
        · have : p * n' ≤ (p - 1) * (p - 1) * n' := Nat.mul_le_mul_right _ hsq
          have : (p - 1) * (p - 1) * n' ≤ (p - 1) * (p - 1) * (2 * (t * t)) :=
            Nat.mul_le_mul_left _ ihA
          have e : 2 * ((p - 1) * t * ((p - 1) * t)) = (p - 1) * (p - 1) * (2 * (t * t)) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          omega
        · intro ho
          have := ihB (hodd ho)
          have : p * n' ≤ (p - 1) * (p - 1) * n' := Nat.mul_le_mul_right _ hsq
          have : (p - 1) * (p - 1) * n' ≤ (p - 1) * (p - 1) * (t * t) :=
            Nat.mul_le_mul_left _ (ihB (hodd ho))
          have e : (p - 1) * t * ((p - 1) * t) = (p - 1) * (p - 1) * (t * t) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          omega

end TinyCryptids
