import TinyCryptids.Defs

/-!
# Coprimality facts (core Lean has no `Nat.Coprime` API)
-/

namespace TinyCryptids

theorem gauss {a b c : Nat} (h : Nat.gcd a b = 1) (hd : a ∣ b * c) : a ∣ c := by
  have h1 : a ∣ Nat.gcd (a * c) (b * c) := Nat.dvd_gcd (Nat.dvd_mul_right a c) hd
  rwa [Nat.gcd_mul_right, h, Nat.one_mul] at h1

theorem mul_dvd_of_coprime {a b m : Nat} (h : Nat.gcd a b = 1) (ha : a ∣ m) (hb : b ∣ m) :
    a * b ∣ m := by
  obtain ⟨t, rfl⟩ := ha
  have : b ∣ t := gauss (by rw [Nat.gcd_comm]; exact h) hb
  obtain ⟨u, rfl⟩ := this
  exact ⟨u, by rw [Nat.mul_assoc]⟩

theorem div_mono {x y a : Nat} (h : y ≤ x) : y / a ≤ x / a := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  · exact (Nat.le_div_iff_mul_le ha).mpr (Nat.le_trans (Nat.div_mul_le_self y a) h)

theorem gcd_eq_one_of_dvd {k a b : Nat} (h : Nat.gcd k b = 1) (hab : a ∣ b) : Nat.gcd k a = 1 := by
  have : Nat.gcd k a ∣ Nat.gcd k b := Nat.dvd_gcd (Nat.gcd_dvd_left k a)
    (Nat.dvd_trans (Nat.gcd_dvd_right k a) hab)
  rw [h] at this; exact Nat.eq_one_of_dvd_one this

theorem gcd_mul_eq_one_iff (k a b : Nat) :
    Nat.gcd k (a * b) = 1 ↔ Nat.gcd k a = 1 ∧ Nat.gcd k b = 1 := by
  constructor
  · intro h
    exact ⟨gcd_eq_one_of_dvd h (Nat.dvd_mul_right a b), gcd_eq_one_of_dvd h (Nat.dvd_mul_left b a)⟩
  · rintro ⟨ha, hb⟩
    have hg1 : Nat.gcd (Nat.gcd k (a * b)) a = 1 := by
      have : Nat.gcd (Nat.gcd k (a * b)) a ∣ Nat.gcd k a :=
        Nat.dvd_gcd (Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)) (Nat.gcd_dvd_right _ _)
      rw [ha] at this; exact Nat.eq_one_of_dvd_one this
    have hgb : Nat.gcd k (a * b) ∣ b := gauss hg1 (Nat.gcd_dvd_right _ _)
    have : Nat.gcd k (a * b) ∣ Nat.gcd k b := Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hgb
    rw [hb] at this; exact Nat.eq_one_of_dvd_one this

theorem gcd_mod_left (k a : Nat) : Nat.gcd (k % a) a = Nat.gcd k a := by
  rw [Nat.gcd_comm k a, Nat.gcd_rec a k]

theorem gcd_add_mul_left (k j m : Nat) : Nat.gcd (k + j * m) m = Nat.gcd k m := by
  rw [Nat.gcd_comm, Nat.gcd_add_mul_self, Nat.gcd_comm]

theorem gcd_prime_eq_one {p x : Nat} (hp : Prime p) : Nat.gcd x p = 1 ↔ ¬ p ∣ x := by
  have hd := (prime_iff_dvd p).mp hp
  constructor
  · intro h hpx
    have := Nat.dvd_gcd hpx (Nat.dvd_refl p)
    rw [h] at this; have := Nat.le_of_dvd (by decide) this; have := hp.two_le; omega
  · intro h
    rcases hd.2 _ (Nat.gcd_dvd_right x p) with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ Nat.gcd_dvd_left x p) h

/-- Equal residues modulo coprime `a`, `b` below `a * b` are equal. -/
theorem crt_inj {a b k k' : Nat} (h : Nat.gcd a b = 1) (hk : k < a * b) (hk' : k' < a * b)
    (ha : k % a = k' % a) (hb : k % b = k' % b) : k = k' := by
  have key : ∀ x y, x < a * b → y ≤ x → x % a = y % a → x % b = y % b → x = y := by
    intro x y hx hyx hxa hxb
    have da : a ∣ x - y := by
      have e1 := Nat.mod_add_div x a; have e2 := Nat.mod_add_div y a
      have hle : y / a ≤ x / a := div_mono hyx
      refine ⟨x / a - y / a, ?_⟩
      have e3 : a * (x / a) = a * (y / a) + a * (x / a - y / a) := by
        rw [← Nat.mul_add, Nat.add_sub_cancel' hle]
      omega
    have db : b ∣ x - y := by
      have e1 := Nat.mod_add_div x b; have e2 := Nat.mod_add_div y b
      have hle : y / b ≤ x / b := div_mono hyx
      refine ⟨x / b - y / b, ?_⟩
      have e3 : b * (x / b) = b * (y / b) + b * (x / b - y / b) := by
        rw [← Nat.mul_add, Nat.add_sub_cancel' hle]
      omega
    obtain ⟨t, ht⟩ := mul_dvd_of_coprime h da db
    rcases t with _ | t
    · simp at ht; omega
    · have : a * b ≤ a * b * (t + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
  rcases Nat.le_total k' k with hle | hle
  · exact key k k' hk hle ha hb
  · exact (key k' k hk' hle ha.symm hb.symm).symm

end TinyCryptids
