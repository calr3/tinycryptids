/-!
# The coprimality walk

The walk `0, k, 2k, …` (mod `r`) reaches `1` before `0` iff `gcd k r = 1` (`first_hit`).
This is the arithmetic of `GCD(D, X)` (`Gcd.lean`), with the list and gcd lemmas it needs
(core Lean has no `Nat.Coprime` API).
-/

namespace TM.ABC

/-! ## lists -/

theorem length_le_of_sub {α : Type} [DecidableEq α] :
    ∀ (l m : List α), l.Nodup → (∀ x ∈ l, x ∈ m) → l.length ≤ m.length := by
  intro l
  induction l with
  | nil => intros; simp
  | cons a l ih =>
    intro m hl hsub
    have ha : a ∈ m := hsub a (List.mem_cons_self a l)
    rw [List.nodup_cons] at hl
    have := ih (m.erase a) hl.2 (fun x hx => by
      rw [List.mem_erase_of_ne (fun e => hl.1 (by rw [← e]; exact hx))]
      exact hsub x (List.mem_cons_of_mem a hx))
    rw [List.length_erase_of_mem ha] at this
    have hpos : 0 < m.length := List.length_pos.mpr (fun e => by simp [e] at ha)
    simp only [List.length_cons]; omega

/-- A duplicate-free list inside `m` with at least `m`'s length contains all of `m`. -/
theorem sub_of_length {α : Type} [DecidableEq α] (l m : List α) (hl : l.Nodup)
    (hsub : ∀ x ∈ l, x ∈ m) (hlen : m.length ≤ l.length) : ∀ x ∈ m, x ∈ l := by
  intro x hx
  refine Classical.byContradiction fun hn => ?_
  have := length_le_of_sub l (m.erase x) hl (fun y hy => by
    rw [List.mem_erase_of_ne (fun e => hn (by rw [← e]; exact hy))]; exact hsub y hy)
  rw [List.length_erase_of_mem hx] at this
  have : 0 < m.length := List.length_pos.mpr (fun e => by simp [e] at hx)
  omega

theorem nodup_map_of_inj {α β : Type} {f : α → β} {l : List α} (hl : l.Nodup)
    (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, ih hl.2 (fun x hx y hy => hf x (List.mem_cons_of_mem a hx) y
      (List.mem_cons_of_mem a hy))⟩
    rw [List.mem_map] at h
    obtain ⟨b, hb, hfb⟩ := h
    have := hf a (List.mem_cons_self a l) b (List.mem_cons_of_mem a hb) hfb.symm
    exact hl.1 (this ▸ hb)

/-! ## gcd -/

theorem gauss {a b c : Nat} (h : Nat.gcd a b = 1) (hd : a ∣ b * c) : a ∣ c := by
  have h1 : a ∣ Nat.gcd (a * c) (b * c) := Nat.dvd_gcd (Nat.dvd_mul_right a c) hd
  rwa [Nat.gcd_mul_right, h, Nat.one_mul] at h1

/-! ## the walk -/

theorem inv_exists {k r : Nat} (hr : 2 ≤ r) (h : Nat.gcd k r = 1) : ∃ j, j < r ∧ j * k % r = 1 := by
  have hinj : ∀ x ∈ List.range r, ∀ y ∈ List.range r, x * k % r = y * k % r → x = y := by
    have key : ∀ x y, x < r → y < r → x ≤ y → x * k % r = y * k % r → x = y := by
      intro x y hx hy hxy e
      have h1 : r ∣ k * (y - x) := by
        rw [Nat.mul_comm, Nat.mul_sub_right_distrib]
        have a1 := Nat.div_add_mod (y * k) r
        have a2 := Nat.div_add_mod (x * k) r
        have : y * k - x * k = r * (y * k / r) - r * (x * k / r) := by omega
        rw [this, ← Nat.mul_sub_left_distrib]
        exact Nat.dvd_mul_right r _
      have h2 : r ∣ y - x := gauss (by rw [Nat.gcd_comm]; exact h) h1
      rcases Nat.eq_zero_or_pos (y - x) with h0 | hpos
      · omega
      · have := Nat.le_of_dvd hpos h2; omega
    intro x hx y hy e
    rw [List.mem_range] at hx hy
    rcases Nat.le_total x y with hxy | hxy
    · exact key x y hx hy hxy e
    · exact (key y x hy hx hxy e.symm).symm
  have hsub := sub_of_length _ (List.range r) (nodup_map_of_inj (List.nodup_range r) hinj)
    (fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨j, _, rfl⟩ := hx
      exact List.mem_range.mpr (Nat.mod_lt _ (by omega)))
    (by rw [List.length_map]; exact Nat.le_refl _)
  have := hsub 1 (List.mem_range.mpr (by omega))
  rw [List.mem_map] at this
  obtain ⟨j, hj, e⟩ := this
  exact ⟨j, List.mem_range.mp hj, e⟩

/-- the walk is at `1` after `j` strides -/
def hitC (k r j : Nat) : Prop := j * k % r = 1 % r
/-- the walk is at `0` after `j` strides -/
def hitN (k r j : Nat) : Prop := j * k % r = 0

/-- At the first stride where the walk is at `0` or `1`, it is at `1` iff `gcd k r = 1`. -/
theorem first_hit {k r j : Nat} (hr : 1 ≤ r) (hj : 1 ≤ j)
    (hfirst : ∀ i, 1 ≤ i → i < j → ¬ hitC k r i ∧ ¬ hitN k r i) :
    (hitC k r j → Nat.gcd k r = 1) ∧ (hitN k r j → ¬ hitC k r j → Nat.gcd k r ≠ 1) := by
  constructor
  · intro hc
    rcases Nat.lt_or_ge r 2 with h1 | h2
    · have : r = 1 := by omega
      subst this; exact Nat.gcd_one_right k
    · have hg : Nat.gcd k r ∣ 1 := by
        have e : j * k % r = 1 := by unfold hitC at hc; rw [Nat.mod_eq_of_lt (by omega : 1 < r)] at hc; exact hc
        have d1 : Nat.gcd k r ∣ j * k := Nat.dvd_trans (Nat.gcd_dvd_left k r) (Nat.dvd_mul_left k j)
        have := (Nat.dvd_mod_iff (Nat.gcd_dvd_right k r)).mpr d1
        rwa [e] at this
      exact Nat.eq_one_of_dvd_one hg
  · intro hn hc hg
    have hr2 : 2 ≤ r := by
      rcases Nat.lt_or_ge r 2 with h1 | h2
      · have : r = 1 := by omega
        subst this; exact absurd (by unfold hitC; simp [Nat.mod_one]) hc
      · exact h2
    have hrj : r ∣ j := gauss (by rw [Nat.gcd_comm]; exact hg)
      (by rw [Nat.mul_comm]; exact Nat.dvd_of_mod_eq_zero hn)
    have hjr : r ≤ j := Nat.le_of_dvd (by omega) hrj
    obtain ⟨i, hi, e⟩ := inv_exists hr2 hg
    have hi1 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; simp at e
      · exact h0
    exact (hfirst i hi1 (by omega)).1 (by unfold hitC; rw [e, Nat.mod_eq_of_lt (by omega)])

/-- the walk is at `0` after `r` strides -/
theorem hitN_r (k r : Nat) : hitN k r r := by
  unfold hitN; exact Nat.mul_mod_right r k

end TM.ABC
