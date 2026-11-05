import TinyCryptids.Carmichael.Totient

/-!
# The arithmetic of the Carmichael machine

* The coprimality test: the walk `0, k, 2k, …` (mod `r`) reaches `1` before `0` iff
  `gcd k r = 1` (`first_hit`).
* `φ(M)` counts the `k ∈ [1, M-1]` with `gcd k (M-k) = 1` (`cp`, `cp_succ`, `cp_self`).
* The window: `nm v N` counts the `M ≤ N` with `φ(M) = v`; with `N ≥ 2 v²` a counterexample to
  Carmichael's conjecture is exactly a `v ≥ 2` with `nm v N = 1` (`exists_iff`).
-/

namespace TM.Carmichael
open TinyCryptids

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

/-! ## counting coprime pairs -/

/-- the `k < K` with `gcd k M = 1` -/
def cp (M K : Nat) : Nat := ((List.range K).filter (fun k => Nat.gcd k M == 1)).length

theorem cp_succ (M K : Nat) : cp M (K + 1) = cp M K + (if Nat.gcd K M = 1 then 1 else 0) := by
  unfold cp
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : Nat.gcd K M = 1 <;> simp [h]

theorem cp_one {M : Nat} (hM : 2 ≤ M) : cp M 1 = 0 := by
  unfold cp; simp; omega

theorem cp_self (M : Nat) : cp M M = totient M := rfl

theorem gcd_sub {k M : Nat} (h : k ≤ M) : Nat.gcd k (M - k) = Nat.gcd k M := by
  rw [Nat.gcd_comm k M, Nat.gcd_comm k (M - k)]
  have := gcd_add_mul_left (M - k) 1 k
  rw [Nat.one_mul, show M - k + k = M by omega] at this
  exact this.symm

/-! ## the window -/

/-- how many `M ≤ N` have `φ(M) = v` -/
def nm (v N : Nat) : Nat := ((List.range (N + 1)).filter (fun M => totient M == v)).length

theorem nm_succ (v N : Nat) : nm v (N + 1) = nm v N + (if totient (N + 1) = v then 1 else 0) := by
  unfold nm
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : totient (N + 1) = v <;> simp [h]

theorem nm_one {v : Nat} (hv : 2 ≤ v) : nm v 1 = 0 := by
  have h0 : totient 0 = 0 := rfl
  have h1 : totient 1 = 1 := rfl
  have a : (0 == v) = false := beq_false_of_ne (by omega)
  have b : (1 == v) = false := beq_false_of_ne (by omega)
  unfold nm; rw [show List.range (1 + 1) = [0, 1] from rfl]
  simp [List.filter, h0, h1, a, b]

theorem totient_pos {m : Nat} (hm : 1 ≤ m) : 1 ≤ totient m := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have : m = 1 := by omega
    subst this; decide
  · rw [← cp_self, show m = (m - 2) + 1 + 1 by omega, cp_succ]
    have := cp_succ ((m - 2) + 1 + 1) 1
    have hmono : ∀ a b, cp ((m - 2) + 1 + 1) a ≤ cp ((m - 2) + 1 + 1) (a + b) := by
      intro a b; induction b with
      | zero => exact Nat.le_refl _
      | succ b ih => rw [← Nat.add_assoc, cp_succ]; omega
    have h1 : Nat.gcd 1 ((m - 2) + 1 + 1) = 1 := Nat.gcd_one_left _
    have := hmono 2 (m - 2)
    rw [show 2 + (m - 2) = (m - 2) + 1 + 1 by omega] at this
    simp only [cp_succ, h1, if_true] at this ⊢
    omega

theorem length_eq_one {l : List Nat} {m : Nat} (hl : l.Nodup) (hall : ∀ x ∈ l, x = m) (hm : m ∈ l) :
    l.length = 1 := by
  have h1 := length_le_of_sub l [m] hl (fun x hx => by rw [hall x hx]; simp)
  have h2 : 0 < l.length := List.length_pos.mpr (fun e => by simp [e] at hm)
  simp at h1; omega

/-- With a window `N ≥ 2 v²` for every `v`, a counterexample to Carmichael's conjecture is a
value `v ≥ 2` taken exactly once in its window. -/
theorem exists_iff (W : Nat → Nat) (hW : ∀ v, 2 ≤ v → 2 * (v * v) ≤ W v) :
    (∃ m, 1 ≤ m ∧ ∀ n, n ≠ m → totient n ≠ totient m) ↔ ∃ v, 2 ≤ v ∧ nm v (W v) = 1 := by
  constructor
  · rintro ⟨m, hm, huniq⟩
    have hv1 := totient_pos hm
    have hv2 : 2 ≤ totient m := by
      refine Classical.byContradiction fun hc => ?_
      have e : totient m = 1 := by omega
      by_cases h1 : m = 1
      · subst h1; exact huniq 2 (by decide) (by rw [e]; rfl)
      · exact huniq 1 (Ne.symm h1) (by rw [e]; rfl)
    refine ⟨totient m, hv2, ?_⟩
    have hmW : m ≤ W (totient m) := Nat.le_trans (totient_bound m hm).1 (hW _ hv2)
    refine length_eq_one (m := m) ((List.nodup_range _).filter _) (fun x hx => ?_) ?_
    · rw [List.mem_filter, beq_iff_eq] at hx
      exact Classical.byContradiction fun hne => huniq x hne hx.2
    · rw [List.mem_filter, List.mem_range, beq_iff_eq]; exact ⟨by omega, rfl⟩
  · rintro ⟨v, hv, h1⟩
    have hne : ((List.range (W v + 1)).filter (fun M => totient M == v)) ≠ [] := by
      intro e; unfold nm at h1; rw [e] at h1; simp at h1
    obtain ⟨m, hmem⟩ := List.exists_mem_of_ne_nil _ hne
    have hm' := hmem
    rw [List.mem_filter, List.mem_range, beq_iff_eq] at hm'
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; have : totient 0 = 0 := rfl; omega
      · exact h0
    refine ⟨m, hm1, fun n hn hnm => ?_⟩
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; have : totient 0 = 0 := rfl; omega
      · exact h0
    have hnW : n ≤ W v := by
      have := (totient_bound n hn1).1; rw [hnm, hm'.2] at this; exact Nat.le_trans this (hW v hv)
    have hsub : ∀ x ∈ [m, n], x ∈ (List.range (W v + 1)).filter (fun M => totient M == v) := by
      intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hmem
      · rw [List.mem_filter, List.mem_range, beq_iff_eq]; exact ⟨by omega, by rw [hnm]; exact hm'.2⟩
    have := length_le_of_sub [m, n] _ (by simp; exact Ne.symm hn) hsub
    unfold nm at h1; simp at this; omega

end TM.Carmichael
