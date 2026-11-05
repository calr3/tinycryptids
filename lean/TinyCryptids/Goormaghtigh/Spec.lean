import TinyCryptids.Defs

/-!
# The search, in numbers

For each `V` the machine walks `r = 1, b + 1, b² + b + 1, …` (`r ↦ r * b + 1`, `it`) for
the bases `b = 2 .. V - 2`; base `b` is a *hit* if the walk reaches `V`, i.e. `V` is a
repunit in base `b` (`hit_iff`). `hc V b` counts the hits among the bases `2 .. b - 1`;
`V` is *bad* if it has two hits, and `gc V` counts the bad values below `V`. The machine
halts at the third bad value; 31 and 8191 are the first two.
-/

namespace TM.Goormaghtigh
open TinyCryptids

/-! ## walks -/

/-- `j` steps `r ↦ r * b + 1` from `r` -/
def it (b : Nat) : Nat → Nat → Nat
  | 0, r => r
  | j + 1, r => it b j (r * b + 1)

/-- the walk from `r` reaches `V` -/
def HitFrom (b V r : Nat) : Prop := ∃ j, it b j r = V

/-- `V` is a repunit in base `b` -/
def Hit (b V : Nat) : Prop := HitFrom b V 1

theorem it_ge {b : Nat} (hb : 1 ≤ b) : ∀ j r, r ≤ it b j r
  | 0, _ => Nat.le_refl _
  | j + 1, r => by
    have := it_ge hb j (r * b + 1)
    have : r ≤ r * b + 1 := by have := Nat.le_mul_of_pos_right r hb; omega
    show r ≤ it b j (r * b + 1); omega

theorem hitFrom_self (b V : Nat) : HitFrom b V V := ⟨0, rfl⟩

theorem hitFrom_step {b V r : Nat} (h : r ≠ V) : HitFrom b V r ↔ HitFrom b V (r * b + 1) := by
  constructor
  · rintro ⟨j, hj⟩
    cases j with
    | zero => exact absurd hj h
    | succ j => exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩; exact ⟨j + 1, hj⟩

theorem not_hitFrom_gt {b V r : Nat} (hb : 1 ≤ b) (h : V < r) : ¬ HitFrom b V r := by
  rintro ⟨j, hj⟩; have := it_ge hb j r; omega

/-! ## repunits -/

theorem rep_succ' (b : Nat) : ∀ k, rep b (k + 1) = rep b k * b + 1
  | 0 => by simp [rep]
  | k + 1 => by
    have ih := rep_succ' b k
    have e1 : rep b (k + 1 + 1) = rep b (k + 1) + b ^ (k + 1) := rfl
    have e2 : rep b (k + 1) = rep b k + b ^ k := rfl
    rw [e1, e2, Nat.pow_succ, Nat.add_mul]
    rw [e2] at ih
    omega

theorem rep_one (b : Nat) : rep b 1 = 1 := by simp [rep]

theorem rep_two (b : Nat) : rep b 2 = b + 1 := by simp [rep]; omega

theorem rep_three (b : Nat) : rep b 3 = b * b + b + 1 := by
  simp [rep, Nat.pow_succ]; omega

theorem rep_lt_succ {b : Nat} (hb : 1 ≤ b) (k : Nat) : rep b k < rep b (k + 1) := by
  have : rep b (k + 1) = rep b k + b ^ k := rfl
  have := Nat.pos_pow_of_pos k hb
  omega

theorem rep_mono {b : Nat} (hb : 1 ≤ b) {k : Nat} : ∀ {k'}, k ≤ k' → rep b k ≤ rep b k'
  | 0, h => by rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | k' + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h | h
    · exact Nat.le_trans (rep_mono hb (Nat.le_of_lt_succ h)) (Nat.le_of_lt (rep_lt_succ hb k'))
    · rw [h]; exact Nat.le_refl _

theorem it_rep (b : Nat) : ∀ j k, it b j (rep b (k + 1)) = rep b (j + k + 1)
  | 0, k => by simp [it]
  | j + 1, k => by
    show it b j (rep b (k + 1) * b + 1) = _
    rw [← rep_succ', it_rep b j (k + 1)]
    congr 1; omega

theorem hit_iff (b V : Nat) : Hit b V ↔ ∃ m, 1 ≤ m ∧ rep b m = V := by
  have e : ∀ j, it b j 1 = rep b (j + 1) := fun j => by
    have := it_rep b j 0; rwa [rep_one] at this
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j + 1, by omega, by rw [← e]; exact hj⟩
  · rintro ⟨m, hm, h⟩
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    exact ⟨j, by rw [e]; exact h⟩

/-! ## counting hits and bad values -/

open Classical in
/-- hits among the bases `2 .. b - 1` -/
noncomputable def hc (V : Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => hc V b + if 2 ≤ b ∧ Hit b V then 1 else 0

/-- `V` has two hits among the bases `2 .. V - 2` -/
def bad (V : Nat) : Prop := 2 ≤ hc V (V - 1)

open Classical in
/-- bad values below `V` -/
noncomputable def gc : Nat → Nat
  | 0 => 0
  | V + 1 => gc V + if bad V then 1 else 0

theorem hc_one (V : Nat) : ∀ n, 1 ≤ hc V n ↔ ∃ y, 2 ≤ y ∧ y < n ∧ Hit y V
  | 0 => by simp [hc]
  | n + 1 => by
    have ih := hc_one V n
    show 1 ≤ hc V n + _ ↔ _
    by_cases h : 2 ≤ n ∧ Hit n V
    · rw [if_pos h]; exact ⟨fun _ => ⟨n, h.1, by omega, h.2⟩, fun _ => by omega⟩
    · rw [if_neg h, Nat.add_zero, ih]
      constructor
      · rintro ⟨y, h1, h2, h3⟩; exact ⟨y, h1, by omega, h3⟩
      · rintro ⟨y, h1, h2, h3⟩
        refine ⟨y, h1, ?_, h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | h2
        · exact h2
        · subst h2; exact absurd ⟨h1, h3⟩ h

theorem hc_two (V : Nat) : ∀ n, 2 ≤ hc V n ↔
    ∃ x y, 2 ≤ y ∧ y < x ∧ x < n ∧ Hit x V ∧ Hit y V
  | 0 => by simp [hc]
  | n + 1 => by
    have ih := hc_two V n
    have ih1 := hc_one V n
    show 2 ≤ hc V n + _ ↔ _
    by_cases h : 2 ≤ n ∧ Hit n V
    · rw [if_pos h]
      constructor
      · intro h2
        obtain ⟨y, h1, h2, h3⟩ := ih1.1 (by omega)
        exact ⟨n, y, h1, h2, by omega, h.2, h3⟩
      · rintro ⟨x, y, h1, h2, h3, h4, h5⟩
        have := ih1.2 ⟨y, h1, by omega, h5⟩; omega
    · rw [if_neg h, Nat.add_zero, ih]
      constructor
      · rintro ⟨x, y, h1, h2, h3, h4, h5⟩; exact ⟨x, y, h1, h2, by omega, h4, h5⟩
      · rintro ⟨x, y, h1, h2, h3, h4, h5⟩
        refine ⟨x, y, h1, h2, ?_, h4, h5⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h3 with h3 | h3
        · exact h3
        · subst h3; exact absurd ⟨by omega, h4⟩ h

theorem bad_iff (V : Nat) : bad V ↔ ∃ x y, 2 ≤ y ∧ y < x ∧ x + 2 ≤ V ∧ Hit x V ∧ Hit y V := by
  unfold bad; rw [hc_two]
  constructor
  · rintro ⟨x, y, h1, h2, h3, h4, h5⟩; exact ⟨x, y, h1, h2, by omega, h4, h5⟩
  · rintro ⟨x, y, h1, h2, h3, h4, h5⟩; exact ⟨x, y, h1, h2, by omega, h4, h5⟩

theorem bad_31 : bad 31 := (bad_iff 31).2 ⟨5, 2, by decide, by decide, by decide, ⟨2, rfl⟩, ⟨4, rfl⟩⟩

theorem bad_8191 : bad 8191 :=
  (bad_iff 8191).2 ⟨90, 2, by decide, by decide, by decide, ⟨2, rfl⟩, ⟨12, rfl⟩⟩

/-- the statement in terms of bad values -/
theorem conj_iff : (∃ x y m n, 1 < y ∧ y < x ∧ 2 < m ∧ 2 < n ∧ rep x m = rep y n ∧
    rep x m ≠ 31 ∧ rep x m ≠ 8191) ↔ ∃ V, bad V ∧ V ≠ 31 ∧ V ≠ 8191 := by
  constructor
  · rintro ⟨x, y, m, n, hy, hyx, hm, hn, he, h31, h8191⟩
    refine ⟨rep x m, (bad_iff _).2 ⟨x, y, by omega, hyx, ?_, (hit_iff _ _).2 ⟨m, by omega, rfl⟩,
      (hit_iff _ _).2 ⟨n, by omega, he.symm⟩⟩, h31, h8191⟩
    have h3 : rep x 3 ≤ rep x m := rep_mono (by omega) (by omega)
    have : 1 ≤ x * x := Nat.mul_le_mul (show 1 ≤ x by omega) (show 1 ≤ x by omega)
    rw [rep_three] at h3; omega
  · rintro ⟨V, hb, h31, h8191⟩
    obtain ⟨x, y, h1, h2, h3, h4, h5⟩ := (bad_iff V).1 hb
    obtain ⟨m, hm, em⟩ := (hit_iff _ _).1 h4
    obtain ⟨n, hn, en⟩ := (hit_iff _ _).1 h5
    have big : ∀ b k, 2 ≤ b → b + 2 ≤ V → 1 ≤ k → rep b k = V → 2 < k := by
      intro b k hb hbV hk e
      refine Classical.byContradiction fun hk' => ?_
      rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
      · rw [rep_one] at e; omega
      · rw [rep_two] at e; omega
    exact ⟨x, y, m, n, by omega, h2, big x m (by omega) h3 hm em, big y n h1 (by omega) hn en,
      by rw [em, en], by rw [em]; exact h31, by rw [em]; exact h8191⟩

theorem gc_mono : ∀ a d, gc a ≤ gc (a + d)
  | _, 0 => Nat.le_refl _
  | a, d + 1 => by
    have := gc_mono a d
    show gc a ≤ gc (a + d) + _; omega

open Classical in
theorem gc_succ_bad {V : Nat} (h : bad V) : gc (V + 1) = gc V + 1 := by
  show gc V + _ = _; rw [if_pos h]

open Classical in
/-- the third bad value -/
theorem third_iff : (∃ V, bad V ∧ gc V = 2) ↔ ∃ V, bad V ∧ V ≠ 31 ∧ V ≠ 8191 := by
  constructor
  · rintro ⟨V, hb, hg⟩
    refine Classical.byContradiction fun hno => ?_
    have only : ∀ W, bad W → W = 31 ∨ W = 8191 := fun W hW =>
      Classical.byContradiction fun h => hno ⟨W, hW, by omega, by omega⟩
    have bound : ∀ W, gc W + (if W ≤ 31 then 2 else if W ≤ 8191 then 1 else 0) ≤ 2 := by
      intro W
      induction W with
      | zero => simp [gc]
      | succ W ih =>
        show gc W + (if bad W then 1 else 0) + _ ≤ 2
        by_cases hW : bad W
        · rw [if_pos hW]
          rcases only W hW with rfl | rfl <;> simp at ih ⊢ <;> omega
        · rw [if_neg hW]
          split at ih <;> split <;> (try split at ih) <;> (try split) <;> omega
    have := bound V
    rcases only V hb with rfl | rfl <;> simp at this <;> omega
  · rintro ⟨W, hW, h31, h8191⟩
    have three : ∀ a b c, a < b → b < c → bad a → bad b → bad c → 3 ≤ gc (c + 1) := by
      intro a b c hab hbc ha hb hc
      have e1 := gc_succ_bad ha
      have e2 := gc_succ_bad hb
      have e3 := gc_succ_bad hc
      have m1 := gc_mono (a + 1) (b - (a + 1))
      have m2 := gc_mono (b + 1) (c - (b + 1))
      rw [show a + 1 + (b - (a + 1)) = b by omega] at m1
      rw [show b + 1 + (c - (b + 1)) = c by omega] at m2
      omega
    have hM : ∃ M, 3 ≤ gc M := by
      rcases Nat.lt_or_ge W 31 with h | h
      · exact ⟨_, three W 31 8191 h (by decide) hW bad_31 bad_8191⟩
      rcases Nat.lt_or_ge W 8191 with h' | h'
      · exact ⟨_, three 31 W 8191 (by omega) h' bad_31 hW bad_8191⟩
      · exact ⟨_, three 31 8191 W (by decide) (by omega) bad_31 bad_8191 hW⟩
    obtain ⟨M, hM⟩ := hM
    clear h31 h8191 hW
    induction M with
    | zero => simp [gc] at hM
    | succ M ih =>
      by_cases h : 3 ≤ gc M
      · exact ih h
      · refine ⟨M, ?_, ?_⟩
        · refine Classical.byContradiction fun hb => ?_
          have : gc (M + 1) = gc M := by show gc M + _ = _; rw [if_neg hb, Nat.add_zero]
          omega
        · have : gc (M + 1) ≤ gc M + 1 := by
            show gc M + _ ≤ _; split <;> omega
          omega

end TM.Goormaghtigh
