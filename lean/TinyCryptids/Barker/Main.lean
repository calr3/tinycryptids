import TinyCryptids.Barker.Seed
import TinyCryptids.Barker.Enum
import TinyCryptids.Barker.Bar

/-!
# The design halts iff a Barker sequence of length > 13 exists
-/

namespace TM.Barker
open TinyCryptids

local notation "F" => false

theorem cand_head (a : List Bool) : Cand a ↔ a.head? = some true := by
  unfold Cand Top; rw [List.getLast?_reverse]

/-- from the pass for shift `k`, if every shift from `k` on passes, the machine halts -/
theorem passes (a : List Bool) : ∀ m k c, a.length - k = m → Start (F :: a) k c → k ≤ a.length →
    (∀ k', k ≤ k' → k' < a.length → (psum a k').natAbs ≤ 1) → HaltAt c := by
  intro m
  induction m with
  | zero => intro k c hm hc hk _; obtain rfl : k = a.length := (by omega); exact round_halt a c hc
  | succ m ih =>
    intro k c hm hc hk hp
    obtain ⟨c', h1, h2⟩ := (round a k c hc (by omega)).1 (hp k (by omega) (by omega))
    exact HaltAt.back h2.reach (ih (k + 1) c' (by omega) h1 (by omega) (fun k' a1 a2 => hp k' (by omega) a2))

/-- from the pass for shift `k`: halt, or reach the next candidate's first pass -/
theorem next_cand (a : List Bool) : ∀ m k c, a.length - k = m → Start (F :: a) k c → k ≤ a.length →
    HaltAt c ∨ ∃ c', Start (F :: inc a) 1 c' ∧ Rch c c' := by
  intro m
  induction m with
  | zero => intro k c hm hc hk; obtain rfl : k = a.length := (by omega); exact Or.inl (round_halt a c hc)
  | succ m ih =>
    intro k c hm hc hk
    have hr := round a k c hc (by omega)
    by_cases hp : (psum a k).natAbs ≤ 1
    · obtain ⟨c', h1, h2⟩ := hr.1 hp
      rcases ih (k + 1) c' (by omega) h1 (by omega) with h | ⟨c'', h3, h4⟩
      · exact Or.inl (HaltAt.back h2.reach h)
      · exact Or.inr ⟨c'', h3, Rch.tr h2.reach h4⟩
    · obtain ⟨c', h1, h2⟩ := hr.2 (by omega)
      exact Or.inr ⟨c', h1, h2.reach⟩

theorem iter_cand (n : Nat) : Cand (iter n a0) ∧ 14 ≤ (iter n a0).length := by
  induction n with
  | zero => exact ⟨a0_cand, by decide⟩
  | succ n ih => have := cand_inc _ ih.1; exact ⟨this.1, by show 14 ≤ (inc _).length; omega⟩

theorem reach_iter (n : Nat) : HaltAt start ∨ ∃ c, Start (F :: iter n a0) 1 c ∧ Rch start c := by
  induction n with
  | zero => obtain ⟨c, h1, h2⟩ := seed; exact Or.inr ⟨c, h1, h2⟩
  | succ n ih =>
    rcases ih with h | ⟨c, h1, h2⟩
    · exact Or.inl h
    · rcases next_cand _ _ 1 c rfl h1 (by have := (iter_cand n).2; omega) with h | ⟨c', h3, h4⟩
      · exact Or.inl (HaltAt.back h2 h)
      · exact Or.inr ⟨c', h3, Rch.tr h2 h4⟩

theorem haltAt_of_good (b : List Bool) (hb : Good b) : HaltAt start := by
  obtain ⟨hh, hl, hp⟩ := hb
  obtain ⟨n, hn⟩ := cover b ((cand_head b).2 hh) hl
  rcases reach_iter n with h | ⟨c, h1, h2⟩
  · exact h
  · rw [show iter n a0 = b from hn] at h1
    exact HaltAt.back h2 (passes b _ 1 c rfl h1 (by omega) (fun k' a1 a2 => hp k' a1 a2))

theorem not_halts (hno : ¬ ∃ b, Good b) : ¬ Halts delta start := by
  let Q : Cfg St → Prop := fun c => ∃ a k, Cand a ∧ 14 ≤ a.length ∧ 1 ≤ k ∧ k ≤ a.length ∧
    (∀ k', 1 ≤ k' → k' < k → (psum a k').natAbs ≤ 1) ∧ Start (F :: a) k c
  have prog : ∀ c, Q c → ∃ c', Q c' ∧ Rch1 c c' := by
    rintro c ⟨a, k, hc, hl, hk1, hk2, hp, hs⟩
    have hk : k < a.length := by
      apply Nat.lt_of_le_of_ne hk2; intro e; subst e
      exact hno ⟨a, (cand_head a).1 hc, hl, hp⟩
    have hr := round a k c hs hk
    by_cases h : (psum a k).natAbs ≤ 1
    · obtain ⟨c', h1, h2⟩ := hr.1 h
      exact ⟨c', ⟨a, k + 1, hc, hl, by omega, by omega,
        fun k' a1 a2 => if e : k' = k then e ▸ h else hp k' a1 (by omega), h1⟩, h2⟩
    · obtain ⟨c', h1, h2⟩ := hr.2 (by omega)
      have := cand_inc a hc
      exact ⟨c', ⟨inc a, 1, this.1, by omega, Nat.le_refl _, by omega, fun k' a1 a2 => by omega, h1⟩, h2⟩
  intro hh
  obtain ⟨c, h1, h2⟩ := seed
  have hc : Q c := ⟨a0, 1, a0_cand, by decide, Nat.le_refl _, by decide, fun k' a1 a2 => by omega, h1⟩
  exact not_halts_of_progress delta Q prog c hc (Sys.Halts.of_reach h2 hh)

theorem halts_iff : Halts delta start ↔ ∃ a : List Int, 13 < a.length ∧ IsBarker a := by
  rw [barker_iff]
  constructor
  · intro h; exact Classical.byContradiction fun hno => not_halts hno h
  · rintro ⟨b, hb⟩; exact (haltAt_of_good b hb).halts

theorem haltAt_of (h : ∃ a : List Int, 13 < a.length ∧ IsBarker a) : HaltAt start :=
  let ⟨b, hb⟩ := barker_iff.1 h; haltAt_of_good b hb

end TM.Barker
