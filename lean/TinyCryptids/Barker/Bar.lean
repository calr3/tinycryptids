import TinyCryptids.Barker.Pass
import TinyCryptids.Defs

/-! # `IsBarker` in terms of `psum` on Booleans -/

namespace TM.Barker
open TinyCryptids

def toI (b : Bool) : Int := if b then 1 else -1

theorem isum_shift (f : Nat → Int) : ∀ n, isum f (n + 1) = f 0 + isum (fun t => f (t + 1)) n
  | 0 => by simp [isum]
  | n + 1 => by
    show isum f (n + 1) + f (n + 1) = _
    rw [isum_shift f n]; simp only [isum]; omega

theorem zipsum : ∀ (u v : List Int), ((u.zip v).map (fun p => p.1 * p.2)).sum =
    isum (fun t => u.getD t 0 * v.getD t 0) (min u.length v.length)
  | [], v => by simp [isum]
  | _ :: _, [] => by simp [isum]
  | a :: u, b :: v => by
    rw [show min (a :: u).length (b :: v).length = min u.length v.length + 1 by simp [Nat.min_def]; split <;> omega,
      isum_shift]
    simp [zipsum u v]

theorem getD_drop (l : List Int) : ∀ k t, (l.drop k).getD t 0 = l.getD (t + k) 0 := by
  induction l with
  | nil => intro k t; simp
  | cons a l ih => intro k t; cases k with
    | zero => rfl
    | succ k => simp only [List.drop_succ_cons]; rw [ih]; rfl

theorem getD_map (b : List Bool) : ∀ t, t < b.length → (b.map toI).getD t 0 = toI (b.getD t false) := by
  induction b with
  | nil => intro t h; simp at h
  | cons c b ih => intro t h; cases t with
    | zero => rfl
    | succ t => exact ih t (by simp at h; omega)

theorem autocorr_psum (b : List Bool) (k : Nat) : autocorr (b.map toI) k = psum b k := by
  unfold autocorr psum
  rw [zipsum, List.length_drop, List.length_map, show min b.length (b.length - k) = b.length - k from Nat.min_eq_right (Nat.sub_le _ _)]
  apply isum_congr; intro t ht
  rw [getD_drop, getD_map _ _ (by omega), getD_map _ _ (by omega)]
  cases b.getD t false <;> cases b.getD (t + k) false <;> rfl

theorem getD_not (b : List Bool) : ∀ t, t < b.length → (b.map not).getD t false = !(b.getD t false) := by
  induction b with
  | nil => intro t h; simp at h
  | cons c b ih => intro t h; cases t with
    | zero => rfl
    | succ t => exact ih t (by simp at h; omega)

theorem psum_not (b : List Bool) (k : Nat) : psum (b.map not) k = psum b k := by
  unfold psum; rw [List.length_map]
  apply isum_congr; intro t ht
  rw [getD_not _ _ (by omega), getD_not _ _ (by omega)]
  cases b.getD t false <;> cases b.getD (t + k) false <;> rfl

/-- a candidate passes every shift -/
def Good (b : List Bool) : Prop :=
  b.head? = some true ∧ 14 ≤ b.length ∧ ∀ k, 1 ≤ k → k < b.length → (psum b k).natAbs ≤ 1

theorem barker_iff : (∃ a : List Int, 13 < a.length ∧ IsBarker a) ↔ ∃ b, Good b := by
  constructor
  · rintro ⟨a, ha, hpm, hc⟩
    let b0 := a.map (fun x => x == 1)
    have hb0 : b0.map toI = a := by
      simp only [b0, List.map_map]
      clear hc ha
      induction a with
      | nil => rfl
      | cons x a ih =>
        simp only [List.map_cons]
        rw [ih (fun y hy => hpm y (List.mem_cons_of_mem _ hy))]
        rcases hpm x (List.mem_cons_self _ _) with h | h <;> subst h <;> rfl
    have hp : ∀ k, 1 ≤ k → k < b0.length → (psum b0 k).natAbs ≤ 1 := by
      intro k h1 h2; rw [← autocorr_psum, hb0]; exact hc k h1 (by simpa [b0] using h2)
    have hl : 14 ≤ b0.length := by simp [b0]; omega
    cases hh : b0.head? with
    | none => simp [b0] at hh; subst hh; simp at ha
    | some c => cases c with
      | true => exact ⟨b0, hh, hl, hp⟩
      | false =>
        refine ⟨b0.map not, ?_, by simpa using hl, ?_⟩
        · rw [List.head?_map, hh]; rfl
        · intro k h1 h2; rw [psum_not]; exact hp k h1 (by simpa using h2)
  · rintro ⟨b, -, hl, hp⟩
    refine ⟨b.map toI, by simp; omega, ?_, ?_⟩
    · intro x hx; obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx; cases c <;> simp [toI]
    · intro k h1 h2; rw [autocorr_psum]; exact hp k h1 (by simpa using h2)

end TM.Barker
