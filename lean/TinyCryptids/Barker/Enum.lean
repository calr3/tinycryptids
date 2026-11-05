import TinyCryptids.Barker.Spec

/-!
# The candidates: `inc` from `1 0^13` reaches every list starting with `1` of length ≥ 14
-/

namespace TM.Barker

/-- the value of a reversed list (least significant first) -/
def valR : List Bool → Nat
  | [] => 0
  | b :: r => (if b then 1 else 0) + 2 * valR r

def binR (n : Nat) : List Bool :=
  if h : n = 0 then [] else (n % 2 == 1) :: binR (n / 2)
termination_by n
decreasing_by omega

theorem valR_incR : ∀ r, valR (incR r) = valR r + 1
  | [] => rfl
  | false :: r => by simp [incR, valR]; omega
  | true :: r => by simp [incR, valR, valR_incR r]; omega

/-- "ends in a 1": no leading zero in the usual order -/
def Top (r : List Bool) : Prop := r.getLast? = some true

theorem top_cons (b : Bool) (r : List Bool) (h : r ≠ []) : Top (b :: r) ↔ Top r := by
  unfold Top; cases r with
  | nil => exact absurd rfl h
  | cons c r => simp [List.getLast?_cons_cons]

theorem valR_pos : ∀ r, Top r → 1 ≤ valR r
  | [], h => by simp [Top] at h
  | [b], h => by simp [Top] at h; subst h; simp [valR]
  | b :: c :: r, h => by
    have := valR_pos (c :: r) ((top_cons b (c :: r) (by simp)).1 h)
    simp only [valR] at this ⊢; omega

theorem binR_valR : ∀ r, Top r → binR (valR r) = r
  | [], h => by simp [Top] at h
  | [b], h => by
    simp [Top] at h; subst h
    show binR 1 = [true]
    rw [binR, dif_neg (by omega)]; simp; rw [binR, dif_pos rfl]
  | b :: c :: r, h => by
    have ht := (top_cons b (c :: r) (by simp)).1 h
    have ih := binR_valR (c :: r) ht
    have hp := valR_pos (c :: r) ht
    rw [binR, dif_neg (by simp only [valR] at hp ⊢; omega)]
    have e1 : valR (b :: c :: r) / 2 = valR (c :: r) := by
      show ((if b then 1 else 0) + 2 * valR (c :: r)) / 2 = _; cases b <;> simp <;> omega
    have e2 : (valR (b :: c :: r) % 2 == 1) = b := by
      show (((if b then 1 else 0) + 2 * valR (c :: r)) % 2 == 1) = b; cases b <;> simp <;> omega
    rw [e1, e2, ih]

theorem top_incR : ∀ r, (r = [] ∨ Top r) → Top (incR r)
  | [], _ => rfl
  | false :: r, h => by
    rcases h with h | h; · simp at h
    cases r with
    | nil => rfl
    | cons c r => exact (top_cons true (c :: r) (by simp)).2 ((top_cons false (c :: r) (by simp)).1 h)
  | true :: r, h => by
    have h' : r = [] ∨ Top r := by
      rcases h with h | h; · simp at h
      cases r with
      | nil => exact Or.inl rfl
      | cons c r => exact Or.inr ((top_cons true (c :: r) (by simp)).1 h)
    have := top_incR r h'
    show Top (false :: incR r)
    have hne : incR r ≠ [] := by intro e; rw [e] at this; simp [Top] at this
    exact (top_cons false _ hne).2 this

theorem len_incR : ∀ r, r.length ≤ (incR r).length
  | [] => by simp [incR]
  | false :: r => by simp [incR]
  | true :: r => by simp [incR]; exact len_incR r

theorem pow_le_valR : ∀ r, Top r → 2 ^ (r.length - 1) ≤ valR r
  | [], h => by simp [Top] at h
  | [b], h => by simp [Top] at h; subst h; simp [valR]
  | b :: c :: r, h => by
    have := pow_le_valR (c :: r) ((top_cons b (c :: r) (by simp)).1 h)
    simp only [List.length_cons, valR] at this ⊢
    rw [show r.length + 1 + 1 - 1 = (r.length + 1 - 1) + 1 by omega, Nat.pow_succ]; omega

/-- `inc` applied `n` times -/
def iter : Nat → List Bool → List Bool
  | 0, a => a
  | n + 1, a => inc (iter n a)

/-- the candidates, in the usual order: first element 1 -/
def Cand (a : List Bool) : Prop := Top a.reverse

theorem cand_inc (a : List Bool) (h : Cand a) : Cand (inc a) ∧ a.length ≤ (inc a).length := by
  unfold Cand inc; rw [List.reverse_reverse]
  refine ⟨top_incR _ (Or.inr h), ?_⟩
  have := len_incR a.reverse; simp at this ⊢; exact this

theorem a0_cand : Cand (true :: List.replicate 13 false) := rfl

theorem cover (b : List Bool) (hb : Cand b) (hl : 14 ≤ b.length) :
    ∃ n, iter n (true :: List.replicate 13 false) = b := by
  have v0 : valR (true :: List.replicate 13 false).reverse = 2 ^ 13 := by decide
  have vb := pow_le_valR b.reverse hb
  rw [List.length_reverse] at vb
  have : 2 ^ 13 ≤ 2 ^ (b.length - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨valR b.reverse - 2 ^ 13, ?_⟩
  have key : ∀ n, Cand (iter n (true :: List.replicate 13 false)) ∧
      valR (iter n (true :: List.replicate 13 false)).reverse = 2 ^ 13 + n := by
    intro n
    induction n with
    | zero => exact ⟨a0_cand, v0⟩
    | succ n ih =>
      show Cand (inc (iter n _)) ∧ valR (inc (iter n _)).reverse = _
      refine ⟨(cand_inc _ ih.1).1, ?_⟩
      unfold inc; rw [List.reverse_reverse, valR_incR, ih.2]; omega
  obtain ⟨k1, k2⟩ := key (valR b.reverse - 2 ^ 13)
  rw [show 2 ^ 13 + (valR b.reverse - 2 ^ 13) = valR b.reverse by omega] at k2
  have := congrArg binR k2
  rw [binR_valR _ k1, binR_valR _ hb] at this
  simpa using congrArg List.reverse this

end TM.Barker
