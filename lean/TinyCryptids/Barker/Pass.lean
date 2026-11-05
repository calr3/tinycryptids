import TinyCryptids.Barker.Pair
import TinyCryptids.Barker.Spec

/-! # A whole pass: the counter ends at the sum of `sgn` over the pairs at the shift -/

namespace TM.Barker

/-- `f 0 + … + f (n - 1)` -/
def isum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => isum f n + f n

theorem isum_congr {f g : Nat → Int} : ∀ n, (∀ t, t < n → f t = g t) → isum f n = isum g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [isum]; rw [isum_congr n (fun t ht => h t (by omega)), h n (by omega)]

/-- the pairs `(l[t], l[t + k])`, `t + k < l.length`, summed with `sgn` -/
def psum (l : List Bool) (k : Nat) : Int :=
  isum (fun t => sgn (l.getD t false) (l.getD (t + k) false)) (l.length - k)

theorem getD_append_left (l l' : List Bool) (n : Nat) (d : Bool) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  induction l generalizing n with
  | nil => simp at h
  | cons c l ih => cases n with
    | zero => rfl
    | succ n => exact ih n (by simp at h; omega)

theorem getD_append_right (l l' : List Bool) (d : Bool) :
    (l ++ l').getD l.length d = l'.getD 0 d := by
  induction l with
  | nil => rfl
  | cons c l ih => exact ih

theorem psum_snoc (l : List Bool) (y : Bool) (k : Nat) (hk : 1 ≤ k) (hl : k ≤ l.length) :
    psum (l ++ [y]) k = psum l k + sgn (l.getD (l.length - k) false) y := by
  unfold psum
  rw [show (l ++ [y]).length - k = (l.length - k) + 1 by rw [List.length_append, List.length_singleton]; omega]
  simp only [isum]
  congr 1
  · apply isum_congr; intro t ht
    rw [getD_append_left _ _ _ _ (by omega), getD_append_left _ _ _ _ (by omega)]
  · rw [getD_append_left _ _ _ _ (by omega), show l.length - k + k = l.length by omega,
      getD_append_right]; rfl

theorem tail_getD (A' : List Bool) (w x : Bool) (B : List Bool) :
    ((A' ++ w :: x :: B).tail).getD A'.length false = x := by
  cases A' with
  | nil => rfl
  | cons a A'' =>
    show (A'' ++ w :: x :: B).getD (A''.length + 1) false = x
    rw [show A'' ++ w :: x :: B = (A'' ++ [w]) ++ x :: B by simp,
      show A''.length + 1 = (A'' ++ [w]).length by simp, getD_append_right]; rfl

theorem pass_n (n : Nat) : ∀ (A : List Bool), A.length = n → ∀ (x : Bool) (B : List Bool) (y : Bool)
    (C : List Bool) (S : Int), ∃ x0 B0 y0 C0, x0 :: B0 ++ y0 :: C0 = A ++ x :: B ++ y :: C ∧
      B0.length = B.length ∧
      Rch (P A x B y C S) (P [] x0 B0 y0 C0 (S + psum ((A ++ x :: B ++ [y]).tail) (B.length + 1))) := by
  induction n with
  | zero =>
    intro A hA x B y C S
    obtain rfl : A = [] := List.eq_nil_of_length_eq_zero hA
    refine ⟨x, B, y, C, by simp, rfl, ?_⟩
    have : psum (([] ++ x :: B ++ [y]).tail) (B.length + 1) = 0 := by
      unfold psum; simp [isum]
    rw [this, Int.add_zero]; fin
  | succ n ih =>
    intro A hA x B y C S
    obtain ⟨A', w, rfl⟩ := nonempty_snoc A (by intro h; rw [h] at hA; simp at hA)
    obtain ⟨B', y', hB⟩ := nonempty_snoc (x :: B) (by simp)
    obtain ⟨x0, B0, y0, C0, h1, h2, h3⟩ := ih A' (by simp at hA; omega) w B' y' (y :: C) (S + sgn x y)
    have hl : B'.length = B.length := by
      have := congrArg List.length hB; simp at this; omega
    refine ⟨x0, B0, y0, C0, ?_, by rw [h2, hl], Rch.tr (pair A' w x B y C S B' y' hB.symm) ?_⟩
    · rw [h1]
      calc A' ++ w :: B' ++ y' :: y :: C = A' ++ w :: ((B' ++ [y']) ++ y :: C) := by simp
        _ = A' ++ [w] ++ x :: B ++ y :: C := by rw [hB]; simp
    · have e : (A' ++ [w] ++ x :: B ++ [y]).tail = (A' ++ w :: x :: B).tail ++ [y] := by
        cases A' <;> simp
      have e2 : A' ++ w :: B' ++ [y'] = A' ++ w :: x :: B := by
        rw [show A' ++ w :: B' ++ [y'] = A' ++ w :: (B' ++ [y']) by simp, hB]
      rw [e, psum_snoc _ _ _ (by omega) (by cases A' <;> simp <;> omega), show
          (A' ++ w :: x :: B).tail.length - (B.length + 1) = A'.length by cases A' <;> simp <;> omega,
        tail_getD]
      rw [e2, hl] at h3
      have : S + sgn x y + psum (A' ++ w :: x :: B).tail (B.length + 1) =
          S + (psum (A' ++ w :: x :: B).tail (B.length + 1) + sgn x y) := by omega
      rw [← this]; exact h3

end TM.Barker
