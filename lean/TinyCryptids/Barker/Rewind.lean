import TinyCryptids.Barker.Pair

/-!
# End of a pass and the rewind

`Rw A x B y C S`: `RJa` on `x`'s element, `x` marked (`i`), `y` marked (`j`), positions
`A ++ [x] ++ B ++ [y] ++ C`. Each round moves `j` one position right (halting if there is none),
and then, unless `j` is now the last position, `i` too. When `j` is the last position, the check
starts: `Kc A x M z S` is `K0` on the counter's first cell, `i` on `x`, `j` on the last position `z`.
-/

namespace TM.Barker
open St

local notation "F" => false
local notation "T" => true

def Rw (A : List Bool) (x : Bool) (B : List Bool) (y : Bool) (C : List Bool) (S : Int) : Cfg St :=
  ⟨RJa, F ::: UL A blank, x ::: app (U B) (F ::: y ::: app (U C) (Zt S))⟩

def Kc (A : List Bool) (x : Bool) (M : List Bool) (z : Bool) (S : Int) : Cfg St :=
  ⟨K0, F ::: F ::: z ::: F ::: UL M (x ::: F ::: UL A blank), Zs S⟩

theorem keyR {qp qa : St} (hp : delta qp T = some (T, Dir.R, qa))
    (ha : ∀ b, delta qa b = some (b, Dir.R, qp)) (l : List Bool) (L R : Strm) :
    Rch ⟨qp, L, app (U l) R⟩ ⟨qp, UL l L, R⟩ := scanUR ha hp l L R

theorem keyL {qa qp : St} (ha : ∀ b, delta qa b = some (b, Dir.L, qp))
    (hp : delta qp T = some (T, Dir.L, qa)) (l : List Bool) (s R : Strm) :
    Rch (cfgL qa (UL l s) R) (cfgL qa s (app (U l) R)) := scanUL ha hp l s R

/-- `i` was the dummy: re-mark it and start the rewind -/
theorem pass_end (x : Bool) (B : List Bool) (y : Bool) (C : List Bool) (S : Int) :
    Rch (P [] x B y C S) (Rw [] x B y C S) := by
  unfold P Rw
  show Rch (cfgL Ia (F ::: blank) _) _
  gL; rw [← cons_blank]; gR; gR; gR
  simp only [tl_cons, tl_blank, UL_nil, cons_blank]; fin

theorem rw_step (A : List Bool) (x : Bool) (B : List Bool) (y z z' : Bool) (C : List Bool) (S : Int)
    (b : Bool) (B2 : List Bool) (hb : b :: B2 = B ++ [y]) :
    Rch (Rw A x B y (z :: z' :: C) S) (Rw (A ++ [x]) b B2 z (z' :: C) S) := by
  unfold Rw
  cases x <;> cases y <;> cases z <;> cases z'
  all_goals
    gR
    refine Rch.tr (keyR (by rfl) (fun b => by cases b <;> rfl) B _ _) ?_
    gR; gR; gR; gR; gL; gL; gL
    rw [← UL_snoc]
    refine Rch.tr (keyL (fun b => by cases b <;> rfl) (by rfl) (B ++ [_]) _ _) ?_
    gL; gR; gR
    rw [← hb, appU_cons]
    gR
    rw [UL_snoc]; fin

theorem rw_exit (A : List Bool) (x : Bool) (B : List Bool) (y z : Bool) (S : Int) :
    Rch (Rw A x B y [z] S) (Kc A x (B ++ [y]) z S) := by
  unfold Rw Kc Zt
  cases x <;> cases y <;> cases z
  all_goals
    gR
    refine Rch.tr (keyR (by rfl) (fun b => by cases b <;> rfl) B _ _) ?_
    gR; gR; gR; gR; gR; gR
    rw [UL_snoc]; fin

/-- the run reaches the halting state -/
def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨St.halt, L, R⟩

theorem HaltAt.back {c c' : Cfg St} (h : Rch c c') (h' : HaltAt c') : HaltAt c :=
  let ⟨L, R, hr⟩ := h'; ⟨L, R, Rch.tr h hr⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, hr⟩ := h; Reach.halts delta hr (halt_none rfl)

theorem rw_halt (A : List Bool) (x : Bool) (B : List Bool) (y : Bool) (S : Int) :
    HaltAt (Rw A x B y [] S) := by
  unfold Rw Zt
  cases x <;> cases y
  all_goals
    exact ⟨_, _, Rch.tr (sR (by rfl)) (Rch.tr (keyR (by rfl) (fun b => by cases b <;> rfl) B _ _)
      (Rch.tr (sR (by rfl)) (Rch.tr (sR (by rfl)) (Rch.tr (sR (by rfl)) (Reach.refl delta _)))))⟩

/-- the whole rewind, when `j` is not the last position -/
theorem rewind (C : List Bool) : ∀ (A : List Bool) (x : Bool) (B : List Bool) (y z : Bool) (S : Int),
    ∃ A' x' M, A' ++ x' :: M = A ++ x :: B ++ y :: C ∧ A'.length = A.length + C.length ∧
      Rch (Rw A x B y (C ++ [z]) S) (Kc A' x' M z S) := by
  induction C with
  | nil => intro A x B y z S; exact ⟨A, x, B ++ [y], by simp, by simp, rw_exit A x B y z S⟩
  | cons c C ih =>
    intro A x B y z S
    obtain ⟨b, B2, hb⟩ : ∃ b B2, b :: B2 = B ++ [y] := by
      cases B with
      | nil => exact ⟨y, [], rfl⟩
      | cons b B => exact ⟨b, B ++ [y], rfl⟩
    obtain ⟨z', C', hC⟩ : ∃ z' C', C ++ [z] = z' :: C' := by
      cases C with
      | nil => exact ⟨z, [], rfl⟩
      | cons c' C => exact ⟨c', C ++ [z], rfl⟩
    obtain ⟨A', x', M, h1, h2, h3⟩ := ih (A ++ [x]) b B2 c z S
    refine ⟨A', x', M, ?_, ?_, ?_⟩
    · rw [h1]
      calc (A ++ [x]) ++ b :: B2 ++ c :: C = (A ++ [x]) ++ ((b :: B2) ++ c :: C) := by simp
        _ = (A ++ [x]) ++ ((B ++ [y]) ++ c :: C) := by rw [hb]
        _ = A ++ x :: B ++ y :: c :: C := by simp
    · rw [h2]; simp; omega
    · refine Rch.tr ?_ h3
      have := rw_step A x B y c z' C' S b B2 hb; rw [← hC] at this; exact this

end TM.Barker
