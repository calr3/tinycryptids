import TinyCryptids.Barker.Tac

/-!
# The tape

Every element of the sequence is a cell pair `[p][a]`: `a` the element (`true` = +1), `p = 1`
unmarked, `p = 0` marked. `U l` is a list of unmarked positions, left to right; `UL l s` is the
same placed left of the head (read leftwards, nearest cell first), followed by `s`.
Right of the positions: the gap `0 0`, then the counter `Zs S`.
-/

namespace TM.Barker
open St

local notation "F" => false
local notation "T" => true

/-- unmarked positions, left to right -/
def U : List Bool → List Bool
  | [] => []
  | x :: l => T :: x :: U l

/-- unmarked positions left of the head (read leftwards), then `s` -/
def UL (l : List Bool) (s : Strm) : Strm := app (U l).reverse s

@[simp] theorem U_nil : U [] = [] := rfl
@[simp] theorem U_cons (x : Bool) (l : List Bool) : U (x :: l) = T :: x :: U l := rfl

theorem U_append (l m : List Bool) : U (l ++ m) = U l ++ U m := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

@[simp] theorem UL_nil (s : Strm) : UL [] s = s := rfl

theorem UL_snoc (l : List Bool) (x : Bool) (s : Strm) : UL (l ++ [x]) s = x ::: T ::: UL l s := by
  simp [UL, U_append, app_append]

theorem UL_cons (x : Bool) (l : List Bool) (s : Strm) : UL (x :: l) s = UL l (x ::: T ::: s) := by
  simp [UL, app_append]

theorem UL_append (l m : List Bool) (s : Strm) : UL (l ++ m) s = UL m (UL l s) := by
  simp [UL, U_append, app_append]

theorem appU_cons (x : Bool) (l : List Bool) (s : Strm) :
    app (U (x :: l)) s = T ::: x ::: app (U l) s := rfl

theorem appU_append (l m : List Bool) (s : Strm) : app (U (l ++ m)) s = app (U l) (app (U m) s) := by
  rw [U_append, app_append]

theorem appU_snoc (l : List Bool) (x : Bool) (s : Strm) :
    app (U (l ++ [x])) s = app (U l) (T ::: x ::: s) := by
  rw [appU_append]; rfl

/-- the counter: `S ≤ 0` is `1^(-S)`, `S > 0` is `0 1^S`; blank after it -/
def Zs (S : Int) : Strm := if S ≤ 0 then ones S.natAbs blank else F ::: ones S.natAbs blank

/-- the gap and the counter -/
def Zt (S : Int) : Strm := F ::: F ::: Zs S

/-! ## scanning over unmarked positions -/

/-- a right scanner: `qa` on an element cell moves on, `qp` on an unmarked position moves on -/
theorem scanUR {qa qp : St} (ha : ∀ b, delta qa b = some (b, Dir.R, qp))
    (hp : delta qp T = some (T, Dir.R, qa)) (l : List Bool) (L R : Strm) :
    Rch ⟨qp, L, app (U l) R⟩ ⟨qp, UL l L, R⟩ := by
  induction l generalizing L with
  | nil => fin
  | cons x l ih =>
    rw [appU_cons]
    refine Rch.tr (sR hp) (Rch.tr (sR (ha x)) ?_)
    have := ih (x ::: T ::: L); rwa [← UL_cons] at this

/-- a left scanner, started on an element cell -/
theorem scanUL {qa qp : St} (ha : ∀ b, delta qa b = some (b, Dir.L, qp))
    (hp : delta qp T = some (T, Dir.L, qa)) (l : List Bool) (s R : Strm) :
    Rch (cfgL qa (UL l s) R) (cfgL qa s (app (U l) R)) := by
  induction l generalizing s R with
  | nil => fin
  | cons x l ih =>
    rw [UL_cons]
    refine Rch.tr (ih _ _) (Rch.tr (sL (ha x)) (Rch.tr (sL hp) ?_))
    fin

end TM.Barker
