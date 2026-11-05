import TinyCryptids.Barker.Z

/-!
# One pair of the pass

The positions (the dummy first) are `A ++ [x] ++ B ++ [y] ++ C`, the markers `i` on `x` and
`j` on `y`. `P A x B y C S` is the loop's checkpoint: `Ia` on the element of `A`'s last
position, `i` just unmarked, the counter `S`. One pair compares `x` with `y`, moves both
markers one position left and adds `±1` to the counter.
-/

namespace TM.Barker
open St

local notation "F" => false
local notation "T" => true

def P (A : List Bool) (x : Bool) (B : List Bool) (y : Bool) (C : List Bool) (S : Int) : Cfg St :=
  cfgL Ia (UL A blank) (T ::: x ::: app (U B) (F ::: y ::: app (U C) (Zt S)))

/-- `+1` for equal elements, `-1` for different ones -/
def sgn (x y : Bool) : Int := if x = y then 1 else -1

theorem pair (A' : List Bool) (w x : Bool) (B : List Bool) (y : Bool) (C : List Bool) (S : Int)
    (B' : List Bool) (y' : Bool) (hB : B' ++ [y'] = x :: B) :
    Rch (P (A' ++ [w]) x B y C S) (P A' w B' y' (y :: C) (S + sgn x y)) := by
  unfold P
  rw [UL_snoc]
  have key : ∀ (qp qa : St), delta qp T = some (T, Dir.R, qa) →
      (∀ b, delta qa b = some (b, Dir.R, qp)) → ∀ (L R : Strm) (l : List Bool),
      Rch ⟨qp, L, app (U l) R⟩ ⟨qp, UL l L, R⟩ := fun qp qa hp ha L R l => scanUR ha hp l L R
  have keyL : ∀ (qa qp : St), (∀ b, delta qa b = some (b, Dir.L, qp)) →
      delta qp T = some (T, Dir.L, qa) → ∀ (s R : Strm) (l : List Bool),
      Rch (cfgL qa (UL l s) R) (cfgL qa s (app (U l) R)) := fun qa qp ha hp s R l => scanUL ha hp l s R
  cases w <;> cases x <;> cases y
  all_goals
    gL; gR; gR; gR; gR
    refine Rch.tr (key _ _ (by rfl) (by intro b; cases b <;> rfl) _ _ B) ?_
    gR; gL; gL
    rw [← UL_cons, ← hB, UL_snoc]
    cases y'
    all_goals
      gL; gR; gR
      refine Rch.tr (key _ _ (by rfl) (by intro b; cases b <;> rfl) _ _ (_ :: C)) ?_
      unfold Zt; gR; gR
      first | refine Rch.tr (zA _ _) ?_ | refine Rch.tr (zD _ _) ?_
      refine Rch.tr (keyL _ _ (fun b => by cases b <;> rfl) (by rfl) _ _ (_ :: C)) ?_
      gL; gL
      refine Rch.tr (keyL _ _ (fun b => by cases b <;> rfl) (by rfl) _ _ B') ?_
      gL; gL; fin

end TM.Barker
