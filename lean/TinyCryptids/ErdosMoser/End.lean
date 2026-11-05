import TinyCryptids.ErdosMoser.Compare
namespace TM.ErdosMoser
open St

/-! The end of a pair: A = 0 and R = 1 are written right of M, the marker on M's third cell
from the right (base 1), then the next pair: `(k + 1, m - 1)` (the separator between K and M
moves one cell right) or, after `(k, 1)`, `(2, k)` (K grows by one cell on the left, a new
separator after its fourth cell). -/

macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))
macro "gLb" : tactic => `(tactic| first | gL | (refine blankR ?_; gL))

/-- the start of a pair `(k, m)`: the anchor, the marker on `m` (base 1), A = 0, R = 1 -/
def pairC (k m : Nat) : Cfg St := eAtC k 1 m 1 (rep 1) 1

/-- from the clear (M has `m + 4` cells) to M's cell `m - 1` (state `P5`), A and R written, the
marker placed on cell `m + 1` -/
theorem end_common (k m : Nat) :
    Rch (clrC (true ::: ones (m + 3) (KL k 1)))
      (cfgL P5 (ones m (KL k 1)) (true ::: F ::: true ::: true ::: rgt (rep 1) 1 0)) := by
  unfold clrC
  gRb; gRb; gRb; gRb; gRb; gRb; gRb
  gLb; gL; gL; gL; gL; gL; gL; gL; gL; gL; gL; gL
  unfold rgt sep
  simp [ones_succ, cons_blank]
  fin

/-- `(k, m + 2) → (k + 1, m + 1)` -/
theorem end_shift (k m : Nat) :
    Rch (clrC (true ::: ones (m + 4) (KL k 1))) (pairC (k + 1) (m + 1)) := by
  refine Rch.tr (end_common k (m + 1)) ?_
  unfold KL
  gL
  sLn m
  gL; gR; gR
  rw [ones_cons_true]
  gL; gL
  rw [show k + 1 - 1 = k by omega, tl_cons]
  have e1 : true ::: ones k (F ::: ones 1 blank) = app (rep (k + 1)) (F ::: true ::: blank) := by
    simp [app_replicate, ones_succ, ones_cons_true]
  rw [e1]
  refine Rch.tr (PLG.find (Clean.replicate _) _ _) ?_
  gR
  unfold pairC eAtC
  simp [rgt, sep, app_replicate, List.reverse_replicate, ones_succ, ones_cons_true, cons_blank]
  fin

/-- `(k + 2, 1) → (2, k + 2)` -/
theorem end_reset (k : Nat) :
    Rch (clrC (true ::: ones 3 (KL (k + 2) 1))) (pairC 2 (k + 2)) := by
  refine Rch.tr (end_common (k + 2) 0) ?_
  unfold KL
  rw [show k + 2 + 1 - 1 = k + 2 by omega, ones_zero]
  gL; gL
  sLn (k + 2)
  gL; gL; gL; gR; gR; gR; gR; gR
  rw [ones_succ]
  gR
  rw [ones_cons_true]
  gL; gL
  have e1 : app (List.replicate 2 true) (false ::: true ::: blank) =
      true ::: true ::: false ::: true ::: false ::: tl (tl blank) := by
    simp [app_replicate, ones_succ, cons_blank]
  have := PLG.find (Clean.replicate 2) blank
    (false ::: false ::: ones k (true ::: true ::: F ::: true ::: true ::: rgt (rep 1) 1 0))
  rw [e1] at this
  refine Rch.tr this ?_
  gR
  unfold pairC eAtC
  simp [rgt, sep, app_replicate, List.reverse_replicate, ones_succ, ones_cons_true, cons_blank]
  fin

end TM.ErdosMoser
