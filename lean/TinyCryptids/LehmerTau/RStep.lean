import TinyCryptids.LehmerTau.RLoop

/-!
# From one `i` to the next

After the d-loop the frame D is unshifted (`D = 1`, its hole back at cell 1); E tells the
phase: E at rest (3 cells) is the R phase. If Re has more than two cells, `i + 1 < n`: Re gives
a cell to Rd (`ri_next`). Otherwise the L phase starts (`ri_last`, in `LStart.lean`).
-/

namespace TM.LehmerTau
open St

local notation "F" => false

/-- the d-loop is over: D unshifted with its hole, `UK1` on E's cell 0 -/
theorem ud_uk (K : List KB) (a i : Nat) (hi : 1 ≤ i) (B : Strm) :
    Rch (F2 (LS a (.pl 1 :: .pl 13 :: K)) B i)
      ⟨UK1, F ::: F ::: LS a (.pl (i + 1) :: .dg 1 1 :: .pl 1 :: .pl 13 :: K), B⟩ := by
  refine Rch.tr (F2_UN _ _ i hi) ?_
  rw [LS_pl, show ones 1 (F ::: F ::: LS a (.pl 13 :: K)) = true ::: (F ::: F ::: LS a (.pl 13 :: K)) from rfl]
  refine Rch.tr (unshift _ i _ hi) ?_
  rw [ones_add, show i - 1 + 2 = i + 1 by omega]
  gR; gR; gR; gR; gR; gR; gR; gR; gR
  sRn (i + 1); gR; gR
  simp only [LS_pl, LS_dg1]; fin

/-- the next `i` (Re has `j + 1 ≥ 3` cells) -/
theorem ri_next (K : List KB) (a i j : Nat) (hj : 2 ≤ j) :
    Rch ⟨UK1, F ::: F ::: LS a (.pl (i + 1) :: .dg 1 1 :: .pl 1 :: .pl 13 :: K), BD j⟩
      (DV (LS a (.pl 1 :: .pl 13 :: K)) (BD (j - 1)) 1 i) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  unfold BD DV RB
  gR; gR; gR; gR; gR; gR; gR
  gL; gL; gL; gL; gL; gL; gL; gL; gL; gL
  rw [LS_pl]
  sLn (i + 1)
  rw [LS_dg1, LS_pl]
  refine Rch.tr (PPDz.find2 0 0 _ _) ?_
  gL
  simp only [LS_pl, Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega]
  rw [ones_succ' i, ones_add2 i]; fin

end TM.LehmerTau
