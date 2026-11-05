import TinyCryptids.BrocardPrimes.Blocks
namespace TM.BrocardPrimes
open St

/-! # The scan left to the marker `00100` (after a square), and crossings to the right -/

/-- from the 1 after two 0s, across a block (read leftwards) and the `00` left of it -/
theorem ls_blk (a b : Nat) (s R : Strm) :
    Rch (cfgL lc (blkR a b (F ::: F ::: s)) R) (cfgL lc s (F ::: F ::: blk a b R)) := by
  unfold blkR blk
  cases b with
  | zero =>
    simp only [ones_zero]
    gL; gL; cases a with
    | zero => simp only [ones_zero]; gL; gL; gL; fin
    | succ a => rw [ones_succ]; gL; sLn a; gL; gL; gL; simp only [ones_succ, ones_cons_true]; fin
  | succ b =>
    rw [ones_succ]; gL; gL; sLn b; gL; rw [ones_cons_true a]; gL; sLn a; gL; gL
    simp only [ones_succ, ones_cons_true]; fin

/-- across a processed zone `00 B 00 B … 00 B 00` from its right end -/
theorem ls_zone (l : List (Nat × Nat)) : ∀ (L0 R : Strm),
    Rch (cfgL la (pzR l (F ::: F ::: L0)) R) (cfgL lc L0 (F ::: F ::: pz l R)) := by
  induction l with
  | nil => intro L0 R; simp only [pzR, pz]; gL; gL; fin
  | cons x l ih =>
    intro L0 R
    obtain ⟨a, b⟩ := x
    simp only [pzR]
    refine Rch.tr (ih _ R) ?_
    exact ls_blk a b L0 _

end TM.BrocardPrimes
