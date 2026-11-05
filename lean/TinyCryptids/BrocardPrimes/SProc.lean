import TinyCryptids.BrocardPrimes.Tape
namespace TM.BrocardPrimes
open St

/-! # After the sweep: the square counter S and the counter `1^(c+1)` right of it -/

/-- prime mode: S cannot wrap, its hole moves left; K gains a cell; then home to copy M. -/
theorem s_prime (a b c : Nat) (Lz : Strm) :
    Rch ⟨p3, Lz, F ::: blk (a+1) b (F ::: ones (c+1) blank)⟩
      (cfgL hc1 (ones (c+1) (F ::: blkR a (b+1) (F ::: Lz))) (true ::: blank)) := by
  unfold blk blkR
  gR; sRn (a+2); gR; rw [ones_cons_true b]; gL; gL; gL; rw [ones_cons_true a]; gR; gR
  simp only [← ones_succ]
  sRn (b+2); gR; sRn (c+1); refine blankR ?_; gL
  simp only [ones_succ, ones_cons_true]; fin

/-- composite mode, no wrap: the hole moves left, then home. -/
theorem s_comp (a b : Nat) (Lz R : Strm) :
    Rch ⟨q3, Lz, F ::: blk (a+1) b R⟩
      (cfgL hg1 (ones a (true ::: F ::: Lz)) (F ::: ones (b+1) (true ::: R))) := by
  unfold blk
  gR; sRn (a+2); gR; rw [ones_cons_true b]; gL; gL; gL; rw [ones_cons_true a]; gR; gL
  simp only [ones_succ, ones_cons_true]; fin

/-- composite mode, wrap (m+1 is a square): S grows by 2 with its hole at the last index,
K moves two cells right; then the scan for the marker starts. -/
theorem s_square (b c : Nat) (Lz : Strm) :
    Rch ⟨q3, Lz, F ::: blk 0 b (F ::: ones (c+1) blank)⟩
      (cfgL la (ones c (F ::: true ::: F ::: ones (b+3) (F ::: Lz))) (true ::: blank)) := by
  unfold blk
  simp only [ones_zero]
  gR; gR; gR; rw [ones_cons_true b]; gL; gL; gL; gR
  show Rch ⟨tW, _, ones (b+3) _⟩ _
  sRn (b+3); gR; gR
  rcases c with _ | c
  · refine blankR ?_; gR; refine blankR ?_; gL
    simp only [ones_succ, ones_cons_true, ones_zero]; fin
  · gR; sRn c; refine blankR ?_; gR; refine blankR ?_; gL
    exact Reach.refl delta _

end TM.BrocardPrimes
