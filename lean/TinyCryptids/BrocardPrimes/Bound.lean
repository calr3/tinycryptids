import TinyCryptids.BrocardPrimes.SProc
namespace TM.BrocardPrimes
open St

/-! # A prime square: move the marker, check and reset the counter -/

/-- the marker after a prime square: the block of `q = x + 3` (hole at its last index) moves
three cells right; its old left guard becomes the marker. -/
theorem bd_shift (x : Nat) (Lu Rr : Strm) :
    Rch (cfgL lg (F ::: ones (x+2) (true ::: F ::: F ::: Lu)) (true ::: F ::: F ::: true ::: Rr))
      ⟨r1, F ::: F ::: true ::: F ::: F ::: Lu, ones (x+3) (F ::: true ::: Rr)⟩ := by
  gR; gR; gL; gL; sLn (x+3); gL; gR; gR; gR; gR
  simp only [ones_succ, ones_cons_true]; fin

/-- right over runs of at most three 0s -/
theorem rcross {w : List Bool} (hw : Clean3 w) (L X : Strm) :
    Rch ⟨r1, L, app w X⟩ ⟨r1, app w.reverse L, X⟩ := by
  induction hw generalizing L with
  | nil => fin
  | @one l _ ih => gR; simpa [app_append] using ih (true ::: L)
  | @z1 l _ ih => gR; gR; simpa [app_append] using ih (true ::: F ::: L)
  | @z2 l _ ih => gR; gR; gR; simpa [app_append] using ih (true ::: F ::: F ::: L)
  | @z3 l _ ih => gR; gR; gR; gR; simpa [app_append] using ih (true ::: F ::: F ::: F ::: L)

/-- at the right end: erase the counter `1^(c+5)` from the right, keep one cell -/
theorem e_reset (c : Nat) (Y : Strm) :
    Rch ⟨r1, ones (c+5) (F ::: Y), blank⟩ (cfgL hg1 (F ::: Y) (true ::: blank)) := by
  refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gL
  zLn 3; gL; gL; gL; gL; gL; eLn c; gR; rw [zeros_cons_false]; gL
  simp only [zeros_cons_false, zeros_blank, cons_blank]; fin

/-- fewer than 4 cells besides the first: HALT -/
theorem e_halt (c : Nat) (hc : c < 4) (Y : Strm) : HaltAt ⟨r1, ones (c+1) (F ::: Y), blank⟩ := by
  rcases c with _ | _ | _ | _ | c
  all_goals first
    | omega
    | (apply Exists.intro; apply Exists.intro
       refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gL
       zLn 3; gL; repeat gL
       simp only [ones_zero]; gR; fin)

end TM.BrocardPrimes
