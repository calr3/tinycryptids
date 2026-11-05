import TinyCryptids.LegendreSieve.Home
namespace TM.LegendreSieve
open St

/-! ## Copying M to its left (after a prime) -/

/-- Copy loop, state `cL1`: the new M (`nm` cells) on the far left, then `00`,
then old M: `u + v` ones (its guard and the region left of the cursor; the
head is on the last of the first `u`), the cursor (a hole), `k` ones, the
right guard, and `Z`. -/
def cpyC (u v nm k : Nat) (Z : Strm) : Cfg St :=
  cfgL cL1 (ones u (F ::: F ::: ones nm blank)) (ones v (F ::: ones k (true ::: Z)))

/-- home, then start the new M with two cells and put the cursor at index 0 -/
theorem home_copy {w : List Bool} (hw : Clean3 w) (R : Strm) (k : Nat) (Z : Strm)
    (hR : app w.reverse R = true ::: ones k (true ::: Z)) :
    Rch (cfgL hc1 (app w (true ::: blank)) R) (cpyC 1 0 2 k Z) := by
  refine Rch.tr (HC.cross hw _ _) ?_
  rw [hR]; unfold cpyC
  gL; refine blankL ?_; gL; refine blankL ?_; gL; refine blankL ?_; gL; refine blankL ?_
  gR; gR; gR; gR; gR; gL
  simp only [ones_succ, ones_zero, cons_blank]; fin

/-- one round: the new M gains a cell, the cursor moves one cell right -/
theorem cpy_step (u v nm k : Nat) (Z : Strm) :
    Rch (cpyC u v nm (k+1) Z) (cpyC (u+v) 1 (nm+1) k Z) := by
  unfold cpyC
  sLn u; gL; gL; sLn nm; refine blankL ?_; gR
  sRn nm; gR; gR; rw [ones_add]; sRn (u+v); gR; gR; rw [ones_cons_true k]; gL; gL; gL
  simp only [ones_succ, ones_zero, ones_cons_true]; fin

/-- last round: the cursor is at the last index and stays there; go home -/
theorem cpy_last (u v nm : Nat) (Z : Strm) :
    Rch (cpyC u v nm 0 (F ::: Z))
      (cfgL hg1 (true ::: F ::: ones (u+v) (F ::: F ::: ones (nm+1) blank)) (F ::: Z)) := by
  unfold cpyC
  sLn u; gL; gL; sLn nm; refine blankL ?_; gR
  sRn nm; gR; gR; rw [ones_add]; sRn (u+v); gR; gR; gL
  simp only [ones_succ, ones_zero, ones_cons_true]; fin

theorem cpy_all (Z : Strm) : ∀ k u v nm,
    Rch (cpyC u v nm k (F ::: Z))
      (cfgL hg1 (true ::: F ::: ones (u+v+k) (F ::: F ::: ones (nm+k+1) blank)) (F ::: Z)) := by
  intro k
  induction k with
  | zero => intro u v nm; exact cpy_last u v nm Z
  | succ k ih =>
    intro u v nm
    refine Rch.tr (cpy_step u v nm k _) ?_
    have := ih (u+v) 1 (nm+1)
    rw [show u + v + 1 + k = u + v + (k+1) by omega, show nm + 1 + k + 1 = nm + (k+1) + 1 by omega] at this
    exact this

end TM.LegendreSieve
