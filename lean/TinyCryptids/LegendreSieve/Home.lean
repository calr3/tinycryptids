import TinyCryptids.LegendreSieve.SProc
namespace TM.LegendreSieve
open St

/-! ## Going home: left over runs of at most three 0s, stop at the fourth. -/

/-- zero-runs of length 1..3, each followed by a 1 -/
inductive Clean3 : List Bool → Prop
  | nil : Clean3 []
  | one {l} : Clean3 l → Clean3 (true :: l)
  | z1 {l} : Clean3 l → Clean3 (false :: true :: l)
  | z2 {l} : Clean3 l → Clean3 (false :: false :: true :: l)
  | z3 {l} : Clean3 l → Clean3 (false :: false :: false :: true :: l)

theorem Clean3.append {l m : List Bool} (hl : Clean3 l) (hm : Clean3 m) : Clean3 (l ++ m) := by
  induction hl with
  | nil => exact hm
  | one _ ih => exact Clean3.one ih
  | z1 _ ih => exact Clean3.z1 ih
  | z2 _ ih => exact Clean3.z2 ih
  | z3 _ ih => exact Clean3.z3 ih

theorem Clean3.rep (n : Nat) : Clean3 (List.replicate n true) := by
  induction n with
  | zero => exact Clean3.nil
  | succ n ih => exact Clean3.one ih

structure Home4 (δ : St → Bool → Option (Bool × Dir × St)) (h1 h2 h3 h4 : St) : Prop where
  a1 : δ h1 true = some (true, Dir.L, h1)
  a0 : δ h1 false = some (false, Dir.L, h2)
  b1 : δ h2 true = some (true, Dir.L, h1)
  b0 : δ h2 false = some (false, Dir.L, h3)
  c1 : δ h3 true = some (true, Dir.L, h1)
  c0 : δ h3 false = some (false, Dir.L, h4)
  d1 : δ h4 true = some (true, Dir.L, h1)

theorem Home4.cross {h1 h2 h3 h4 : St} (H : Home4 delta h1 h2 h3 h4) {w : List Bool} (hw : Clean3 w)
    (s R : Strm) : Rch (cfgL h1 (app w s) R) (cfgL h1 s (app w.reverse R)) := by
  induction hw generalizing R with
  | nil => exact Reach.refl delta _
  | @one l _ ih =>
    refine Rch.tr (stepL' (δ := delta) (s := app (true :: l) s) H.a1) ?_
    simpa [app_append] using ih (true ::: R)
  | @z1 l _ ih =>
    refine Rch.tr (stepL' (δ := delta) (s := app (false :: true :: l) s) H.a0) ?_
    refine Rch.tr (stepL' (δ := delta) (s := app (true :: l) s) H.b1) ?_
    simpa [app_append] using ih (true ::: false ::: R)
  | @z2 l _ ih =>
    refine Rch.tr (stepL' (δ := delta) (s := app (false :: false :: true :: l) s) H.a0) ?_
    refine Rch.tr (stepL' (δ := delta) (s := app (false :: true :: l) s) H.b0) ?_
    refine Rch.tr (stepL' (δ := delta) (s := app (true :: l) s) H.c1) ?_
    simpa [app_append] using ih (true ::: false ::: false ::: R)
  | @z3 l _ ih =>
    refine Rch.tr (stepL' (δ := delta) (s := app (false :: false :: false :: true :: l) s) H.a0) ?_
    refine Rch.tr (stepL' (δ := delta) (s := app (false :: false :: true :: l) s) H.b0) ?_
    refine Rch.tr (stepL' (δ := delta) (s := app (false :: true :: l) s) H.c0) ?_
    refine Rch.tr (stepL' (δ := delta) (s := app (true :: l) s) H.d1) ?_
    simpa [app_append] using ih (true ::: false ::: false ::: false ::: R)

theorem HG : Home4 delta hg1 hg2 hg3 hg4 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem HC : Home4 delta hc1 hc2 hc3 hc4 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem blankL {q : St} {R : Strm} {X : Cfg St} (h : Rch (cfgL q (F ::: blank) R) X) :
    Rch (cfgL q blank R) X := by rw [cons_blank] at h; exact h

/-- The checkpoint: state `hg5` three cells left of the leftmost 1, all blank to its left. -/
def chkW (W : List Bool) : Cfg St := ⟨hg5, blank, F ::: F ::: F ::: app W blank⟩

/-- home over `w` to the leftmost cell of the tape, then to the checkpoint -/
theorem home_chk {w : List Bool} (hw : Clean3 w) (R : List Bool) :
    Rch (cfgL hg1 (app w (true ::: blank)) (app R blank)) (chkW (true :: w.reverse ++ R)) := by
  refine Rch.tr (HG.cross hw _ _) ?_
  unfold chkW
  gL; refine blankL ?_; gL; refine blankL ?_; gL; refine blankL ?_; gL; refine blankL ?_; gR
  simp only [app_append, app_cons, List.cons_append, tl_blank, cons_blank]; fin

/-- from the checkpoint: M grows by one at its left end, sweep starts in prime mode -/
theorem chk_grow (n : Nat) (X : Strm) :
    Rch ⟨hg5, blank, F ::: F ::: F ::: ones n X⟩ ⟨p1, true ::: blank, ones n X⟩ := by
  gR; gR; gR; simp only [cons_blank]; fin

end TM.LegendreSieve
