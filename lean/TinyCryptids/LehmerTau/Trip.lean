import TinyCryptids.Core.Lemmas

/-!
# Trips to the ends of the tape

The machine's tape is a word `W` on a blank tape whose zero-runs have length one (holes) or two
(separators), with 1s at both ends (`Wd W`). The parsers here run to the end of such a word:
`FarL`/`FarR` over everything up to three 0s; `HoleL` (a hole-finder that also stops at three
0s) over a word with separators only.
-/

namespace TM

variable {Q : Type} {δ : Q → Bool → Option (Bool × Dir × Q)}

local notation "F" => false

/-! ## words -/

def Wd (W : List Bool) : Prop := Clean12 W ∧ Clean12 W.reverse

theorem Clean12.suffix' {w : List Bool} (h : Clean12 w) : ∀ l m, w = l ++ m → Clean12 m := by
  induction h with
  | nil => intro l m e; cases l <;> simp_all; exact Clean12.nil
  | @one w _ ih =>
    intro l m e; cases l with
    | nil => simp at e; rw [← e]; exact Clean12.one (by assumption)
    | cons c l => simp at e; exact ih l m e.2
  | @z1 w hw ih =>
    intro l m e; cases l with
    | nil => simp at e; rw [← e]; exact Clean12.z1 hw
    | cons c l =>
      simp at e; cases l with
      | nil => simp at e; rw [← e.2]; exact Clean12.one hw
      | cons d l => simp at e; exact ih l m e.2.2
  | @z2 w hw ih =>
    intro l m e; cases l with
    | nil => simp at e; rw [← e]; exact Clean12.z2 hw
    | cons c l =>
      simp at e; cases l with
      | nil => simp at e; rw [← e.2]; exact Clean12.z1 hw
      | cons d l =>
        simp at e; cases l with
        | nil => simp at e; rw [← e.2.2]; exact Clean12.one hw
        | cons g l => simp at e; exact ih l m e.2.2.2

theorem Clean12.suffix {l m : List Bool} (h : Clean12 (l ++ m)) : Clean12 m := h.suffix' l m rfl

/-- the cells the head meets going right from `v` -/
theorem Wd.right {W u v : List Bool} (hW : Wd W) (hs : W = u ++ v) : Clean12 v :=
  Clean12.suffix (l := u) (hs ▸ hW.1)

/-- the cells the head meets going left from the last cell of `u` -/
theorem Wd.left {W u v : List Bool} (hW : Wd W) (hs : W = u ++ v) : Clean12 u.reverse := by
  have := hW.2; rw [hs, List.reverse_append] at this; exact Clean12.suffix this

/-! ## far parsers -/

structure FarL (δ : Q → Bool → Option (Bool × Dir × Q)) (p1 p2 p3 : Q) : Prop where
  a1 : δ p1 true = some (true, Dir.L, p1)
  a0 : δ p1 false = some (false, Dir.L, p2)
  b1 : δ p2 true = some (true, Dir.L, p1)
  b0 : δ p2 false = some (false, Dir.L, p3)
  c1 : δ p3 true = some (true, Dir.L, p1)

structure FarR (δ : Q → Bool → Option (Bool × Dir × Q)) (p1 p2 p3 : Q) : Prop where
  a1 : δ p1 true = some (true, Dir.R, p1)
  a0 : δ p1 false = some (false, Dir.R, p2)
  b1 : δ p2 true = some (true, Dir.R, p1)
  b0 : δ p2 false = some (false, Dir.R, p3)
  c1 : δ p3 true = some (true, Dir.R, p1)

theorem FarL.cross {p1 p2 p3 : Q} (P : FarL δ p1 p2 p3) {w : List Bool} (hw : Clean12 w)
    (s R : Strm) : Reach δ (cfgL p1 (app w s) R) (cfgL p1 s (app w.reverse R)) := by
  induction hw generalizing R with
  | nil => exact Reach.refl δ _
  | @one l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) P.a1) ?_
    simpa [app_append] using ih (true ::: R)
  | @z1 l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: true :: l) s) P.a0) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) P.b1) ?_
    simpa [app_append] using ih (true ::: false ::: R)
  | @z2 l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: false :: true :: l) s) P.a0) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: true :: l) s) P.b0) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) P.c1) ?_
    simpa [app_append] using ih (true ::: false ::: false ::: R)

theorem FarR.cross {p1 p2 p3 : Q} (P : FarR δ p1 p2 p3) {w : List Bool} (hw : Clean12 w)
    (L R : Strm) : Reach δ ⟨p1, L, app w R⟩ ⟨p1, app w.reverse L, R⟩ := by
  induction hw generalizing L with
  | nil => exact Reach.refl δ _
  | @one l _ ih =>
    refine Reach.trans δ (stepR (δ := δ) (R := app (true :: l) R) P.a1) ?_
    simpa [app_append] using ih (true ::: L)
  | @z1 l _ ih =>
    refine Reach.trans δ (stepR (δ := δ) (R := app (false :: true :: l) R) P.a0) ?_
    refine Reach.trans δ (stepR (δ := δ) (R := app (true :: l) R) P.b1) ?_
    simpa [app_append] using ih (true ::: false ::: L)
  | @z2 l _ ih =>
    refine Reach.trans δ (stepR (δ := δ) (R := app (false :: false :: true :: l) R) P.a0) ?_
    refine Reach.trans δ (stepR (δ := δ) (R := app (false :: true :: l) R) P.b0) ?_
    refine Reach.trans δ (stepR (δ := δ) (R := app (true :: l) R) P.c1) ?_
    simpa [app_append] using ih (true ::: false ::: false ::: L)

/-- left over the word and two blanks: `p3` on the third blank -/
theorem FarL.go {p1 p2 p3 : Q} (P : FarL δ p1 p2 p3) {w : List Bool} (hw : Clean12 w) (R : Strm) :
    Reach δ (cfgL p1 (app w blank) R) (cfgL p3 blank (F ::: F ::: app w.reverse R)) := by
  refine Reach.trans δ (P.cross hw blank R) ?_
  exact Reach.trans δ (stepL' (δ := δ) (s := blank) P.a0) (stepL' (δ := δ) (s := tl blank) P.b0)

/-- right over the word and two blanks: `p3` on the third blank -/
theorem FarR.go {p1 p2 p3 : Q} (P : FarR δ p1 p2 p3) {w : List Bool} (hw : Clean12 w) (L : Strm) :
    Reach δ ⟨p1, L, app w blank⟩ ⟨p3, F ::: F ::: app w.reverse L, blank⟩ := by
  refine Reach.trans δ (P.cross hw L blank) ?_
  exact Reach.trans δ (stepR (δ := δ) (R := blank) P.a0) (stepR (δ := δ) (R := tl blank) P.b0)

/-! ## a hole-finder that stops at the far left -/

structure HoleL (δ : Q → Bool → Option (Bool × Dir × Q)) (p1 p2 p3 : Q) : Prop where
  a1 : δ p1 true = some (true, Dir.L, p1)
  a0 : δ p1 false = some (false, Dir.L, p2)
  b0 : δ p2 false = some (false, Dir.L, p3)
  c1 : δ p3 true = some (true, Dir.L, p1)

theorem HoleL.cross {p1 p2 p3 : Q} (P : HoleL δ p1 p2 p3) {w : List Bool} (hw : Clean w)
    (s R : Strm) : Reach δ (cfgL p1 (app w s) R) (cfgL p1 s (app w.reverse R)) := by
  induction hw generalizing R with
  | nil => exact Reach.refl δ _
  | @one l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) P.a1) ?_
    simpa [app_append] using ih (true ::: R)
  | @sep l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: false :: true :: l) s) P.a0) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: true :: l) s) P.b0) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) P.c1) ?_
    simpa [app_append] using ih (true ::: false ::: false ::: R)

/-- to a hole: `p2` on the cell left of it -/
theorem HoleL.find {p1 p2 p3 : Q} (P : HoleL δ p1 p2 p3) {w : List Bool} (hw : Clean w) (s R : Strm) :
    Reach δ (cfgL p1 (app w (F ::: true ::: s)) R) (cfgL p2 (true ::: s) (F ::: app w.reverse R)) :=
  Reach.trans δ (P.cross hw _ R) (stepL' (δ := δ) (s := F ::: true ::: s) P.a0)

/-- to the far left: `p3` on the third blank -/
theorem HoleL.far {p1 p2 p3 : Q} (P : HoleL δ p1 p2 p3) {w : List Bool} (hw : Clean w) (R : Strm) :
    Reach δ (cfgL p1 (app w blank) R) (cfgL p3 blank (F ::: F ::: app w.reverse R)) := by
  refine Reach.trans δ (P.cross hw blank R) ?_
  exact Reach.trans δ (stepL' (δ := δ) (s := blank) P.a0) (stepL' (δ := δ) (s := tl blank) P.b0)

end TM
