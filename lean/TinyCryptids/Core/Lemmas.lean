import TinyCryptids.Core.Basic

namespace TM

variable {Q : Type} {δ : Q → Bool → Option (Bool × Dir × Q)}

def app : List Bool → Strm → Strm
  | [], s => s
  | b :: l, s => b ::: app l s

@[simp] theorem app_nil (s : Strm) : app [] s = s := rfl
@[simp] theorem app_cons (b : Bool) (l : List Bool) (s : Strm) : app (b :: l) s = b ::: app l s := rfl
theorem app_append (l m : List Bool) (s : Strm) : app (l ++ m) s = app l (app m s) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih]
theorem app_replicate (n : Nat) (s : Strm) : app (List.replicate n true) s = ones n s := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih, ones_succ]

/-! ## single steps -/

theorem stepR {q q' : Q} {L R : Strm} {w : Bool} (h : δ q (R 0) = some (w, Dir.R, q')) :
    Reach δ ⟨q, L, R⟩ ⟨q', w ::: L, tl R⟩ :=
  reach_step δ (by simp [step, h])

theorem stepL {q q' : Q} {L R : Strm} {w : Bool} (h : δ q (R 0) = some (w, Dir.L, q')) :
    Reach δ ⟨q, L, R⟩ ⟨q', tl L, L 0 ::: w ::: tl R⟩ :=
  reach_step δ (by simp [step, h])

theorem stepR1 {q q' : Q} {L R : Strm} {w : Bool} (h : δ q (R 0) = some (w, Dir.R, q')) :
    Reach1 δ ⟨q, L, R⟩ ⟨q', w ::: L, tl R⟩ :=
  ⟨0, by simp [run, Sys.run, step, h]⟩

theorem halt_none {q : Q} {L R : Strm} (h : δ q (R 0) = none) : Halts δ ⟨q, L, R⟩ :=
  halts_of_step δ (by simp [step, h])

/-! ## scanning over runs of ones -/

theorem scanR {q : Q} (h : δ q true = some (true, Dir.R, q)) (n : Nat) (L R : Strm) :
    Reach δ ⟨q, L, ones n R⟩ ⟨q, ones n L, R⟩ := by
  induction n generalizing L with
  | zero => exact Reach.refl δ _
  | succ n ih =>
    refine Reach.trans δ (stepR (δ := δ) (R := ones (n+1) R) h) ?_
    have := ih (true ::: L); rw [← ones_succ'] at this; exact this

/-- Configuration whose head reads `s 0` with `tl s` to its left: the natural
shape for leftward motion (the mirror image of `⟨q, L, s⟩`). -/
def cfgL (q : Q) (s R : Strm) : Cfg Q := ⟨q, tl s, s 0 ::: R⟩

theorem stepL' {q q' : Q} {s R : Strm} {w : Bool} (h : δ q (s 0) = some (w, Dir.L, q')) :
    Reach δ (cfgL q s R) (cfgL q' (tl s) (w ::: R)) :=
  stepL (δ := δ) (L := tl s) (R := s 0 ::: R) h

theorem scanL {q : Q} (h : δ q true = some (true, Dir.L, q)) (n : Nat) (s R : Strm) :
    Reach δ (cfgL q (ones n s) R) (cfgL q s (ones n R)) := by
  induction n generalizing R with
  | zero => exact Reach.refl δ _
  | succ n ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := ones (n+1) s) h) ?_
    have := ih (true ::: R); rw [← ones_succ'] at this; exact this

theorem scanR0 {q : Q} (h : δ q false = some (false, Dir.R, q)) (n : Nat) (L R : Strm) :
    Reach δ ⟨q, L, zeros n R⟩ ⟨q, zeros n L, R⟩ := by
  induction n generalizing L with
  | zero => exact Reach.refl δ _
  | succ n ih =>
    refine Reach.trans δ (stepR (δ := δ) (R := zeros (n+1) R) h) ?_
    have := ih (false ::: L); rw [← zeros_succ'] at this; exact this

theorem scanL0 {q : Q} (h : δ q false = some (false, Dir.L, q)) (n : Nat) (s R : Strm) :
    Reach δ (cfgL q (zeros n s) R) (cfgL q s (zeros n R)) := by
  induction n generalizing R with
  | zero => exact Reach.refl δ _
  | succ n ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := zeros (n+1) s) h) ?_
    have := ih (false ::: R); rw [← zeros_succ'] at this; exact this

theorem eraseR {q : Q} (h : δ q true = some (false, Dir.R, q)) (n : Nat) (L R : Strm) :
    Reach δ ⟨q, L, ones n R⟩ ⟨q, zeros n L, R⟩ := by
  induction n generalizing L with
  | zero => exact Reach.refl δ _
  | succ n ih =>
    refine Reach.trans δ (stepR (δ := δ) (R := ones (n+1) R) h) ?_
    have := ih (false ::: L); rw [← zeros_succ'] at this; exact this

theorem eraseL {q : Q} (h : δ q true = some (false, Dir.L, q)) (n : Nat) (s R : Strm) :
    Reach δ (cfgL q (ones n s) R) (cfgL q s (zeros n R)) := by
  induction n generalizing R with
  | zero => exact Reach.refl δ _
  | succ n ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := ones (n+1) s) h) ?_
    have := ih (false ::: R); rw [← zeros_succ'] at this; exact this

/-! ## clean segments and hole-finding parsers -/

/-- Lists whose zero-runs all have length exactly two and are followed by a 1. -/
inductive Clean : List Bool → Prop
  | nil : Clean []
  | one {l} : Clean l → Clean (true :: l)
  | sep {l} : Clean l → Clean (false :: false :: true :: l)

theorem Clean.append {l m : List Bool} (hl : Clean l) (hm : Clean m) : Clean (l ++ m) := by
  induction hl with
  | nil => exact hm
  | one _ ih => exact Clean.one ih
  | sep _ ih => exact Clean.sep ih

theorem Clean.replicate (n : Nat) : Clean (List.replicate n true) := by
  induction n with
  | zero => exact Clean.nil
  | succ n ih => exact Clean.one ih

structure ParserR (δ : Q → Bool → Option (Bool × Dir × Q)) (p1 p2 : Q) : Prop where
  h1 : δ p1 true = some (true, Dir.R, p1)
  h0 : δ p1 false = some (false, Dir.R, p2)
  h2 : δ p2 false = some (false, Dir.R, p1)

structure ParserL (δ : Q → Bool → Option (Bool × Dir × Q)) (p1 p2 : Q) : Prop where
  h1 : δ p1 true = some (true, Dir.L, p1)
  h0 : δ p1 false = some (false, Dir.L, p2)
  h2 : δ p2 false = some (false, Dir.L, p1)

theorem ParserR.cross {p1 p2 : Q} (P : ParserR δ p1 p2) {w : List Bool} (hw : Clean w)
    (L R : Strm) : Reach δ ⟨p1, L, app w R⟩ ⟨p1, app w.reverse L, R⟩ := by
  induction hw generalizing L with
  | nil => exact Reach.refl δ _
  | @one l _ ih =>
    refine Reach.trans δ (stepR (δ := δ) (R := app (true :: l) R) P.h1) ?_
    simpa [app_append] using ih (true ::: L)
  | @sep l _ ih =>
    refine Reach.trans δ (stepR (δ := δ) (R := app (false :: false :: true :: l) R) P.h0) ?_
    refine Reach.trans δ (stepR (δ := δ) (R := app (false :: true :: l) R) P.h2) ?_
    refine Reach.trans δ (stepR (δ := δ) (R := app (true :: l) R) P.h1) ?_
    simpa [app_append] using ih (true ::: false ::: false ::: L)

/-- Right parser: crosses a clean segment and stops one cell past the hole. -/
theorem ParserR.find {p1 p2 : Q} (P : ParserR δ p1 p2) {w : List Bool} (hw : Clean w)
    (L R : Strm) :
    Reach δ ⟨p1, L, app w (false ::: true ::: R)⟩ ⟨p2, false ::: app w.reverse L, true ::: R⟩ :=
  Reach.trans δ (P.cross hw L _) (stepR (δ := δ) (R := false ::: true ::: R) P.h0)

theorem ParserL.cross {p1 p2 : Q} (P : ParserL δ p1 p2) {w : List Bool} (hw : Clean w)
    (s R : Strm) : Reach δ (cfgL p1 (app w s) R) (cfgL p1 s (app w.reverse R)) := by
  induction hw generalizing R with
  | nil => exact Reach.refl δ _
  | @one l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) P.h1) ?_
    simpa [app_append] using ih (true ::: R)
  | @sep l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: false :: true :: l) s) P.h0) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: true :: l) s) P.h2) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) P.h1) ?_
    simpa [app_append] using ih (true ::: false ::: false ::: R)

/-- Left parser: crosses a clean segment and stops one cell past the hole. -/
theorem ParserL.find {p1 p2 : Q} (P : ParserL δ p1 p2) {w : List Bool} (hw : Clean w)
    (s R : Strm) :
    Reach δ (cfgL p1 (app w (false ::: true ::: s)) R)
      (cfgL p2 (true ::: s) (false ::: app w.reverse R)) :=
  Reach.trans δ (P.cross hw _ R) (stepL' (δ := δ) (s := false ::: true ::: s) P.h0)

/-- zero-runs of length one or two, each followed by a 1 -/
inductive Clean12 : List Bool → Prop
  | nil : Clean12 []
  | one {l} : Clean12 l → Clean12 (true :: l)
  | z1 {l} : Clean12 l → Clean12 (false :: true :: l)
  | z2 {l} : Clean12 l → Clean12 (false :: false :: true :: l)

theorem Clean12.of_clean {l : List Bool} (h : Clean l) : Clean12 l := by
  induction h with
  | nil => exact Clean12.nil
  | one _ ih => exact Clean12.one ih
  | sep _ ih => exact Clean12.z2 ih

theorem Clean12.append {l m : List Bool} (hl : Clean12 l) (hm : Clean12 m) : Clean12 (l ++ m) := by
  induction hl with
  | nil => exact hm
  | one _ ih => exact Clean12.one ih
  | z1 _ ih => exact Clean12.z1 ih
  | z2 _ ih => exact Clean12.z2 ih

/-- "go home": move left over runs of at most two zeros until three blanks, then
come back right to the first 1 and step onto the next cell -/
structure Home (δ : Q → Bool → Option (Bool × Dir × Q)) (h1 h2 h3 h4 k : Q) : Prop where
  a1 : δ h1 true = some (true, Dir.L, h1)
  a0 : δ h1 false = some (false, Dir.L, h2)
  b1 : δ h2 true = some (true, Dir.L, h1)
  b0 : δ h2 false = some (false, Dir.L, h3)
  c1 : δ h3 true = some (true, Dir.L, h1)
  c0 : δ h3 false = some (false, Dir.R, h4)
  d0 : δ h4 false = some (false, Dir.R, h4)
  d1 : δ h4 true = some (true, Dir.R, k)

theorem Home.cross {h1 h2 h3 h4 k : Q} (H : Home δ h1 h2 h3 h4 k) {w : List Bool} (hw : Clean12 w)
    (s R : Strm) : Reach δ (cfgL h1 (app w s) R) (cfgL h1 s (app w.reverse R)) := by
  induction hw generalizing R with
  | nil => exact Reach.refl δ _
  | @one l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) H.a1) ?_
    simpa [app_append] using ih (true ::: R)
  | @z1 l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: true :: l) s) H.a0) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) H.b1) ?_
    simpa [app_append] using ih (true ::: false ::: R)
  | @z2 l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: false :: true :: l) s) H.a0) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: true :: l) s) H.b0) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) H.c1) ?_
    simpa [app_append] using ih (true ::: false ::: false ::: R)

theorem Home.go' {h1 h2 h3 h4 k : Q} (H : Home δ h1 h2 h3 h4 k) {w : List Bool} (hw : Clean12 w)
    (B R : Strm) :
    Reach δ (cfgL h1 (app w (true ::: false ::: false ::: false ::: B)) R)
      ⟨k, true ::: false ::: false ::: false ::: B, app w.reverse R⟩ := by
  refine Reach.trans δ (H.cross hw _ R) ?_
  refine Reach.trans δ (stepL' (δ := δ) (s := true ::: false ::: false ::: false ::: B) H.a1) ?_
  refine Reach.trans δ (stepL' (δ := δ) (s := false ::: false ::: false ::: B) H.a0) ?_
  refine Reach.trans δ (stepL' (δ := δ) (s := false ::: false ::: B) H.b0) ?_
  refine Reach.trans δ (stepR (δ := δ) (L := B)
    (R := false ::: false ::: false ::: true ::: app w.reverse R) H.c0) ?_
  refine Reach.trans δ (stepR (δ := δ) (R := false ::: false ::: true ::: app w.reverse R) H.d0) ?_
  refine Reach.trans δ (stepR (δ := δ) (R := false ::: true ::: app w.reverse R) H.d0) ?_
  exact stepR (δ := δ) (R := true ::: app w.reverse R) H.d1

/-- go home across `w` followed by the leftmost cell (a 1) of the tape -/
theorem Home.go {h1 h2 h3 h4 k : Q} (H : Home δ h1 h2 h3 h4 k) {w : List Bool} (hw : Clean12 w)
    (R : Strm) : Reach δ (cfgL h1 (app w (true ::: blank)) R) ⟨k, true ::: blank, app w.reverse R⟩ := by
  have := H.go' hw blank R
  simp only [cons_blank] at this
  exact this

theorem Home.goHole' {h1 h2 h3 h4 k : Q} (H : Home δ h1 h2 h3 h4 k) {w : List Bool} (hw : Clean12 w)
    (B R : Strm) :
    Reach δ (cfgL h1 (app w (false ::: true ::: false ::: false ::: false ::: B)) R)
      ⟨k, true ::: false ::: false ::: false ::: B, false ::: app w.reverse R⟩ := by
  refine Reach.trans δ (H.cross hw _ R) ?_
  refine Reach.trans δ (stepL' (δ := δ) (s := false ::: true ::: false ::: false ::: false ::: B) H.a0) ?_
  refine Reach.trans δ (stepL' (δ := δ) (s := true ::: false ::: false ::: false ::: B) H.b1) ?_
  refine Reach.trans δ (stepL' (δ := δ) (s := false ::: false ::: false ::: B) H.a0) ?_
  refine Reach.trans δ (stepL' (δ := δ) (s := false ::: false ::: B) H.b0) ?_
  refine Reach.trans δ (stepR (δ := δ) (L := B)
    (R := false ::: false ::: false ::: true ::: false ::: app w.reverse R) H.c0) ?_
  refine Reach.trans δ (stepR (δ := δ) (R := false ::: false ::: true ::: false ::: app w.reverse R) H.d0) ?_
  refine Reach.trans δ (stepR (δ := δ) (R := false ::: true ::: false ::: app w.reverse R) H.d0) ?_
  exact stepR (δ := δ) (R := true ::: false ::: app w.reverse R) H.d1

/-- go home when the leftmost block carries a hole at its cell 1 -/
theorem Home.goHole {h1 h2 h3 h4 k : Q} (H : Home δ h1 h2 h3 h4 k) {w : List Bool} (hw : Clean12 w)
    (R : Strm) :
    Reach δ (cfgL h1 (app w (false ::: true ::: blank)) R) ⟨k, true ::: blank, false ::: app w.reverse R⟩ := by
  have := H.goHole' hw blank R
  simp only [cons_blank] at this
  exact this

/-- like `Home`, but the leftmost block grows by one cell at its left end -/
structure HomeG (δ : Q → Bool → Option (Bool × Dir × Q)) (h1 h2 h3 h4 h5 k : Q) : Prop where
  a1 : δ h1 true = some (true, Dir.L, h1)
  a0 : δ h1 false = some (false, Dir.L, h2)
  b1 : δ h2 true = some (true, Dir.L, h1)
  b0 : δ h2 false = some (false, Dir.L, h3)
  c1 : δ h3 true = some (true, Dir.L, h1)
  c0 : δ h3 false = some (false, Dir.R, h4)
  d0 : δ h4 false = some (false, Dir.R, h5)
  e0 : δ h5 false = some (true, Dir.R, k)

theorem HomeG.cross {h1 h2 h3 h4 h5 k : Q} (H : HomeG δ h1 h2 h3 h4 h5 k) {w : List Bool} (hw : Clean12 w)
    (s R : Strm) : Reach δ (cfgL h1 (app w s) R) (cfgL h1 s (app w.reverse R)) := by
  induction hw generalizing R with
  | nil => exact Reach.refl δ _
  | @one l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) H.a1) ?_
    simpa [app_append] using ih (true ::: R)
  | @z1 l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: true :: l) s) H.a0) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) H.b1) ?_
    simpa [app_append] using ih (true ::: false ::: R)
  | @z2 l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: false :: true :: l) s) H.a0) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: true :: l) s) H.b0) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) H.c1) ?_
    simpa [app_append] using ih (true ::: false ::: false ::: R)

theorem HomeG.go' {h1 h2 h3 h4 h5 k : Q} (H : HomeG δ h1 h2 h3 h4 h5 k) {w : List Bool} (hw : Clean12 w)
    (B R : Strm) :
    Reach δ (cfgL h1 (app w (true ::: false ::: false ::: false ::: B)) R)
      ⟨k, true ::: false ::: false ::: B, true ::: app w.reverse R⟩ := by
  refine Reach.trans δ (H.cross hw _ R) ?_
  refine Reach.trans δ (stepL' (δ := δ) (s := true ::: false ::: false ::: false ::: B) H.a1) ?_
  refine Reach.trans δ (stepL' (δ := δ) (s := false ::: false ::: false ::: B) H.a0) ?_
  refine Reach.trans δ (stepL' (δ := δ) (s := false ::: false ::: B) H.b0) ?_
  refine Reach.trans δ (stepR (δ := δ) (L := B)
    (R := false ::: false ::: false ::: true ::: app w.reverse R) H.c0) ?_
  refine Reach.trans δ (stepR (δ := δ) (R := false ::: false ::: true ::: app w.reverse R) H.d0) ?_
  exact stepR (δ := δ) (R := false ::: true ::: app w.reverse R) H.e0

theorem HomeG.go {h1 h2 h3 h4 h5 k : Q} (H : HomeG δ h1 h2 h3 h4 h5 k) {w : List Bool} (hw : Clean12 w)
    (R : Strm) :
    Reach δ (cfgL h1 (app w (true ::: blank)) R) ⟨k, true ::: blank, true ::: app w.reverse R⟩ := by
  have := H.go' hw blank R
  simp only [cons_blank] at this
  exact this

end TM
