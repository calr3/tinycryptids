import TinyCryptids.Lychrel.Find
import TinyCryptids.Gilbreath.Walk
import TinyCryptids.Singmaster.Machine
import TinyCryptids.Singmaster.Spec

/-!
# Tapes as lists

A configuration is written `cl q Lw Rw`: `Lw` lists the cells left of the head (nearest first),
`Rw` the head cell and the cells to its right; both continue with blank. `cL q HL Rw` is the
same with the head cell at the front of `HL` (the shape for leftward motion):
`cl q Lw (x :: Rw) = cL q (x :: Lw) Rw` by definition.
-/

namespace TM.Singmaster
open St TinyCryptids

local notation "F" => false
local notation "T" => true

abbrev Rch := Reach delta

def cl (q : St) (Lw Rw : List Bool) : Cfg St := ⟨q, app Lw blank, app Rw blank⟩
def cL (q : St) (HL Rw : List Bool) : Cfg St := cfgL q (app HL blank) (app Rw blank)

theorem cl_cL (q : St) (x : Bool) (Lw Rw : List Bool) : cl q Lw (x :: Rw) = cL q (x :: Lw) Rw := rfl

theorem Rch.tr {a b c : Cfg St} (h1 : Rch a b) (h2 : Rch b c) : Rch a c := Reach.trans delta h1 h2

theorem rep_cons {α : Type} (a : α) (l : List α) :
    ∀ n, List.replicate n a ++ a :: l = List.replicate (n + 1) a ++ l
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, rep_cons a l n]

@[simp] theorem rep_cons' {α : Type} (a : α) (l : List α) :
    ∀ n, List.replicate n a ++ a :: l = a :: (List.replicate n a ++ l)
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, rep_cons' a l n]

@[simp] theorem rep_snoc {α : Type} (a : α) (n : Nat) : List.replicate n a ++ [a] = a :: List.replicate n a := by
  simpa using rep_cons' a [] n

@[simp] theorem rep_rep {α : Type} (x : α) (a b : Nat) (l : List α) :
    List.replicate a x ++ (List.replicate b x ++ l) = List.replicate (a + b) x ++ l := by
  rw [← List.append_assoc, List.append_replicate_replicate]

theorem app_FF (l : List Bool) : app (l ++ [F]) blank = app l blank := by
  rw [app_append]; show app l (F ::: blank) = _; rw [cons_blank]

theorem app_reps (l : List Bool) : ∀ n, app (l ++ List.replicate n F) blank = app l blank
  | 0 => by simp
  | n + 1 => by
    have := rep_cons F [] n
    rw [List.append_nil] at this
    rw [← this, ← List.append_assoc, app_FF, app_reps l n]

/-- pad the right part with blanks -/
theorem cl_padR (q : St) (Lw Rw : List Bool) (n : Nat) :
    cl q Lw Rw = cl q Lw (Rw ++ List.replicate n F) := by
  unfold cl; rw [app_reps]

theorem cL_padR (q : St) (HL Rw : List Bool) (n : Nat) :
    cL q HL (Rw ++ List.replicate n F) = cL q HL Rw := by
  unfold cL; rw [app_reps]

theorem cl_padL (q : St) (Lw Rw : List Bool) (n : Nat) :
    cl q Lw Rw = cl q (Lw ++ List.replicate n F) Rw := by
  unfold cl; rw [app_reps]

theorem cL_padL (q : St) (HL Rw : List Bool) (n : Nat) :
    cL q HL Rw = cL q (HL ++ List.replicate n F) Rw := by
  unfold cL; rw [app_reps]

/-- one step right / left on lists -/
theorem sr {q q' : St} {b w : Bool} (h : delta q b = some (w, Dir.R, q')) (Lw Rw : List Bool) :
    Rch (cl q Lw (b :: Rw)) (cl q' (w :: Lw) Rw) := stepR (δ := delta) (R := app (b :: Rw) blank) h

theorem sl {q q' : St} {b w : Bool} (h : delta q b = some (w, Dir.L, q')) (x : Bool) (Lw Rw : List Bool) :
    Rch (cl q (x :: Lw) (b :: Rw)) (cl q' Lw (x :: w :: Rw)) :=
  stepL (δ := delta) (L := app (x :: Lw) blank) (R := app (b :: Rw) blank) h

/-- a left step into the `cL` shape (no need to know the cell to the left) -/
theorem slc {q q' : St} {b w : Bool} (h : delta q b = some (w, Dir.L, q')) (Lw Rw : List Bool) :
    Rch (cl q Lw (b :: Rw)) (cL q' Lw (w :: Rw)) :=
  stepL (δ := delta) (L := app Lw blank) (R := app (b :: Rw) blank) h

macro "glc" : tactic => `(tactic| refine Rch.tr (slc (by rfl) _ _) ?_)
macro "gr" : tactic => `(tactic| refine Rch.tr (sr (by rfl) _ _) ?_)
macro "gl" : tactic => `(tactic| refine Rch.tr (sl (by rfl) _ _ _) ?_)
macro "fin" : tactic => `(tactic| exact Reach.refl delta _)
macro "norm" : tactic => `(tactic| simp only [List.append_eq, List.append_assoc, List.cons_append,
  List.nil_append, List.append_nil])
macro "lnorm" : tactic => `(tactic| simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append,
  List.append_nil, List.replicate_succ, rep_cons', rep_snoc, List.reverse_append, List.reverse_cons,
  List.reverse_replicate, List.singleton_append, List.reverse_nil, List.replicate_zero, List.reverse_reverse,
  rep_rep, List.append_replicate_replicate, Nat.add_zero, Nat.zero_add])
/-- normalize the lists of both configurations, then close by reflexivity -/
macro "lfin" : tactic => `(tactic| (simp only [List.append_eq, List.append_assoc, List.cons_append, List.nil_append,
  List.append_nil, List.replicate_succ, rep_cons', rep_snoc, List.reverse_append, List.reverse_cons,
  List.reverse_replicate, List.singleton_append, List.reverse_nil, List.replicate_zero, List.reverse_reverse,
  rep_rep, List.append_replicate_replicate, Nat.add_zero, Nat.zero_add]; try exact Reach.refl delta _))

theorem srn {q : St} (h : delta q T = some (T, Dir.R, q)) (n : Nat) (Lw Rw : List Bool) :
    Rch (cl q Lw (List.replicate n T ++ Rw)) (cl q (List.replicate n T ++ Lw) Rw) := by
  induction n generalizing Lw with
  | zero => exact Reach.refl delta _
  | succ n ih =>
    refine Rch.tr (sr h _ _) ?_
    have := ih (T :: Lw)
    rwa [rep_cons] at this

theorem sln {q : St} (h : delta q T = some (T, Dir.L, q)) (n : Nat) (HL Rw : List Bool) :
    Rch (cL q (List.replicate n T ++ HL) Rw) (cL q HL (List.replicate n T ++ Rw)) := by
  induction n generalizing Rw with
  | zero => exact Reach.refl delta _
  | succ n ih =>
    have e1 : cL q (List.replicate (n + 1) T ++ HL) Rw =
        cfgL q (T ::: app (List.replicate n T ++ HL) blank) (app Rw blank) := rfl
    rw [e1]
    refine Rch.tr (stepL' (δ := delta) (s := T ::: app (List.replicate n T ++ HL) blank) h) ?_
    have := ih (T :: Rw)
    have e2 := rep_cons T Rw n
    rw [e2] at this; exact this

theorem slz {q : St} (h : delta q F = some (F, Dir.L, q)) (n : Nat) (HL Rw : List Bool) :
    Rch (cL q (List.replicate n F ++ HL) Rw) (cL q HL (List.replicate n F ++ Rw)) := by
  induction n generalizing Rw with
  | zero => exact Reach.refl delta _
  | succ n ih =>
    have e1 : cL q (List.replicate (n + 1) F ++ HL) Rw =
        cfgL q (F ::: app (List.replicate n F ++ HL) blank) (app Rw blank) := rfl
    rw [e1]
    refine Rch.tr (stepL' (δ := delta) (s := F ::: app (List.replicate n F ++ HL) blank) h) ?_
    have := ih (F :: Rw)
    have e2 := rep_cons F Rw n
    rw [e2] at this; exact this

theorem sln' {q : St} (h : delta q T = some (T, Dir.L, q)) (n : Nat) {HL : List Bool} (HL' Rw : List Bool)
    (e : HL = List.replicate n T ++ HL') : Rch (cL q HL Rw) (cL q HL' (List.replicate n T ++ Rw)) :=
  e ▸ sln h n HL' Rw

theorem srn' {q : St} (h : delta q T = some (T, Dir.R, q)) (n : Nat) (Lw : List Bool) {Rw : List Bool}
    (Rw' : List Bool) (e : Rw = List.replicate n T ++ Rw') :
    Rch (cl q Lw Rw) (cl q (List.replicate n T ++ Lw) Rw') :=
  e ▸ srn h n Lw Rw'

/-! ## finders on lists -/

theorem fr_cross {p z1 z2 : St} (H : FindR delta p z1 z2) {w : List Bool} (hw : GC w)
    (Lw Rw : List Bool) : Rch (cl p Lw (w ++ Rw)) (cl p (w.reverse ++ Lw) Rw) := by
  have := H.cross hw (app Lw blank) (app Rw blank)
  unfold cl; rwa [app_append, app_append]

theorem fl_cross {p z1 z2 : St} (H : FindL delta p z1 z2) {w : List Bool} (hw : GC w)
    (HL Rw : List Bool) : Rch (cL p (w ++ HL) Rw) (cL p HL (w.reverse ++ Rw)) := by
  have := H.cross hw (app HL blank) (app Rw blank)
  unfold cL; rwa [app_append, app_append]

theorem fr_cross' {p z1 z2 : St} (H : FindR delta p z1 z2) {w : List Bool} (hw : GC w)
    (Lw : List Bool) {Rw : List Bool} (Rw' : List Bool) (h : Rw = w ++ Rw') :
    Rch (cl p Lw Rw) (cl p (w.reverse ++ Lw) Rw') := h ▸ fr_cross H hw Lw Rw'

/-- a left finder from `cl p Lw (x :: Rw)`, i.e. the head cell `x` is crossed first -/
theorem fl_cross' {p z1 z2 : St} (H : FindL delta p z1 z2) {w : List Bool} (hw : GC w)
    {x : Bool} {Lw : List Bool} (HL' : List Bool) (Rw : List Bool) (h : x :: Lw = w ++ HL') :
    Rch (cl p Lw (x :: Rw)) (cL p HL' (w.reverse ++ Rw)) := by
  rw [cl_cL, h]; exact fl_cross H hw HL' Rw

theorem fl_crossE {p z1 z2 : St} (H : FindL delta p z1 z2) {w : List Bool} (hw : GC w)
    {HL : List Bool} (HL' Rw : List Bool) (h : HL = w ++ HL') :
    Rch (cL p HL Rw) (cL p HL' (w.reverse ++ Rw)) := h ▸ fl_cross H hw HL' Rw

/-- the four-zero walk (without its return state) -/
structure Walk4 (w1 w2 w3 w4 : St) : Prop where
  a1 : delta w1 T = some (T, Dir.R, w1)
  a0 : delta w1 F = some (F, Dir.R, w2)
  b1 : delta w2 T = some (T, Dir.R, w1)
  b0 : delta w2 F = some (F, Dir.R, w3)
  c1 : delta w3 T = some (T, Dir.R, w1)
  c0 : delta w3 F = some (F, Dir.R, w4)
  d1 : delta w4 T = some (T, Dir.R, w1)

theorem w4_cross {w1 w2 w3 w4 : St} (H : Walk4 w1 w2 w3 w4) {w : List Bool} (hw : WC w)
    (Lw Rw : List Bool) : Rch (cl w1 Lw (w ++ Rw)) (cl w1 (w.reverse ++ Lw) Rw) := by
  induction hw generalizing Lw with
  | nil => exact Reach.refl delta _
  | @one l _ ih =>
    refine Rch.tr (sr H.a1 _ _) ?_
    simpa using ih (T :: Lw)
  | @gap l k hk _ ih =>
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · refine Rch.tr (sr H.a0 _ _) (Rch.tr (sr H.b1 _ _) ?_)
      simpa using ih (T :: F :: Lw)
    · refine Rch.tr (sr H.a0 _ _) (Rch.tr (sr H.b0 _ _) (Rch.tr (sr H.c1 _ _) ?_))
      simpa using ih (T :: F :: F :: Lw)
    · refine Rch.tr (sr H.a0 _ _) (Rch.tr (sr H.b0 _ _) (Rch.tr (sr H.c0 _ _)
        (Rch.tr (sr H.d1 _ _) ?_)))
      simpa using ih (T :: F :: F :: F :: Lw)

theorem w4_cross' {w1 w2 w3 w4 : St} (H : Walk4 w1 w2 w3 w4) {w : List Bool} (hw : WC w)
    (Lw : List Bool) {Rw : List Bool} (Rw' : List Bool) (h : Rw = w ++ Rw') :
    Rch (cl w1 Lw Rw) (cl w1 (w.reverse ++ Lw) Rw') := h ▸ w4_cross H hw Lw Rw'

theorem FE_ : FindR delta eP eZ1 eZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FF_ : FindR delta fP fZ1 fZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FR_ : FindR delta rP rZ1 rZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FN_ : FindL delta nP nZ1 nZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FD_ : FindL delta dP dZ1 dZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FS_ : FindL delta sP sZ1 sZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FG_ : FindL delta gP gZ1 gZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem WW_ : Walk4 W1 W2 W3 W4 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem WT_ : Walk4 WT1 WT2 WT3 WT4 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h'⟩ := h; ⟨L, R, Rch.tr hab h'⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h'⟩ := h; Reach.halts delta h' (halt_none (by rfl))

macro "hr" : tactic => `(tactic| refine HaltAt.back (sr (by rfl) _ _) ?_)
macro "hl" : tactic => `(tactic| refine HaltAt.back (sl (by rfl) _ _ _) ?_)

end TM.Singmaster
