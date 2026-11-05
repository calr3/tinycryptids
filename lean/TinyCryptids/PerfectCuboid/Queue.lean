import TinyCryptids.PerfectCuboid.Step

/-!
# The queue: going home to A, and the scan that fills the holes after an abort

`qL t` is the queue `A 00 B 00 C 00 Z`. The tuple start `TS t s` reads A's first cell in `n5`,
with `W = 2` and S home.
-/

namespace TM.PerfectCuboid

open St

local notation "F" => false
local notation "T" => true

def rep (n : Nat) : List Bool := List.replicate n T

def qL : Tup → List Bool
  | (x, y, z) => rep x ++ [F, F] ++ rep y ++ [F, F] ++ rep z ++ [F, F] ++ [T, T, T]

def TS (t : Tup) (s : Nat × Nat) : Cfg St := ⟨n5, blank, app (qL t ++ gapL 2) (Sb s)⟩

/-! ## home: `wa` crosses blocks and separators to the left end -/

theorem wcross {l : List Bool} (hl : Clean l) (s R : Strm) :
    Rch (cfgL wa (app l s) R) (cfgL wa s (app l.reverse R)) := by
  induction hl generalizing R with
  | nil => fin
  | @one l _ ih =>
    refine Rch.tr (sL (s := app l s) rfl) ?_
    simpa [app_append] using ih (T ::: R)
  | @sep l _ ih =>
    refine Rch.tr (sL (s := app (F :: T :: l) s) rfl) ?_
    refine Rch.tr (sL (s := app (T :: l) s) rfl) ?_
    refine Rch.tr (sL (s := app l s) rfl) ?_
    simpa [app_append] using ih (T ::: F ::: F ::: R)

theorem home (l : List Bool) (hl : Clean l) (R : Strm) :
    Rch (cfgL wa (app l blank) R) ⟨n5, blank, app l.reverse R⟩ := by
  refine Rch.tr (wcross hl blank R) ?_
  show Rch ⟨wa, blank, F ::: _⟩ _
  rw [← cons_blank, ← cons_blank]
  gl; gl; gR; gR; gR
  apply rch_eq _ rfl
  simp only [cons_blank]

theorem clean_rep (n : Nat) (l : List Bool) (hl : Clean l) : Clean (rep n ++ l) := by
  induction n with
  | zero => exact hl
  | succ n ih => exact Clean.one ih

theorem clean_sep (n : Nat) (l : List Bool) (hl : Clean l) : Clean (F :: F :: (rep (n + 1) ++ l)) :=
  Clean.sep (clean_rep n l hl)

/-- the queue read from Z's last cell to A's first -/
theorem qrev (t : Tup) : (qL t).reverse =
    [T, T, T] ++ [F, F] ++ rep t.2.2 ++ [F, F] ++ rep t.2.1 ++ [F, F] ++ rep t.1 := by
  obtain ⟨x, y, z⟩ := t
  simp [qL, rep, List.reverse_append, List.reverse_replicate]

theorem clean_qtail (t : Tup) (ht : Valid3 t) :
    Clean ([F, F] ++ rep t.2.2 ++ [F, F] ++ rep t.2.1 ++ [F, F] ++ rep t.1) := by
  obtain ⟨x, y, z⟩ := t
  obtain ⟨hx, hy, hz⟩ := ht
  obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  obtain ⟨z', rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine clean_sep z' _ (clean_sep y' _ ?_)
  have := clean_sep x' [] Clean.nil
  simpa using this

theorem clean_qrev (t : Tup) (ht : Valid3 t) : Clean (qL t).reverse := by
  rw [qrev]
  have := clean_qtail t ht
  simp only [List.append_assoc] at this ⊢
  exact Clean.one (Clean.one (Clean.one this))

theorem clean_ffq (t : Tup) (ht : Valid3 t) : Clean ([F, F] ++ (qL t).reverse) := by
  rw [qrev]
  have := clean_qtail t ht
  simp only [List.append_assoc, List.cons_append, List.nil_append] at this ⊢
  exact Clean.sep (Clean.one (Clean.one this))

/-- from G's cell 3 after Z (W = 0 or 1): home to A -/
theorem wrap (t : Tup) (ht : Valid3 t) (W : Nat) (hW : W ≤ 1) (s : Nat × Nat) :
    Rch ⟨n5, F ::: F ::: app (qL t).reverse blank, app (gm W ++ [F, F]) (Sb s)⟩
      ⟨n5, blank, app (qL t ++ gapL W) (Sb s)⟩ := by
  have hg : gm W = F :: F :: (if W = 0 then [F, F] else [T, T]) := by
    rcases W with _ | _ | W <;> simp [gm] <;> omega
  rw [hg]
  simp only [List.cons_append, app_cons]
  gl
  have := home ([F, F] ++ (qL t).reverse) (clean_ffq t ht)
    (F ::: F ::: app ((if W = 0 then [F, F] else [T, T]) ++ [F, F]) (Sb s))
  simp only [List.cons_append, List.nil_append, app_cons] at this
  refine Rch.tr this ?_
  apply rch_eq rfl
  simp [List.reverse_append, app_append, gapL, hg]

/-! ## the scan after an abort: left to A, filling every hole on the way -/

/-- `Cl l l'`: read leftwards, `l` becomes `l'` (its holes filled) -/
inductive Cl : List Bool → List Bool → Prop
  | nil : Cl [] []
  | one {l l'} : Cl l l' → Cl (T :: l) (T :: l')
  | sep {l l'} : Cl l l' → Cl (F :: F :: T :: l) (F :: F :: T :: l')
  | hole {l l'} : Cl (T :: l) (T :: l') → Cl (F :: T :: l) (T :: T :: l')
  | seph {l l'} : Cl (T :: l) (T :: l') → Cl (F :: F :: F :: T :: l) (F :: F :: T :: T :: l')

theorem Cl.reps (n : Nat) {l l' : List Bool} (h : Cl l l') : Cl (TM.PerfectCuboid.rep n ++ l) (TM.PerfectCuboid.rep n ++ l') := by
  induction n with
  | zero => exact h
  | succ n ih => exact Cl.one ih

theorem Cl.refl_clean {l : List Bool} (h : Clean l) : Cl l l := by
  induction h with
  | nil => exact Cl.nil
  | one _ ih => exact Cl.one ih
  | sep _ ih => exact Cl.sep ih

theorem clscan {l l' : List Bool} (h : Cl l l') (s R : Strm) :
    Rch (cfgL q1 (app l s) R) (cfgL q1 s (app l'.reverse R)) := by
  induction h generalizing R with
  | nil => fin
  | @one l l' _ ih =>
    refine Rch.tr (sL (s := app l s) rfl) ?_
    simpa [app_append] using ih (T ::: R)
  | @sep l l' _ ih =>
    refine Rch.tr (sL (s := app (F :: T :: l) s) rfl) ?_
    refine Rch.tr (sL (s := app (T :: l) s) rfl) ?_
    refine Rch.tr (sL (s := app l s) rfl) ?_
    simpa [app_append] using ih (T ::: F ::: F ::: R)
  | @hole l l' _ ih =>
    refine Rch.tr (sL (s := app (T :: l) s) rfl) ?_
    refine Rch.tr (sR (q := q2) rfl) ?_
    refine Rch.tr (sL2 (q := q3) rfl) ?_
    simpa [app_append] using ih (T ::: R)
  | @seph l l' _ ih =>
    refine Rch.tr (sL (s := app (F :: F :: T :: l) s) rfl) ?_
    refine Rch.tr (sL (s := app (F :: T :: l) s) rfl) ?_
    refine Rch.tr (sL (s := app (T :: l) s) rfl) ?_
    refine Rch.tr (sR (q := q5) rfl) ?_
    refine Rch.tr (sL2 (q := q3) rfl) ?_
    simpa [app_append] using ih (T ::: F ::: F ::: R)

/-- the scan reaches the blank left of A: then to A's first cell, in NEXCOM's `ea0` -/
theorem clean_home {l l' : List Bool} (h : Cl l l') (R : Strm) :
    Rch (cfgL q1 (app l blank) R) ⟨ea0, blank, app l'.reverse R⟩ := by
  refine Rch.tr (clscan h blank R) ?_
  show Rch ⟨q1, blank, F ::: _⟩ _
  rw [← cons_blank, ← cons_blank, ← cons_blank]
  gl; gl; gl; gR; gR; gR; gR
  apply rch_eq _ rfl
  simp only [cons_blank]

end TM.PerfectCuboid
