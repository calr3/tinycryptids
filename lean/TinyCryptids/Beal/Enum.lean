import TinyCryptids.Beal.Tuple

/-!
# The enumeration step

NEXCOM on the six block lengths minus 4 (minimal blocks `1111`). `UE`/`SU`: the transfer loop,
with `k` minimal blocks between x and the block `B_h` that gives up its excess.
-/

namespace TM.Beal
open St

/-- `k` minimal blocks `1111 00`, then `s` -/
def minc : Nat → Strm → Strm
  | 0, s => s
  | k + 1, s => ones 4 (F ::: F ::: minc k s)

def mincL : Nat → List Bool
  | 0 => []
  | k + 1 => [true, true, true, true, F, F] ++ mincL k

theorem app_mincL (k : Nat) (s : Strm) : app (mincL k) s = minc k s := by
  induction k with
  | zero => rfl
  | succ k ih => simp [mincL, minc, app_append, ih, ones_succ]

theorem minc_comm (k : Nat) (L : Strm) : minc k (ones 4 (F ::: F ::: L)) = minc (k + 1) L := by
  induction k with
  | zero => rfl
  | succ k ih => show ones 4 (F ::: F ::: minc k (ones 4 (F ::: F ::: L))) = _; rw [ih]; rfl

/-- through the chain of minimal blocks (state `u2` on a separator's second cell) -/
theorem uchain (k : Nat) : ∀ (L S : Strm),
    Rch ⟨u2, L, F ::: minc k S⟩ ⟨u2, minc k L, F ::: S⟩ := by
  induction k with
  | zero => intro L S; fin
  | succ k ih =>
    intro L S
    show Rch ⟨u2, L, F ::: true ::: true ::: true ::: true ::: F ::: F ::: minc k S⟩ _
    gR; gR; gR; gR; gR; gR
    refine Rch.tr (ih _ S) ?_
    rw [show (true ::: true ::: true ::: true ::: F ::: F ::: L) = ones 4 (F ::: F ::: L) from rfl, minc_comm]; fin

theorem mincL_succ_rev (k : Nat) :
    (mincL (k + 1)).reverse = (mincL k).reverse ++ [F, F, true, true, true, true] := by
  simp [mincL]

theorem app_mincL_rev (k : Nat) : ∀ Y : Strm,
    app (mincL k).reverse (F ::: F ::: true ::: true ::: true ::: true ::: Y) =
      F ::: F ::: minc k (true ::: true ::: true ::: true ::: Y) := by
  induction k with
  | zero => intro Y; rfl
  | succ k ih =>
    intro Y
    rw [mincL_succ_rev, app_append]
    show app (mincL k).reverse (F ::: F ::: true ::: true ::: true ::: true ::: F ::: F ::: true ::: true :::
      true ::: true ::: Y) = _
    rw [ih]
    show F ::: F ::: minc k (ones 4 (F ::: F ::: ones 4 Y)) = _
    rw [minc_comm]; rfl

theorem clean_chain2 (k n : Nat) :
    Clean (mincL k ++ rep (n + 1)) ∧ Clean (F :: F :: (mincL k ++ rep (n + 1))) := by
  induction k with
  | zero => exact ⟨Clean.replicate _, Clean.sep (Clean.replicate n)⟩
  | succ k ih =>
    exact ⟨Clean.one (Clean.one (Clean.one (Clean.one ih.2))), Clean.sep (Clean.one (Clean.one (Clean.one ih.2)))⟩

theorem clean_chain (k n : Nat) : Clean ([true, true, true, true, F, F] ++ mincL k ++ rep (n + 1)) :=
  (clean_chain2 (k + 1) n).1

/-- state `uh` on x's anchor, x with `E1` cells right of it, `k` minimal blocks, `B_h` of length `ℓ` -/
def UE (E1 k ℓ : Nat) (R : Strm) : Cfg St :=
  ⟨uh, true ::: blank, F ::: ones E1 (F ::: F ::: minc k (ones ℓ (F ::: F ::: R)))⟩
def SU (E1 k ℓ : Nat) (R : Strm) : Cfg St :=
  ⟨gA0, true ::: blank, F ::: ones E1 (F ::: F ::: minc k (ones ℓ (F ::: F ::: R)))⟩

theorem PHU : ParserL delta HU1 HU2 := ⟨rfl, rfl, rfl⟩
theorem PHS : ParserL delta HS1 HS2 := ⟨rfl, rfl, rfl⟩
theorem PHL : ParserL delta HL1 HL2 := ⟨rfl, rfl, rfl⟩

theorem chain_eq (k E1 : Nat) :
    true ::: true ::: true ::: true ::: F ::: F ::: minc k (true ::: ones E1 (F ::: true ::: blank)) =
      app ([true, true, true, true, F, F] ++ mincL k ++ rep (E1 + 1)) (F ::: true ::: blank) := by
  simp [app_append, app_replicate, app_mincL, ones_succ]

theorem u_unit_more (E1 k m : Nat) (R : Strm) : Rch (UE E1 k (m + 6) R) (UE (E1 + 1) k (m + 5) R) := by
  unfold UE
  gR; sRn E1; gR
  refine Rch.tr (uchain k _ _) ?_
  gR; gR; gR; gR; gR; gR; gL
  show Rch (cfgL HU1 (true ::: true ::: true ::: true ::: F ::: F ::: minc k (true ::: ones E1 (F ::: true ::: blank)))
    (true ::: ones m (F ::: F ::: R))) _
  rw [chain_eq]
  refine Rch.tr (PHU.find (clean_chain k E1) _ _) ?_
  gR
  simp only [List.reverse_append, List.reverse_replicate, List.append_assoc, app_append, app_replicate]
  show Rch ⟨uh, true ::: blank, F ::: ones (E1 + 1) (app (mincL k).reverse
    (F ::: F ::: true ::: true ::: true ::: true ::: true ::: ones m (F ::: F ::: R)))⟩ _
  rw [app_mincL_rev]; fin

theorem u_unit_last (E1 k : Nat) (R : Strm) : Rch (UE E1 k 5 R) (SU (E1 + 1) k 4 R) := by
  unfold UE SU
  gR; sRn E1; gR
  refine Rch.tr (uchain k _ _) ?_
  gR; gR; gR; gR; gR; gR; gL
  show Rch (cfgL HS1 (true ::: true ::: true ::: true ::: F ::: F ::: minc k (true ::: ones E1 (F ::: true ::: blank)))
    (F ::: F ::: R)) _
  rw [chain_eq]
  refine Rch.tr (PHS.find (clean_chain k E1) _ _) ?_
  gR
  simp only [List.reverse_append, List.reverse_replicate, List.append_assoc, app_append, app_replicate]
  show Rch ⟨gA0, true ::: blank, F ::: ones (E1 + 1) (app (mincL k).reverse
    (F ::: F ::: true ::: true ::: true ::: true ::: F ::: F ::: R))⟩ _
  rw [app_mincL_rev]; fin

theorem u_loop (k : Nat) (R : Strm) : ∀ m E1, Rch (UE E1 k (m + 5) R) (SU (E1 + m + 1) k 4 R) := by
  intro m
  induction m with
  | zero => intro E1; exact u_unit_last E1 k R
  | succ m ih =>
    intro E1
    refine Rch.tr (u_unit_more E1 k m R) ?_
    rw [show E1 + (m + 1) + 1 = (E1 + 1) + m + 1 by omega]; exact ih (E1 + 1)

theorem app_mincL_rev2 (k : Nat) : ∀ Z : Strm,
    app (mincL k).reverse (F ::: F ::: Z) = F ::: F ::: minc k Z := by
  induction k with
  | zero => intro Z; rfl
  | succ k ih =>
    intro Z
    rw [mincL_succ_rev, app_append]
    show app (mincL k).reverse (F ::: F ::: true ::: true ::: true ::: true ::: F ::: F ::: Z) = _
    rw [ih]
    show F ::: F ::: minc k (ones 4 (F ::: F ::: Z)) = _
    rw [minc_comm]

/-- the f-scan over minimal blocks (state `f2` on a block's cell 0) -/
theorem fchain (k : Nat) : ∀ (L S : Strm),
    Rch ⟨f2, L, minc k S⟩ ⟨f2, app (mincL k).reverse L, S⟩ := by
  induction k with
  | zero => intro L S; fin
  | succ k ih =>
    intro L S
    show Rch ⟨f2, L, true ::: true ::: true ::: true ::: F ::: F ::: minc k S⟩ _
    gR; gR; gR; gR; gR; gR
    refine Rch.tr (ih _ S) ?_
    rw [mincL_succ_rev, app_append]; fin

theorem clean_rev_chain (k : Nat) : ∀ (l : List Bool), Clean l → Clean ((mincL k).reverse ++ l) := by
  induction k with
  | zero => intro l hl; exact hl
  | succ k ih =>
    intro l hl
    rw [mincL_succ_rev, List.append_assoc]
    exact ih _ (Clean.sep (Clean.one (Clean.one (Clean.one hl))))

/-- `B_h` (`t + 5` cells, after `k` minimal blocks) gives one cell to the next block and its
remaining excess to x -/
theorem enum_mid (k t ℓ : Nat) (R0 : Strm) :
    Rch ⟨en2, F ::: true ::: blank, ones 2 (F ::: F ::: minc k (ones (t + 5) (F ::: F ::: ones (ℓ + 4) R0)))⟩
      (SU (t + 2) k 4 (ones (ℓ + 5) R0)) := by
  gR; gR; gR; gR
  refine Rch.tr (fchain k _ _) ?_
  gR; gR; gR; gR; gR; sRn t; gR; gR; gR; gL
  simp only [ones_cons_true]
  gL; gL; gL; gL; gL; gL; gL; gL
  cases t with
  | zero =>
    rw [ones_zero, app_mincL_rev2]
    gL; gL
    have e2 : minc k (true ::: true ::: F ::: true ::: blank) = app (mincL k ++ rep 2) (F ::: true ::: blank) := by
      simp [app_append, app_mincL]; rfl
    rw [e2]
    refine Rch.tr (PHS.find (clean_chain2 k 1).1 _ _) ?_
    gR
    unfold SU
    simp only [List.reverse_append, List.reverse_replicate, app_append, app_replicate]
    show Rch ⟨gA0, true ::: blank, F ::: ones 2 (app (mincL k).reverse
      (F ::: F ::: true ::: true ::: true ::: true ::: F ::: F ::: true ::: true ::: true ::: ones (ℓ + 2) R0))⟩ _
    rw [app_mincL_rev]; fin
  | succ t =>
    simp only [ones_succ]
    gL
    rw [app_mincL_rev2]
    have hw : Clean (rep t ++ F :: F :: (mincL k ++ rep 2)) := Clean.rep_append t (clean_chain2 k 1).2
    have e2 : ones t (F ::: F ::: minc k (true ::: true ::: F ::: true ::: blank)) =
        app (rep t ++ F :: F :: (mincL k ++ rep 2)) (F ::: true ::: blank) := by
      simp [app_append, app_mincL, app_replicate]; rfl
    rw [e2]
    refine Rch.tr (PHU.find hw _ _) ?_
    gR
    have := u_loop k (ones (ℓ + 5) R0) t 2
    rw [show 2 + t + 1 = t + 1 + 2 by omega] at this
    refine Rch.tr ?_ this
    unfold UE
    simp only [List.reverse_append, List.reverse_replicate, app_append, app_replicate, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.singleton_append, app_cons, app_nil]
    show Rch ⟨uh, true ::: blank, F ::: ones 2 (app (mincL k).reverse (F ::: F ::: ones t
      (true ::: true ::: true ::: true ::: true ::: F ::: F ::: true ::: true ::: true ::: ones (ℓ + 2) R0)))⟩ _
    rw [app_mincL_rev2]
    show Rch ⟨uh, true ::: blank, F ::: ones 2 (F ::: F ::: minc k (ones t (ones 5
      (F ::: F ::: true ::: true ::: true ::: ones (ℓ + 2) R0))))⟩ _
    rw [ones_add]; fin

/-- x is not minimal: x gives a cell to y -/
theorem enum_first (e L2 : Nat) (R : Strm) :
    Rch ⟨en2, F ::: true ::: blank, ones (e + 3) (F ::: F ::: ones L2 R)⟩
      ⟨gA0, true ::: blank, F ::: ones (e + 2) (F ::: F ::: ones (L2 + 1) R)⟩ := by
  rw [show e + 3 = 3 + e by omega, ← ones_add]
  gR; gR; gR; sRn e; gL
  simp only [ones_cons_true]
  gR; gR; gL
  have hw : Clean ([F, F] ++ rep (e + 2)) := Clean.sep (Clean.replicate (e + 1))
  have e1 : F ::: F ::: true ::: true ::: ones e (F ::: true ::: blank) =
      app ([F, F] ++ rep (e + 2)) (F ::: true ::: blank) := by
    simp [app_append, app_replicate, ones_succ, ones_cons_true]
  show Rch (cfgL HS1 (F ::: F ::: true ::: true ::: ones e (F ::: true ::: blank)) _) _
  rw [e1]
  refine Rch.tr (PHS.find hw _ _) ?_
  gR
  simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, ones_succ, ones_cons_true]
  fin

/-- the last block c is the first non-minimal one: x grows by one, then takes c's excess -/
theorem enum_last (t : Nat) :
    Rch ⟨en2, F ::: true ::: blank, ones 2 (F ::: F ::: minc 4 (ones (t + 5) (F ::: F ::: true ::: F ::: F ::: ones 2 blank)))⟩
      (SU (t + 4) 4 4 (true ::: F ::: F ::: ones 2 blank)) := by
  gR; gR; gR; gR
  refine Rch.tr (fchain 4 _ _) ?_
  gR; gR; gR; gR; gR; sRn t; gR; gR; gR; gL
  show Rch (cfgL HL1 (true ::: F ::: F ::: ones t (true ::: true ::: true ::: true ::: true :::
    app (mincL 4).reverse (F ::: F ::: true ::: true ::: F ::: true ::: blank))) _) _
  rw [app_mincL_rev2]
  have hw : Clean ([true, F, F] ++ rep (t + 5) ++ F :: F :: (mincL 4 ++ rep 2)) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact Clean.one (Clean.sep (Clean.rep_append (t + 4) (clean_chain2 4 1).2))
  have e1 : true ::: F ::: F ::: ones t (true ::: true ::: true ::: true ::: true ::: F ::: F :::
      minc 4 (true ::: true ::: F ::: true ::: blank)) =
      app ([true, F, F] ++ rep (t + 5) ++ F :: F :: (mincL 4 ++ rep 2)) (F ::: true ::: blank) := by
    simp only [app_append, app_cons, app_nil, app_replicate, app_mincL]
    rw [show ones (t + 5) = fun X => ones t (ones 5 X) from funext fun X => (ones_add t 5 X).symm]; rfl
  rw [e1]
  refine Rch.tr (PHL.find hw _ _) ?_
  gL; gR; gR; gL
  have := u_loop 4 (true ::: F ::: F ::: ones 2 blank) t 3
  rw [show 3 + t + 1 = t + 4 by omega] at this
  refine Rch.tr ?_ this
  unfold UE
  simp only [List.reverse_append, List.reverse_replicate, app_append, app_replicate, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.singleton_append, app_cons, app_nil, List.append_assoc]
  rw [app_mincL_rev2]; fin

end TM.Beal
