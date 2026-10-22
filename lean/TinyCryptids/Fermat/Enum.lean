import TinyCryptids.Fermat.Tuple
namespace TM.Fermat
open St

/-- `k` minimal blocks `111 00`, then `s` -/
def minc : Nat → Strm → Strm
  | 0, s => s
  | k + 1, s => ones 3 (F ::: F ::: minc k s)

def mincL : Nat → List Bool
  | 0 => []
  | k + 1 => [true, true, true, F, F] ++ mincL k

theorem app_mincL (k : Nat) (s : Strm) : app (mincL k) s = minc k s := by
  induction k with
  | zero => rfl
  | succ k ih => simp [mincL, minc, app_append, ih, ones_succ]

theorem mincL_rev (k : Nat) : (mincL k).reverse = List.reverse (mincL k) := rfl

theorem minc_comm (k : Nat) (L : Strm) : minc k (ones 3 (F ::: F ::: L)) = minc (k+1) L := by
  induction k with
  | zero => rfl
  | succ k ih => show ones 3 (F ::: F ::: minc k (ones 3 (F ::: F ::: L))) = _; rw [ih]; rfl

/-- moving through the chain of minimal blocks (state `u2` on the second separator cell) -/
theorem uchain (k : Nat) : ∀ (L S : Strm),
    Rch ⟨u2, L, F ::: minc k S⟩ ⟨u2, minc k L, F ::: S⟩ := by
  induction k with
  | zero => intro L S; fin
  | succ k ih =>
    intro L S
    show Rch ⟨u2, L, F ::: true ::: true ::: true ::: F ::: F ::: minc k S⟩ _
    gR; gR; gR; gR; gR
    refine Rch.tr (ih _ S) ?_
    rw [show (true ::: true ::: true ::: F ::: F ::: L) = ones 3 (F ::: F ::: L) from rfl, minc_comm]; fin

theorem mincL_succ_rev (k : Nat) : (mincL (k+1)).reverse = (mincL k).reverse ++ [F, F, true, true, true] := by
  simp [mincL]

theorem app_mincL_rev (k : Nat) : ∀ Y : Strm,
    app (mincL k).reverse (F ::: F ::: true ::: true ::: true ::: Y) = F ::: F ::: minc k (true ::: true ::: true ::: Y) := by
  induction k with
  | zero => intro Y; rfl
  | succ k ih =>
    intro Y
    rw [mincL_succ_rev, app_append]
    show app (mincL k).reverse (F ::: F ::: true ::: true ::: true ::: F ::: F ::: true ::: true ::: true ::: Y) = _
    rw [ih]
    show F ::: F ::: minc k (ones 3 (F ::: F ::: ones 3 Y)) = _
    rw [minc_comm]; rfl

theorem clean_chain2 (k n : Nat) :
    Clean (mincL k ++ rep (n+1)) ∧ Clean (F :: F :: (mincL k ++ rep (n+1))) := by
  induction k with
  | zero => exact ⟨Clean.replicate _, Clean.sep (Clean.replicate n)⟩
  | succ k ih =>
    refine ⟨Clean.one (Clean.one (Clean.one ih.2)), Clean.sep (Clean.one (Clean.one ih.2))⟩

theorem clean_chain (k n : Nat) : Clean ([true, true, true, F, F] ++ mincL k ++ rep (n+1)) :=
  (clean_chain2 (k+1) n).1

/-- transfer loop configurations: state `uh` on the exponent cursor (B1 cell 1,
B1 value `E1`), `k` minimal blocks, then B_h of length `ℓ` -/
def UE (E1 k ℓ : Nat) (R : Strm) : Cfg St :=
  ⟨uh, true ::: blank, false ::: ones E1 (F ::: F ::: minc k (ones ℓ (F ::: F ::: R)))⟩
def SU (E1 k ℓ : Nat) (R : Strm) : Cfg St :=
  ⟨su0, true ::: blank, false ::: ones E1 (F ::: F ::: minc k (ones ℓ (F ::: F ::: R)))⟩

theorem PHU : ParserL delta HU1 HU2 := ⟨rfl, rfl, rfl⟩
theorem PHS : ParserL delta HS1 HS2 := ⟨rfl, rfl, rfl⟩
theorem PHL : ParserL delta HL1 HL2 := ⟨rfl, rfl, rfl⟩

theorem chain_eq (k E1 : Nat) : true ::: true ::: true ::: F ::: F ::: minc k (true ::: ones E1 (F ::: true ::: blank)) =
    app ([true, true, true, F, F] ++ mincL k ++ rep (E1+1)) (F ::: true ::: blank) := by
  simp [app_append, app_replicate, app_mincL, ones_succ]

theorem u_unit_more (E1 k m : Nat) (R : Strm) : Rch (UE E1 k (m+5) R) (UE (E1+1) k (m+4) R) := by
  unfold UE
  gR; sRn E1; gR
  refine Rch.tr (uchain k _ _) ?_
  gR; gR; gR; gR; gR; gL
  show Rch (cfgL HU1 (true ::: true ::: true ::: F ::: F ::: minc k (true ::: ones E1 (F ::: true ::: blank)))
    (true ::: ones m (F ::: F ::: R))) _
  rw [chain_eq]
  refine Rch.tr (PHU.find (clean_chain k E1) _ _) ?_
  gR
  simp only [List.reverse_append, List.reverse_replicate, List.append_assoc, app_append, app_replicate]
  show Rch ⟨uh, true ::: blank, F ::: ones (E1 + 1) (app (mincL k).reverse
    (F ::: F ::: true ::: true ::: true ::: true ::: ones m (F ::: F ::: R)))⟩ _
  rw [app_mincL_rev]; fin

theorem u_unit_last (E1 k : Nat) (R : Strm) : Rch (UE E1 k 4 R) (SU (E1+1) k 3 R) := by
  unfold UE SU
  gR; sRn E1; gR
  refine Rch.tr (uchain k _ _) ?_
  gR; gR; gR; gR; gR; gL
  show Rch (cfgL HS1 (true ::: true ::: true ::: F ::: F ::: minc k (true ::: ones E1 (F ::: true ::: blank)))
    (F ::: F ::: R)) _
  rw [chain_eq]
  refine Rch.tr (PHS.find (clean_chain k E1) _ _) ?_
  gR
  simp only [List.reverse_append, List.reverse_replicate, List.append_assoc, app_append, app_replicate]
  show Rch ⟨su0, true ::: blank, F ::: ones (E1 + 1) (app (mincL k).reverse
    (F ::: F ::: true ::: true ::: true ::: F ::: F ::: R))⟩ _
  rw [app_mincL_rev]; fin

theorem u_loop (k : Nat) (R : Strm) : ∀ m E1, Rch (UE E1 k (m+4) R) (SU (E1 + m + 1) k 3 R) := by
  intro m
  induction m with
  | zero => intro E1; exact u_unit_last E1 k R
  | succ m ih =>
    intro E1
    refine Rch.tr (u_unit_more E1 k m R) ?_
    rw [show E1 + (m + 1) + 1 = (E1 + 1) + m + 1 by omega]; exact ih (E1+1)

/-- the configuration after the first step from a checkpoint -/
def en2C (E a b c : Nat) : Cfg St := ⟨en2, F ::: true ::: blank, ones E (app (tailL a b c) blank)⟩

theorem chk_step (E a b c : Nat) : step delta (chk E a b c) = some (en2C E a b c) := rfl

macro "c12" : tactic => `(tactic| repeat (first | exact Clean.nil | apply Clean.one | apply Clean.sep))

theorem enum_E (e a b c : Nat) : Rch (en2C (e+4) a b c) (suC (e+3) (a+1) b c) := by
  unfold en2C suC
  gR; gR; gR; gR; sRn e
  simp only [tailL, app_cons]
  gL; simp only [ones_cons_true]; gR; gR; gL
  have hw : Clean ([F, F] ++ rep (e+3)) := by simpa using Clean.sepRep (e+2) Clean.nil
  have e1 : F ::: F ::: true ::: true ::: true ::: ones e (F ::: true ::: blank) =
      app ([F, F] ++ rep (e+3)) (F ::: true ::: blank) := by
    simp [app_append, app_replicate, ones_succ, ones_cons_true]
  show Rch (cfgL HS1 (F ::: F ::: true ::: true ::: true ::: ones e (F ::: true ::: blank)) _) _
  rw [e1]
  refine Rch.tr (PHS.find hw _ _) ?_
  gR
  simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, ones_succ, ones_cons_true]
  fin

theorem enum_B2a (b c : Nat) : Rch (en2C 3 2 b c) (suC 3 1 (b+1) c) := by
  unfold en2C suC
  simp only [tailL, app_cons, app_append, app_replicate]
  gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR
  gL; gL; gL; gL; gL; gL; gL; gL; gL; gL
  refine Rch.tr (PHS.find (w := [true, true, true]) (by c12) _ _) ?_
  gR
  simp [ones_succ, ones_cons_true]; fin

theorem suC_SU (E a b c : Nat) :
    suC E (a+1) b c = SU E 0 (a+3) (ones (b+2) (F ::: F ::: ones (c+2) (F ::: F ::: true ::: F ::: F ::: F ::: true ::: blank))) := by
  unfold suC SU tailL; simp [app_append, app_replicate, minc]

theorem enum_B2b (m b c : Nat) : Rch (en2C 3 (m+3) b c) (suC (m+4) 1 (b+1) c) := by
  unfold en2C
  simp only [tailL, app_cons, app_append, app_replicate]
  gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; sRn m
  gR; gR; gR; gL; gL; gL; gL; simp only [ones_cons_true]
  gL; gL; gL; gL; gL
  have hw : Clean (rep m ++ [F, F, true, true, true]) := Clean.rep_append m (by c12)
  have e : ones m (false ::: false ::: true ::: true ::: true ::: F ::: true ::: blank) =
      app (rep m ++ [F, F, true, true, true]) (F ::: true ::: blank) := by
    simp [app_append, app_replicate]
  rw [e]
  refine Rch.tr (PHU.find hw _ _) ?_
  gR
  rw [suC_SU]
  have := u_loop 0 (ones (b+1+2) (F ::: F ::: ones (c+2) (F ::: F ::: true ::: F ::: F ::: F ::: true ::: blank))) m 3
  rw [show 3 + m + 1 = m + 4 by omega] at this
  refine Rch.tr ?_ this
  unfold UE
  simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, minc, ones_succ, ones_cons_true]
  fin

theorem enum_B3a (c : Nat) : Rch (en2C 3 1 2 c) (suC 3 1 1 (c+1)) := by
  unfold en2C suC
  simp only [tailL, app_cons, app_append, app_replicate]
  gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR
  gL; gL; gL; gL; gL; gL; gL; gL; gL; gL
  refine Rch.tr (PHS.find (w := [true, true, true, F, F, true, true, true]) (by c12) _ _) ?_
  gR
  simp [ones_succ, ones_cons_true]; fin

theorem enum_B3b (m c : Nat) : Rch (en2C 3 1 (m+3) c) (suC (m+4) 1 1 (c+1)) := by
  unfold en2C
  simp only [tailL, app_cons, app_append, app_replicate]
  gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; sRn m
  gR; gR; gR; gL; gL; gL; gL; simp only [ones_cons_true]
  gL; gL; gL; gL; gL
  have hw : Clean (rep m ++ [F, F, true, true, true, F, F, true, true, true]) := Clean.rep_append m (by c12)
  have e : ones m (false ::: false ::: true ::: true ::: true ::: false ::: false ::: true ::: true :::
      true ::: F ::: true ::: blank) =
      app (rep m ++ [F, F, true, true, true, F, F, true, true, true]) (F ::: true ::: blank) := by
    simp [app_append, app_replicate]
  rw [e]
  refine Rch.tr (PHU.find hw _ _) ?_
  gR
  have hs : suC (m+4) 1 1 (c+1) = SU (m+4) 1 3 (ones (c+1+2) (F ::: F ::: true ::: F ::: F ::: F ::: true ::: blank)) := by
    unfold suC SU tailL; simp [app_append, app_replicate, minc]
  rw [hs]
  have := u_loop 1 (ones (c+1+2) (F ::: F ::: true ::: F ::: F ::: F ::: true ::: blank)) m 3
  rw [show 3 + m + 1 = m + 4 by omega] at this
  refine Rch.tr ?_ this
  unfold UE
  simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, minc, ones_succ, ones_cons_true]
  fin

theorem enum_last (m : Nat) : Rch (en2C 3 1 1 (m+2)) (suC (m+5) 1 1 1) := by
  unfold en2C
  simp only [tailL, app_cons, app_append, app_replicate]
  gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; sRn m
  gR; gR; gR; gL
  have hw : Clean ([true, F, F] ++ rep (m+4) ++ [F, F, true, true, true, F, F, true, true, true, F, F, true, true, true]) := by
    show Clean (true :: F :: F :: true :: (rep (m+3) ++
      [F, F, true, true, true, F, F, true, true, true, F, F, true, true, true]))
    exact Clean.one (Clean.sep (Clean.rep_append _ (by c12)))
  have e : true ::: false ::: false ::: ones m (true ::: true ::: true ::: true ::: F ::: F ::: true ::: true :::
      true ::: F ::: F ::: true ::: true ::: true ::: F ::: F ::: true ::: true ::: true ::: F ::: true ::: blank) =
      app ([true, F, F] ++ rep (m+4) ++ [F, F, true, true, true, F, F, true, true, true, F, F, true, true, true])
        (F ::: true ::: blank) := by
    simp [app_append, app_replicate, ones_succ, ones_cons_true]
  show Rch (cfgL HL1 (true ::: false ::: false ::: ones m (true ::: true ::: true ::: true ::: F ::: F ::: true :::
      true ::: true ::: F ::: F ::: true ::: true ::: true ::: F ::: F ::: true ::: true ::: true ::: F :::
      true ::: blank)) _) _
  rw [e]
  refine Rch.tr (PHL.find hw _ _) ?_
  gL; gR; gR; gL
  have hs : suC (m+5) 1 1 1 = SU (m+5) 2 3 (true ::: F ::: F ::: F ::: true ::: blank) := by
    unfold suC SU tailL; simp [app_append, app_replicate, minc, ones_succ]
  rw [hs]
  have := u_loop 2 (true ::: F ::: F ::: F ::: true ::: blank) m 4
  rw [show 4 + m + 1 = m + 5 by omega] at this
  refine Rch.tr ?_ this
  unfold UE
  simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, minc, ones_succ, ones_cons_true]
  fin

end TM.Fermat
