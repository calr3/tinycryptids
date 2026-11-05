import TinyCryptids.LehmerTau.RAct

/-!
# The R phase: the action at a divisor `d` of `i`

D divides `i`: the walk moves to the frame E (E gets its hole: `e = 1` divides `j`), goes
through the divisors `e` of `j` (`eact`), unshifts E back to rest, gives D its hole back and
resumes the walk on D. P gains `Σ_{e ∣ j} d⁵ e⁵ · pK KL`.
-/

namespace TM.LehmerTau
open St

local notation "F" => false

/-- right of Rd in the R phase: E at rest (3 cells), Re (`j + 1` cells), S0 -/
def BD (j : Nat) : Strm := ones 3 (F ::: F ::: ones (j + 1) (F ::: F ::: ones 2 blank))

/-- D divides `i`: to E, which gets its hole -/
theorem dd_e (K : List KB) (a d rd j : Nat) (hd : 1 ≤ d) (hj : 1 ≤ j) :
    Rch (DV (LS a (.pl 1 :: .pl 13 :: K)) (BD j) d rd)
      (DV (LS a (.pl (rd + 2) :: .dg d 1 :: .pl 1 :: .pl 13 :: K)) (ones 2 blank) 1 (j - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  unfold DV BD RB
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [LS_pl]
  gL; gL; gL; gR; gR; gR; gR; gR; gR; gR
  sRn d'; gR; gR; sRn (rd + 2); gR; gR; gR; gR; gR; gL; gL; gL; gL
  simp only [LS_pl, LS_dg1, ones_succ' d', Nat.add_sub_cancel]
  rw [ones_add2 m]; fin

/-- the e-loop is over: E unshifted, D's hole back, resume D -/
theorem ue_d (K : List KB) (a d rd j : Nat) (hj : 1 ≤ j) :
    Rch (F2 (LS a (.pl (rd + 2) :: .pl (d + 2) :: .pl 1 :: .pl 13 :: K)) (ones 2 blank) j)
      (RS (LS a (.pl 1 :: .pl 13 :: K)) (BD j) d rd) := by
  refine Rch.tr (F2_UN _ _ j hj) ?_
  rw [LS_pl, show ones (rd + 2) (F ::: F ::: LS a (.pl (d + 2) :: .pl 1 :: .pl 13 :: K)) =
    true ::: ones (rd + 1) (F ::: F ::: LS a (.pl (d + 2) :: .pl 1 :: .pl 13 :: K)) from rfl]
  refine Rch.tr (unshift _ j _ hj) ?_
  rw [LS_pl, LS_pl]
  unfold RS BD RB
  gL; sLn rd; gL; gL; sLn (d + 2); gR; gR; gR
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [ones_add2 rd, ones_add, show m + 2 = m + 1 + 1 from rfl]; fin

/-- **The action at a divisor `d` of `i`** (R phase) -/
theorem dact_R (KL : List KB) (hKL : ∀ b ∈ KL, b.ok) (hr : rsK KL = KL) (a d rd j : Nat) (hd : 1 ≤ d) (hj : 1 ≤ j) :
    Rch (DV (LS a (.pl 1 :: .pl 13 :: KL)) (BD j) d rd)
      (RS3 (LS (a + dsum (fun e => d ^ 5 * e ^ 5 * pK KL) j j) (.pl 1 :: .pl 13 :: KL)) (BD j) d rd) := by
  refine Rch.tr (dd_e KL a d rd j hd hj) ?_
  have s1 := eact KL hKL hr a d rd 1 (j - 1) hd (Nat.le_refl _) (.dg d 1) (Or.inr rfl)
  refine Rch.tr s1 ?_
  let Xs : Nat → Strm := fun a => LS a (.pl (rd + 2) :: .pl (d + 2) :: .pl 1 :: .pl 13 :: KL)
  have s2 := dloopR Xs (ones 2 blank) (fun e => d ^ 5 * e ^ 5 * pK KL) j
    (fun a' x hx _ _ => eact KL hKL hr a' d rd x (j - x) hd hx (.pl (d + 2)) (Or.inl rfl))
    (j - 1) (a + d ^ 5 * 1 ^ 5 * pK KL) 1 rfl (Nat.le_refl _) hj
  refine Rch.tr s2 ?_
  have e1 : dsum (fun e => d ^ 5 * e ^ 5 * pK KL) j 1 = d ^ 5 * 1 ^ 5 * pK KL := by
    simp [dsum, Nat.mod_one]
  have m1 := dsum_mono (fun e => d ^ 5 * e ^ 5 * pK KL) j hj
  rw [e1] at m1 ⊢
  rw [show a + d ^ 5 * 1 ^ 5 * pK KL + dsum (fun e => d ^ 5 * e ^ 5 * pK KL) j j - d ^ 5 * 1 ^ 5 * pK KL =
    a + dsum (fun e => d ^ 5 * e ^ 5 * pK KL) j j by omega]
  exact Rch.tr (ue_d KL _ d rd j hj) (rs_rs3 _ _ d rd hd)

end TM.LehmerTau
