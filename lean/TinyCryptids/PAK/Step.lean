import TinyCryptids.PAK.Cand
import TinyCryptids.PA.Search

/-!
# One iteration, and the search finds `v0 ∈ v0` iff T proves it

As `PA/Step.lean` and `PA/Search.lean`, for this machine's candidates: their order
(`configs.py`, D = 8: B2, B6c, B3, B8b, B8c, B8a, B1, B4, B6b, B7, E, then B6a) and forms (B4,
B8b and E with two antecedents swapped).  `stepK` is one iteration of `pa/ref.py`'s
`iterate_tail` with these candidates; `iterK_eq`: main's iteration computes it.  The
enumeration of proof codes (`TM.PA.decStep`, `TM.PA.steps`, `TM.PA.listCode`) is shared.
-/

namespace TMK.PA

open TinyCryptids Wff
open TM.PA (A S Stp decStep nextWs unpair pair impC allC enc code decode Prov Prop3 QAx elem
  decode_impC decode_allC decode_exC decode_andC decode_negC decode_elC decode_eqC decode_code
  decode_zero decode_one perm_r e_swap prop3_T qax_T eq00 decode0 Good good_push elem_zero
  steps listCode steps_listCode encStp decStep_enc decStep_snd_le provable_iff unpair_pair)

/-- the twelve axiom candidates for parameters `p1 p2 p3`; B6a is `v0 = v0` (code 0) when `p3`
is `p1` or `p2` -/
def candList (p1 p2 p3 : Nat) : List Nat :=
  [axB2 p1 p2 p3, axB6c p1 p2 p3, axB3 p1 p2 p3, axB8b p1 p2 p3, axB8c p1 p2 p3, axB8a p1 p2 p3,
   axB1 p1 p2 p3, axB4 p1 p2 p3, axB6b p1 p2 p3, axB7 p1 p2 p3, axE p1 p2 p3,
   if p2 = p3 ∨ p3 = p1 then 0 else axB6a p1 p2 p3]

/-- the kept theorem (as `TM.PA.kept`, with these candidates) -/
def kept (ac p1 p2 p3 top ws : Nat) : Nat :=
  if ac = 0 then 0
  else if ac ≤ 12 then (candList p1 p2 p3).getD (ac - 1) 0
  else if ac = 13 then allC p1 top
  else if (unpair ws).snd = impC top p1 then p1 else 0

def runStp (s : Stp) (top ws : Nat) : Nat × Nat :=
  (kept s.ac s.p1 s.p2 s.p3 top ws, nextWs s.ac top ws)

/-- one iteration -/
def stepK (σ : S) : S :=
  let d := decStep σ.code
  ⟨d.snd, σ.np', (runStp d.fst σ.top σ.ws).fst, (runStp d.fst σ.top σ.ws).snd⟩

/-- main's iteration from a register file whose stack is empty (on its base) and `param2` zero -/
theorem iterK_eq (a : A) (hs : a.stk = []) (hp : a.p2 = 0) :
    let σ : S := ⟨a.pl, a.np, a.top, a.base⟩
    (iterK a).pl = (stepK σ).pl ∧ (iterK a).np = (stepK σ).np ∧ (iterK a).top = (stepK σ).top ∧
      enc (iterK a).base (iterK a).stk = (stepK σ).ws ∧ (iterK a).p2 = 0 := by
  obtain ⟨pl, np, top, ac, p1, p2, p3, base, stk⟩ := a
  simp only at hs hp
  subst hs hp
  simp only [iterK, decodeK, A.reload, A.zeroAc, A.zeroP1, A.zeroP3, A.decAc, A.decP1, A.decP2,
    A.decP3, A.push, kcB2_eq, kcB6c_eq, kcB3_eq, kcB8b_eq, kcB8c_eq, kcB8a_eq, kcB1_eq, kcB4_eq,
    kcB6b_eq, kcB7_eq, kcE_eq, kcB6a_eq, stepK, decStep, S.code, S.np', runStp, kept, nextWs, candList,
    Nat.zero_add]
  generalize (unpair (unpair (unpair (unpair (if pl = 0 then np else pl - 1)).fst).fst).fst).snd = P3
  generalize (unpair (unpair (unpair (unpair (if pl = 0 then np else pl - 1)).fst).fst).fst).fst = RST
  generalize (unpair (unpair (unpair (if pl = 0 then np else pl - 1)).fst).fst).snd = P2
  generalize (unpair (unpair (if pl = 0 then np else pl - 1)).fst).snd = P1
  generalize (unpair (if pl = 0 then np else pl - 1)).snd = AC
  rcases AC with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | AC
  all_goals simp [A.gen, A.det, A.decAc1, A.pop3, A.pop2, A.pop, A.par1, A.par3, A.wal, A.wim, A.v2,
    A.v4, A.cons, A.push, A.incT, A.detCmp, A.drop, enc, TM.PA.allC, TM.PA.impC]

/-! ## soundness: every candidate decodes to a theorem of T -/

theorem cand_sound (p1 p2 p3 k : Nat) (hk : k < 12) :
    Prov Axiom (decode ((candList p1 p2 p3).getD k 0)) := by
  have hP := prop3_T
  have hQ := qax_T
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · simp only [candList, List.getD, List.get?, Option.getD, axB2, decode_impC, decode_negC]
    exact Prov.ax (Axiom.b2 _)
  · simp only [candList, List.getD, List.get?, Option.getD, axB6c, decode_impC, decode_exC, decode_allC]
    exact Prov.ax (Axiom.b6c _ _)
  · simp only [candList, List.getD, List.get?, Option.getD, axB3, decode_impC, decode_negC]
    exact Prov.ax (Axiom.b3 _ _)
  · -- B8b (form 1)
    simp only [candList, List.getD, List.get?, Option.getD, axB8b, decode_impC, decode_eqC, decode_elC]
    exact perm_r hP (Prov.ax (Axiom.b8b _ _ _))
  · simp only [candList, List.getD, List.get?, Option.getD, axB8c, decode_impC, decode_eqC, decode_elC]
    exact Prov.ax (Axiom.b8c _ _ _)
  · simp only [candList, List.getD, List.get?, Option.getD, axB8a, decode_impC, decode_eqC]
    exact Prov.ax (Axiom.b8a _ _ _)
  · simp only [candList, List.getD, List.get?, Option.getD, axB1, decode_impC]
    exact Prov.ax (Axiom.b1 _ _ _)
  · -- B4 (form 1)
    simp only [candList, List.getD, List.get?, Option.getD, axB4, decode_impC, decode_allC]
    exact perm_r hP (Prov.ax (Axiom.b4 _ _ _))
  · simp only [candList, List.getD, List.get?, Option.getD, axB6b, decode_impC, decode_allC]
    exact Prov.ax (Axiom.b6b _ _ _)
  · simp only [candList, List.getD, List.get?, Option.getD, axB7, decode_exC, decode_eqC]
    exact Prov.ax (Axiom.b7 _ _)
  · -- E (form 1)
    have := (e_swap hP hQ (decode p3)).1
    simp only [candList, List.getD, List.get?, Option.getD, axE, decode_exC, decode_allC,
      decode_andC, decode_impC, decode_negC, decode_elC, decode_eqC]
    exact Prov.mp this (Prov.ax (Axiom.e _))
  · simp only [candList, List.getD, List.get?, Option.getD]
    by_cases h : p2 = p3 ∨ p3 = p1
    · rw [if_pos h]; exact decode0
    · rw [if_neg h]
      simp only [axB6a, decode_andC, decode_impC, decode_eqC, decode_elC, decode_allC]
      exact Prov.ax (Axiom.b6a _ _ _ (fun e => h (Or.inl e.symm)) (fun e => h (Or.inr e)))
  · omega

theorem good_step {σ : S} (h : Good σ) : Good (stepK σ) := by
  obtain ⟨ht, hw⟩ := h
  simp only [stepK, runStp, Good]
  generalize (decStep σ.code).fst = st
  obtain ⟨ac, p1, p2, p3⟩ := st
  simp only [kept, nextWs]
  by_cases h0 : ac = 0
  · subst h0; simp only [if_true, Nat.zero_le]; exact ⟨decode0, good_push ht hw⟩
  by_cases h12 : ac ≤ 12
  · simp only [h0, h12, if_true, if_false]
    exact ⟨cand_sound _ _ _ _ (by omega), good_push ht hw⟩
  by_cases h13 : ac = 13
  · subst h13
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl, if_neg (by decide), if_pos rfl]
    refine ⟨?_, hw⟩
    rw [decode_allC]; exact Prov.gen _ ht
  · simp only [h0, h12, h13, if_false]
    refine ⟨?_, fun n => hw (n + 1)⟩
    by_cases he : (unpair σ.ws).snd = impC σ.top p1
    · rw [if_pos he]
      have := hw 0
      simp only [elem, he, decode_impC] at this
      exact Prov.mp this ht
    · rw [if_neg he]; exact decode0

/-! ## completeness: the candidates derive every axiom of T -/

/-- formulas whose code the machine can keep as an axiom candidate -/
def MAx (φ : Wff) : Prop := ∃ p1 p2 p3 k, k < 12 ∧ (candList p1 p2 p3).getD k 0 = code φ

theorem prop3_M : Prop3 MAx :=
  ⟨fun φ ψ χ => Prov.ax ⟨code χ, code φ, code ψ, 6, by decide, rfl⟩,
   fun φ => Prov.ax ⟨code φ, 0, 0, 0, by decide, rfl⟩,
   fun φ ψ => Prov.ax ⟨0, code φ, code ψ, 2, by decide, rfl⟩⟩

theorem qax_M : QAx MAx := fun x φ ψ =>
  perm_r prop3_M (Prov.ax ⟨code ψ, x, code φ, 7, by decide, rfl⟩)

theorem axiom_M {φ : Wff} (h : Axiom φ) : Prov MAx φ := by
  cases h with
  | b1 => exact prop3_M.b1 _ _ _
  | b2 => exact prop3_M.b2 _
  | b3 => exact prop3_M.b3 _ _
  | b4 => exact qax_M _ _ _
  | b6a x y z h1 h2 =>
    refine Prov.ax ⟨y, x, z, 11, by decide, ?_⟩
    have : ¬ (x = z ∨ z = y) := fun e => e.elim (fun e => h1 e.symm) (fun e => h2 e)
    simp only [candList, List.getD, List.get?, Option.getD, if_neg this]; rfl
  | b6b x y φ => exact Prov.ax ⟨code φ, x, y, 8, by decide, rfl⟩
  | b6c x φ => exact Prov.ax ⟨code φ, x, 0, 1, by decide, rfl⟩
  | b7 x y => exact Prov.ax ⟨y, x, 0, 9, by decide, rfl⟩
  | b8a x y z => exact Prov.ax ⟨z, x, y, 5, by decide, rfl⟩
  | b8b x y z => exact perm_r prop3_M (Prov.ax ⟨y, x, z, 3, by decide, rfl⟩)
  | b8c x y z => exact Prov.ax ⟨z, x, y, 4, by decide, rfl⟩
  | e φ => exact Prov.mp (e_swap prop3_M qax_M φ).2 (Prov.ax ⟨0, 0, code φ, 10, by decide, rfl⟩)

theorem T_to_M {φ : Wff} (h : Prov Axiom φ) : Prov MAx φ := TM.PA.Prov.mono (fun _ => axiom_M) h

/-! ## completeness: reverse Polish replay of a derivation -/

def runL : List Stp → Nat × Nat → Nat × Nat
  | [], tw => tw
  | s :: l, tw => runL l (runStp s tw.fst tw.snd)

theorem runL_append (l m : List Stp) (tw : Nat × Nat) : runL (l ++ m) tw = runL m (runL l tw) := by
  induction l generalizing tw with
  | nil => rfl
  | cons s l ih => exact ih _

theorem rpn {φ : Wff} (h : Prov MAx φ) :
    ∃ L : List Stp, L ≠ [] ∧ ∀ t w, runL L (t, w) = (code φ, pair w t) := by
  induction h with
  | ax h =>
    obtain ⟨p1, p2, p3, k, hk, hc⟩ := h
    refine ⟨[⟨k + 1, p1, p2, p3⟩], by simp, fun t w => ?_⟩
    simp only [runL, runStp, kept, nextWs]
    rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel, hc]
  | @mp φ ψ _ _ ih1 ih2 =>
    obtain ⟨L1, _, h1⟩ := ih1
    obtain ⟨L2, _, h2⟩ := ih2
    refine ⟨L1 ++ L2 ++ [⟨14, code ψ, 0, 0⟩], by simp, fun t w => ?_⟩
    rw [runL_append, runL_append, h1, h2]
    simp [runL, runStp, kept, nextWs, code, unpair_pair]
  | @gen x φ _ ih =>
    obtain ⟨L, _, h⟩ := ih
    refine ⟨L ++ [⟨13, x, 0, 0⟩], by simp, fun t w => ?_⟩
    rw [runL_append, h]
    simp [runL, runStp, kept, nextWs, code]

/-! ## the enumeration of proof codes -/

/-- `k` iterations -/
def iterS : Nat → S → S
  | 0, σ => σ
  | k + 1, σ => iterS k (stepK σ)

theorem iterS_add (j k : Nat) (σ : S) : iterS (j + k) σ = iterS k (iterS j σ) := by
  induction j generalizing σ with
  | zero => simp [iterS]
  | succ j ih => rw [Nat.succ_add, iterS, ih, iterS]

theorem iterS_succ (k : Nat) (σ : S) : iterS (k + 1) σ = stepK (iterS k σ) := by
  rw [iterS_add k 1]; rfl

theorem run_code (m : Nat) : ∀ σ : S, σ.code = m →
    (iterS (steps m).length σ).pl = 0 ∧ (iterS (steps m).length σ).np = σ.np' ∧
      ((iterS (steps m).length σ).top, (iterS (steps m).length σ).ws) = runL (steps m) (σ.top, σ.ws) := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro σ hσ
    rw [steps]
    by_cases hr : (decStep m).snd = 0
    · simp only [dif_pos hr, List.length_singleton, iterS, runL, stepK, hσ, hr]
      simp
    · simp only [dif_neg hr, List.length_cons, iterS]
      have hpl : (stepK σ).pl = (decStep m).snd := by simp only [stepK, hσ]
      have h1 : (stepK σ).code = (decStep m).snd - 1 := by
        show (if (stepK σ).pl = 0 then _ else _) = _
        rw [hpl, if_neg hr]
      have h2 : (stepK σ).np' = σ.np' := by
        show (if (stepK σ).pl = 0 then _ else _) = _
        rw [hpl, if_neg hr]; rfl
      have := ih _ (by have := decStep_snd_le m; omega) (stepK σ) h1
      rw [h2] at this
      refine ⟨this.1, this.2.1, ?_⟩
      rw [this.2.2]
      simp only [runL, stepK, hσ]

/-- the initial registers -/
def σ0 : S := ⟨0, 0, 0, 0⟩

theorem reach_code (n : Nat) : ∃ k, (iterS k σ0).pl = 0 ∧ (iterS k σ0).np = n := by
  induction n with
  | zero => exact ⟨0, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨k, h1, h2⟩ := ih
    have hc : (iterS k σ0).code = n := by simp [S.code, h1, h2]
    obtain ⟨h3, h4, _⟩ := run_code n _ hc
    refine ⟨k + (steps n).length, ?_, ?_⟩
    · rw [iterS_add]; exact h3
    · rw [iterS_add, h4]; simp [S.np', h1, h2]

theorem good_iter (k : Nat) : Good (iterS k σ0) := by
  suffices ∀ k σ, Good σ → Good (iterS k σ) from this k σ0 TM.PA.good_init
  intro k; induction k with
  | zero => intro σ h; exact h
  | succ k ih => intro σ h; exact ih _ (good_step h)

/-- the search keeps `v0 ∈ v0` (code 1) at some iteration iff T proves it -/
theorem search_iff : (∃ k, (iterS (k + 1) σ0).top = 1) ↔ Provable (el 0 0) := by
  rw [provable_iff]
  constructor
  · rintro ⟨k, hk⟩
    have := (good_iter (k + 1)).1
    rwa [hk, decode_one] at this
  · intro h
    obtain ⟨L, hL, hrun⟩ := rpn (T_to_M h)
    obtain ⟨k, h1, h2⟩ := reach_code (listCode L)
    have hc : (iterS k σ0).code = listCode L := by simp [S.code, h1, h2]
    obtain ⟨_, _, h5⟩ := run_code _ _ hc
    rw [steps_listCode L hL, hrun] at h5
    have hlen : 0 < L.length := List.length_pos.mpr hL
    refine ⟨k + L.length - 1, ?_⟩
    rw [show k + L.length - 1 + 1 = k + L.length by omega, iterS_add]
    have := congrArg Prod.fst h5
    simp only at this
    rw [this]; rfl

end TMK.PA
