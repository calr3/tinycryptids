import TinyCryptids.PA.Step
import TinyCryptids.PA.Logic

/-!
# The proof search finds `v0 ∈ v0` iff T proves it

* Soundness: every candidate decodes to a theorem of T (`cand_sound`; E and B4 are in a form
  with two antecedents swapped, `e_swap` and `perm`), GEN and DET keep theorems, and `v0 = v0`
  (code 0) is a theorem; so every value on the stack and in `topwff` decodes to a theorem.
* Completeness: every axiom of T is derivable from the machine's candidates (`MAx`); a
  derivation is replayed in reverse Polish notation by a list of steps (`rpn`), and every list of
  steps is the proof code of some `n`, which the search reaches (`reach_code`).
-/

namespace TM.PA

open TinyCryptids Wff

theorem prop3_T : Prop3 Axiom :=
  ⟨fun _ _ _ => Prov.ax (Axiom.b1 _ _ _), fun _ => Prov.ax (Axiom.b2 _), fun _ _ => Prov.ax (Axiom.b3 _ _)⟩

theorem qax_T : QAx Axiom := fun _ _ _ => Prov.ax (Axiom.b4 _ _ _)

/-- `⊢ v0 = v0` -/
theorem eq00 : Prov Axiom (eq 0 0) := by
  have hP := prop3_T
  have hQ := qax_T
  -- v1 = v0 → v0 = v0, so ∃v1 v1 = v0 → ∃v1 v0 = v0
  have h1 : Prov Axiom (imp (eq 1 0) (eq 0 0)) :=
    Prov.mp (contr hP _ _) (Prov.ax (Axiom.b8a 1 0 0))
  have h2 : Prov Axiom (ex 1 (eq 0 0)) := Prov.mp (ex_congr hP hQ 1 h1) (Prov.ax (Axiom.b7 1 0))
  -- v0 = v0 → ∀v1 v0 = v0 (B6a), so ∃v1 ∀v1 v0 = v0, and B6c
  have h3 : Prov Axiom (imp (eq 0 0) (all 1 (eq 0 0))) :=
    Prov.mp (andl hP _ _) (Prov.ax (Axiom.b6a 0 0 1 (by decide) (by decide)))
  have h4 : Prov Axiom (ex 1 (all 1 (eq 0 0))) := Prov.mp (ex_congr hP hQ 1 h3) h2
  exact Prov.mp (Prov.ax (Axiom.b6c 1 (eq 0 0))) h4

theorem decode0 : Prov Axiom (decode 0) := by rw [decode_zero]; exact eq00

/-- every candidate decodes to a theorem of T -/
theorem cand_sound (p1 p2 p3 k : Nat) (hk : k < 12) :
    Prov Axiom (decode ((candList p1 p2 p3).getD k 0)) := by
  have hP := prop3_T
  have hQ := qax_T
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · -- E (form 1)
    have := (e_swap hP hQ (decode p3)).1
    simp only [candList, List.getD, List.get?, Option.getD, axE, decode_exC, decode_allC,
      decode_andC, decode_impC, decode_negC, decode_elC, decode_eqC]
    exact Prov.mp this (Prov.ax (Axiom.e _))
  · simp only [candList, List.getD, List.get?, Option.getD, axB2, decode_impC, decode_negC]
    exact Prov.ax (Axiom.b2 _)
  · simp only [candList, List.getD, List.get?, Option.getD, axB8c, decode_impC, decode_eqC, decode_elC]
    exact Prov.ax (Axiom.b8c _ _ _)
  · simp only [candList, List.getD, List.get?, Option.getD, axB8b, decode_impC, decode_eqC, decode_elC]
    exact Prov.ax (Axiom.b8b _ _ _)
  · simp only [candList, List.getD, List.get?, Option.getD, axB8a, decode_impC, decode_eqC]
    exact Prov.ax (Axiom.b8a _ _ _)
  · simp only [candList, List.getD, List.get?, Option.getD, axB3, decode_impC, decode_negC]
    exact Prov.ax (Axiom.b3 _ _)
  · simp only [candList, List.getD, List.get?, Option.getD, axB7, decode_exC, decode_eqC]
    exact Prov.ax (Axiom.b7 _ _)
  · -- B4 (form 1)
    simp only [candList, List.getD, List.get?, Option.getD, axB4, decode_impC, decode_allC]
    exact perm_r hP (Prov.ax (Axiom.b4 _ _ _))
  · simp only [candList, List.getD, List.get?, Option.getD, axB6b, decode_impC, decode_allC]
    exact Prov.ax (Axiom.b6b _ _ _)
  · simp only [candList, List.getD, List.get?, Option.getD, axB1, decode_impC]
    exact Prov.ax (Axiom.b1 _ _ _)
  · simp only [candList, List.getD, List.get?, Option.getD, axB6c, decode_impC, decode_exC, decode_allC]
    exact Prov.ax (Axiom.b6c _ _)
  · simp only [candList, List.getD, List.get?, Option.getD]
    by_cases h : p2 = p3 ∨ p3 = p1
    · rw [if_pos h]; exact decode0
    · rw [if_neg h]
      simp only [axB6a, decode_andC, decode_impC, decode_eqC, decode_elC, decode_allC]
      exact Prov.ax (Axiom.b6a _ _ _ (fun e => h (Or.inl e.symm)) (fun e => h (Or.inr e)))
  · omega

/-! ## soundness of an iteration -/

/-- the `n`-th value on a stack -/
def elem (w : Nat) : Nat → Nat
  | 0 => (unpair w).snd
  | n + 1 => elem (unpair w).fst n

/-- `topwff` and everything on the stack decode to theorems of T -/
def Good (σ : S) : Prop := Prov Axiom (decode σ.top) ∧ ∀ n, Prov Axiom (decode (elem σ.ws n))

theorem elem_zero (n : Nat) : elem 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem good_init : Good ⟨0, 0, 0, 0⟩ := ⟨decode0, fun n => by simp only [elem_zero]; exact decode0⟩

theorem good_push {t w : Nat} (ht : Prov Axiom (decode t)) (hw : ∀ n, Prov Axiom (decode (elem w n))) :
    ∀ n, Prov Axiom (decode (elem (pair w t) n)) := by
  intro n; cases n with
  | zero => simpa [elem] using ht
  | succ n => simpa [elem] using hw n

theorem good_step {σ : S} (h : Good σ) : Good σ.step := by
  obtain ⟨ht, hw⟩ := h
  simp only [S.step, runStp, Good]
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

/-! ## completeness: the machine's candidates derive every axiom of T -/

/-- formulas whose code the machine can keep as an axiom candidate -/
def MAx (φ : Wff) : Prop := ∃ p1 p2 p3 k, k < 12 ∧ (candList p1 p2 p3).getD k 0 = code φ

theorem prop3_M : Prop3 MAx :=
  ⟨fun φ ψ χ => Prov.ax ⟨code χ, code ψ, code φ, 9, by decide, rfl⟩,
   fun φ => Prov.ax ⟨0, 0, code φ, 1, by decide, rfl⟩,
   fun φ ψ => Prov.ax ⟨0, code φ, code ψ, 5, by decide, rfl⟩⟩

theorem qax_M : QAx MAx := fun x φ ψ =>
  perm_r prop3_M (Prov.ax ⟨x, code ψ, code φ, 7, by decide, rfl⟩)

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
  | b6b x y φ => exact Prov.ax ⟨y, x, code φ, 8, by decide, rfl⟩
  | b6c x φ => exact Prov.ax ⟨0, x, code φ, 10, by decide, rfl⟩
  | b7 x y => exact Prov.ax ⟨y, x, 0, 6, by decide, rfl⟩
  | b8a x y z => exact Prov.ax ⟨z, x, y, 4, by decide, rfl⟩
  | b8b x y z => exact Prov.ax ⟨z, x, y, 3, by decide, rfl⟩
  | b8c x y z => exact Prov.ax ⟨y, x, z, 2, by decide, rfl⟩
  | e φ => exact Prov.mp (e_swap prop3_M qax_M φ).2 (Prov.ax ⟨0, 0, code φ, 0, by decide, rfl⟩)

theorem T_to_M {φ : Wff} (h : Prov Axiom φ) : Prov MAx φ := Prov.mono (fun _ => axiom_M) h

/-! ## completeness: reverse Polish replay of a derivation -/

def runL : List Stp → Nat × Nat → Nat × Nat
  | [], tw => tw
  | s :: l, tw => runL l (runStp s tw.fst tw.snd)

theorem runL_append (l m : List Stp) (tw : Nat × Nat) : runL (l ++ m) tw = runL m (runL l tw) := by
  induction l generalizing tw with
  | nil => rfl
  | cons s l ih => exact ih _

/-- a derivation from the candidates is a list of steps that, from any stack, leaves the
theorem's code in `topwff` and pushes the old `topwff` -/
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

/-- a step followed by the rest `r` of a proof code -/
def encStp (s : Stp) (r : Nat) : Nat := pair (pair (pair (pair r s.p3) s.p2) s.p1) s.ac

theorem decStep_enc (s : Stp) (r : Nat) : decStep (encStp s r) = (s, r) := by
  simp [decStep, encStp, unpair_pair]

theorem decStep_snd_le (n : Nat) : (decStep n).snd ≤ n := by
  simp only [decStep]
  exact Nat.le_trans (unpair_fst_le _) (Nat.le_trans (unpair_fst_le _)
    (Nat.le_trans (unpair_fst_le _) (unpair_fst_le _)))

/-- the steps of a proof code -/
def steps (n : Nat) : List Stp :=
  (decStep n).fst :: (if h : (decStep n).snd = 0 then [] else steps ((decStep n).snd - 1))
termination_by n
decreasing_by have := decStep_snd_le n; omega

/-- a proof code for a list of steps -/
def listCode : List Stp → Nat
  | [] => 0
  | [s] => encStp s 0
  | s :: t => encStp s (listCode t + 1)

theorem steps_listCode : ∀ L : List Stp, L ≠ [] → steps (listCode L) = L
  | [], h => absurd rfl h
  | [s], _ => by rw [listCode, steps, decStep_enc]; simp
  | s :: t :: u, _ => by
    have e : listCode (s :: t :: u) = encStp s (listCode (t :: u) + 1) := rfl
    rw [e, steps, decStep_enc]
    simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, dif_neg, not_false_eq_true]
    rw [steps_listCode (t :: u) (List.cons_ne_nil t u)]

/-- `k` iterations -/
def iterS : Nat → S → S
  | 0, σ => σ
  | k + 1, σ => iterS k σ.step

theorem iterS_add (j k : Nat) (σ : S) : iterS (j + k) σ = iterS k (iterS j σ) := by
  induction j generalizing σ with
  | zero => simp [iterS]
  | succ j ih => rw [Nat.succ_add, iterS, ih, iterS]

/-- running one proof code: its steps, then `prooflist` is 0 again and `nextproof` moved on -/
theorem run_code (m : Nat) : ∀ σ : S, σ.code = m →
    (iterS (steps m).length σ).pl = 0 ∧ (iterS (steps m).length σ).np = σ.np' ∧
      ((iterS (steps m).length σ).top, (iterS (steps m).length σ).ws) = runL (steps m) (σ.top, σ.ws) := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro σ hσ
    rw [steps]
    by_cases hr : (decStep m).snd = 0
    · simp only [dif_pos hr, List.length_singleton, iterS, runL, S.step, hσ, hr]
      simp
    · simp only [dif_neg hr, List.length_cons, iterS]
      have hpl : σ.step.pl = (decStep m).snd := by simp only [S.step, hσ]
      have h1 : σ.step.code = (decStep m).snd - 1 := by
        show (if σ.step.pl = 0 then _ else _) = _
        rw [hpl, if_neg hr]
      have h2 : σ.step.np' = σ.np' := by
        show (if σ.step.pl = 0 then _ else _) = _
        rw [hpl, if_neg hr]; rfl
      have := ih _ (by have := decStep_snd_le m; omega) σ.step h1
      rw [h2] at this
      refine ⟨this.1, this.2.1, ?_⟩
      rw [this.2.2]
      simp only [runL, S.step, hσ]

/-- the initial registers -/
def σ0 : S := ⟨0, 0, 0, 0⟩

/-- the search reaches every proof code: at some iteration `prooflist = 0` and `nextproof = n` -/
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
  suffices ∀ k σ, Good σ → Good (iterS k σ) from this k σ0 good_init
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

end TM.PA
