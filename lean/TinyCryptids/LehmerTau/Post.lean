import TinyCryptids.LehmerTau.Loop

/-!
# After a run

`PE` goes to the right end, `EL` erases the copies (the var digits) back to S0, and the head
stops in `PD2` on the last cell of the block left of S0.
-/

namespace TM.LehmerTau
open St

local notation "F" => false

theorem FPE : FarR delta PE1 PE2 PE3 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `EL1` on the last cell of the tape `W` -/
def ELc (W : List Bool) : Cfg St := ⟨EL1, app W.dropLast.reverse blank, true ::: blank⟩

theorem ENDc_ELc (W : List Bool) (hW : Wd W) (h0 : ∃ w, W = true :: w) (h1 : ∃ w, W = w ++ [true]) :
    Rch (ENDc W) (ELc W) := by
  obtain ⟨w, rfl⟩ := h1
  unfold ENDc ELc
  have hc : Clean12 (F :: F :: (w ++ [true])) := by
    have h := hW.1
    obtain ⟨v, hv⟩ := h0
    rw [hv] at h ⊢; cases h with | one h => exact Clean12.z2 h
  have := FPE.go hc blank
  show Rch ⟨PE1, blank, app (F :: F :: (w ++ [true])) blank⟩ _
  refine Rch.tr this ?_
  gL0; gL0; gL0
  simp [List.reverse_append, app_append, List.dropLast_concat]
  simp only [cons_blank]; fin

theorem dropLast_snoc (l : List Bool) (x : Bool) : (l ++ [x]).dropLast = l := List.dropLast_concat

/-- erase one var digit (factor `f ≥ 1`) -/
theorem el_one (a : Nat) (kR : List KB) (l : List (Nat × Nat)) (f : Nat) (hf : 1 ≤ f) :
    Rch (ELc (TW a kR ((f, 0) :: l))) (ELc (TW a kR l)) := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have e : TW a kR l = (TW a kR l).dropLast ++ [true] := by
    simp [TW]
  unfold ELc
  rw [TW_cons]
  simp only [vwi, if_pos, ite_true]
  rw [show TW a kR l ++ F :: F :: rep (g + 1 + 1) ++ [true] = (TW a kR l ++ F :: F :: rep (g + 1 + 1)) ++ [true] by simp,
    dropLast_snoc]
  simp only [List.reverse_append, app_append, rep_rev, app_rep, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, app_cons, app_nil]
  rw [e]
  simp only [List.reverse_append, app_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, app_cons, app_nil, rep_succ, ones_succ]
  gL; gL; gR; gR; gL
  show Rch (cfgL EL6 (ones (g + 2) (F ::: F ::: true ::: app (TW a kR l).dropLast.reverse blank)) (F ::: blank)) _
  eLn (g + 2)
  gL; gL
  simp only [zeros_cons_false, cons_blank, zeros_blank]; rw [dropLast_snoc]; fin

theorem el_all (a : Nat) (kR : List KB) : ∀ vs : List (Nat × Nat), (∀ d ∈ vs, VOk d) → zv vs = vs →
    Rch (ELc (TW a kR vs)) (ELc (TW a kR [])) := by
  intro vs
  induction vs with
  | nil => intro _ _; fin
  | cons d l ih =>
    intro hv hz
    obtain ⟨f, p⟩ := d
    simp only [zv, List.map_cons, List.cons.injEq, Prod.mk.injEq, true_and] at hz
    obtain ⟨rfl, hz⟩ := hz
    exact Rch.tr (el_one a kR l f (hv (f, 0) (List.mem_cons_self _ _)).1)
      (ih (fun x hx => hv x (List.mem_cons_of_mem _ hx)) hz)

/-- S0 reached: `PD2` on the last cell of the block left of S0 -/
theorem el_s0 (a : Nat) (kR : List KB) :
    Rch (ELc (TW a kR [])) (cfgL PD2 (app (lpR kR ++ rep (a + 1)) blank) (F ::: F ::: true ::: true ::: blank)) := by
  unfold ELc
  rw [TW_nil, show rep (a + 1) ++ (lpR kR).reverse ++ [F, F, true, true] =
    (rep (a + 1) ++ (lpR kR).reverse ++ [F, F, true]) ++ [true] by simp, dropLast_snoc]
  simp only [List.reverse_append, app_append, rep_rev, List.reverse_reverse, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, app_cons, app_nil, List.cons_append]
  gL; gL; gL; gL
  simp only [app_append, app_rep]; fin

theorem rep_app_true (n : Nat) (l : List Bool) : ∃ w, rep n ++ true :: l = true :: w := by
  cases n with
  | zero => exact ⟨l, rfl⟩
  | succ n => exact ⟨rep n ++ true :: l, rfl⟩

/-- **After a run**: the copies erased, `PD2` left of S0 -/
theorem runpost (a : Nat) (kR : List KB) (vs : List (Nat × Nat)) (hk : ∀ b ∈ kR, b.ok) (hv : ∀ d ∈ vs, VOk d)
    (hne : vs ≠ []) (hz : zv vs = vs) (hr : rsK kR = kR)
    (x : Bool) (u r : List Bool) (hr' : r ≠ []) (hW : u.reverse ++ x :: r = TW a kR vs) :
    Rch ⟨AL1, app u blank, x ::: app r blank⟩
      (cfgL PD2 (app (lpR kR ++ rep (a + pV vs * pK kR + 1)) blank) (F ::: F ::: true ::: true ::: blank)) := by
  refine Rch.tr (run a kR vs hk hv hne hz hr x u r hr' hW) ?_
  have h0 : ∃ w, TW (a + pV vs * pK kR) kR vs = true :: w := by
    rw [TW_K]; simp only [LK, List.reverse_cons, List.reverse_append, rep_rev, rep_succ, List.append_assoc,
      List.cons_append]; exact rep_app_true _ _
  refine Rch.tr (ENDc_ELc _ (Wd_TW _ kR vs hk hv) h0 ⟨_, rfl⟩) ?_
  exact Rch.tr (el_all _ kR vs hv hz) (el_s0 _ kR)

end TM.LehmerTau
