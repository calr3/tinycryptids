import TinyCryptids.ErdosMoser.Next
namespace TM.ErdosMoser
open St

/-! The compare: A (`x` cells) against R (`y` cells), erasing one cell of each in turn;
HALT iff they run out together, else the stack is cleared and the head stops right of M. -/

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c := by
  obtain ⟨L, R, h⟩ := h
  exact Reach.halts delta h (halt_none (δ := delta) (by cases hR : R 0 <;> rfl))

/-- the zig-zag: `zH1` on a gap of `i + 1` zeros left and `j` zeros right of the head, A's `x`
cells on the left (then `LA`, which starts with a separator), R's `y` cells on the right
(then `00` and blank) -/
def Z (LA : Strm) (i j x y : Nat) : Cfg St :=
  cfgL zH1 (zeros (i + 1) (ones x LA)) (zeros j (ones y (sep blank)))

/-- after the clear: on the cell right of M (state `cr4`), blank to the right -/
def clrC (LM : Strm) : Cfg St := ⟨cr4, LM, blank⟩

theorem zz_step (LA : Strm) (i j x y : Nat) :
    Rch (Z LA i j (x + 2) (y + 2)) (Z LA (i + j + 2) 0 (x + 1) (y + 1)) := by
  unfold Z
  zLn (i + 1)
  gL; gR
  rw [show F ::: zeros (i + 1) (zeros j (ones (y + 2) (sep blank))) = zeros (i + j + 2) (ones (y + 2) (sep blank)) by
    rw [zeros_add, show i + j + 2 = (i + 1 + j) + 1 by omega]; rfl]
  zRn (i + j + 2)
  gR; gL
  fin

/-- A runs out: halt if R does too, else erase the rest of R and go back to M -/
theorem zz_A (LM : Strm) (i j y : Nat) :
    (y = 0 → HaltAt (Z (sep (true ::: LM)) i j 1 (y + 1))) ∧
    (1 ≤ y → Rch (Z (sep (true ::: LM)) i j 1 (y + 1)) (clrC (true ::: LM))) := by
  have h0 : Rch (Z (sep (true ::: LM)) i j 1 (y + 1))
      ⟨zK2, F ::: zeros (i + j + 2) (sep (true ::: LM)), ones y (sep blank)⟩ := by
    unfold Z sep
    zLn (i + 1)
    gL; gR
    rw [show F ::: zeros (i + 1) (zeros j (ones (y + 1) (F ::: F ::: blank))) =
      zeros (i + j + 2) (ones (y + 1) (F ::: F ::: blank)) by
      rw [zeros_add, show i + j + 2 = (i + 1 + j) + 1 by omega]; rfl]
    zRn (i + j + 2)
    gR; fin
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · subst hy
    exact HaltAt.back h0 ⟨_, _, sR (by rfl)⟩
  · refine Rch.tr h0 ?_
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    unfold sep clrC
    gR
    eRn y'
    gL
    zLn y'; gL; gL; zLn (i + j + 2); gL; gL
    gR
    simp only [zeros_cons_false, zeros_blank, cons_blank]
    fin

/-- R runs out first: erase the rest of A and go back to M -/
theorem zz_R (LM : Strm) (i j x : Nat) :
    Rch (Z (sep (true ::: LM)) i j (x + 2) 1) (clrC (true ::: LM)) := by
  unfold Z sep clrC
  zLn (i + 1)
  gL; gR
  rw [show F ::: zeros (i + 1) (zeros j (ones 1 (F ::: F ::: blank))) =
    zeros (i + j + 2) (ones 1 (F ::: F ::: blank)) by
    rw [zeros_add, show i + j + 2 = (i + 1 + j) + 1 by omega]; rfl]
  zRn (i + j + 2)
  gR; gL
  zLn (i + j + 3)
  gL
  eLn x
  gL; gL; gR
  simp only [zeros_cons_false, zeros_blank, cons_blank]
  fin

/-- the whole compare -/
theorem zz (LM : Strm) : ∀ x y i j, 1 ≤ x → 1 ≤ y →
    (x = y → HaltAt (Z (sep (true ::: LM)) i j x y)) ∧
    (x ≠ y → Rch (Z (sep (true ::: LM)) i j x y) (clrC (true ::: LM))) := by
  intro x
  induction x with
  | zero => intro y i j h; omega
  | succ x ih =>
    intro y i j _ hy
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    rcases x with _ | x
    · have := zz_A LM i j y'
      exact ⟨fun h => this.1 (by omega), fun h => this.2 (by omega)⟩
    rcases y' with _ | y'
    · exact ⟨fun h => by omega, fun _ => zz_R LM i j x⟩
    have st := zz_step (sep (true ::: LM)) i j x y'
    have := ih (y' + 1) (i + j + 2) 0 (by omega) (by omega)
    exact ⟨fun h => HaltAt.back st (this.1 (by omega)), fun h => Rch.tr st (this.2 (by omega))⟩

theorem PCP : ParserR delta CP1 CP2 := ⟨rfl, rfl, rfl⟩

/-- after the power with the marker on cell 1: fill the marker, go to R, fill its hole and erase
its first cell, then the zig-zag starts -/
theorem final_start (k m a r : Nat) (hr : 1 ≤ r) :
    Rch (nbC k 1 m (rep (a + 1)) r) (Z (sep (true ::: ones (m + 2) (KL k 1))) 1 1 (a + 1) (r + 1)) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  unfold nbC
  gL; gL
  unfold KL
  gR; gR; gR
  have hw : Clean (rep (m + 1) ++ F :: F :: (rep (a + 1) ++ [F, F, true])) :=
    Clean.rep_append _ (Clean.sep (Clean.rep_append a (Clean.sep Clean.nil)))
  have e1 : true ::: ones m (rgt (rep (a + 1)) (r' + 1) 0) =
      app (rep (m + 1) ++ F :: F :: (rep (a + 1) ++ [F, F, true])) (F ::: true ::: ones r' (sep blank)) := by
    simp [rgt, sep, app_append, app_replicate, ones_succ, ones_cons_true]
  rw [e1]
  refine Rch.tr (PCP.find hw _ _) ?_
  gL; gL
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.reverse_replicate,
    List.nil_append, List.cons_append, List.singleton_append, List.append_assoc, app_append, app_cons,
    app_nil, app_replicate]
  gL
  unfold Z sep
  simp [zeros, ones_succ, ones_cons_true]
  fin

end TM.ErdosMoser
