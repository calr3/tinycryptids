import TinyCryptids.Fermat.NextBase
namespace TM.Fermat
open St

/-! The compare: A (`x` cells) against R (`y` cells), erasing the last cell of A and the first
of R in turn. HALT iff R runs out first with exactly one cell of A left (`x = y + 1`); otherwise
the rest of A or R is erased and the head stops right of M. -/

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c := by
  obtain ⟨L, R, h⟩ := h
  exact Reach.halts delta h (halt_none (δ := delta) (by cases hR : R 0 <;> rfl))

/-- the zig-zag: `zH1` on a gap of `i + 1` zeros left and `j` zeros right of the head, A's `x`
cells on the left (then `LA`, which starts with a separator), R's `y` cells on the right (then
blank) -/
def Z (LA : Strm) (i j x y : Nat) : Cfg St :=
  cfgL zH1 (zeros (i + 1) (ones x LA)) (zeros j (ones y blank))

/-- after the clear: on the cell right of M (state `cr4`), blank to the right -/
def clrC (LM : Strm) : Cfg St := ⟨cr4, LM, blank⟩

theorem zz_step (LA : Strm) (i j x y : Nat) :
    Rch (Z LA i j (x + 2) (y + 2)) (Z LA (i + j + 2) 0 (x + 1) (y + 1)) := by
  unfold Z
  zLn (i + 1)
  gL; gR
  rw [show F ::: zeros (i + 1) (zeros j (ones (y + 2) blank)) = zeros (i + j + 2) (ones (y + 2) blank) by
    rw [zeros_add, show i + j + 2 = (i + 1 + j) + 1 by omega]; rfl]
  zRn (i + j + 2)
  gR; gL
  fin

theorem zeros_gap (i j y : Nat) (Y : Strm) :
    F ::: zeros (i + 1) (zeros j (ones y Y)) = zeros (i + j + 2) (ones y Y) := by
  rw [zeros_add, show i + j + 2 = (i + 1 + j) + 1 by omega]; rfl

/-- A runs out first (`x = 1`): erase the rest of R and go back to M -/
theorem zz_A (LM : Strm) (i j y : Nat) :
    Rch (Z (sep (true ::: LM)) i j 1 (y + 1)) (clrC (true ::: LM)) := by
  unfold Z sep clrC
  zLn (i + 1)
  gL; gR
  rw [zeros_gap]
  zRn (i + j + 2)
  gR
  eRn y
  refine blankR ?_
  gL
  show Rch (cfgL cr3 (zeros y (F ::: zeros (i + j + 2) (F ::: F ::: true ::: LM))) (F ::: blank)) _
  rw [show zeros y (F ::: zeros (i + j + 2) (F ::: F ::: true ::: LM)) =
      zeros (y + 1 + (i + j + 2) + 2) (true ::: LM) by
    rw [← zeros_succ', zeros_add, show y + 1 + (i + j + 2) + 2 = (y + 1 + (i + j + 2)) + 1 + 1 by omega,
      zeros_succ', zeros_succ']]
  zLn (y + 1 + (i + j + 2) + 2)
  gR
  simp only [zeros_cons_false, zeros_blank, cons_blank]
  fin

/-- R runs out first (`y = 1`): one more cell of A is erased; HALT if A is then empty, else
erase the rest of A and go back to M -/
theorem zz_R (LM : Strm) (i j x : Nat) :
    (x = 0 → HaltAt (Z (sep (true ::: LM)) i j (x + 2) 1)) ∧
    (1 ≤ x → Rch (Z (sep (true ::: LM)) i j (x + 2) 1) (clrC (true ::: LM))) := by
  have h0 : Rch (Z (sep (true ::: LM)) i j (x + 2) 1)
      (cfgL zX2 (ones x (F ::: F ::: true ::: LM)) (F ::: zeros (i + j + 3) blank)) := by
    unfold Z sep
    zLn (i + 1)
    gL; gR
    rw [zeros_gap]
    zRn (i + j + 2)
    gR
    refine blankR ?_
    gL
    show Rch (cfgL zX1 (zeros (i + j + 3) (true ::: ones x (F ::: F ::: true ::: LM))) (F ::: blank)) _
    zLn (i + j + 3)
    gL
    simp only [zeros_cons_false, zeros_blank, cons_blank]
    fin
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · subst hx
    exact HaltAt.back h0 ⟨_, _, sR (by rfl)⟩
  · refine Rch.tr h0 ?_
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    unfold clrC
    gL
    eLn x'
    gL; gL; gR
    simp only [zeros_cons_false, zeros_blank, cons_blank]
    fin

/-- the whole compare -/
theorem zz (LM : Strm) : ∀ x y i j, 1 ≤ x → 1 ≤ y →
    (x = y + 1 → HaltAt (Z (sep (true ::: LM)) i j x y)) ∧
    (x ≠ y + 1 → Rch (Z (sep (true ::: LM)) i j x y) (clrC (true ::: LM))) := by
  intro x
  induction x with
  | zero => intro y i j h; omega
  | succ x ih =>
    intro y i j _ hy
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    rcases x with _ | x
    · exact ⟨fun h => by omega, fun _ => zz_A LM i j y'⟩
    rcases y' with _ | y'
    · have := zz_R LM i j x
      exact ⟨fun h => this.1 (by omega), fun h => this.2 (by omega)⟩
    have st := zz_step (sep (true ::: LM)) i j x y'
    have := ih (y' + 1) (i + j + 2) 0 (by omega) (by omega)
    exact ⟨fun h => HaltAt.back st (this.1 (by omega)), fun h => Rch.tr st (this.2 (by omega))⟩

theorem PCP : ParserR delta CP1 CP2 := ⟨rfl, rfl, rfl⟩

/-- after the power of the last base: the next block is M, so to R; the zig-zag starts on the
single 0 between A and R -/
theorem compare_entry (pre : List Bool) (k β α r : Nat) (hr : 1 ≤ r) :
    Rch (nbC pre k β (true :: F :: F :: rep α) r)
      (Z (sep (true ::: F ::: F ::: ones (β + 2) (leftOf pre k 1))) 0 0 α r) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  unfold nbC rgt
  gR; sRn β
  simp only [sep, app_cons, app_nil, app_replicate]
  gR; gR; gR; gR; gR
  have e : ones α (F ::: ones (r' + 1) (F ::: ones 0 blank)) =
      app (rep α) (F ::: true ::: ones r' blank) := by
    simp [app_replicate, ones_succ, cons_blank]
  rw [e]
  refine Rch.tr (PCP.find (Clean.replicate α) _ _) ?_
  gL
  unfold Z
  simp [sep, List.reverse_replicate, app_replicate, zeros, ones_succ, ones_cons_true, cons_blank]
  fin

end TM.Fermat
