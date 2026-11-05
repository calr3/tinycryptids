import TinyCryptids.Firoozbakht.Tac

/-!
# The comparison `B ≤ A`

Tape: `… 00 B 00 A` with `B = 1 0 1^b`, `A = 1 0 1^a` (`a, b ≥ 1`).  In turn the last cell of
`B` and the last cell of `A` are erased; `B` used up first (`b ≤ a`): HALT; `A` used up first:
the rest of `A` and `B` is erased and the head stops on the first separator cell, state `ms`.
-/

namespace TM.Firoozbakht
open St

local notation "F" => false
local notation "T" => true

/-- the zig-zag: `B = 1 0 1^x` (head on its last cell, state `z11`), `g` blanks, `A = 1 0 1^y` -/
def ZC (Lb : Strm) (x g y : Nat) : Cfg St :=
  ⟨z11, ones (x - 1) (F ::: T ::: F ::: F ::: Lb), T ::: zeros g (T ::: F ::: ones y blank)⟩

theorem zc_halt (Lb : Strm) (g y : Nat) : HaltAt (ZC Lb 1 g y) := by
  apply Exists.intro; apply Exists.intro
  unfold ZC
  simp only [Nat.sub_self, ones_zero]
  gL; gR; fin

theorem zc_step (Lb : Strm) (x g y : Nat) (hg : 1 ≤ g) :
    Rch (ZC Lb (x + 2) g (y + 2)) (ZC Lb (x + 1) (g + 1) (y + 1)) := by
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  unfold ZC
  rw [show x + 2 - 1 = x + 1 by omega, show x + 1 - 1 = x by omega]
  gL; rw [ones_succ]; gR
  show Rch ⟨z3, T ::: ones x (F ::: T ::: F ::: F ::: Lb), F ::: zeros (g + 1) (T ::: F ::: T ::: ones (y + 1) blank)⟩ _
  rw [← zeros_cons_false, ← zeros_succ']
  zRn (g + 1 + 1)
  gR; gR; gR
  sRn (y + 1)
  refine blankR ?_; gR
  refine blankR ?_; gL
  show Rch (cfgL z6 (F ::: ones (y + 1) (T ::: F ::: T ::: zeros (g + 1 + 1) (T ::: ones x (F ::: T ::: F ::: F ::: Lb))))
    (F ::: blank)) _
  gL; rw [ones_succ]; gL; rw [ones_cons_true]; gL
  sLn y
  gL; gL
  rw [zeros_succ', zeros_succ', zeros_cons_false, zeros_cons_false]
  gL; gL
  zLn g
  have e1 : zeros g (F ::: F ::: T ::: F ::: ones y (T ::: F ::: F ::: F ::: blank)) =
      zeros (g + 1 + 1) (T ::: F ::: ones (y + 1) blank) := by
    rw [zeros_succ', zeros_succ', ones_succ', cons_blank, cons_blank, cons_blank]
  rw [e1]; fin

/-- `A` used up first: erase the rest of `A` and of `B` -/
theorem zc_clean (Lb : Strm) (x g : Nat) (hg : 1 ≤ g) :
    Rch (ZC Lb (x + 2) g 1) ⟨ms, Lb, blank⟩ := by
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  unfold ZC
  rw [show x + 2 - 1 = x + 1 by omega]
  gL; rw [ones_succ]; gR
  show Rch ⟨z3, T ::: ones x (F ::: T ::: F ::: F ::: Lb), F ::: zeros (g + 1) (T ::: F ::: T ::: blank)⟩ _
  rw [← zeros_cons_false, ← zeros_succ']
  zRn (g + 1 + 1)
  gR; gR; gR
  refine blankR ?_; gR
  refine blankR ?_; gL
  gL; gL; gL; gL
  zLn (g + 1 + 1)
  gL
  eLn x
  gL; gL; gL
  simp only [zeros_cons_false, cons_blank, zeros_blank]
  show Rch ⟨ms, Lb, F ::: blank⟩ _
  rw [cons_blank]; fin

theorem zc_run (Lb : Strm) : ∀ y x g, 1 ≤ x → 1 ≤ y → 1 ≤ g →
    (x ≤ y → HaltAt (ZC Lb x g y)) ∧ (y < x → Rch (ZC Lb x g y) ⟨ms, Lb, blank⟩) := by
  intro y
  induction y with
  | zero => intro x g _ h; omega
  | succ y ih =>
    intro x g hx _ hg
    obtain ⟨x, rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    cases x with
    | zero => exact ⟨fun _ => zc_halt Lb g _, fun h => absurd h (by omega)⟩
    | succ x =>
      cases y with
      | zero => exact ⟨fun h => absurd h (by omega), fun _ => zc_clean Lb x g hg⟩
      | succ y =>
        have := ih (x + 1) (g + 1) (by omega) (by omega) (by omega)
        have hs := zc_step Lb x g y hg
        exact ⟨fun h => HaltAt.back hs (this.1 (by omega)),
          fun h => Rch.tr hs (this.2 (by omega))⟩

/-- **Compare**: from `B`'s cell 2 (state `z0`) -/
theorem compare (Lb : Strm) (b a : Nat) (hb : 1 ≤ b) (ha : 1 ≤ a) :
    (b ≤ a → HaltAt ⟨z0, F ::: T ::: F ::: F ::: Lb, ones b (F ::: F ::: T ::: F ::: ones a blank)⟩) ∧
    (a < b → Rch ⟨z0, F ::: T ::: F ::: F ::: Lb, ones b (F ::: F ::: T ::: F ::: ones a blank)⟩
      ⟨ms, Lb, blank⟩) := by
  have h0 : Rch ⟨z0, F ::: T ::: F ::: F ::: Lb, ones b (F ::: F ::: T ::: F ::: ones a blank)⟩
      (ZC Lb b 2 a) := by
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    sRn (b' + 1)
    gL
    unfold ZC
    simp only [Nat.add_sub_cancel, ones_succ]
    fin
  have := zc_run Lb a b 2 hb ha (by omega)
  exact ⟨fun h => HaltAt.back h0 (this.1 h), fun h => Rch.tr h0 (this.2 h)⟩

end TM.Firoozbakht
