import TinyCryptids.Amicable.Scan

/-!
# One round: the number `x = k + 1`

`CS k`: N = `1^k`, everything else blank, the head right after N in state `k0`.

1. `k0 … k7` write N's next four cells and a marker two cells further, and copy N
   (`k + 3` units) into a fresh accumulator P left of N; `f3` finds the marker (`CE1`),
   N gets its fifth new cell, `V3` erases P's last cell (P = `ACC (k + 2) 0`: preload `x + 1`),
   `C1`, `C2` cut N into D = 1, R, and the scan of `x` (pass 1) runs (`pass1`).
2. `G0 … G4`: P's hole is at the far end iff `properDivSum x ≥ x + 1`; then P (4 cells more)
   is scanned with a fresh accumulator (pass 2, `pass2`); otherwise the cleanup.
3. After pass 2, `R1 … T3` fill its block and copy N (`x` units) into the boundary of pass 2's
   accumulator: one cell remains left of the hole iff `properDivSum m = x` (the beep, `H5`
   reading 0).
4. `x1`, `er`, `bk` erase everything left of N: `CS (k + 1)`.
-/

namespace TM.Amicable

open St TinyCryptids

local notation "F" => false
local notation "T" => true

def CS (k : Nat) : Cfg St := ⟨k0, ones k blank, blank⟩

theorem zeros_blank : ∀ n, zeros n blank = blank
  | 0 => rfl
  | n + 1 => by rw [zeros_succ', cons_blank, zeros_blank n]

theorem blank_eq : blank = F ::: F ::: ones 0 (F ::: ones 0 blank) := by
  show blank = F ::: F ::: F ::: blank
  rw [cons_blank, cons_blank, cons_blank]

theorem ACC00 : ACC 0 0 = blank := by show F ::: blank = blank; rw [cons_blank]

/-- the copy of N into a fresh P and the cut of N: the scan of `x = k + 1` starts -/
theorem start1 (k : Nat) :
    Rch (CS k) (SEP (F ::: ACC (k + 2) 0) blank 0 k) := by
  unfold CS
  gRb; gRb; gRb; gRb; gRb; refine blankR ?_
  show Rch ⟨k5, F ::: F ::: T ::: T ::: T ::: ones k blank, F ::: blank⟩ _
  gL; gL
  show Rch (cfgL k7 (F ::: T ::: T ::: T ::: ones k blank) (F ::: T ::: blank)) _
  gL
  show Rch (cfgL a2 (ones (k + 2 + 1) blank) (T ::: ones 0 (F ::: T ::: blank))) _
  have h := add_from 0 (k + 2) 0 (ones 0 blank) (F ::: T ::: blank)
  rw [← blank_eq, tln_ones, Nat.zero_sub] at h
  refine Rch.tr h ?_
  gR; gL
  show Rch (cfgL CE1 (F ::: ones (k + 2 + 0 + 2) (F ::: F ::: ones (0 + (k + 2) + 1) (F ::: ones 0 blank)))
    (F ::: blank)) _
  gL
  rw [show k + 2 + 0 + 2 = k + 4 by omega, show 0 + (k + 2) + 1 = (k + 2) + 1 by omega]
  sLn (k + 4); gL; gL; gR
  rw [← ones_succ']
  gR; gR; gR
  show Rch ⟨C1, T ::: F ::: F ::: F ::: ones (k + 2) (F ::: ones 0 blank), ones (k + 4) (F ::: blank)⟩ _
  gR; gL
  unfold SEP ACC
  show Rch ⟨f2, T ::: F ::: F ::: F ::: ones (k + 2) (F ::: blank), F ::: F ::: ones (k + 2) (F ::: blank)⟩ _
  rw [cons_blank]
  fin

/-- pass 1: the scan of `x = k + 1` with P's preload `x + 1` -/
theorem pass1 (k : Nat) :
    Rch (CS k) (RE (F ::: ACC (k + 2 - properDivSum (k + 1)) (properDivSum (k + 1))) blank (k + 1)) := by
  refine Rch.tr (start1 k) ?_
  rcases k with _ | j
  · have : properDivSum (0 + 1) = 0 := by decide
    rw [this]; exact shift_end _ _ 0
  · refine Rch.tr (shift _ _ 0 j) ?_
    have := scan (j + 2) (j + 1 + 2) 0 blank (by omega)
    rw [show j + 2 - 2 = j by omega, Nat.zero_add] at this
    exact this

/-- after pass 1: back to P's hole (filled on the way); `a` cells beyond it -/
theorem to_hole1 (x a s : Nat) (hx : 1 ≤ x) :
    Rch (RE (F ::: ACC a s) blank x) (cfgL G4 (ones a blank) (T ::: ones s (F ::: F ::: ones x blank))) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  unfold RE ACC
  gR; refine blankR ?_; gR; refine blankR ?_; gL
  gL; gL; gL; gL; gL; gL; gL
  sLn y; gL; gL
  show Rch (cfgL G3 (ones s (F ::: ones a blank)) _) _
  sLn s; gL
  rw [show ones y (T ::: F ::: F ::: F ::: F ::: F ::: F ::: F ::: blank) = ones (y + 1) blank by
    rw [← ones_succ']; simp only [cons_blank]]
  fin

theorem cfgL_blank (q : St) (R : Strm) : cfgL q blank R = cfgL q (F ::: blank) R := by
  rw [cons_blank]

/-- the cleanup: erase the block left of N (the head on it, `p` of its cells to the left), back
to the round start for `x` -/
theorem cleanup (p q x : Nat) (hx : 1 ≤ x) :
    Rch ⟨x1, ones p blank, ones q (F ::: F ::: ones x blank)⟩ (CS x) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  sRn q
  refine Rch.tr (stepL (δ := deltaNB) (by rfl)) ?_
  show Rch (cfgL er (ones q (ones p blank)) (F ::: F ::: ones (y + 1) blank)) _
  rw [ones_add]
  eLn (q + p)
  rw [cfgL_blank]
  gR
  zRn (q + p)
  gR; gR; gR
  sRn y
  unfold CS
  show Rch ⟨k0, ones y (T ::: F ::: F ::: zeros (q + p) (F ::: blank)), blank⟩ _
  rw [cons_blank, zeros_blank, cons_blank, cons_blank, ← ones_succ']
  fin

/-- P's hole is not at the far end (`properDivSum x ≤ x`): clean up -/
theorem reject1 (a s x : Nat) (hx : 1 ≤ x) :
    Rch (cfgL G4 (ones (a + 1) blank) (T ::: ones s (F ::: F ::: ones x blank))) (CS x) := by
  gR
  exact cleanup (a + 1) (s + 1) x hx

/-- P's hole is at the far end: P with 4 more cells is cut for the scan of `s` -/
theorem start2 (s x : Nat) (hs : 1 ≤ s) :
    Rch (cfgL G4 (ones 0 blank) (T ::: ones s (F ::: F ::: ones x blank)))
      (SEP (F ::: ACC 0 0) (F ::: ones x blank) 0 (s - 1)) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  show Rch (cfgL G4 blank _) _
  rw [cfgL_blank]; gL; rw [cfgL_blank]; gL; rw [cfgL_blank]; gL; rw [cfgL_blank]
  gR; gR; gR; gL
  unfold SEP ACC
  rw [Nat.add_sub_cancel, show ones (t + 2) (F ::: F ::: ones x blank) = T ::: T ::: ones t (F ::: F ::: ones x blank) from rfl]
  show Rch ⟨f2, T ::: F ::: blank, F ::: F ::: T ::: T ::: ones t (F ::: F ::: ones x blank)⟩ _
  show Rch _ ⟨f2, ones 1 (F ::: F ::: F ::: blank), _⟩
  rw [show (F ::: F ::: F ::: blank) = F ::: blank by rw [cons_blank, cons_blank, cons_blank]]
  fin

/-- pass 2: the scan of `m ≥ 2` with a fresh accumulator; N is right of it -/
theorem pass2 (m x : Nat) (hm : 2 ≤ m) :
    Rch (cfgL G4 (ones 0 blank) (T ::: ones m (F ::: F ::: ones x blank)))
      (RE (F ::: ACC 0 (properDivSum m)) (F ::: ones x blank) m) := by
  refine Rch.tr (start2 m x (by omega)) ?_
  rw [show m - 1 = (m - 2) + 1 by omega]
  refine Rch.tr (shift _ _ 0 (m - 2)) ?_
  have := scan m 0 0 (F ::: ones x blank) hm
  rw [Nat.zero_sub, Nat.zero_add] at this
  exact this

theorem ACC0 (b : Nat) : ACC 0 b = ones b blank := by
  show ones b (F ::: blank) = _; rw [cons_blank]

/-- after pass 2: fill the block, copy N (`x` units) into the boundary of pass 2's
accumulator (`s2` cells), erase N's extra cell, back to the hole (filled on the way) -/
theorem post2 (m x s2 : Nat) (hx : 1 ≤ x) (hm : 1 ≤ m) :
    Rch (RE (F ::: ACC 0 s2) (F ::: ones x blank) m)
      (cfgL H4 (ones (s2 - (x - 1)) blank) (T ::: ones (m + 4 + x) (F ::: F ::: ones x blank))) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  unfold RE
  rw [ACC0]
  gR; gR; gL; gL; gL; gL; gL; gL; gL; gR
  rw [show T ::: T ::: T ::: T ::: F ::: F ::: T ::: ones y blank =
    ones 4 (F ::: F ::: ones (y + 1) blank) from rfl]
  sRn 4; gR; gR; sRn (y + 1); refine blankR ?_; gL
  show Rch (cfgL a2 (ones (y + 1) (F ::: F ::: ones 4 (ones (n + 1) (F ::: F ::: ones s2 blank)))) (T ::: ones 0 blank)) _
  rw [ones_add, show 4 + (n + 1) = n + 5 by omega]
  show Rch (cfgL a2 (ones (y + 1) (F ::: F ::: ones (n + 5) (F ::: (F ::: ones s2 blank)))) (T ::: ones 0 blank)) _
  refine Rch.tr (add_from (n + 5) y 0 _ _) ?_
  rw [show tln (y + 1) (F ::: ones s2 blank) = ones (s2 - y) blank from tln_ones s2 y,
    show y + 0 + 2 = (y + 1) + 1 by omega]
  gRb; gRb; refine blankR ?_; gL; gL; gL; gL
  sLn (y + 1); gL; gL
  sLn (n + 5 + y + 1); gL
  rw [show y + 1 - 1 = y by omega, show n + 1 + 4 + (y + 1) = n + 5 + y + 1 by omega,
    show (F ::: F ::: F ::: F ::: blank) = blank by simp only [cons_blank]]
  fin

/-- just before the beep: the hole has exactly one cell beyond it -/
def BeepCfg (x q : Nat) : Cfg St := cfgL H5 (ones 0 blank) (T ::: T ::: ones q (F ::: F ::: ones x blank))

/-- not one cell beyond the hole (`properDivSum m ≠ x`): clean up -/
theorem check_no (a q x : Nat) (hx : 1 ≤ x) (ha : a ≠ 1) :
    Rch (cfgL H4 (ones a blank) (T ::: ones q (F ::: F ::: ones x blank))) (CS x) := by
  rcases a with _ | _ | j
  · show Rch (cfgL H4 blank _) _
    rw [cfgL_blank]; gR
    show Rch ⟨x1, F ::: blank, ones (q + 1) (F ::: F ::: ones x blank)⟩ _
    rw [show (F ::: blank) = ones 0 blank from cons_blank]
    exact cleanup 0 (q + 1) x hx
  · exact absurd rfl ha
  · gL; gR
    exact cleanup (j + 1) (q + 2) x hx

theorem check_beep (q x : Nat) :
    Rch (cfgL H4 (ones 1 blank) (T ::: ones q (F ::: F ::: ones x blank))) (BeepCfg x q) := by
  gL; fin

/-- the beep (`H5` reading 0, a transition of `delta` only), then the cleanup -/
theorem after_beep (q x : Nat) (hx : 1 ≤ x) : Reach delta (BeepCfg x q) (CS x) := by
  refine Reach.trans delta (stepR (δ := delta) (by rfl)) (Reach.sub deltaNB_sub ?_)
  show Rch ⟨x1, F ::: blank, ones (q + 2) (F ::: F ::: ones x blank)⟩ _
  rw [show (F ::: blank) = ones 0 blank from cons_blank]
  exact cleanup 0 (q + 2) x hx

/-- the round for `x = k + 1` without a beep -/
theorem round_no (k : Nat) (h : ¬ Small (k + 1)) : Rch (CS k) (CS (k + 1)) := by
  refine Rch.tr (pass1 k) (Rch.tr (to_hole1 _ _ _ (by omega)) ?_)
  rcases Nat.lt_or_ge (k + 1) (properDivSum (k + 1)) with hl | hg
  · rw [show k + 2 - properDivSum (k + 1) = 0 by omega]
    refine Rch.tr (pass2 _ _ (by omega)) (Rch.tr (post2 _ _ _ (by omega) (by omega)) ?_)
    exact check_no _ _ _ (by omega) (fun he => h ⟨hl, by omega⟩)
  · rw [show k + 2 - properDivSum (k + 1) = (k + 1 - properDivSum (k + 1)) + 1 by omega]
    exact reject1 _ _ _ (by omega)

/-- the round for `x = k + 1` up to the beep -/
theorem round_beep (k : Nat) (h : Small (k + 1)) : ∃ q, Rch (CS k) (BeepCfg (k + 1) q) := by
  refine ⟨properDivSum (k + 1) + 4 + (k + 1), Rch.tr (pass1 k) (Rch.tr (to_hole1 _ _ _ (by omega)) ?_)⟩
  rw [show k + 2 - properDivSum (k + 1) = 0 by have := h.1; omega]
  refine Rch.tr (pass2 _ _ (by have := h.1; omega)) (Rch.tr (post2 _ _ _ (by omega) (by have := h.1; omega)) ?_)
  rw [h.2, show k + 1 - (k + 1 - 1) = 1 by omega]
  exact check_beep _ _

end TM.Amicable
