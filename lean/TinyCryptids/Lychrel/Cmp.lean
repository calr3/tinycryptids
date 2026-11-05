import TinyCryptids.Lychrel.Iter

/-!
# The compare: A = x ?  then x := x + A

A hole walks X from cell `x + 1` down; for each position a cell of A is moved to X's end.
-/

namespace TM.Lychrel
open St

local notation "F" => false

/-- left of X: its separator from D, and D with its hole at `d10` -/
def DL : Strm := F ::: F ::: ones 1 (F ::: ones 10 blank)

/-- the walk with X's hole at cell `c` and `j` cells right of it; A has `m + 1` cells -/
def K (c j G m : Nat) : Cfg St := ⟨ka1, ones j (F ::: ones c DL), zeros G (ones (m + 1) blank)⟩

/-- after the walk: X has `n` cells and no hole -/
def N (n G m : Nat) : Cfg St := ⟨ka1, ones n DL, zeros G (ones (m + 1) blank)⟩

/-- the end of an iteration with t = 0: A's last cell and T are erased, the compare starts -/
theorem pl_zero (x g r : Nat) (hg : 2 ≤ g) (hr : 1 ≤ r) :
    Rch (PL x g 0 3 r 0) (K (x + 1) 1 (g + 8) (r - 1)) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 2 := ⟨g - 2, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  unfold PL RtP
  rw [show 10 - 0 = 10 by rfl]
  refine Rch.tr (bstep_wrap _) ?_
  gR; gR; gR; gR; sRn (x + 2); gR; zRn (g' + 1); gR; gL; gR; gR; gR; gR; gR; gR; gL; gL; gL; gL
  show Rch (cfgL cm0 (F ::: F ::: F ::: zeros (g' + 1) (F ::: ones (x + 2) (true ::: DL)))
    (zeros 5 (ones (r' + 1) blank))) _
  rw [zeros_fa, ones_tr]
  show Rch (cfgL cm0 (zeros (g' + 2 + 3) (ones (x + 3) DL)) _) _
  zLn (g' + 2 + 3); gL; gR; gR
  unfold K
  rw [zeros_add, show r' + 1 - 1 + 1 = r' + 1 by omega, show g' + 2 + 3 + 5 = g' + 2 + 8 by omega]
  fin

/-- one cell of A moved, the hole moves one cell left -/
theorem k_step (c j G m : Nat) (hj : 1 ≤ j) (hG : 1 ≤ G) :
    Rch (K (c + 2) j G (m + 1)) (K (c + 1) (j + 2) G m) := by
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  unfold K
  gR; zRn G'; gR; gL; gL; zLn G'; gL; gR; gL; sLn (j' + 1); gL; gL; gR; gR; gR; sRn (j' + 1); gR
  show Rch ⟨ka1, true ::: ones (j' + 1) (true ::: F ::: ones (c + 1) DL), zeros G' (F ::: ones (m + 1) blank)⟩ _
  rw [zeros_fa, ones_tr, ← ones_succ]
  fin

/-- the hole was at cell 1: it is filled, the rest of A is moved without a hole -/
theorem k_one (j G m : Nat) (hj : 1 ≤ j) (hG : 1 ≤ G) :
    Rch (K 1 j G (m + 1)) (N (j + 3) G m) := by
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  unfold K N
  gR; zRn G'; gR; gL; gL; zLn G'; gL; gR; gL; sLn (j' + 1); gL; gL; gR; gR; gR; sRn (j' + 1); gR
  show Rch ⟨ka1, true ::: ones (j' + 1) (true ::: true ::: DL), zeros G' (F ::: ones (m + 1) blank)⟩ _
  rw [zeros_fa, ones_tr, ones_tr, ← ones_succ]
  fin

/-- no hole: one more cell of A moved -/
theorem n_step (n G m : Nat) (hn : 1 ≤ n) (hG : 1 ≤ G) :
    Rch (N n G (m + 1)) (N (n + 1) G m) := by
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  unfold N
  gR; zRn G'; gR; gL; gL; zLn G'; gL; gR; gL; sLn (n' + 1); gL; gR; gR; sRn (n' + 1); gR
  show Rch ⟨ka1, true ::: ones (n' + 1) DL, zeros G' (F ::: ones (m + 1) blank)⟩ _
  rw [zeros_fa, ← ones_succ]
  fin

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h'⟩ := h; ⟨L, R, Rch.tr hab h'⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h'⟩ := h; Reach.halts delta h' (halts_of_step delta rfl)

/-- A has one cell left while X's hole is at cell 1: A = x, halt -/
theorem k_halt (j G : Nat) (hj : 1 ≤ j) (hG : 1 ≤ G) : HaltAt (K 1 j G 0) := by
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  unfold K
  unfold HaltAt; apply Exists.intro; apply Exists.intro
  gR; zRn G'; gR; refine blankR ?_; gL; gL; zLn G'; gL; gL; sLn j'; gL; gL; gR
  fin

/-- A has one cell left, X's hole at cell `c + 2`: fill it, the next round starts -/
theorem k_end (c j G : Nat) (hj : 1 ≤ j) (hG : 1 ≤ G) :
    Rch (K (c + 2) j G 0) (DV [] (c + j) 1 9 G 0 none) := by
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  unfold K
  gR; zRn G'; gR; refine blankR ?_; gL; gL; zLn G'; gL; gL; sLn j'; gL; gL; gR; gR; gL
  show Rch (cfgL ix1 (ones (c + 2) DL) _) _
  sLn (c + 2); gR; gR; gL; gL; gL; gL; gL; gL; gR
  unfold DV TAQ Qp
  rw [show c + (j' + 1) + 2 - 1 = c + 1 + (j' + 1) by omega, ← ones_add (c + 1) (j' + 1), ones_tr j', ones_tr c, cons_blank]
  fin

/-- A has one cell left and X no hole: the next round starts -/
theorem n_end (n G : Nat) (hG : 1 ≤ G) :
    Rch (N (n + 3) G 0) (DV [] n 1 9 G 0 none) := by
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  unfold N
  gR; zRn G'; gR; refine blankR ?_; gL; gL; zLn G'; gL; gL; sLn (n + 2); gL; gR; gR
  gR; gL; gL; gL; gL; gL; gL; gR
  unfold DV TAQ Qp
  rw [show n + 2 - 1 = n + 1 by omega, ones_tr, cons_blank]
  fin

end TM.Lychrel
