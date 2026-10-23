import TinyCryptids.Sierpinski.Cycle

/-!
# The counter and the step to a new k

`C` holds `v < 2^16` in four groups of four bits, each group followed by a marker 1; seen
from its right end (nearest cell first) a group is the marker, then bits 0, 1, 2, 3.  The loop
on K ends on the marker of the lowest group (`t1`), which reads it as `Dm` would.
-/

namespace TM.Sierpinski
open St TinyCryptids

local notation "F" => false

/-- a group seen from its right end: the marker, then bits 0..3 of `u` -/
def grp (u : Nat) (s : Strm) : Strm :=
  true ::: decide (u % 2 = 1) ::: decide (u / 2 % 2 = 1) ::: decide (u / 4 % 2 = 1) :::
    decide (u / 8 % 2 = 1) ::: s

/-- the counter seen from its right end -/
def Cs (v : Nat) : Strm := grp (v % 16) (grp (v / 16 % 16) (grp (v / 256 % 16) (grp (v / 4096 % 16) blank)))

/-- the states that read a group's marker and go on to its bit 0 -/
def Mk (q : St) : Prop := delta q true = some (true, Dir.L, D0)

theorem mk_Dm : Mk Dm := rfl
theorem mk_t1 : Mk t1 := rfl

theorem grp_zero {q : St} (hq : Mk q) (s R : Strm) : Rch (cfgL q (grp 0 s) R) (cfgL Dm s (ones 5 R)) := by
  unfold grp; refine Rch.tr (sL hq) ?_; gL; gL; gL; gL; fin

theorem grp_15 (s : Strm) : grp 15 s = ones 5 s := rfl

/-- decrement a group `u > 0` (the groups below were 0 and are now `ones t`), return to K -/
theorem grp_dec {q : St} (hq : Mk q) (u : Nat) (hu : 0 < u) (h16 : u < 16) (s Z : Strm) (t : Nat) :
    Rch (cfgL q (grp u s) (ones t (F ::: Z))) ⟨b2, F ::: ones t (grp (u - 1) s), Z⟩ := by
  unfold grp
  refine Rch.tr (sL hq) ?_
  rcases (show u % 2 = 1 ∨ u % 4 = 2 ∨ u % 8 = 4 ∨ u = 8 by omega) with h | h | h | h
  · rw [show decide (u % 2 = 1) = true by simp [h], show decide ((u - 1) % 2 = 1) = false by simp; omega,
      show (u - 1) / 2 = u / 2 by omega, show (u - 1) / 4 = u / 4 by omega, show (u - 1) / 8 = u / 8 by omega]
    gR; sRn (t + 1); gR
    rw [ones_succ']; fin
  · rw [show decide (u % 2 = 1) = false by simp; omega, show decide (u / 2 % 2 = 1) = true by simp; omega,
      show decide ((u - 1) % 2 = 1) = true by simp; omega,
      show decide ((u - 1) / 2 % 2 = 1) = false by simp; omega,
      show (u - 1) / 4 = u / 4 by omega, show (u - 1) / 8 = u / 8 by omega]
    gL; gR; sRn (t + 2); gR
    rw [show t + 2 = t + 1 + 1 from rfl, ones_succ', ones_succ']; fin
  · rw [show decide (u % 2 = 1) = false by simp; omega, show decide (u / 2 % 2 = 1) = false by simp; omega,
      show decide (u / 4 % 2 = 1) = true by simp; omega,
      show decide ((u - 1) % 2 = 1) = true by simp; omega,
      show decide ((u - 1) / 2 % 2 = 1) = true by simp; omega,
      show decide ((u - 1) / 4 % 2 = 1) = false by simp; omega, show (u - 1) / 8 = u / 8 by omega]
    gL; gL; gR; sRn (t + 3); gR
    rw [show t + 3 = t + 1 + 1 + 1 from rfl, ones_succ', ones_succ', ones_succ']; fin
  · subst h
    gL; gL; gL; gR; sRn (t + 4); gR
    rw [show t + 4 = t + 1 + 1 + 1 + 1 from rfl, ones_succ', ones_succ', ones_succ', ones_succ']; fin

/-- `v = 0`: the borrow runs past the top group: HALT -/
theorem cnt_zero (R : Strm) : HaltAt (cfgL t1 (Cs 0) R) := by
  unfold HaltAt Cs; apply Exists.intro; apply Exists.intro
  refine Rch.tr (grp_zero mk_t1 _ _) (Rch.tr (grp_zero mk_Dm _ _) (Rch.tr (grp_zero mk_Dm _ _)
    (Rch.tr (grp_zero mk_Dm _ _) ?_)))
  gR; fin

/-- decrement `v = w + 1`, return to the cell right of C's separator -/
theorem cnt_dec (w : Nat) (hw : w + 1 < 65536) (Z : Strm) :
    Rch (cfgL t1 (Cs (w + 1)) (F ::: Z)) ⟨b2, F ::: Cs w, Z⟩ := by
  unfold Cs
  by_cases h0 : (w + 1) % 16 = 0
  · rw [h0]
    refine Rch.tr (grp_zero mk_t1 _ _) ?_
    by_cases h1 : (w + 1) / 16 % 16 = 0
    · rw [h1]
      refine Rch.tr (grp_zero mk_Dm _ _) ?_
      by_cases h2 : (w + 1) / 256 % 16 = 0
      · rw [h2]
        refine Rch.tr (grp_zero mk_Dm _ _) ?_
        have h3 : 0 < (w + 1) / 4096 % 16 := by omega
        refine Rch.tr (grp_dec mk_Dm _ h3 (Nat.mod_lt _ (by omega)) _ _ (5 + 5 + 5)) ?_
        rw [show w % 16 = 15 by omega, show w / 16 % 16 = 15 by omega, show w / 256 % 16 = 15 by omega,
          show w / 4096 % 16 = (w + 1) / 4096 % 16 - 1 by omega, grp_15, grp_15, grp_15, ones_add, ones_add]
        fin
      · refine Rch.tr (grp_dec mk_Dm _ (by omega) (Nat.mod_lt _ (by omega)) _ _ (5 + 5)) ?_
        rw [show w % 16 = 15 by omega, show w / 16 % 16 = 15 by omega,
          show w / 256 % 16 = (w + 1) / 256 % 16 - 1 by omega, show w / 4096 = (w + 1) / 4096 by omega,
          grp_15, grp_15, ones_add]
        fin
    · refine Rch.tr (grp_dec mk_Dm _ (by omega) (Nat.mod_lt _ (by omega)) _ _ 5) ?_
      rw [show w % 16 = 15 by omega, show w / 16 % 16 = (w + 1) / 16 % 16 - 1 by omega,
        show w / 256 = (w + 1) / 256 by omega, show w / 4096 = (w + 1) / 4096 by omega, grp_15]
      fin
  · refine Rch.tr (grp_dec mk_t1 _ (by omega) (Nat.mod_lt _ (by omega)) _ _ 0) ?_
    rw [show w % 16 = (w + 1) % 16 - 1 by omega, show w / 16 = (w + 1) / 16 by omega,
      show w / 256 = (w + 1) / 256 by omega, show w / 4096 = (w + 1) / 4096 by omega]
    fin

/-- the new region: fill K's gap (k += 2), cross K', the copy T becomes D := 3 and R -/
theorem newk (C : Strm) (K : Nat) (hK : 7 ≤ K) :
    Rch ⟨b2, F ::: C, F ::: ones K (F ::: ones K blank)⟩
      (cfgL s1 (ones (K - 7) (F ::: YR (ones (K + 1) (F ::: C)))) blank) := by
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 7 := ⟨K - 7, by omega⟩
  gR; sRn (n + 7); gR; gR
  rw [show ones (n + 7) (true ::: F ::: C) = ones (n + 7 + 1) (F ::: C) from (ones_succ' _ _).symm,
    show n + 7 - 7 = n by omega]
  exact rtail _ n

/-- the step to k = 1: T has 6 cells, one short of R's cell 0, which `g6` makes on a blank cell -/
theorem newk_pseudo (C : Strm) :
    Rch ⟨b2, F ::: C, F ::: ones 6 (F ::: ones 6 blank)⟩
      (cfgL s1 (F ::: YR (ones 7 (F ::: C))) blank) := by
  gR; sRn 6; gR; gR
  gR; gR; gR; gR; gR; refine blankR ?_; gR; refine blankR ?_; gL
  show Rch (cfgL s1 (F ::: F ::: F ::: F ::: true ::: true ::: true ::: F ::: ones 6 (true ::: F ::: C))
    (F ::: blank)) _
  rw [cons_blank, show ones 6 (true ::: F ::: C) = ones 7 (F ::: C) from (ones_succ' _ _).symm]
  fin

end TM.Sierpinski
