import TinyCryptids.Lychrel.Tac
import TinyCryptids.Lychrel.Find

/-!
# The counter D

D is 12 cells `d0 … d11`, left of everything else, with one hole at `d(p+1)`:
the counter `p` mod 10.  A configuration at the hole has `ones (p+1) blank` on its
left and `F ::: ones (10 - p) Rt` on its right.
-/

namespace TM.Lychrel
open St

local notation "F" => false

/-- p += 1 (p ≤ 8); the head ends on `d(p+3)` in `nP` -/
theorem fstep (p k : Nat) (Rt : Strm) :
    Rch ⟨fA, ones (p + 1) blank, F ::: ones (k + 2) Rt⟩ ⟨nP, F ::: ones (p + 2) blank, ones (k + 1) Rt⟩ := by
  gR; gR; gL; gR; fin

/-- p = 9 → 0: the hole goes back to `d1`; the head ends on `d2` in `wP` -/
theorem fstep_wrap (Rt : Strm) :
    Rch ⟨fA, ones 10 blank, F ::: ones 1 (F ::: Rt)⟩ ⟨wP, F ::: ones 1 blank, ones 10 (F ::: Rt)⟩ := by
  gR; gR; gL
  show Rch (cfgL fw1 (ones 12 blank) (F ::: Rt)) _
  sLn 12
  show Rch ⟨fw1, blank, F ::: ones 12 (F ::: Rt)⟩ _
  gR; gR; gR
  rw [cons_blank]; fin

/-- p -= 1 (p ≥ 1); the head ends on `d(p+1)` in `rP1` -/
theorem bstep (p k : Nat) (Rt : Strm) :
    Rch ⟨bA, ones (p + 2) blank, F ::: ones (k + 1) Rt⟩ ⟨rP1, F ::: ones (p + 1) blank, ones (k + 2) Rt⟩ := by
  gL; gL; gR; gR; fin

/-- p = 0 → 9: the hole goes to `d10`; the head ends on `d11` in `rA1` -/
theorem bstep_wrap (Rt : Strm) :
    Rch ⟨bA, ones 1 blank, F ::: ones 10 (F ::: Rt)⟩ ⟨rA1, F ::: ones 10 blank, ones 1 (F ::: Rt)⟩ := by
  gL; gL
  show Rch ⟨bD, blank, F ::: ones 12 (F ::: Rt)⟩ _
  gR; sRn 12; gL; gL; gR
  rw [cons_blank]; fin

end TM.Lychrel
