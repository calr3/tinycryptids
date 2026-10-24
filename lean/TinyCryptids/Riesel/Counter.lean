import TinyCryptids.Riesel.Cycle

/-!
# The counter and the step to a new k

`C` holds `v < 2^20` in five groups of four bits, each group followed by a marker 1; seen
from its right end (nearest cell first) a group is the marker, then bits 0, 1, 2, 3.
-/

namespace TM.Riesel
open St TinyCryptids

local notation "F" => false

/-- a group seen from its right end: the marker, then bits 0..3 of `u` -/
def grp (u : Nat) (s : Strm) : Strm :=
  true ::: decide (u % 2 = 1) ::: decide (u / 2 % 2 = 1) ::: decide (u / 4 % 2 = 1) :::
    decide (u / 8 % 2 = 1) ::: s

/-- a counter of `g` groups seen from its right end -/
def Cg : Nat → Nat → Strm
  | 0, _ => blank
  | g + 1, v => grp (v % 16) (Cg g (v / 16))

/-- the counter: five groups -/
def Cs (v : Nat) : Strm := Cg 5 v

theorem grp_zero (s R : Strm) : Rch (cfgL Dm (grp 0 s) R) (cfgL Dm s (ones 5 R)) := by
  unfold grp; gL; gL; gL; gL; gL; fin

theorem grp_15 (s : Strm) : grp 15 s = ones 5 s := rfl

/-- decrement a group `u > 0` (the groups below were 0 and are now `ones t`), return to K -/
theorem grp_dec (u : Nat) (hu : 0 < u) (h16 : u < 16) (s Z : Strm) (t : Nat) :
    Rch (cfgL Dm (grp u s) (ones t (F ::: F ::: Z))) ⟨b2, F ::: F ::: ones t (grp (u - 1) s), Z⟩ := by
  unfold grp
  rcases (show u % 2 = 1 ∨ u % 4 = 2 ∨ u % 8 = 4 ∨ u = 8 by omega) with h | h | h | h
  · rw [show decide (u % 2 = 1) = true by simp [h], show decide ((u - 1) % 2 = 1) = false by simp; omega,
      show (u - 1) / 2 = u / 2 by omega, show (u - 1) / 4 = u / 4 by omega, show (u - 1) / 8 = u / 8 by omega]
    gL; gR; sRn (t + 1); gR; gR
    rw [ones_succ']; fin
  · rw [show decide (u % 2 = 1) = false by simp; omega, show decide (u / 2 % 2 = 1) = true by simp; omega,
      show decide ((u - 1) % 2 = 1) = true by simp; omega,
      show decide ((u - 1) / 2 % 2 = 1) = false by simp; omega,
      show (u - 1) / 4 = u / 4 by omega, show (u - 1) / 8 = u / 8 by omega]
    gL; gL; gR; sRn (t + 2); gR; gR
    rw [show t + 2 = t + 1 + 1 from rfl, ones_succ', ones_succ']; fin
  · rw [show decide (u % 2 = 1) = false by simp; omega, show decide (u / 2 % 2 = 1) = false by simp; omega,
      show decide (u / 4 % 2 = 1) = true by simp; omega,
      show decide ((u - 1) % 2 = 1) = true by simp; omega,
      show decide ((u - 1) / 2 % 2 = 1) = true by simp; omega,
      show decide ((u - 1) / 4 % 2 = 1) = false by simp; omega, show (u - 1) / 8 = u / 8 by omega]
    gL; gL; gL; gR; sRn (t + 3); gR; gR
    rw [show t + 3 = t + 1 + 1 + 1 from rfl, ones_succ', ones_succ', ones_succ']; fin
  · subst h
    gL; gL; gL; gL; gR; sRn (t + 4); gR; gR
    rw [show t + 4 = t + 1 + 1 + 1 + 1 from rfl, ones_succ', ones_succ', ones_succ', ones_succ']; fin

/-- `v = 0`: the borrow runs past the top group: HALT -/
theorem cg_zero : ∀ g (R : Strm), HaltAt (cfgL Dm (Cg g 0) R)
  | 0, R => by unfold HaltAt Cg; apply Exists.intro; apply Exists.intro; gR; fin
  | g + 1, R => HaltAt.back (grp_zero _ _) (cg_zero g _)

theorem cnt_zero (R : Strm) : HaltAt (cfgL Dm (Cs 0) R) := cg_zero 5 R

/-- decrement `w + 1` (the groups below are `ones t`), return to K's first cell -/
theorem cg_dec : ∀ g w t (Z : Strm), w + 1 < 16 ^ g →
    Rch (cfgL Dm (Cg g (w + 1)) (ones t (F ::: F ::: Z))) ⟨b2, F ::: F ::: ones t (Cg g w), Z⟩
  | 0, w, _, _, hw => by simp at hw
  | g + 1, w, t, Z, hw => by
    unfold Cg
    by_cases h0 : (w + 1) % 16 = 0
    · rw [h0]
      refine Rch.tr (grp_zero _ _) ?_
      obtain ⟨u, hu⟩ : ∃ u, (w + 1) / 16 = u + 1 := ⟨(w + 1) / 16 - 1, by omega⟩
      rw [hu]
      have hp : 16 ^ (g + 1) = 16 ^ g * 16 := by rw [Nat.pow_succ]
      rw [ones_add]
      refine Rch.tr (cg_dec g u (5 + t) Z (by omega)) ?_
      rw [show w % 16 = 15 by omega, show w / 16 = u by omega, grp_15, ones_add, Nat.add_comm 5 t]
      fin
    · refine Rch.tr (grp_dec _ (by omega) (Nat.mod_lt _ (by omega)) _ _ t) ?_
      rw [show w % 16 = (w + 1) % 16 - 1 by omega, show w / 16 = (w + 1) / 16 by omega]
      fin

theorem cnt_dec (w : Nat) (hw : w + 1 < 2 ^ 20) (Z : Strm) :
    Rch (cfgL Dm (Cs (w + 1)) (F ::: F ::: Z)) ⟨b2, F ::: F ::: Cs w, Z⟩ :=
  cg_dec 5 w 0 Z (by simpa using hw)

/-- the new region: fill K's gap (k += 2), cross X', the copy T gets the D hole -/
theorem newk (C : Strm) (K : Nat) (hK : 9 ≤ K) :
    Rch ⟨b2, F ::: F ::: C, F ::: F ::: ones K (F ::: F ::: ones K blank)⟩
      (cfgL s1 (ones (K - 9) (F ::: YR (ones (K + 2) (F ::: F ::: C)))) blank) := by
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 9 := ⟨K - 9, by omega⟩
  gR; gR; sRn (n + 9); gR; gR; gR; gR
  rw [show ones (n + 9) (true ::: true ::: F ::: F ::: C) = ones (n + 9 + 2) (F ::: F ::: C) from
    ones_add (n + 9) 2 _, show n + 9 - 9 = n by omega]
  exact rtail _ n

end TM.Riesel
