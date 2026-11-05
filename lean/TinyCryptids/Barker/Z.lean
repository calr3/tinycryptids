import TinyCryptids.Barker.Tape

/-! # Updating the counter: `ZA` adds 1, `ZD` subtracts 1, then back to X's last element -/

namespace TM.Barker
open St

local notation "F" => false
local notation "T" => true

/-- a left step reading the blank right part -/
theorem sLb {q q' : St} {s : Strm} {w : Bool} (h : delta q F = some (w, Dir.L, q')) :
    Rch ⟨q, s, blank⟩ (cfgL q' s (w ::: blank)) := stepL (δ := delta) (L := s) (R := blank) h

theorem FFb : F ::: F ::: blank = blank := by rw [cons_blank, cons_blank]

section
variable (W : Strm)

theorem zA_neg (u : Nat) :
    Rch ⟨ZA, F ::: F ::: W, ones (u + 1) blank⟩ (cfgL LPa W (F ::: F ::: ones u blank)) := by
  rw [ones_succ]; gR; sRn u
  refine Rch.tr (sLb (by rfl)) ?_
  rw [ones_cons_true]; gL; sLn u; gL; gL; rw [FFb]; fin

theorem zA_zero : Rch ⟨ZA, F ::: F ::: W, blank⟩ (cfgL LPa W (F ::: F ::: F ::: ones 1 blank)) := by
  rw [← cons_blank]; gR
  refine Rch.tr (sLb (by rfl)) ?_
  gL; gL; gL; rw [cons_blank]; fin

theorem zA_pos (v : Nat) :
    Rch ⟨ZA, F ::: F ::: W, F ::: ones v blank⟩ (cfgL LPa W (F ::: F ::: F ::: ones (v + 1) blank)) := by
  gR; sRn v
  refine Rch.tr (sLb (by rfl)) ?_
  sLn v; gL; gL; gL; rw [ones_succ']; fin

theorem zD_neg (u : Nat) :
    Rch ⟨ZD, F ::: F ::: W, ones (u + 1) blank⟩ (cfgL LPa W (F ::: F ::: ones (u + 2) blank)) := by
  rw [ones_succ]; gR; sRn u
  refine Rch.tr (sLb (by rfl)) ?_
  rw [← ones_succ']; sLn (u + 1); gL; gL; rw [← ones_succ']; fin

theorem zD_zero : Rch ⟨ZD, F ::: F ::: W, blank⟩ (cfgL LPa W (F ::: F ::: ones 1 blank)) := by
  rw [← cons_blank]; gR
  refine Rch.tr (sLb (by rfl)) ?_
  gL; gL; gL; fin

theorem zD_pos (v : Nat) :
    Rch ⟨ZD, F ::: F ::: W, F ::: ones (v + 1) blank⟩ (cfgL LPa W (F ::: F ::: F ::: ones v blank)) := by
  rw [ones_succ]; gR; gR; sRn v
  refine Rch.tr (sLb (by rfl)) ?_
  rw [ones_cons_true]; gL; sLn v; gL; gL; gL; rw [FFb]; fin

end

/-- agreement: the counter goes up by 1 -/
theorem zA (W : Strm) (S : Int) : Rch ⟨ZA, F ::: F ::: W, Zs S⟩ (cfgL LPa W (Zt (S + 1))) := by
  unfold Zt Zs
  rcases Int.lt_trichotomy S 0 with h | h | h
  · obtain ⟨u, hu⟩ : ∃ u : Nat, S = -((u : Int) + 1) := ⟨S.natAbs - 1, by omega⟩
    subst hu
    rw [if_pos (by omega), if_pos (by omega),
      show (-((u : Int) + 1)).natAbs = u + 1 by omega, show (-((u : Int) + 1) + 1).natAbs = u by omega]
    exact zA_neg W u
  · subst h; rw [if_pos (by omega), if_neg (by omega)]; exact zA_zero W
  · obtain ⟨v, rfl⟩ : ∃ v : Nat, S = (v : Int) + 1 := ⟨S.natAbs - 1, by omega⟩
    rw [if_neg (by omega), if_neg (by omega),
      show ((v : Int) + 1).natAbs = v + 1 by omega, show ((v : Int) + 1 + 1).natAbs = v + 2 by omega]
    exact zA_pos W (v + 1)

/-- disagreement: the counter goes down by 1 -/
theorem zD (W : Strm) (S : Int) : Rch ⟨ZD, F ::: F ::: W, Zs S⟩ (cfgL LPa W (Zt (S - 1))) := by
  unfold Zt Zs
  rcases Int.lt_trichotomy S 0 with h | h | h
  · obtain ⟨u, hu⟩ : ∃ u : Nat, S = -((u : Int) + 1) := ⟨S.natAbs - 1, by omega⟩
    subst hu
    rw [if_pos (by omega), if_pos (by omega),
      show (-((u : Int) + 1)).natAbs = u + 1 by omega, show (-((u : Int) + 1) - 1).natAbs = u + 2 by omega]
    exact zD_neg W u
  · subst h; rw [if_pos (by omega), if_pos (by omega)]; exact zD_zero W
  · obtain ⟨v, rfl⟩ : ∃ v : Nat, S = (v : Int) + 1 := ⟨S.natAbs - 1, by omega⟩
    rcases v with _ | v
    · rw [if_neg (by omega), if_pos (by omega)]
      rw [show (((0 : Nat) : Int) + 1).natAbs = 0 + 1 from rfl,
        show (((0 : Nat) : Int) + 1 - 1).natAbs = 0 from rfl]
      have := zD_pos W 0; simp only [ones_zero, cons_blank] at this ⊢; exact this
    · rw [if_neg (by omega), if_neg (by omega),
        show (((v + 1 : Nat) : Int) + 1).natAbs = v + 2 by omega,
        show (((v + 1 : Nat) : Int) + 1 - 1).natAbs = v + 1 by omega]
      exact zD_pos W (v + 1)

end TM.Barker
