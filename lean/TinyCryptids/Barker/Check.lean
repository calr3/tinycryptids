import TinyCryptids.Barker.Rewind

/-!
# The check `|S| ≤ 1`

From `Kc A x M z S`: if `|S| ≤ 1` the counter is erased and the next pass starts
(`P A x M z [] 0`); otherwise the counter is erased and the machine goes to `FCa` on the last
element (`Fc`), to move on to the next candidate.
-/

namespace TM.Barker
open St

local notation "F" => false
local notation "T" => true

def Fc (A : List Bool) (x : Bool) (M : List Bool) (z : Bool) : Cfg St :=
  cfgL FCa (z ::: F ::: UL M (x ::: F ::: UL A blank)) blank

theorem Zt_zero : Zt 0 = blank := by
  unfold Zt Zs; rw [if_pos (by omega)]; simp [cons_blank]
theorem Zs_zero : Zs 0 = blank := by unfold Zs; rw [if_pos (by omega)]; rfl
theorem Zs_one : Zs 1 = F ::: T ::: blank := by unfold Zs; rw [if_neg (by omega)]; rfl
theorem Zs_m1 : Zs (-1) = T ::: blank := by unfold Zs; rw [if_pos (by omega)]; rfl
theorem Zs_pos (v : Nat) : Zs ((v : Int) + 2) = F ::: ones (v + 2) blank := by
  unfold Zs; rw [if_neg (by omega), show ((v : Int) + 2).natAbs = v + 2 by omega]
theorem Zs_neg (u : Nat) : Zs (-((u : Int) + 2)) = ones (u + 2) blank := by
  unfold Zs; rw [if_pos (by omega), show (-((u : Int) + 2)).natAbs = u + 2 by omega]

/-- back from the counter to the next pass's first pair -/
theorem ret (A : List Bool) (x : Bool) (M : List Bool) (z : Bool) :
    Rch (cfgL LPa (z ::: F ::: UL M (x ::: F ::: UL A blank)) blank) (P A x M z [] 0) := by
  unfold P; rw [Zt_zero]
  cases z <;> cases x
  all_goals
    gL; gL
    refine Rch.tr (keyL (fun b => by cases b <;> rfl) (by rfl) M _ _) ?_
    gL; gL; fin

theorem check_pass (A : List Bool) (x : Bool) (M : List Bool) (z : Bool) (S : Int)
    (hS : S.natAbs ≤ 1) : Rch (Kc A x M z S) (P A x M z [] 0) := by
  refine Rch.tr ?_ (ret A x M z)
  unfold Kc
  rcases (by omega : S = 0 ∨ S = 1 ∨ S = -1) with h | h | h <;> subst h
  · rw [Zs_zero, ← cons_blank]; gR
    refine Rch.tr (sLb (by rfl)) ?_
    gL; gL; gL; simp only [cons_blank]; fin
  · rw [Zs_one]; gR; gR
    refine Rch.tr (sLb (by rfl)) ?_
    gL; gL; gL; gL; simp only [cons_blank]; fin
  · rw [Zs_m1]; gR
    refine Rch.tr (sLb (by rfl)) ?_
    gL; gL; gL; simp only [cons_blank]; fin

theorem check_fail (A : List Bool) (x : Bool) (M : List Bool) (z : Bool) (S : Int)
    (hS : 2 ≤ S.natAbs) : Rch (Kc A x M z S) (Fc A x M z) := by
  unfold Kc Fc
  rcases (by omega : 2 ≤ S ∨ S ≤ -2) with h | h
  · obtain ⟨v, rfl⟩ : ∃ v : Nat, S = (v : Int) + 2 := ⟨S.natAbs - 2, by omega⟩
    rw [Zs_pos, ones_succ, ones_succ]
    gR; gR; gR; sRn v
    refine Rch.tr (sLb (by rfl)) ?_
    rw [← ones_succ', ← ones_succ']
    refine Rch.tr (eraseL'' (by rfl) (v + 1 + 1) _ _) ?_
    gL; gL; gL; simp only [cons_blank, zeros_blank]; fin
  · obtain ⟨u, rfl⟩ : ∃ u : Nat, S = -((u : Int) + 2) := ⟨S.natAbs - 2, by omega⟩
    rw [Zs_neg, ones_succ, ones_succ]
    gR; gR; sRn u
    refine Rch.tr (sLb (by rfl)) ?_
    rw [← ones_succ', ← ones_succ']
    refine Rch.tr (eraseL'' (by rfl) (u + 1 + 1) _ _) ?_
    gL; gL; simp only [cons_blank, zeros_blank]; fin

end TM.Barker
