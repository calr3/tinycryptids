import TinyCryptids.HardyLittlewood2.Pair

/-!
# The test at a prime, from the end of trial division to the region again

Left of the trial-division region the tape holds (left to right) B', A and C:

    B' = h_{G-1} … h₁   A = h₁ h₂ … h_{G-1}   C = c

with a hole at cell 1 of A's first block (`h₁ = 1`). `XG g c` is this part read leftwards from
C's last cell, for `g = [h₁, …, h_{G-1}]`.
-/

namespace TM.HardyLittlewood2
open St

local notation "F" => false

def XG (g : List Nat) (c : Nat) : Strm :=
  ones (c + 2) (F ::: F ::: bks g.tail.reverse (ones 1 (F ::: ones 1 (F ::: F ::: bks g blank))))

/-- the trial-division region after a prime `m`: D (hole at cell 1, `m` more cells) and R = 2 cells -/
def D0 (m : Nat) : Strm := ones 1 (F ::: ones m (F ::: F ::: ones 2 blank))

theorem PPS : ParserL delta PS1 PS2 := ⟨rfl, rfl, rfl⟩
theorem PPB : ParserL delta PB1 PB2 := ⟨rfl, rfl, rfl⟩
theorem PEP : ParserR delta EP1 EP2 := ⟨rfl, rfl, rfl⟩
theorem PEQ : ParserR delta EQ1 EQ2 := ⟨rfl, rfl, rfl⟩

/-- after a prime: the top hole into C, then to the parked hole -/
theorem start_check (g₀ : List Nat) (c m : Nat) (hc : 1 ≤ c) (hm : 1 ≤ m) :
    Rch (P6 (XG (1 :: g₀) c) m) (BF 0 (1 :: g₀) 1 1 g₀.reverse c c (F ::: F ::: D0 m)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, c = i + 1 := ⟨c - 1, by omega⟩
  unfold P6
  refine blankR ?_
  show Rch (cfgL sh6 (F ::: ones 2 (F ::: F ::: ones (k + 1) (F ::: true ::: F ::: F ::: XG (1 :: g₀) (i + 1)))) blank) _
  gL
  refine Rch.tr (PPS.find2 2 k _ _) ?_
  gL; gL; gL
  unfold XG
  show Rch (cfgL t3 (true ::: true ::: ones (i + 1) (F ::: F ::: _)) _) _
  gL; gL
  refine Rch.tr (scanL PPB.h1 (i + 1) _ _) ?_
  refine Rch.tr (sL PPB.h0) ?_
  refine Rch.tr (sL PPB.h2) ?_
  simp only [List.tail_cons]
  refine Rch.tr (PL_bks PPB g₀.reverse _ _) ?_
  show Rch (cfgL PB1 (true ::: F ::: true ::: _) _) _
  gL; gL
  unfold cfgL; gR
  unfold BF LB RB D0
  simp only [cons_blank, List.reverse_reverse, ones_zero, bks]
  rw [show 1 + 1 - 1 = 1 from rfl, show i + 1 + 1 - (i + 1) = 1 by omega]
  exact Reach.refl _ _

/-- the test passed: past the parked hole to the D hole -/
theorem end_check (g₀ : List Nat) (c m : Nat) (hm : 1 ≤ m) :
    Rch ⟨EP1, ones (c + 1) blank, true ::: F ::: F ::: bks (1 :: g₀).reverse
          (ones 1 (F ::: ones 1 (F ::: F ::: bks (g₀ ++ [c]) (D0 m))))⟩
      ⟨q1, ones 1 (F ::: F ::: ones (c + 2) (F ::: F ::: bks g₀.reverse
          (ones 1 (F ::: ones 1 (F ::: F ::: bks (1 :: g₀ ++ [c]) blank))))),
        F ::: ones m (F ::: F ::: ones 2 blank)⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  gR
  refine Rch.tr (sR PEP.h0) ?_
  refine Rch.tr (sR PEP.h2) ?_
  refine Rch.tr (PR_bks PEP _ _ _) ?_
  show Rch ⟨EP1, _, true ::: F ::: true ::: _⟩ _
  gR; gR; gR
  refine Rch.tr (sR PEQ.h0) ?_
  refine Rch.tr (sR PEQ.h2) ?_
  refine Rch.tr (PR_bks PEQ _ _ _) ?_
  unfold D0
  show Rch ⟨EQ1, _, true ::: F ::: true ::: _⟩ _
  gR; gR
  show Rch (cfgL EQ2 (true ::: _) _) _
  gL
  simp only [List.reverse_append, List.reverse_reverse, List.cons_append]
  rw [show [c].reverse = [c] from rfl, List.singleton_append,
    show (1 :: (g₀ ++ [c])) = (1 :: g₀) ++ [c] from rfl, bks_snoc]
  simp only [cons_blank]
  exact Reach.refl _ _

end TM.HardyLittlewood2
