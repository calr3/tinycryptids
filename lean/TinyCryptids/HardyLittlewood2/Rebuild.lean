import TinyCryptids.HardyLittlewood2.Check

/-!
# The rebuild of the trial-division region for the next candidate `m + 2`

* composite (`d ∣ m` found): C gets one more cell, D := 3, R := `m + 2 - 3`;
* prime (after the test): a new C of one cell, D := 3, R := `m + 2 - 3`.

Both fill the D/R separator, append cells at the right end, come back to the D hole and
write the same pattern three cells left of it (the prime path first moves the hole four cells
right, so the pattern lands after the new C).
-/

namespace TM.HardyLittlewood2
open St

local notation "F" => false

theorem ones2 (n : Nat) (Z : Strm) : true ::: true ::: ones n Z = ones (n + 2) Z := rfl

/-- from three cells left of the hole (`x₀ x₁ 1`, then the hole, then `r + 8` ones): C's new
cell (or the new C's last), 00, D = 3 with its hole, 00, R's cell 0 and its hole; then back to
the D hole -/
theorem writer (A : Strm) (x0 x1 : Bool) (r : Nat) :
    Rch ⟨W0, A, x0 ::: x1 ::: true ::: F ::: ones (r + 8) blank⟩ (MW (true ::: A) 3 r 0 1) := by
  have : Rch ⟨W1, true ::: A, x1 ::: true ::: F ::: ones (r + 8) blank⟩ (MW (true ::: A) 3 r 0 1) := by
    have : Rch ⟨W2, F ::: true ::: A, true ::: F ::: ones (r + 8) blank⟩ (MW (true ::: A) 3 r 0 1) := by
      gR; gR; gR; gR; gR; gR; gR; gR; gR
      show Rch (cfgL W11 (true ::: _) _) _
      gL
      refine Rch.tr (PPM.find2 1 2 _ _) ?_
      gR
      unfold MW
      rw [show 3 - 0 = 3 from rfl, show r + 1 - 1 = r by omega]
      exact Reach.refl _ _
    cases x1 <;> (gR; exact this)
  cases x0 <;> (gR; exact this)

/-- the mod walk found a divisor `d` of `m = d + r`: C gets a cell, D := 3, R := `m + 2 - 3` -/
theorem comp_rebuild (W : Strm) (k d r : Nat) (hd : 3 ≤ d) (hr : 1 ≤ r) :
    Rch (MW (ones (k + 1) (F ::: F ::: W)) d r (d - 1) r) (MW (ones (k + 2) (F ::: F ::: W)) 3 (d + r - 1) 0 1) := by
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  unfold MW
  rw [show c + 1 - 1 = c by omega, show c + 1 - c = 1 by omega, show b + 1 + 1 - (b + 1) = 1 by omega]
  refine Rch.tr (Dma.toDW.wrap (c + 1) (F ::: _) _) ?_
  refine Rch.tr (PPR.find2 (c + 1) b _ blank) ?_
  gL; gR; gR; refine blankR ?_; gL
  refine Rch.tr (PPK.find2 (b + 3) c _ _) ?_
  gL; gR; gR; gR
  sRn (c + 1); gR; gR; sRn (b + 3)
  gR; refine blankR ?_; gR; refine blankR ?_; gL
  show Rch (cfgL RL (true ::: true ::: ones (b + 3) (true ::: true ::: ones (c + 1)
    (F ::: true ::: F ::: F ::: ones (k + 1) (F ::: F ::: W)))) (true ::: blank)) _
  rw [ones2 (c + 1), ones_add, ones2, show b + 3 + (c + 1 + 2) + 2 = b + c + 8 by omega]
  sLn (b + c + 8); gL; gL; gL
  rw [ones_snoc]
  refine Rch.tr (writer (ones (k + 1) (F ::: F ::: W)) F F (b + c + 1)) ?_
  unfold MW
  rw [show c + 1 + (b + 1) - 1 = b + c + 1 by omega]
  exact Reach.refl _ _

/-- after the test at the prime `m`: a new C (one cell), D := 3, R := `m + 2 - 3` -/
theorem prime_rebuild (X : Strm) (m : Nat) (hm : 5 ≤ m) :
    Rch ⟨q1, ones 1 (F ::: F ::: X), F ::: ones m (F ::: F ::: ones 2 blank)⟩
      (MW (ones 3 (F ::: F ::: X)) 3 (m - 1) 0 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 5 := ⟨m - 5, by omega⟩
  gR; gR; gR; gR; gR
  sRn (n + 1); gR; gR; sRn 2
  refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR
  refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gL
  have e : ∀ Z : Strm, (true ::: true ::: true ::: true ::: true ::: true ::: ones 2 (true ::: true ::: ones (n + 1) Z))
      = ones (n + 11) Z := by
    intro Z; rw [ones2 (n + 1) Z, ones_add, show n + 11 = 2 + (n + 1 + 2) + 6 by omega]; rfl
  show Rch (cfgL RL (true ::: true ::: true ::: true ::: true ::: true ::: ones 2 (true ::: true ::: ones (n + 1)
    (F ::: true ::: true ::: true ::: true ::: ones 1 (F ::: F ::: X)))) (true ::: blank)) _
  rw [e]
  sLn (n + 11); gL; gL; gL
  rw [ones_snoc, show n + 5 - 1 = n + 4 by omega]
  exact writer (ones 2 (F ::: F ::: X)) true true (n + 4)

end TM.HardyLittlewood2
