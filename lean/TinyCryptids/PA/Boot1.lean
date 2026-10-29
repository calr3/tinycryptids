import TinyCryptids.PA.Tape

/-!
# boot1: the 5-state counter

From the blank tape, states `0a.boot1.A`–`E` grow a run of pairs `(10)^k` at the left end by
*sweeps*: each sweep turns three ones of the block `1^b` right of the pairs into four more pairs
(`sweep`).  When fewer than three ones are left the block is rebuilt from the pairs (`endZero`:
`1^(2k+4)`, and the run of ones after it grows by one) or, with two ones left, the counter stops
(`endTwo`).  Seven rounds (blocks 4, 10, 26, 76, 202, 538, 1434) end with `(10)^1909 1 1 0 1111`
and state `3.prooflist.inc` on the second `1` (`boot1`), after 2,133,492 steps.
-/

namespace TM.PA

open TM

/-- `(10)^k` -/
def pairs : Nat → List Bool
  | 0 => []
  | k + 1 => true :: false :: pairs k

/-- `(01)^k` -/
def rpairs : Nat → List Bool
  | 0 => []
  | k + 1 => false :: true :: rpairs k

theorem rpairs_snoc (k : Nat) : rpairs k ++ [false, true] = false :: true :: rpairs k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rpairs, ih]

theorem pairs_rev (k : Nat) : (pairs k).reverse = rpairs k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pairs, ih, rpairs_snoc, rpairs]

theorem rpairs_tail (n : Nat) : true :: rpairs n ++ [false, true, false] = pairs (n + 2) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rpairs, List.cons_append, pairs] at ih ⊢; rw [ih]

theorem pairs_succ' (k : Nat) : pairs (k + 1) = pairs k ++ [true, false] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pairs] at ih ⊢; exact ih

theorem pairs_add (j k : Nat) : pairs (j + k) = pairs j ++ pairs k := by
  induction j with
  | zero => simp [pairs]
  | succ j ih => simp [Nat.succ_add, pairs, ih]

section
variable {dag : Nat → Option (Ch × Ch)}

/-- a left move onto the blank part of the tape -/
theorem sLb {q q' : St} {R : Strm} {c w : Bool} (h : delta dag 0 q c = some (w, Dir.L, q')) :
    Rch dag ⟨q, blank, c ::: R⟩ ⟨q', blank, false ::: w ::: R⟩ :=
  stepL (δ := delta dag 0) (L := blank) (R := c ::: R) h

macro "gLb" : tactic => `(tactic| refine Rch.tr (sLb (by rfl)) ?_)

/-- a sweep start: `A` on the first of two zeros, pairs, a block of ones, the rest `X` -/
def Sw (k b : Nat) (X : Strm) : Cfg St := ⟨.bA, blank, false ::: false ::: app (pairs k) (ones b X)⟩

/-- a round start: `A` on a zero, the block `1^a`, a zero, `1^t`, the rest `Z` -/
def Big (a t : Nat) (Z : Strm) : Cfg St := ⟨.bA, blank, false ::: ones a (false ::: ones t Z)⟩

/-- `D` and `E` cross pairs to the right -/
theorem scanDE (n : Nat) (L Y : Strm) :
    Rch dag ⟨.bD, L, app (pairs n) Y⟩ ⟨.bD, app (pairs n).reverse L, Y⟩ := by
  induction n generalizing L with
  | zero => exact Reach.refl _ _
  | succ n ih =>
    show Rch dag ⟨.bD, L, true ::: false ::: app (pairs n) Y⟩ _
    gR; gR
    refine Rch.tr (ih _) (Rch.of_eq ?_)
    simp [pairs, app_append]

/-- `B` and `D` cross pairs to the left, turning each `10` into `01` -/
theorem scanBD (n : Nat) (L R : Strm) :
    Rch dag (cfgL .bD (app (rpairs n) L) R) (cfgL .bD L (app (rpairs n) R)) := by
  induction n generalizing R with
  | zero => exact Reach.refl _ _
  | succ n ih =>
    show Rch dag (cfgL .bD (false ::: true ::: app (rpairs n) L) R) _
    gL; gL
    refine Rch.tr (ih _) (Rch.of_eq ?_)
    have := congrArg (fun l => app l R) (rpairs_snoc n)
    simp only [app_append, app_cons, app_nil] at this
    simp only [rpairs, app_cons, this]

/-- `A` and `C` cross pairs to the left, turning each `10` into `11` -/
theorem scanAC (n : Nat) (L R : Strm) :
    Rch dag (cfgL .bA (true ::: app (rpairs n) L) R) (cfgL .bA (true ::: L) (ones (2 * n) R)) := by
  induction n generalizing R with
  | zero => exact Reach.refl _ _
  | succ n ih =>
    show Rch dag (cfgL .bA (true ::: false ::: true ::: app (rpairs n) L) R) _
    gL; gL
    refine Rch.tr (ih _) (Rch.of_eq ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, ones_succ', ones_succ']

/-- the left end of a sweep: two more pairs, then `D` on the first -/
theorem gadget (k : Nat) (Y : Strm) :
    Rch dag ⟨.bA, blank, false ::: false ::: app (pairs k) Y⟩ ⟨.bD, blank, app (pairs (k + 2)) Y⟩ := by
  gR; gLc; gLb; gLb; gR; gLc
  exact Rch.of_eq (by simp [pairs])

/-- a sweep: three ones become four pairs -/
theorem sweep (k b : Nat) (X : Strm) : Rch dag (Sw k (b + 3) X) (Sw (k + 4) b X) := by
  unfold Sw
  refine Rch.tr (gadget k _) ?_
  refine Rch.tr (scanDE (k + 2) _ _) ?_
  rw [show b + 3 = b + 1 + 1 + 1 by omega, ones_succ, ones_succ, ones_succ, pairs_rev]
  -- the turn on the block
  gR; gR; gLc
  show Rch dag ⟨.bD, true ::: app (false :: true :: rpairs (k + 1)) blank, false ::: false ::: ones b X⟩ _
  gLc; gLc
  show Rch dag (cfgL .bD (app (rpairs (k + 2)) blank) (false ::: true ::: false ::: ones b X)) _
  refine Rch.tr (scanBD (k + 2) _ _) ?_
  show Rch dag ⟨.bD, blank, false ::: app (rpairs (k + 2)) (false ::: true ::: false ::: ones b X)⟩ _
  gLb; gLb
  exact Rch.of_eq (by
    have := congrArg (fun l => app l (ones b X)) (rpairs_tail (k + 2))
    simp only [app_append, app_cons, app_nil, List.cons_append] at this
    simp only [this])

/-- a right move onto the blank part of the tape -/
theorem sRb {q q' : St} {L : Strm} {w : Bool} (h : delta dag 0 q false = some (w, Dir.R, q')) :
    Rch dag ⟨q, L, blank⟩ ⟨q', w ::: L, blank⟩ :=
  stepR (δ := delta dag 0) (L := L) (R := blank) h

theorem sweeps (j : Nat) : ∀ k b (X : Strm), Rch dag (Sw k (b + 3 * j) X) (Sw (k + 4 * j) b X) := by
  induction j with
  | zero => intro k b X; exact Reach.refl _ _
  | succ j ih =>
    intro k b X
    rw [show b + 3 * (j + 1) = (b + 3 * j) + 3 by omega]
    refine Rch.tr (sweep k _ X) ?_
    rw [show k + 4 * (j + 1) = (k + 4) + 4 * j by omega]
    exact ih _ _ _

/-- the first 16 steps -/
theorem init1 : Rch dag ⟨.bA, blank, blank⟩ (Big 4 1 blank) := by
  refine Rch.tr (sRb (by rfl)) ?_
  refine Rch.tr (stepL (δ := delta dag 0) (L := true ::: blank) (R := blank) (by rfl)) ?_
  show Rch dag ⟨.bA, blank, true ::: false ::: blank⟩ _
  gLb; gLb; gR; gLc; gR; gR; gR; gR
  refine Rch.tr (stepL (δ := delta dag 0) (L := false ::: true ::: false ::: true ::: blank) (R := blank) (by rfl)) ?_
  show Rch dag ⟨.bB, true ::: false ::: true ::: blank, false ::: true ::: blank⟩ _
  gLc; gLc; gLc; gLb; gLb
  exact Rch.of_eq (by simp [Big, ones, cons_blank])

/-- the start of a round: the block is cut into three pairs and the rest -/
theorem bigSw (a t : Nat) (Z : Strm) : Rch dag (Big (a + 4) t Z) (Sw 3 a (false ::: ones t Z)) := by
  unfold Big Sw
  rw [show a + 4 = a + 1 + 1 + 1 + 1 by omega, ones_succ, ones_succ, ones_succ, ones_succ]
  gR; gLc; gR; gR; gR; gR; gLc; gLc; gLc; gLc; gLb; gLb; gLb
  exact Rch.of_eq rfl

/-- the end of a round with no ones left: the pairs become the next block -/
theorem endZero (k t : Nat) (Z : Strm) :
    Rch dag (Sw k 0 (false ::: ones t Z)) (Big (2 * k + 4) (t + 1) Z) := by
  unfold Sw Big
  refine Rch.tr (gadget k _) ?_
  refine Rch.tr (scanDE (k + 2) _ _) ?_
  rw [ones_zero, pairs_rev]
  show Rch dag ⟨.bD, app (false :: true :: rpairs (k + 1)) blank, false ::: ones t Z⟩ _
  gLc
  show Rch dag ⟨.bB, true ::: app (rpairs (k + 1)) blank, false ::: true ::: ones t Z⟩ _
  gLc
  show Rch dag (cfgL .bA (true ::: app (rpairs (k + 1)) blank) (false ::: true ::: ones t Z)) _
  refine Rch.tr (scanAC (k + 1) _ _) ?_
  show Rch dag ⟨.bA, blank, true ::: ones (2 * (k + 1)) (false ::: true ::: ones t Z)⟩ _
  gLb; gLb
  exact Rch.of_eq (by
    rw [show 2 * k + 4 = 2 * (k + 1) + 1 + 1 by omega, ones_succ, ones_succ, ones_succ])

/-- the end of the last round, two ones left: `3.prooflist.inc` on the second -/
theorem endTwo (k : Nat) (Y : Strm) :
    Rch dag (Sw k 2 (false ::: Y)) ⟨.incL 0, true ::: app (rpairs (k + 2)) blank, true ::: false ::: Y⟩ := by
  unfold Sw
  refine Rch.tr (gadget k _) ?_
  refine Rch.tr (scanDE (k + 2) _ _) ?_
  rw [pairs_rev]
  show Rch dag ⟨.bD, app (rpairs (k + 2)) blank, true ::: true ::: false ::: Y⟩ _
  gR; gR; gLc; gR; gLc; gLc; gR
  exact Reach.refl _ _

theorem sw_merge (k : Nat) (X : Strm) : Sw k 1 (false ::: X) = Sw (k + 1) 0 X := by
  unfold Sw
  rw [pairs_succ', app_append]; rfl

/-- boot1: from the blank tape to `(10)^1909 1 [1] 0 1111` in `3.prooflist.inc` -/
theorem boot1 :
    Rch dag ⟨.bA, blank, blank⟩ ⟨.incL 0, true ::: app (rpairs 1909) blank, true ::: false ::: ones 4 blank⟩ := by
  refine Rch.tr init1 ?_
  -- round 1: block 4
  refine Rch.tr (bigSw 0 1 blank) ?_
  refine Rch.tr (endZero 3 1 blank) ?_
  -- round 2: block 10
  refine Rch.tr (bigSw 6 2 blank) ?_
  refine Rch.tr (sweeps 2 3 0 _) ?_
  refine Rch.tr (endZero 11 2 blank) ?_
  -- round 3: block 26; one one left joins the run after it
  refine Rch.tr (bigSw 22 3 blank) ?_
  refine Rch.tr (sweeps 7 3 1 _) ?_
  rw [show 3 + 4 * 7 = 31 by rfl, sw_merge]
  refine Rch.tr (sweeps 1 32 0 _) ?_
  rw [show (blank : Strm) = false ::: ones 0 blank from cons_blank.symm]
  refine Rch.tr (endZero 36 0 _) ?_
  -- rounds 4–6: blocks 76, 202, 538
  refine Rch.tr (bigSw 72 1 _) ?_
  refine Rch.tr (sweeps 24 3 0 _) ?_
  refine Rch.tr (endZero 99 1 _) ?_
  refine Rch.tr (bigSw 198 2 _) ?_
  refine Rch.tr (sweeps 66 3 0 _) ?_
  refine Rch.tr (endZero 267 2 _) ?_
  refine Rch.tr (bigSw 534 3 _) ?_
  refine Rch.tr (sweeps 178 3 0 _) ?_
  refine Rch.tr (endZero 715 3 _) ?_
  -- round 7: block 1434, two ones left
  refine Rch.tr (bigSw 1430 4 _) ?_
  refine Rch.tr (sweeps 476 3 2 _) ?_
  refine Rch.tr (endTwo 1907 _) ?_
  exact Rch.of_eq (by simp [ones, cons_blank])


end

end TM.PA
