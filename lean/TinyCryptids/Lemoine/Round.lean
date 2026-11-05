import TinyCryptids.Lemoine.Test

/-!
# The routes between two checkpoints

Tape (left to right):

    1 0 [Dp 00 Rp] 0^G [Dq 00 Rq] 0 1

* `PL d r` : the P pair seen from its right end (R's last cell first), then the left sentinel;
* `QS d r` : the Q pair from its cell 0, then the right sentinel;
* `K q dp rp dq rq` : the checkpoint (state `PQ1`, head on the last cell but one of Rq), the gap
  `2q - 2`; for `(n, q)` it holds `dp + rp = n - 2q + 2` (two cells of Rp are still to go) and
  `dq + rq = q`.
-/

namespace TM.Lemoine

open St

local notation "F" => false

def LS : Strm := true ::: blank

/-- the P pair seen from R's last cell, then `0 1` (the left sentinel) -/
def PL (d r : Nat) : Strm := ones (r + 2) (F ::: F ::: ones d (F ::: true ::: F ::: LS))

/-- the Q pair from its cell 0, then `0 1` (the right sentinel) -/
def QS (d r : Nat) : Strm := true ::: F ::: ones d (F ::: F ::: ones (r + 2) (F ::: LS))

/-- the checkpoint -/
def K (q dp rp dq rq : Nat) : Cfg St :=
  cfgL PQ1 (ones (rq + 1) (F ::: F ::: ones dq (F ::: true ::: zeros (2 * q - 2) (PL dp rp))))
    (true ::: F ::: LS)

/-- right of the P pair during its test (after the first gap cell) -/
def RyP (q dq rq : Nat) : Strm := zeros (2 * q - 1) (QS dq rq)

/-- left of the Q pair during its test (after its cell -1) -/
def LxQ (q dp rp : Nat) : Strm := zeros (2 * q - 1) (PL dp rp)

/-! ## generic pieces -/

theorem ParserR.zeros2 {p1 p2 : St} (P : ParserR delta p1 p2) (k : Nat) (L R : Strm) :
    Rch ⟨p1, L, zeros (2 * k) R⟩ ⟨p1, zeros (2 * k) L, R⟩ := by
  induction k generalizing L with
  | zero => fin
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    show Rch ⟨p1, L, F ::: F ::: zeros (2 * k) R⟩ _
    refine Rch.tr (sR P.h0) (Rch.tr (sR P.h2) ?_)
    have := ih (F ::: F ::: L)
    rw [show zeros (2 * k) (F ::: F ::: L) = zeros (2 * k + 2) L by
      rw [zeros_succ', zeros_succ']] at this
    exact this

theorem fillL {q : St} (h : delta q false = some (true, Dir.L, q)) (n : Nat) (s R : Strm) :
    Rch (cfgL q (zeros n s) R) (cfgL q s (ones n R)) := by
  induction n generalizing R with
  | zero => fin
  | succ n ih =>
    refine Rch.tr (sL (s := zeros n s) h) ?_
    have := ih (true ::: R); rw [← ones_succ'] at this; exact this

theorem zeros_two (k : Nat) (X : Strm) : F ::: F ::: zeros k X = zeros (k + 2) X := by
  rw [zeros_succ', zeros_succ', zeros_cons_false, zeros_cons_false]

/-! ## from the checkpoint to the test of p -/

/-- P's two last R cells erased, then normalized; `n - 2q = dp + rp - 2` -/
theorem chk_norm (q dp rp dq rq : Nat) (hq : 2 ≤ q) (hdq : 1 ≤ dq) :
    Rch (K q dp rp dq rq) (NZ LS (F ::: RyP q dq rq) dp rp) := by
  obtain ⟨e, rfl⟩ : ∃ e, dq = e + 1 := ⟨dq - 1, by omega⟩
  unfold K NZ RyP
  refine Rch.tr (PPQ.find2 (rq + 1) e _ _) ?_
  gL; zLn (2 * q - 2)
  unfold PL; gL; gL
  rw [show 2 * q - 1 = (2 * q - 2) + 1 by omega, zeros_succ']
  unfold QS
  rw [zeros_cons_false, ones_succ' (rq + 1)]; fin

/-! ## q += 1 -/

/-- from Dq's cell 3 (after the parser found the Q hole): on to the single 0 before the right
sentinel; the sentinel moves one cell right and Rq gets a cell; back to the checkpoint -/
theorem nq_tail (Z : Strm) (f rq : Nat) :
    Rch ⟨w, true ::: F ::: true ::: Z, ones (f + 1) (F ::: F ::: ones (rq + 2) (F ::: LS))⟩
      (cfgL PQ1 (ones (rq + 2) (F ::: F ::: ones (f + 2) (F ::: true ::: Z))) (true ::: F ::: LS)) := by
  gR
  refine Rch.tr (PPN.find2 f (rq + 1) _ blank) ?_
  gR; refine blankR ?_; gL; gL; gL
  rw [show ones (rq + 1 + 1) (F ::: F ::: ones f (true ::: true ::: F ::: true ::: Z)) =
    ones (rq + 2) (F ::: F ::: ones (f + 2) (F ::: true ::: Z)) by
      rw [show ones f (true ::: true ::: F ::: true ::: Z) = ones (f + 2) (F ::: true ::: Z) by
        rw [show (true ::: true ::: F ::: true ::: Z) = ones 2 (F ::: true ::: Z) from rfl, ones_add]]]
  unfold LS; fin

/-- p composite (`k1b` on the left sentinel): to the Q hole, then `q += 1` -/
theorem p_comp (q d r dq rq : Nat) (hq : 1 ≤ q) (hdq : 2 ≤ dq) :
    Rch (CK LS (RyP q dq rq) d r) (K (q + 1) d r dq (rq + 1)) := by
  obtain ⟨f, rfl⟩ : ∃ f, dq = f + 2 := ⟨dq - 2, by omega⟩
  unfold CK RyP K
  show Rch ⟨k1b, blank, true ::: _⟩ _
  gR; gR; gR; gR
  rw [← app_blk]
  refine Rch.tr (PPN.cross (clean_blk d (r + 1)) _ _) ?_
  rw [app_blk_rev, show F ::: zeros (2 * q - 1) (QS (f + 2) rq) = zeros (2 * q) (QS (f + 2) rq) by
    rw [← zeros_cons_false, ← zeros_succ', show 2 * q - 1 + 1 = 2 * q by omega]]
  refine Rch.tr (ParserR.zeros2 PPN q _ _) ?_
  unfold QS
  show Rch ⟨PN1, _, ones 1 (F ::: true ::: ones (f + 1) _)⟩ _
  refine Rch.tr (PPN.find0 1 _ _) ?_
  gR
  have := nq_tail (zeros (2 * q) (ones (r + 2) (F ::: F ::: ones d (F ::: true ::: F ::: LS)))) f rq
  rw [show 2 * (q + 1) - 2 = 2 * q by omega]
  unfold PL
  exact this

/-- q composite (`k1b` in the gap): to the Q hole, then `q += 1` -/
theorem q_comp (q p d r : Nat) (hq : 1 ≤ q) (hd : 2 ≤ d) :
    Rch (CK (LxQ q p 0) LS d r) (K (q + 1) p 0 d (r + 1)) := by
  obtain ⟨f, rfl⟩ : ∃ f, d = f + 2 := ⟨d - 2, by omega⟩
  unfold CK LxQ K
  rw [show 2 * q - 1 = (2 * q - 2) + 1 by omega]
  show Rch ⟨k1b, zeros (2 * q - 2) (PL p 0), F ::: _⟩ _
  gR; gR
  show Rch ⟨PN1, _, ones 1 (F ::: true ::: ones (f + 1) _)⟩ _
  refine Rch.tr (PPN.find0 1 _ _) ?_
  gR
  have := nq_tail (zeros (2 * q) (PL p 0)) f r
  rw [show 2 * (q + 1) - 2 = 2 * q by omega]
  rw [show F ::: F ::: zeros (2 * q - 2) (PL p 0) = zeros (2 * q) (PL p 0) by
    rw [zeros_two, show 2 * q - 2 + 2 = 2 * q by omega]] at *
  exact this

/-! ## p prime: normalize Q -/

theorem p_prime (q p dq rq : Nat) (hq : 1 ≤ q) (hdq : 2 ≤ dq) :
    Rch (CP LS (RyP q dq rq) p) (NZ (LxQ q p 0) (F ::: LS) dq (rq + 2)) := by
  obtain ⟨f, rfl⟩ : ∃ f, dq = f + 2 := ⟨dq - 2, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  unfold CP RyP NZ LxQ
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  show Rch ⟨pd, _, F ::: zeros (2 * k) _⟩ _
  gR
  refine Rch.tr (ParserR.zeros2 PPS k _ _) ?_
  unfold QS
  show Rch ⟨PS1, _, ones 1 (F ::: true ::: ones (f + 1) _)⟩ _
  refine Rch.tr (PPS.find0 1 _ _) ?_
  gR; gR
  refine Rch.tr (PPS.find2 f (rq + 1) _ blank) ?_
  gR; refine blankR ?_; gL; gL; gL
  rw [show ones f (true ::: true ::: F ::: ones 1 (zeros (2 * k) (F ::: F ::: ones 2
      (F ::: F ::: ones p (F ::: true ::: F ::: LS))))) =
    ones (f + 2) (F ::: true ::: F ::: zeros (2 * k + 1) (PL p 0)) by
      rw [show (true ::: true ::: F ::: ones 1 (zeros (2 * k) (F ::: F ::: ones 2
        (F ::: F ::: ones p (F ::: true ::: F ::: LS))))) =
        ones 2 (F ::: true ::: F ::: zeros (2 * k + 1) (PL p 0)) by
          unfold PL; rw [← zeros_succ', ← zeros_succ']; rfl, ones_add]]
  unfold LS; rw [cons_blank]; fin

/-! ## q prime: the next n -/

macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))
macro "gLb" : tactic => `(tactic| first | gL | (refine blankR ?_; gL))

/-- the seed's tail (also the end of the next-n route): the second gap cell, Q with `q = 1`,
the right sentinel, then `q += 1` -/
theorem seed_tail (Z : Strm) :
    Rch ⟨seed14, Z, blank⟩
      (cfgL PQ1 (ones 1 (F ::: F ::: ones 2 (F ::: true ::: F ::: Z))) (true ::: F ::: LS)) := by
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  refine blankR ?_; gL; gL; gL
  unfold LS; fin

/-- q prime: erase Q, fill the gap into Rp, write a new gap, Q (`q = 2`) and the sentinel -/
theorem q_prime (q p : Nat) (hq : 1 ≤ q) :
    Rch (CP (LxQ q p 0) LS q) (K 2 p (2 * q) 2 0) := by
  unfold CP LxQ K LS
  gL; gL; eLn 2; gL; gL; eLn q; gL; gL
  rw [show F ::: zeros (2 * q - 1) (PL p 0) = zeros (2 * q) (PL p 0) by
    rw [← zeros_cons_false, ← zeros_succ', show 2 * q - 1 + 1 = 2 * q by omega]]
  refine Rch.tr (fillL rfl (2 * q) _ _) ?_
  unfold PL
  gR; sRn (2 * q); gR
  simp only [cons_blank, zeros_blank]
  refine Rch.tr (seed_tail _) ?_
  rw [show ones (2 * q + 2) (F ::: F ::: ones p (F ::: true ::: F ::: LS)) =
    ones (2 * q) (true ::: true ::: F ::: F ::: ones p (F ::: true ::: F ::: LS)) from
      (ones_add _ _ _).symm]
  fin

end TM.Lemoine
