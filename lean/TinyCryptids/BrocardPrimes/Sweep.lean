import TinyCryptids.BrocardPrimes.Tac
namespace TM.BrocardPrimes
open St

abbrev F := false

/-- A block read rightwards: guard, `a` ones, the hole, `b` ones, guard.
Its region has `a + b + 1` cells and the hole is at region index `a`. -/
def blk (a b : Nat) (s : Strm) : Strm := true ::: ones a (F ::: ones b (true ::: s))

/-- The same block lying to the left of the head (read leftwards). -/
def blkR (a b : Nat) (L : Strm) : Strm := true ::: ones b (F ::: ones a (true ::: L))

/-! ## The sweep: one parser per mode (`false` = no divisor found yet). -/

def S1 : Bool → St | false => p1 | true => q1
def S2 : Bool → St | false => p2 | true => q2
def S3 : Bool → St | false => p3 | true => q3

/-- A hole not at region index 0 moves one cell left; the mode is unchanged. -/
theorem blk_move (c : Bool) (a b : Nat) (L R : Strm) :
    Rch ⟨S3 c, F ::: F ::: L, blk (a+1) b (F ::: F ::: R)⟩
      ⟨S3 c, F ::: F ::: blkR a (b+1) (F ::: F ::: L), R⟩ := by
  unfold blk blkR
  cases c <;> simp only [S3] <;>
  · gR; sRn (a+1); gR; rw [ones_cons_true b]; gL; gL; gL; rw [ones_cons_true a]; gR; gR
    simp only [← ones_succ]
    sRn (b+2); gR; gR
    simp only [ones_succ, ones_cons_true]; fin

/-- A hole at region index 0 wraps to the last index: the new value of `m`
is divisible by this block's prime, and the sweep continues in mode `true`. -/
theorem blk_wrap (c : Bool) (b : Nat) (L R : Strm) :
    Rch ⟨S3 c, F ::: F ::: L, blk 0 b (F ::: F ::: R)⟩
      ⟨S3 true, F ::: F ::: blkR b 0 (F ::: F ::: L), R⟩ := by
  unfold blk blkR
  cases c <;> simp only [S3, ones_zero] <;>
  · gR; gR; rw [ones_cons_true b]; gL; gL; gL; gR
    rw [show (true ::: true ::: true ::: ones b (F ::: F ::: R) : Strm) = ones (b+3) (F ::: F ::: R) by
      simp only [ones_succ, ones_cons_true]]
    sRn (b+3); gL; gL; gR; gR; gR; gR
    simp only [ones_succ, ones_cons_true, ones_zero]; fin

/-! ## The whole P zone -/

/-- blocks given as (hole index, cells right of the hole), each followed by `00` -/
def pz : List (Nat × Nat) → Strm → Strm
  | [], s => s
  | (a, b) :: l, s => blk a b (F ::: F ::: pz l s)

/-- processed blocks on the left of the head (the first block ends up deepest) -/
def pzR : List (Nat × Nat) → Strm → Strm
  | [], L => L
  | (a, b) :: l, L => pzR l (F ::: F ::: blkR a b L)

/-- one sweep step on a block: the hole moves left, or wraps -/
def stp : Nat × Nat → Nat × Nat
  | (0, b) => (b, 0)
  | (a + 1, b) => (a, b + 1)

/-- does some block wrap? -/
def wraps : List (Nat × Nat) → Bool
  | [] => false
  | (a, _) :: l => a == 0 || wraps l

theorem zone (l : List (Nat × Nat)) : ∀ (c : Bool) (L R : Strm),
    Rch ⟨S3 c, F ::: F ::: L, pz l R⟩ ⟨S3 (c || wraps l), pzR (l.map stp) (F ::: F ::: L), R⟩ := by
  induction l with
  | nil => intro c L R; simp only [pz, pzR, wraps, Bool.or_false, List.map]; fin
  | cons x l ih =>
    intro c L R
    obtain ⟨a, b⟩ := x
    cases a with
    | zero =>
      refine Rch.tr (blk_wrap c b L (pz l R)) ?_
      have := ih true (blkR b 0 (F ::: F ::: L)) R
      simp only [Bool.true_or, wraps, beq_self_eq_true, Bool.or_true] at this ⊢
      exact this
    | succ a =>
      refine Rch.tr (blk_move c a b L (pz l R)) ?_
      have := ih c (blkR a (b+1) (F ::: F ::: L)) R
      have e : (a + 1 == 0) = false := rfl
      simp only [wraps, e, Bool.false_or] at this ⊢
      exact this

end TM.BrocardPrimes
