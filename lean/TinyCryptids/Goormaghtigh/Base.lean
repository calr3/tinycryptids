import TinyCryptids.Goormaghtigh.Step

/-!
# The ends of a base and of a value

`Env k fl f` is what lies left of the base hole K: Vb's `k` cells left of K, the run of
`f + 1` zeros, and F (`fl` cells), read leftwards.
-/

namespace TM.Goormaghtigh
open St

local notation "F" => false

/-- left of K: `k` cells of Vb, `f + 1` zeros, F with `fl` cells -/
def Env (k fl f : Nat) : Strm := ones k (zeros (f + 1) (ones fl blank))

/-- the start of base `b` of value `V = k + 1 + b`: `r = 1`, `d = V - 1` -/
def CB (k b fl f : Nat) : Cfg St := XC 1 (k + b) (LK b (Env k fl f))

/-- the halting state -/
def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h'⟩ := h; ⟨L, R, Rch.tr hab h'⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c := by
  obtain ⟨L, R, h⟩ := h
  exact Reach.halts delta h (halt_none (q := St.halt) rfl)

/-! ## a hit: `r = V`; update `f` -/

theorem hit0 (V b k fl : Nat) :
    Rch (XC V 0 (LK b (Env (k + 1) (fl + 1) 0))) (KE (Env (k + 1) fl 1) b (V + 1)) := by
  unfold XC LK Env KE
  refine blankR ?_
  gL; gL; sLn V; gL; gL; sLn b; gL; sLn (k + 1); gL; gR; gR; gR; sRn k; gL
  simp only [ones_cons_true, ← ones_succ, ones_add, cons_blank]
  finc

theorem hit1 (V b k fl : Nat) :
    Rch (XC V 0 (LK b (Env (k + 1) (fl + 1) 1))) (KE (Env (k + 1) fl 2) b (V + 1)) := by
  unfold XC LK Env KE
  refine blankR ?_
  gL; gL; sLn V; gL; gL; sLn b; gL; sLn (k + 1); gL; gL; gR; gR; gR; gR; sRn k; gL
  simp only [ones_cons_true, ← ones_succ, ones_add, cons_blank]
  finc

theorem hit2 (V b k fl : Nat) :
    Rch (XC V 0 (LK b (Env (k + 1) fl 2))) (KE (Env (k + 1) fl 2) b (V + 1)) := by
  unfold XC LK Env KE
  refine blankR ?_
  gL; gL; sLn V; gL; gL; sLn b; gL; sLn (k + 1); gL; gL; gR; gR; gR; gR; sRn k; gL
  simp only [ones_cons_true, ← ones_succ, ones_add, cons_blank]
  finc

/-! ## the next base -/

/-- K moves one cell left (`b + 1`), the region is reset to `R = 1`, `H`, `D` -/
theorem kstep (k b fl f m : Nat) :
    Rch (KE (Env (k + 2) fl f) b (m + 2)) (XC 1 m (LK (b + 1) (Env (k + 1) fl f))) := by
  unfold KE Env XC LK
  gL; gR; gR; sRn (b + 1); gR; gR; gR; gR
  fin

/-! ## the next value -/

/-- the end of the next-value step, from inside F (`a` cells of F left of the head, `c` from
it): K on Vb's third cell from the right, the region grows, `R = 1`, `H` -/
theorem vend_tail (a c b : Nat) :
    Rch ⟨VR1, ones a blank, ones c (F ::: ones (b + 3) (F ::: F ::: ones (b + 3) blank))⟩
      (CB b 2 (a + c) 0) := by
  unfold CB XC LK Env
  sRn c; gR; sRn (b + 3); gL; gL; gL; gR; sRn 2; gR; gR; sRn (b + 3)
  refine blankR ?_
  gL; sLn (b + 3); gR; gR; gR
  simp only [ones_cons_true, ← ones_succ, ones_add, cons_blank]
  finc

/-- the next value after a value without hits: F moves one cell left -/
theorem vend0 (b fl : Nat) :
    Rch (KE (Env 1 (fl + 1) 0) b (b + 3)) (CB b 2 (fl + 1) 0) := by
  unfold KE Env
  gL; gL; gL; sLn fl; gR
  rw [tl_blank, Nat.add_comm fl 1]
  exact vend_tail 1 fl b

/-- after a value with one hit: F gets its cell back and moves one cell left -/
theorem vend1 (b fl : Nat) :
    Rch (KE (Env 1 (fl + 1) 1) b (b + 3)) (CB b 2 (fl + 2) 0) := by
  unfold KE Env
  gL; gL; gL; gL; sLn fl; gR
  rw [tl_blank, show fl + 2 = 1 + (fl + 1) by omega, ← ones_succ']
  exact vend_tail 1 (fl + 1) b

/-- after a bad value: F gets one of its two cells back and moves one cell left -/
theorem vend2 (b fl : Nat) :
    Rch (KE (Env 1 (fl + 1) 2) b (b + 3)) (CB b 2 (fl + 2) 0) := by
  unfold KE Env
  gL; gL; gL; gL; gR
  exact vend_tail (fl + 1) 1 b

/-- after a bad value when F is empty: halt -/
theorem vend_halt (b : Nat) : HaltAt (KE (Env 1 0 2) b (b + 3)) := by
  unfold KE Env HaltAt
  apply Exists.intro; apply Exists.intro
  gL; gL; gL; gL; gR
  fin

/-! ## the seed -/

theorem sLb {q q' : St} {R : Strm} {w : Bool} (h : delta q false = some (w, Dir.L, q')) :
    Rch (cfgL q blank R) (cfgL q' blank (w ::: R)) := by
  have := sL (s := blank) (R := R) h
  rwa [cons_blank] at this

/-- the seed writes the tape of `V = 3` (F with 4 cells) and finishes its next-value step:
the start of base 2 of `V = 4` -/
theorem seed_reach : Rch start (CB 1 2 4 0) := by
  have e : start = cfgL seed0 blank blank := by
    show (⟨seed0, blank, blank⟩ : Cfg St) = ⟨seed0, blank, false ::: blank⟩; rw [cons_blank]
  rw [e]
  repeat (refine Rch.tr (sLb (by rfl)) ?_)
  refine Rch.tr (sR (L := blank) (by rfl)) ?_
  exact vend_tail 1 3 1

end TM.Goormaghtigh
