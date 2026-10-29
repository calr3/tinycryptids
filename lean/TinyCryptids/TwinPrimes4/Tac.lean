import TinyCryptids.Core.BeepK
import TinyCryptids.TwinPrimes4.Machine

/-!
# Blocks, one-step tactics and scans for the 4-symbol twin prime machine

Every routine is proved for `deltaNB`, the machine without its beep transition: a run of
`deltaNB` is a run of `delta` (`deltaNB_sub`, `Core/BeepK.lean`). Only the beep step itself
uses `delta`.

* `rp a n s`: `n` cells holding `a`, then `s`.
* `cfgL q s R`: the head on `s 0`, the cells left of it `tl s` (read leftwards), right of it `R`.
-/

namespace TMK.TwinPrimes4

open TM (Dir)

/-- `n` cells holding `a`, then `s` -/
def rp (a : Nat) : Nat → Strm → Strm
  | 0, s => s
  | n + 1, s => a ∷ rp a n s

@[simp] theorem rp_zero (a : Nat) (s : Strm) : rp a 0 s = s := rfl
theorem rp_succ (a n : Nat) (s : Strm) : rp a (n + 1) s = a ∷ rp a n s := rfl

theorem rp_add (a m n : Nat) (s : Strm) : rp a m (rp a n s) = rp a (m + n) s := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.add_right_comm, rp_succ, rp_succ, ih]

theorem rp_succ' (a n : Nat) (s : Strm) : rp a (n + 1) s = rp a n (a ∷ s) :=
  (rp_add a n 1 s).symm

theorem rp_get_lt (a n i : Nat) (s : Strm) (h : i < n) : rp a n s i = a := by
  induction n generalizing i with
  | zero => omega
  | succ n ih => cases i with
    | zero => rfl
    | succ i => exact ih i (by omega)

theorem rp_get_self (a n : Nat) (s : Strm) : rp a n s n = s 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- the head on `s 0`, the cells left of it `tl s`, the cells right of it `R` -/
def cfgL (q : St) (s R : Strm) : Cfg St := ⟨q, tl s, s 0 ∷ R⟩

abbrev Rch := Reach deltaNB
abbrev Rch1 := Reach1 deltaNB

theorem deltaNB_sub : ∀ q b t, deltaNB q b = some t → delta q b = some t := by
  intro q b t h; unfold deltaNB at h; split at h
  · exact absurd h (by simp)
  · exact h

theorem deltaNB_beep : deltaNB St.beep 0 = none := rfl

theorem sR {q q' : St} {L R : Strm} {b w : Nat} (h : deltaNB q b = some (w, Dir.R, q')) :
    Rch ⟨q, L, b ∷ R⟩ ⟨q', w ∷ L, R⟩ := stepR (δ := deltaNB) (R := b ∷ R) h

theorem sL {q q' : St} {s R : Strm} {b w : Nat} (h : deltaNB q b = some (w, Dir.L, q')) :
    Rch (cfgL q (b ∷ s) R) (cfgL q' s (w ∷ R)) := stepL (δ := deltaNB) (R := b ∷ R) h

theorem Rch.tr {a b c : Cfg St} (h1 : Rch a b) (h2 : Rch b c) : Rch a c :=
  Reach.trans deltaNB h1 h2

/-- one step right / left, continuing with the remaining goal -/
macro "gR" : tactic => `(tactic| refine Rch.tr (sR (by rfl)) ?_)
macro "gL" : tactic => `(tactic| refine Rch.tr (sL (by rfl)) ?_)
macro "fin" : tactic => `(tactic| exact Reach.refl deltaNB _)

theorem scanR {q : St} {a : Nat} (h : deltaNB q a = some (a, Dir.R, q)) :
    ∀ (n : Nat) (L R : Strm), Rch ⟨q, L, rp a n R⟩ ⟨q, rp a n L, R⟩ := by
  intro n
  induction n with
  | zero => intro L R; exact Reach.refl deltaNB _
  | succ n ih => intro L R; rw [rp_succ' a n L]; exact Rch.tr (sR h) (ih _ _)

theorem scanL {q : St} {a : Nat} (h : deltaNB q a = some (a, Dir.L, q)) :
    ∀ (n : Nat) (s R : Strm), Rch (cfgL q (rp a n s) R) (cfgL q s (rp a n R)) := by
  intro n
  induction n with
  | zero => intro s R; exact Reach.refl deltaNB _
  | succ n ih => intro s R; rw [rp_succ' a n R]; exact Rch.tr (sL h) (ih _ _)

/-- scan right / left over `n` cells holding `a` -/
macro "sRn" a:term:max n:term:max : tactic =>
  `(tactic| refine Rch.tr (scanR (a := $a) (by rfl) $n _ _) ?_)
macro "sLn" a:term:max n:term:max : tactic =>
  `(tactic| refine Rch.tr (scanL (a := $a) (by rfl) $n _ _) ?_)

/-! ## steps on a blank cell (`blank` is `0 ∷ blank`) -/

/-- right, on the blank right of the tape -/
theorem sRb {q q' : St} {L : Strm} {w : Nat} (h : deltaNB q 0 = some (w, Dir.R, q')) :
    Rch ⟨q, L, blank⟩ ⟨q', w ∷ L, blank⟩ := by
  have := sR (L := L) (R := blank) h; rwa [cons_blank] at this

/-- left, on the blank right of the tape -/
theorem sLr {q q' : St} {L : Strm} {w : Nat} (h : deltaNB q 0 = some (w, Dir.L, q')) :
    Rch ⟨q, L, blank⟩ (cfgL q' L (w ∷ blank)) := by
  have := sL (s := L) (R := blank) h
  rwa [show cfgL q (0 ∷ L) blank = ⟨q, L, blank⟩ by
    unfold cfgL; rw [cons_zero, cons_blank]; rfl] at this

/-- right, on the blank left of the tape -/
theorem sRc {q q' : St} {R : Strm} {w : Nat} (h : deltaNB q 0 = some (w, Dir.R, q')) :
    Rch (cfgL q blank R) ⟨q', w ∷ blank, R⟩ := sR (L := blank) (R := R) h

end TMK.TwinPrimes4
