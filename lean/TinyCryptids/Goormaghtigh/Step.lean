import TinyCryptids.Goormaghtigh.Tac

/-!
# One step `r := r * b + 1` of a walk

Tape (left to right): `E` (everything left of the base hole K), K, Vb's `b` cells right of K
(during a step: `b1` cells, the pass cursor P, `b2` cells), the separator `00`, the region:
`R` (`r` cells, during a pass the copy cursor C on one of them), the marker M, the copies
`Q`, the hole H, `D` (`d` cells), then blank.

Configurations are written with the cells left of the head as a stream read leftwards.
-/

namespace TM.Goormaghtigh
open St

local notation "F" => false

/-- left of the region with no pass cursor: the separator, Vb's `b` cells right of K, K, `E` -/
def LK (b : Nat) (E : Strm) : Strm := F ::: F ::: ones b (F ::: E)

/-- left of the region during a step: P has `b1` cells between it and K, `b2` right of it -/
def LP (b1 b2 : Nat) (E : Strm) : Strm := F ::: F ::: ones b2 (F ::: ones b1 (F ::: E))

/-- between steps: `X` on D's first cell (or the blank after the region if `d = 0`) -/
def XC (r d : Nat) (A : Strm) : Cfg St := ⟨X, F ::: ones r A, ones d blank⟩

/-- a tick: C on R's cell `c`, `u` cells of R right of it, head on the cell after C -/
def TJc (c u q d : Nat) (A : Strm) : Cfg St :=
  ⟨TJ, F ::: ones c A, ones u (F ::: ones q (F ::: ones d blank))⟩

/-- the end of a base: the head on the cell left of K (filled), Vb's `b + 1` cells from K,
the separator, the region (`n` cells, all 1) -/
def KE (E : Strm) (b n : Nat) : Cfg St := cfgL K2 E (ones (b + 1) (F ::: F ::: ones n blank))

/-! ## ticks and passes -/

theorem tick (c u q d : Nat) (A : Strm) :
    Rch (TJc c (u + 1) q (d + 1) A) (TJc (c + 1) u (q + 1) d A) := by
  unfold TJc
  sRn (u + 1); gR; sRn q; gR; gL
  sLn (q + 1); gL; sLn (u + 1); gR; gR
  rw [ones_succ]; fin

theorem tick_last (c q d : Nat) (A : Strm) :
    Rch (TJc c 0 q (d + 1) A) (cfgL PQ (ones (c + 1) A) (F ::: ones (q + 1) (F ::: ones d blank))) := by
  unfold TJc
  gR; sRn q; gR; gL
  sLn (q + 1); gL; gR; gL
  rw [ones_succ]; fin

/-- a whole pass: C walks the rest of R, H moves `u + 1` cells -/
theorem pass (A : Strm) : ∀ u c q d, u + 1 ≤ d →
    Rch (TJc c u q d A)
      (cfgL PQ (ones (c + u + 1) A) (F ::: ones (q + u + 1) (F ::: ones (d - (u + 1)) blank))) := by
  intro u
  induction u with
  | zero =>
    intro c q d h
    obtain ⟨d, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [show d + 1 - (0 + 1) = d by omega]
    exact tick_last c q d A
  | succ u ih =>
    intro c q d h
    obtain ⟨d, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    refine Rch.tr (tick c u q d A) ?_
    have := ih (c + 1) (q + 1) d (by omega)
    rw [show c + 1 + u + 1 = c + (u + 1) + 1 by omega, show q + 1 + u + 1 = q + (u + 1) + 1 by omega,
      show d - (u + 1) = d + 1 - (u + 1 + 1) by omega] at this
    exact this

/-- an overflow: H is on the region's last cell when a tick needs it to move; fill M, C, P
and K and stop left of K -/
theorem tick_ovf (c u q b1 b2 : Nat) (E : Strm) :
    Rch (TJc c u q 0 (LP b1 b2 E)) (KE E (b1 + b2 + 1) (c + u + q + 3)) := by
  unfold TJc LP KE
  sRn u; gR; sRn q; gR
  refine blankR ?_
  gL
  sLn (q + 1); gL; sLn u; gL; sLn c; gL; gL; sLn b2; gL; sLn b1; gL
  simp only [ones_cons_true, ← ones_succ, ones_add, cons_blank]
  finc

/-- an overflow during a pass -/
theorem pass_ovf (b1 b2 : Nat) (E : Strm) : ∀ u c q d, d < u + 1 →
    Rch (TJc c u q d (LP b1 b2 E)) (KE E (b1 + b2 + 1) (c + u + q + d + 3)) := by
  intro u
  induction u with
  | zero =>
    intro c q d h
    obtain rfl : d = 0 := by omega
    exact tick_ovf c 0 q b1 b2 E
  | succ u ih =>
    intro c q d h
    rcases d with _ | d
    · exact tick_ovf c (u + 1) q b1 b2 E
    · refine Rch.tr (tick c u q d _) ?_
      have := ih (c + 1) (q + 1) d (by omega)
      rw [show c + 1 + u + (q + 1) + d + 3 = c + (u + 1) + q + (d + 1) + 3 by omega] at this
      exact this

/-! ## pass ends and the step start -/

/-- after a pass: back to P, move it one cell right, punch C on R's first cell -/
theorem pass_next (r b1 b2 q d : Nat) (E : Strm) :
    Rch (cfgL PQ (ones (r + 1) (LP b1 (b2 + 1) E)) (F ::: ones q (F ::: ones d blank)))
      (TJc 0 r q d (LP (b1 + 1) b2 E)) := by
  unfold LP TJc
  sLn (r + 1); gL; gL; sLn (b2 + 1); gR; gR; sRn b2; gR; gR; gR
  fin

/-- after the last pass (P on Vb's last cell): fill P, merge (fill M), to the cell after H -/
theorem pass_last (r b1 q d : Nat) (E : Strm) :
    Rch (cfgL PQ (ones r (LP b1 0 E)) (F ::: ones q (F ::: ones d blank)))
      (XC (r + 1 + q) d (LK (b1 + 1) E)) := by
  unfold LP LK XC
  sLn r; gL; gL; gR; gR; gR; sRn r; gR; sRn q; gR
  simp only [ones_cons_true, ← ones_succ, ones_add]
  finc

/-- the step start: H becomes M, a new H on D's first cell, P on K + 2, C on R's first cell -/
theorem step_start (r b d : Nat) (E : Strm) :
    Rch (XC (r + 1) (d + 1) (LK (b + 2) E)) (TJc 0 r 0 d (LP 1 b E)) := by
  unfold XC LK TJc LP
  gL; gL; sLn (r + 1); gL; gL; sLn (b + 2); gR; gR; gR; sRn b; gR; gR; gR
  fin

/-- the passes from the one with `b2` cells right of P -/
theorem passes (r : Nat) (E : Strm) : ∀ b2 b1 q d, (r + 1) * (b2 + 1) ≤ d →
    Rch (TJc 0 r q d (LP b1 b2 E))
      (XC (r + 1 + 1 + q + (r + 1) * (b2 + 1)) (d - (r + 1) * (b2 + 1)) (LK (b1 + b2 + 1) E)) := by
  intro b2
  induction b2 with
  | zero =>
    intro b1 q d h
    rw [Nat.mul_one] at h ⊢
    refine Rch.tr (pass _ r 0 q d (by omega)) ?_
    have := pass_last (0 + r + 1) b1 (q + r + 1) (d - (r + 1)) E
    rw [show 0 + r + 1 + 1 + (q + r + 1) = r + 1 + 1 + q + (r + 1) by omega] at this
    exact this
  | succ b2 ih =>
    intro b1 q d h
    rw [Nat.mul_succ] at h ⊢
    refine Rch.tr (pass _ r 0 q d (by omega)) ?_
    rw [show 0 + r + 1 = r + 1 by omega]
    refine Rch.tr (pass_next r b1 b2 (q + r + 1) (d - (r + 1)) E) ?_
    have := ih (b1 + 1) (q + r + 1) (d - (r + 1)) (by omega)
    rw [show r + 1 + 1 + (q + r + 1) + (r + 1) * (b2 + 1) = r + 1 + 1 + q + ((r + 1) * (b2 + 1) + (r + 1)) by omega,
      show d - (r + 1) - (r + 1) * (b2 + 1) = d - ((r + 1) * (b2 + 1) + (r + 1)) by omega,
      show b1 + 1 + b2 + 1 = b1 + (b2 + 1) + 1 by omega] at this
    exact this

/-- an overflow in one of the passes -/
theorem passes_ovf (r : Nat) (E : Strm) : ∀ b2 b1 q d, d < (r + 1) * (b2 + 1) →
    Rch (TJc 0 r q d (LP b1 b2 E)) (KE E (b1 + b2 + 1) (r + q + d + 3)) := by
  intro b2
  induction b2 with
  | zero =>
    intro b1 q d h
    rw [Nat.mul_one] at h
    have := pass_ovf b1 0 E r 0 q d (by omega)
    rw [show 0 + r + q + d + 3 = r + q + d + 3 by omega] at this
    exact this
  | succ b2 ih =>
    intro b1 q d h
    rw [Nat.mul_succ] at h
    by_cases hd : d < r + 1
    · have := pass_ovf b1 (b2 + 1) E r 0 q d hd
      rw [show 0 + r + q + d + 3 = r + q + d + 3 by omega] at this
      exact this
    · refine Rch.tr (pass _ r 0 q d (by omega)) ?_
      rw [show 0 + r + 1 = r + 1 by omega]
      refine Rch.tr (pass_next r b1 b2 (q + r + 1) (d - (r + 1)) E) ?_
      have := ih (b1 + 1) (q + r + 1) (d - (r + 1)) (by omega)
      rw [show r + (q + r + 1) + (d - (r + 1)) + 3 = r + q + d + 3 by omega,
        show b1 + 1 + b2 + 1 = b1 + (b2 + 1) + 1 by omega] at this
      exact this

/-! ## a whole step -/

/-- `r ↦ r * b + 1` (with `r = r' + 1`, `b = b' + 2`), when it is at most `V` -/
theorem step_ok (r b d : Nat) (E : Strm) (h : (r + 1) * (b + 1) ≤ d) :
    Rch (XC (r + 1) (d + 1) (LK (b + 2) E))
      (XC ((r + 1) * (b + 2) + 1) (d - (r + 1) * (b + 1)) (LK (b + 2) E)) := by
  refine Rch.tr (step_start r b d E) ?_
  have := passes r E b 1 0 d h
  have hm : (r + 1) * (b + 2) = (r + 1) * (b + 1) + (r + 1) := Nat.mul_succ _ _
  rw [show r + 1 + 1 + 0 + (r + 1) * (b + 1) = (r + 1) * (b + 2) + 1 by omega,
    show 1 + b + 1 = b + 2 by omega] at this
  exact this

/-- an overflow: `r * b + 1 > V` -/
theorem step_ovf (r b d : Nat) (E : Strm) (h : d < (r + 1) * (b + 1)) :
    Rch (XC (r + 1) (d + 1) (LK (b + 2) E)) (KE E (b + 2) (r + d + 3)) := by
  refine Rch.tr (step_start r b d E) ?_
  have := passes_ovf r E b 1 0 d h
  rw [show r + 0 + d + 3 = r + d + 3 by omega, show 1 + b + 1 = b + 2 by omega] at this
  exact this

end TM.Goormaghtigh
