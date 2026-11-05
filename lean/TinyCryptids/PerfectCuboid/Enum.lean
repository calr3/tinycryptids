import TinyCryptids.PerfectCuboid.Queue

/-!
# The next tuple (NEXCOM on the tape) and the bootstrap

From `ea0` on A's first cell the queue becomes `qL (nxt t)` and the head goes home to A: the
next tuple starts (`nexcom`). The seed writes S's `101`; the abort routine writes G and, as the
scan finds no queue, `ea0` reads a blank: the chain `zc` writes Z and `(4, 4, 4)` (`boot`).
-/

namespace TM.PerfectCuboid

open St

local notation "F" => false
local notation "T" => true

theorem qL_app (x y z : Nat) (R : Strm) : app (qL (x, y, z)) R =
    ones x (F ::: F ::: ones y (F ::: F ::: ones z (F ::: F ::: T ::: T ::: T ::: R))) := by
  simp [qL, rep, app_append, app_replicate]

theorem home_rep (n : Nat) (R : Strm) : Rch (cfgL wa (ones n blank) R) ⟨n5, blank, ones n R⟩ := by
  have := home (rep n) (by simpa using clean_rep n [] Clean.nil) R
  simpa [rep, app_replicate, List.reverse_replicate] using this

/-- NEXCOM, `x > 4`: `(x - 1, y + 1, z)` -/
theorem nex1 (x y z : Nat) (hx : 5 ≤ x) (R : Strm) :
    Rch ⟨ea0, blank, app (qL (x, y, z)) R⟩ ⟨n5, blank, app (qL (x - 1, y + 1, z)) R⟩ := by
  rw [qL_app, qL_app]
  obtain ⟨n, rfl⟩ : ∃ n, x = 5 + n := ⟨x - 5, by omega⟩
  rw [← ones_add]
  show Rch ⟨ea0, blank, T ::: T ::: T ::: T ::: T ::: ones n _⟩ _
  gR; gR; gR; gR; gR
  sr n
  rw [ones_cons_true n]
  gl; gR; gR; gl
  have := home ([F, F] ++ rep (n + 4)) (by simpa using clean_sep (n + 3) [] Clean.nil)
    (T ::: ones y (F ::: F ::: ones z (F ::: F ::: T ::: T ::: T ::: R)))
  simp only [rep, List.cons_append, List.nil_append, app_cons, app_replicate, List.reverse_cons,
    List.reverse_replicate, List.append_assoc, List.singleton_append, app_append] at this
  refine Rch.tr (rch_eq ?_ rfl) (Rch.tr this ?_)
  · streq
  · apply rch_eq rfl; streq

/-- NEXCOM, `x = 4 < y`: `(y - 1, 4, z + 1)` -/
theorem nex2 (y z : Nat) (hy : 5 ≤ y) (R : Strm) :
    Rch ⟨ea0, blank, app (qL (4, y, z)) R⟩ ⟨n5, blank, app (qL (y - 1, 4, z + 1)) R⟩ := by
  rw [qL_app, qL_app]
  obtain ⟨n, rfl⟩ : ∃ n, y = 5 + n := ⟨y - 5, by omega⟩
  rw [← ones_add]
  show Rch ⟨ea0, blank, T ::: T ::: T ::: T ::: F ::: F ::: T ::: T ::: T ::: T ::: T ::: ones n _⟩ _
  gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR
  sr n
  rw [ones_cons_true n]
  gl; gR; gR; gl; gl
  rw [ones_cons_true n]
  gl
  rw [ones_cons_true n, ones_cons_true n, ones_cons_true n]
  rw [cons_ones, cons_ones, cons_ones]
  sl (n + 3)
  gl; gl; gR
  norm
  rw [show n + (3 + (1 + 1)) = n + 5 by omega]
  sr (n + 5)
  show Rch ⟨cb9, ones (n + 5) (ones 5 blank), F ::: _⟩ _
  rw [ones_add, show n + 5 + 5 = n + 9 + 1 by omega, ones_succ]
  gl
  rw [show n + 9 = n + 8 + 1 by omega, ones_succ]; gl
  rw [show n + 8 = n + 7 + 1 by omega, ones_succ]; gl
  rw [show n + 7 = n + 6 + 1 by omega, ones_succ]; gl
  rw [show n + 6 = n + 5 + 1 by omega, ones_succ]; gl
  rw [show n + 5 = n + 4 + 1 by omega, ones_succ]; gl
  rw [show n + 4 = n + 3 + 1 by omega, ones_succ]; gl
  show Rch (cfgL wa (ones (n + 4) blank) _) _
  refine Rch.tr (home_rep (n + 4) _) ?_
  apply rch_eq rfl; streq

/-- NEXCOM, `x = y = 4`: `(z + 1, 4, 4)` -/
theorem nex3 (z : Nat) (R : Strm) :
    Rch ⟨ea0, blank, app (qL (4, 4, z)) R⟩ ⟨n5, blank, app (qL (z + 1, 4, 4)) R⟩ := by
  rw [qL_app, qL_app]
  show Rch ⟨ea0, blank, T ::: T ::: T ::: T ::: F ::: F ::: T ::: T ::: T ::: T ::: F ::: F ::: _⟩ _
  gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gl
  show Rch ⟨cc2, ones 4 (F ::: F ::: ones 4 blank), T ::: _⟩ _
  sl 4
  gl; gl; gl
  show Rch ⟨cc4, ones 3 blank, T ::: _⟩ _
  sl 3
  rw [← cons_blank]
  gl; gR
  norm
  rw [show 3 + (4 + (z + (1 + (1 + (1 + (1 + 1)))))) = z + 12 by omega]
  sr (z + 12)
  show Rch ⟨cc5, ones (z + 12) (ones 1 blank), F ::: _⟩ _
  rw [ones_add, show z + 12 + 1 = z + 12 + 1 from rfl, ones_succ]
  gl
  rw [show z + 12 = z + 11 + 1 by omega, ones_succ]; gl
  rw [show z + 11 = z + 10 + 1 by omega, ones_succ]; gl
  rw [show z + 10 = z + 9 + 1 by omega, ones_succ]; gl
  rw [show z + 9 = z + 8 + 1 by omega, ones_succ]; gl
  rw [show z + 8 = z + 7 + 1 by omega, ones_succ]; gl
  rw [show z + 7 = z + 6 + 1 by omega, ones_succ]; gl
  rw [show z + 6 = z + 5 + 1 by omega, ones_succ]; gl
  rw [show z + 5 = z + 4 + 1 by omega, ones_succ]; gl
  rw [show z + 4 = z + 3 + 1 by omega, ones_succ]; gl
  rw [show z + 3 = z + 2 + 1 by omega, ones_succ]; gl
  rw [show z + 2 = z + 1 + 1 by omega, ones_succ]; gl
  rw [show z + 1 = z + 0 + 1 by omega, ones_succ]; gl
  show Rch (cfgL wa (ones (z + 1) blank) _) _
  refine Rch.tr (home_rep (z + 1) _) ?_
  apply rch_eq (by rw [cons_blank]) ; streq

theorem nexcom (t : Tup) (ht : Valid3 t) (R : Strm) :
    Rch ⟨ea0, blank, app (qL t) R⟩ ⟨n5, blank, app (qL (nxt t)) R⟩ := by
  obtain ⟨x, y, z⟩ := t
  obtain ⟨hx, hy, hz⟩ := ht
  simp only [nxt]
  by_cases h1 : 5 ≤ x
  · rw [if_pos h1]; exact nex1 x y z h1 R
  · obtain rfl : x = 4 := by omega
    rw [if_neg h1]
    by_cases h2 : 5 ≤ y
    · rw [if_pos h2]; exact nex2 y z h2 R
    · obtain rfl : y = 4 := by omega
      rw [if_neg h2]; exact nex3 z R

/-- a step left onto the blank part of the tape -/
theorem sLb {q q' : St} {R : Strm} {b w : Bool} (h : delta q b = some (w, Dir.L, q')) :
    Rch ⟨q, blank, b ::: R⟩ ⟨q', blank, F ::: w ::: R⟩ := by
  have := sL2 (c := F) (L := blank) (R := R) h
  rw [cons_blank] at this; exact this

macro "gb" : tactic => `(tactic| refine Rch.tr (sLb (by rfl)) ?_)

/-- the seed: S's `101`; the abort routine writes G (W = 2), finds no queue, and the chain
`zc` writes Z and the first tuple `(4, 4, 4)` -/
theorem boot : Rch start (TS (4, 4, 4) (0, 0)) := by
  unfold start
  refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gl; gl
  gb; gb; gb; gb; gb; gb; gb; gb; gb
  refine Rch.tr (clean_home Cl.nil _) ?_
  gb; gb; gb; gb; gb; gb; gb; gb; gb; gb; gb; gb; gb; gb; gb; gb; gb; gb; gb; gb; gb; gb
  refine Rch.tr (home [] Clean.nil _) ?_
  apply rch_eq rfl
  simp [TS, qL, rep, gapL, gm, Sb, Sr, app_append, app_replicate, ones_succ]

end TM.PerfectCuboid
