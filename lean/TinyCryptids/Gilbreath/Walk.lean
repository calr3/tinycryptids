import TinyCryptids.Lychrel.Find

/-!
# The walk to the right end of the queue, and finders entered on a 0

`WalkR` has five states: it moves right across 1s, holes and separators of two or three 0s
(`WC` lists) until it reads a fourth 0 in a row; then it moves back left across those 0s
(state `wz`) to the last 1.  `FindL.cross1`: a gap-tolerant left finder entered in `z1` on
the second 0 of a gap.
-/

namespace TM

variable {Q : Type} {δ : Q → Bool → Option (Bool × Dir × Q)}

/-- runs of one to three 0s, each followed by a 1 -/
inductive WC : List Bool → Prop
  | nil : WC []
  | one {l} : WC l → WC (true :: l)
  | gap {l} (k : Nat) : k ≤ 2 → WC l → WC (List.replicate (k + 1) false ++ true :: l)

theorem WC.append {l m : List Bool} (hl : WC l) (hm : WC m) : WC (l ++ m) := by
  induction hl with
  | nil => exact hm
  | one _ ih => exact WC.one ih
  | gap k hk _ ih => simpa using WC.gap k hk ih

theorem WC.replicate (n : Nat) : WC (List.replicate n true) := by
  induction n with
  | zero => exact WC.nil
  | succ n ih => exact WC.one ih

structure WalkR (δ : Q → Bool → Option (Bool × Dir × Q)) (w1 w2 w3 w4 wz : Q) : Prop where
  a1 : δ w1 true = some (true, Dir.R, w1)
  a0 : δ w1 false = some (false, Dir.R, w2)
  b1 : δ w2 true = some (true, Dir.R, w1)
  b0 : δ w2 false = some (false, Dir.R, w3)
  c1 : δ w3 true = some (true, Dir.R, w1)
  c0 : δ w3 false = some (false, Dir.R, w4)
  d1 : δ w4 true = some (true, Dir.R, w1)
  d0 : δ w4 false = some (false, Dir.L, wz)
  z0 : δ wz false = some (false, Dir.L, wz)

theorem WalkR.cross {w1 w2 w3 w4 wz : Q} (H : WalkR δ w1 w2 w3 w4 wz) {w : List Bool} (hw : WC w)
    (L R : Strm) : Reach δ ⟨w1, L, app w R⟩ ⟨w1, app w.reverse L, R⟩ := by
  induction hw generalizing L with
  | nil => exact Reach.refl δ _
  | @one l _ ih =>
    refine Reach.trans δ (stepR (δ := δ) (R := app (true :: l) R) H.a1) ?_
    simpa [app_append] using ih (true ::: L)
  | @gap l k hk _ ih =>
    have hw2 : ∀ L', Reach δ ⟨w1, L', app (true :: l) R⟩ ⟨w1, app (true :: l).reverse L', R⟩ := by
      intro L'
      refine Reach.trans δ (stepR (δ := δ) (R := app (true :: l) R) H.a1) ?_
      simpa [app_append] using ih (true ::: L')
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · refine Reach.trans δ (stepR (δ := δ) (R := app (false :: true :: l) R) H.a0) ?_
      refine Reach.trans δ (stepR (δ := δ) (R := app (true :: l) R) H.b1) ?_
      simpa [app_append] using ih (true ::: false ::: L)
    · refine Reach.trans δ (stepR (δ := δ) (R := app (false :: false :: true :: l) R) H.a0) ?_
      refine Reach.trans δ (stepR (δ := δ) (R := app (false :: true :: l) R) H.b0) ?_
      refine Reach.trans δ (stepR (δ := δ) (R := app (true :: l) R) H.c1) ?_
      simpa [app_append] using ih (true ::: false ::: false ::: L)
    · refine Reach.trans δ (stepR (δ := δ) (R := app (false :: false :: false :: true :: l) R) H.a0) ?_
      refine Reach.trans δ (stepR (δ := δ) (R := app (false :: false :: true :: l) R) H.b0) ?_
      refine Reach.trans δ (stepR (δ := δ) (R := app (false :: true :: l) R) H.c0) ?_
      refine Reach.trans δ (stepR (δ := δ) (R := app (true :: l) R) H.d1) ?_
      simpa [app_append] using ih (true ::: false ::: false ::: false ::: L)

/-- after the last 1: four 0s, then back to that 1 -/
theorem WalkR.find {w1 w2 w3 w4 wz : Q} (H : WalkR δ w1 w2 w3 w4 wz) (L R : Strm) :
    Reach δ ⟨w1, true ::: L, false ::: false ::: false ::: false ::: R⟩
      (cfgL wz (true ::: L) (false ::: false ::: false ::: false ::: R)) := by
  refine Reach.trans δ (stepR (δ := δ) (R := false ::: false ::: false ::: false ::: R) H.a0) ?_
  refine Reach.trans δ (stepR (δ := δ) (R := false ::: false ::: false ::: R) H.b0) ?_
  refine Reach.trans δ (stepR (δ := δ) (R := false ::: false ::: R) H.c0) ?_
  refine Reach.trans δ (stepL (δ := δ) (L := false ::: false ::: false ::: true ::: L) (R := false ::: R) H.d0) ?_
  show Reach δ (cfgL wz (false ::: false ::: false ::: true ::: L) (false ::: R)) _
  refine Reach.trans δ (stepL' (δ := δ) (s := false ::: false ::: false ::: true ::: L) H.z0) ?_
  refine Reach.trans δ (stepL' (δ := δ) (s := false ::: false ::: true ::: L) H.z0) ?_
  refine Reach.trans δ (stepL' (δ := δ) (s := false ::: true ::: L) H.z0) ?_
  exact Reach.refl δ _

/-- a left finder entered in `z1` on a 0 that follows another 0 -/
theorem FindL.cross1 {p z1 z2 : Q} (H : FindL δ p z1 z2) (k : Nat) {w : List Bool} (hw : GC w)
    (s R : Strm) : Reach δ (cfgL z1 (app (false :: (List.replicate k false ++ true :: w)) s) R)
      (cfgL p s (app (List.replicate (k + 1) false ++ true :: w).reverse R)) := by
  refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: (List.replicate k false ++ true :: w)) s) H.z0) ?_
  have e1 : app (List.replicate k false ++ true :: w) s = TM.zeros k (true ::: app w s) := by
    simp [app_append, app_zeros]
  show Reach δ (cfgL z2 (app (List.replicate k false ++ true :: w) s) (false ::: R)) _
  rw [e1]
  refine Reach.trans δ (H.zeros k _ _) ?_
  refine Reach.trans δ (stepL' (δ := δ) (s := true ::: app w s) H.y1) ?_
  have := H.cross hw s (true ::: TM.zeros k (false ::: R))
  have e2 : app (List.replicate (k + 1) false ++ true :: w).reverse R =
      app w.reverse (true ::: TM.zeros k (false ::: R)) := by
    simp [app_append, app_zeros, List.reverse_replicate, List.replicate_succ]
  rw [e2]; exact this

/-- a left finder entered in `z1` after the first 0 of a gap `false :: w` -/
theorem FindL.crossZ1 {p z1 z2 : Q} (H : FindL δ p z1 z2) {w : List Bool} (hw : GC (false :: w))
    (s R : Strm) : Reach δ (cfgL z1 (app w s) (false ::: R)) (cfgL p s (app (false :: w).reverse R)) := by
  cases hw with
  | gap k hl =>
    have := H.cross1 k hl s (false ::: R)
    simpa [List.replicate_succ, app_append] using this

end TM
