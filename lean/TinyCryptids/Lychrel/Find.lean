import TinyCryptids.Core.Lemmas

/-!
# Gap-tolerant hole finders

A finder has three states: `p` on 1s, `z1` after one 0, `z2` after two or more 0s.
It crosses runs of 1s and runs of at least two 0s, and stops at a single 0 (a hole):
when `z1` reads a 1.  `GC` lists are the segments it crosses.
-/

namespace TM

variable {Q : Type} {δ : Q → Bool → Option (Bool × Dir × Q)}

/-- zero-runs of length at least two, each followed by a 1 -/
inductive GC : List Bool → Prop
  | nil : GC []
  | one {l} : GC l → GC (true :: l)
  | gap {l} (k : Nat) : GC l → GC (false :: false :: (List.replicate k false ++ true :: l))

theorem GC.append {l m : List Bool} (hl : GC l) (hm : GC m) : GC (l ++ m) := by
  induction hl with
  | nil => exact hm
  | one _ ih => exact GC.one ih
  | gap k _ ih => simpa using GC.gap k ih

theorem GC.replicate (n : Nat) : GC (List.replicate n true) := by
  induction n with
  | zero => exact GC.nil
  | succ n ih => exact GC.one ih

structure FindL (δ : Q → Bool → Option (Bool × Dir × Q)) (p z1 z2 : Q) : Prop where
  p1 : δ p true = some (true, Dir.L, p)
  p0 : δ p false = some (false, Dir.L, z1)
  z0 : δ z1 false = some (false, Dir.L, z2)
  y0 : δ z2 false = some (false, Dir.L, z2)
  y1 : δ z2 true = some (true, Dir.L, p)

structure FindR (δ : Q → Bool → Option (Bool × Dir × Q)) (p z1 z2 : Q) : Prop where
  p1 : δ p true = some (true, Dir.R, p)
  p0 : δ p false = some (false, Dir.R, z1)
  z0 : δ z1 false = some (false, Dir.R, z2)
  y0 : δ z2 false = some (false, Dir.R, z2)
  y1 : δ z2 true = some (true, Dir.R, p)

theorem FindL.zeros {p z1 z2 : Q} (H : FindL δ p z1 z2) (k : Nat) (s R : Strm) :
    Reach δ (cfgL z2 (TM.zeros k s) R) (cfgL z2 s (TM.zeros k R)) := scanL0 H.y0 k s R

theorem FindR.zeros {p z1 z2 : Q} (H : FindR δ p z1 z2) (k : Nat) (L R : Strm) :
    Reach δ ⟨z2, L, TM.zeros k R⟩ ⟨z2, TM.zeros k L, R⟩ := scanR0 H.y0 k L R

theorem app_zeros (k : Nat) (s : Strm) : app (List.replicate k false) s = TM.zeros k s := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih, TM.zeros]

theorem FindL.cross {p z1 z2 : Q} (H : FindL δ p z1 z2) {w : List Bool} (hw : GC w)
    (s R : Strm) : Reach δ (cfgL p (app w s) R) (cfgL p s (app w.reverse R)) := by
  induction hw generalizing R with
  | nil => exact Reach.refl δ _
  | @one l _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (true :: l) s) H.p1) ?_
    simpa [app_append] using ih (true ::: R)
  | @gap l k _ ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: false :: (List.replicate k false ++ true :: l)) s) H.p0) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := app (false :: (List.replicate k false ++ true :: l)) s) H.z0) ?_
    have e1 : app (List.replicate k false ++ true :: l) s = TM.zeros k (true ::: app l s) := by
      simp [app_append, app_zeros]
    show Reach δ (cfgL z2 (app (List.replicate k false ++ true :: l) s) (false ::: false ::: R)) _
    rw [e1]
    refine Reach.trans δ (H.zeros k _ _) ?_
    refine Reach.trans δ (stepL' (δ := δ) (s := true ::: app l s) H.y1) ?_
    have := ih (true ::: TM.zeros k (false ::: false ::: R))
    have e2 : app (false :: false :: (List.replicate k false ++ true :: l)).reverse R =
        app l.reverse (true ::: TM.zeros k (false ::: false ::: R)) := by
      simp [app_append, app_zeros, List.reverse_replicate]
    rw [e2]; exact this

theorem FindR.cross {p z1 z2 : Q} (H : FindR δ p z1 z2) {w : List Bool} (hw : GC w)
    (L R : Strm) : Reach δ ⟨p, L, app w R⟩ ⟨p, app w.reverse L, R⟩ := by
  induction hw generalizing L with
  | nil => exact Reach.refl δ _
  | @one l _ ih =>
    refine Reach.trans δ (stepR (δ := δ) (R := app (true :: l) R) H.p1) ?_
    simpa [app_append] using ih (true ::: L)
  | @gap l k _ ih =>
    refine Reach.trans δ (stepR (δ := δ) (R := app (false :: false :: (List.replicate k false ++ true :: l)) R) H.p0) ?_
    refine Reach.trans δ (stepR (δ := δ) (R := app (false :: (List.replicate k false ++ true :: l)) R) H.z0) ?_
    have e1 : app (List.replicate k false ++ true :: l) R = TM.zeros k (true ::: app l R) := by
      simp [app_append, app_zeros]
    show Reach δ ⟨z2, false ::: false ::: L, app (List.replicate k false ++ true :: l) R⟩ _
    rw [e1]
    refine Reach.trans δ (H.zeros k _ _) ?_
    refine Reach.trans δ (stepR (δ := δ) (R := true ::: app l R) H.y1) ?_
    have := ih (true ::: TM.zeros k (false ::: false ::: L))
    have e2 : app (false :: false :: (List.replicate k false ++ true :: l)).reverse L =
        app l.reverse (true ::: TM.zeros k (false ::: false ::: L)) := by
      simp [app_append, app_zeros, List.reverse_replicate]
    rw [e2]; exact this

end TM
