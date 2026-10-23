import TinyCryptids.Core.Lemmas

/-!
# Generic routines shared by the hand-designed machines

Each routine is stated for any transition function that contains the routine's
transitions (a structure listing them), so one proof serves every copy.
-/

namespace TM

variable {Q : Type} {δ : Q → Bool → Option (Bool × Dir × Q)}

/-! ## parsers, in terms of `ones` -/

theorem clean_blk (a b : Nat) :
    Clean (List.replicate a true ++ false :: false :: List.replicate (b + 1) true) :=
  Clean.append (Clean.replicate a) (Clean.sep (Clean.replicate b))

theorem app_blk (a b : Nat) (X : Strm) :
    app (List.replicate a true ++ false :: false :: List.replicate b true) X =
      ones a (false ::: false ::: ones b X) := by
  simp [app_append, app_replicate]

theorem app_blk_rev (a b : Nat) (X : Strm) :
    app (List.replicate a true ++ false :: false :: List.replicate b true).reverse X =
      ones b (false ::: false ::: ones a X) := by
  simp [List.reverse_append, app_append, app_replicate, List.reverse_replicate]

/-- right parser across `a` ones, a separator and `b+1` ones, to a hole -/
theorem ParserR.find2 {p1 p2 : Q} (P : ParserR δ p1 p2) (a b : Nat) (L X : Strm) :
    Reach δ ⟨p1, L, ones a (false ::: false ::: ones (b + 1) (false ::: true ::: X))⟩
      ⟨p2, false ::: ones (b + 1) (false ::: false ::: ones a L), true ::: X⟩ := by
  have := P.find (clean_blk a b) L X
  rw [app_blk, app_blk_rev] at this; exact this

/-- left parser across `a` ones, a separator and `b+1` ones, to a hole -/
theorem ParserL.find2 {p1 p2 : Q} (P : ParserL δ p1 p2) (a b : Nat) (s R : Strm) :
    Reach δ (cfgL p1 (ones a (false ::: false ::: ones (b + 1) (false ::: true ::: s))) R)
      (cfgL p2 (true ::: s) (false ::: ones (b + 1) (false ::: false ::: ones a R))) := by
  have := P.find (clean_blk a b) s R
  rw [app_blk, app_blk_rev] at this; exact this

/-- right parser across `a` ones to a hole -/
theorem ParserR.find0 {p1 p2 : Q} (P : ParserR δ p1 p2) (a : Nat) (L X : Strm) :
    Reach δ ⟨p1, L, ones a (false ::: true ::: X)⟩ ⟨p2, false ::: ones a L, true ::: X⟩ := by
  have := P.find (Clean.replicate a) L X
  rw [app_replicate, List.reverse_replicate, app_replicate] at this; exact this

/-- left parser across `a` ones to a hole -/
theorem ParserL.find0 {p1 p2 : Q} (P : ParserL δ p1 p2) (a : Nat) (s R : Strm) :
    Reach δ (cfgL p1 (ones a (false ::: true ::: s)) R)
      (cfgL p2 (true ::: s) (false ::: ones a R)) := by
  have := P.find (Clean.replicate a) s R
  rw [app_replicate, List.reverse_replicate, app_replicate] at this; exact this

/-! ## cyclic advance of the D hole -/

/-- the transitions shared by both variants: the wrap-around -/
structure DW (δ : Q → Bool → Option (Bool × Dir × Q)) (a1 a2 a3 w1 w2 w3 wrap : Q) : Prop where
  h1 : δ a1 false = some (true, Dir.R, a2)
  h2 : δ a2 true = some (true, Dir.R, a3)
  h3z : δ a3 false = some (false, Dir.L, w1)
  w1o : δ w1 true = some (true, Dir.L, w1)
  w1z : δ w1 false = some (false, Dir.R, w2)
  w2o : δ w2 true = some (true, Dir.R, w3)
  w3o : δ w3 true = some (false, Dir.R, wrap)

/-- advance; without wrap the head ends right of the new hole -/
structure Dadv (δ : Q → Bool → Option (Bool × Dir × Q)) (a1 a2 a3 a4 w1 w2 w3 cont wrap : Q)
    extends DW δ a1 a2 a3 w1 w2 w3 wrap : Prop where
  h3o : δ a3 true = some (true, Dir.L, a4)
  h4 : δ a4 true = some (false, Dir.R, cont)

/-- advance; without wrap the head ends left of the new hole -/
structure DadvL (δ : Q → Bool → Option (Bool × Dir × Q)) (a1 a2 a3 a4 w1 w2 w3 cont wrap : Q)
    extends DW δ a1 a2 a3 w1 w2 w3 wrap : Prop where
  h3o : δ a3 true = some (true, Dir.L, a4)
  h4 : δ a4 true = some (false, Dir.L, cont)

/-- hole at cell `c+1` of a block with `k+2` further cells: it moves to `c+2` -/
theorem Dadv.nowrap {a1 a2 a3 a4 w1 w2 w3 cont wrap : Q} (D : Dadv δ a1 a2 a3 a4 w1 w2 w3 cont wrap)
    (c k : Nat) (Lx Rx : Strm) :
    Reach δ ⟨a1, ones (c + 1) Lx, false ::: ones (k + 2) Rx⟩
      ⟨cont, false ::: ones (c + 2) Lx, ones (k + 1) Rx⟩ := by
  refine Reach.trans δ (stepR (δ := δ) (R := false ::: ones (k + 2) Rx) D.toDW.h1) ?_
  refine Reach.trans δ (stepR (δ := δ) (R := ones (k + 2) Rx) D.toDW.h2) ?_
  refine Reach.trans δ (stepL (δ := δ) (L := true ::: true ::: ones (c + 1) Lx) (R := ones (k + 1) Rx) D.h3o) ?_
  exact stepR (δ := δ) (L := true ::: ones (c + 1) Lx) (R := true ::: true ::: ones k Rx) D.h4

theorem DadvL.nowrap {a1 a2 a3 a4 w1 w2 w3 cont wrap : Q} (D : DadvL δ a1 a2 a3 a4 w1 w2 w3 cont wrap)
    (c k : Nat) (Lx Rx : Strm) :
    Reach δ ⟨a1, ones (c + 1) Lx, false ::: ones (k + 2) Rx⟩
      (cfgL cont (ones (c + 2) Lx) (false ::: ones (k + 1) Rx)) := by
  refine Reach.trans δ (stepR (δ := δ) (R := false ::: ones (k + 2) Rx) D.toDW.h1) ?_
  refine Reach.trans δ (stepR (δ := δ) (R := ones (k + 2) Rx) D.toDW.h2) ?_
  refine Reach.trans δ (stepL (δ := δ) (L := true ::: true ::: ones (c + 1) Lx) (R := ones (k + 1) Rx) D.h3o) ?_
  exact stepL (δ := δ) (L := true ::: ones (c + 1) Lx) (R := true ::: true ::: ones k Rx) D.h4

/-- from a 1 at cell `a+1` of a block without hole: put the hole at cell 1 -/
theorem DW.reset {a1 a2 a3 w1 w2 w3 wrap : Q} (D : DW δ a1 a2 a3 w1 w2 w3 wrap)
    (a b : Nat) (Lx Rx : Strm) :
    Reach δ (cfgL w1 (ones (a + 2) (false ::: Lx)) (ones b Rx))
      ⟨wrap, false ::: true ::: false ::: Lx, ones (a + b) Rx⟩ := by
  refine Reach.trans δ (scanL (δ := δ) D.w1o (a + 2) (false ::: Lx) (ones b Rx)) ?_
  refine Reach.trans δ (stepR (δ := δ) (L := Lx) (R := false ::: ones (a + 2) (ones b Rx)) D.w1z) ?_
  refine Reach.trans δ (stepR (δ := δ) (R := ones (a + 2) (ones b Rx)) D.w2o) ?_
  rw [show ones (a + b) Rx = ones a (ones b Rx) from (ones_add a b Rx).symm]
  exact stepR (δ := δ) (L := true ::: false ::: Lx) (R := true ::: ones a (ones b Rx)) D.w3o

/-- hole at the last cell `d` of the block: it moves back to cell 1 -/
theorem DW.wrap {a1 a2 a3 w1 w2 w3 wrap : Q} (D : DW δ a1 a2 a3 w1 w2 w3 wrap)
    (d : Nat) (Lx Rx : Strm) :
    Reach δ ⟨a1, ones d (false ::: Lx), false ::: true ::: false ::: Rx⟩
      ⟨wrap, false ::: true ::: false ::: Lx, ones d (false ::: Rx)⟩ := by
  refine Reach.trans δ (stepR (δ := δ) (R := false ::: true ::: false ::: Rx) D.h1) ?_
  refine Reach.trans δ (stepR (δ := δ) (R := true ::: false ::: Rx) D.h2) ?_
  refine Reach.trans δ (stepL (δ := δ) (L := true ::: true ::: ones d (false ::: Lx))
    (R := false ::: Rx) D.h3z) ?_
  have := D.reset d 0 Lx (false ::: Rx)
  simp only [cfgL, ones_zero, Nat.add_zero] at this
  exact this

end TM
