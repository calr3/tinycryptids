import TinyCryptids.HardyLittlewood2.Round

/-!
# Lists of blocks, and the routines that cross them

`bks l X`: a block of `h + 2` ones for each `h` in `l`, each followed by `00`, listed away
from the head (to the right, or to the left for a left half of the tape), then `X`.
-/

namespace TM.HardyLittlewood2
open St

local notation "F" => false

def bks : List Nat → Strm → Strm
  | [], X => X
  | h :: l, X => ones (h + 2) (F ::: F ::: bks l X)

theorem bks_append (l m : List Nat) (X : Strm) : bks (l ++ m) X = bks l (bks m X) := by
  induction l with
  | nil => rfl
  | cons h l ih => show ones (h + 2) (F ::: F ::: bks (l ++ m) X) = _; rw [ih]; rfl

theorem bks_snoc (l : List Nat) (h : Nat) (X : Strm) :
    bks (l ++ [h]) X = bks l (ones (h + 2) (F ::: F ::: X)) := by
  rw [bks_append]; rfl

theorem bks_rev_cons (l : List Nat) (h : Nat) (X : Strm) :
    bks (h :: l).reverse X = bks l.reverse (ones (h + 2) (F ::: F ::: X)) := by
  rw [List.reverse_cons, bks_snoc]

theorem ones_snoc (n : Nat) (X : Strm) : ones n (true ::: X) = ones (n + 1) X := (ones_succ' n X).symm

/-! ## right parsers -/

theorem PR_bks {p1 p2 : St} (P : ParserR delta p1 p2) :
    ∀ (l : List Nat) (L Y : Strm), Rch ⟨p1, F ::: F ::: L, bks l Y⟩ ⟨p1, F ::: F ::: bks l.reverse L, Y⟩
  | [], L, Y => Reach.refl _ _
  | h :: l, L, Y => by
    refine Rch.tr (scanR P.h1 (h + 2) _ _) ?_
    refine Rch.tr (sR P.h0) ?_
    refine Rch.tr (sR P.h2) ?_
    rw [bks_rev_cons]
    exact PR_bks P l _ Y

/-! ## left parsers -/

theorem PL_bks {p1 p2 : St} (P : ParserL delta p1 p2) :
    ∀ (l : List Nat) (Z R : Strm),
      Rch (cfgL p1 (bks l Z) (F ::: F ::: R)) (cfgL p1 Z (F ::: F ::: bks l.reverse R))
  | [], Z, R => Reach.refl _ _
  | h :: l, Z, R => by
    refine Rch.tr (scanL P.h1 (h + 2) _ _) ?_
    refine Rch.tr (sL P.h0) ?_
    refine Rch.tr (sL P.h2) ?_
    rw [bks_rev_cons]
    exact PL_bks P l Z _

/-! ## going home: left over holes and separators to a run of three 0s, then one more -/

structure HomeL (h1 h2 h3 h4 h5 : St) : Prop where
  a1 : delta h1 true = some (true, Dir.L, h1)
  a0 : delta h1 false = some (false, Dir.L, h2)
  b1 : delta h2 true = some (true, Dir.L, h1)
  b0 : delta h2 false = some (false, Dir.L, h3)
  c1 : delta h3 true = some (true, Dir.L, h1)
  c0 : delta h3 false = some (false, Dir.L, h4)
  d0 : delta h4 false = some (false, Dir.L, h5)

/-- from inside a block, over `l` to the four 0s before `E` (`n` cells) -/
theorem HomeL.gap {h1 h2 h3 h4 h5 : St} (H : HomeL h1 h2 h3 h4 h5) (n : Nat) :
    ∀ (l : List Nat) (j : Nat) (R : Strm),
      Rch (cfgL h1 (ones j (F ::: F ::: bks l (F ::: F ::: ones n blank))) R)
        (cfgL h5 (ones n blank) (F ::: F ::: F ::: F ::: bks l.reverse (ones j R)))
  | [], j, R => by
    refine Rch.tr (scanL H.a1 j _ R) ?_
    refine Rch.tr (sL H.a0) ?_
    refine Rch.tr (sL H.b0) ?_
    refine Rch.tr (sL H.c0) ?_
    refine Rch.tr (sL H.d0) ?_
    exact Reach.refl _ _
  | h :: l, j, R => by
    refine Rch.tr (scanL H.a1 j _ R) ?_
    refine Rch.tr (sL H.a0) ?_
    refine Rch.tr (sL H.b0) ?_
    refine Rch.tr (sL (s := ones (h + 1) (F ::: F ::: bks l (F ::: F ::: ones n blank))) H.c1) ?_
    rw [bks_rev_cons]
    have := HomeL.gap H n l (h + 1) (true ::: F ::: F ::: ones j R)
    rw [ones_snoc] at this
    exact this

/-- from inside a block, over `l` and the right part of a block, across its hole -/
theorem HomeL.hole {h1 h2 h3 h4 h5 : St} (H : HomeL h1 h2 h3 h4 h5) (k : Nat) (S : Strm) :
    ∀ (l : List Nat) (j : Nat) (R : Strm),
      Rch (cfgL h1 (ones j (F ::: F ::: bks l (ones (k + 1) (F ::: S)))) R)
        (cfgL h2 S (F ::: ones (k + 1) (F ::: F ::: bks l.reverse (ones j R))))
  | [], j, R => by
    refine Rch.tr (scanL H.a1 j _ R) ?_
    refine Rch.tr (sL H.a0) ?_
    refine Rch.tr (sL H.b0) ?_
    refine Rch.tr (sL (s := ones k (F ::: S)) H.c1) ?_
    refine Rch.tr (scanL H.a1 k _ _) ?_
    refine Rch.tr (sL H.a0) ?_
    rw [ones_snoc]
    exact Reach.refl _ _
  | h :: l, j, R => by
    refine Rch.tr (scanL H.a1 j _ R) ?_
    refine Rch.tr (sL H.a0) ?_
    refine Rch.tr (sL H.b0) ?_
    refine Rch.tr (sL (s := ones (h + 1) (F ::: F ::: bks l (ones (k + 1) (F ::: S)))) H.c1) ?_
    rw [bks_rev_cons]
    have := HomeL.hole H k S l (h + 1) (true ::: F ::: F ::: ones j R)
    rw [ones_snoc] at this
    exact this

end TM.HardyLittlewood2
