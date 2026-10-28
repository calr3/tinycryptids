import TinyCryptids.ABC.Nav

/-!
# The compare: `X` against `Y`

`X` (value `x`, left) has its cursor on position `i`, moving left; `Y` (value `y`) on `j`,
moving right; a hole-free gap `g` lies between them.  Each round moves both cursors; `X` runs
out first iff `x ≤ y` (state `xe2`, on the cell two left of `X`), otherwise `Y` does and the
head ends in `xq6` (three cells left of `X`), both blocks filled.
-/

namespace TM.ABC
open St

local notation "F" => false
local notation "T" => true

theorem PYP : ParserR deltaQ YP1 YP2 := ⟨rfl, rfl, rfl⟩
theorem PXP : ParserL deltaQ XP1 XP2 := ⟨rfl, rfl, rfl⟩
theorem PXQ : ParserL deltaQ XQ1 XQ2 := ⟨rfl, rfl, rfl⟩

/-- the tape right of `X`'s cells: the gap, then `Y` with its cursor on `j` -/
def yR (g : List Bool) (y j : Nat) (Ry : Strm) : Strm := app g (ones j (F ::: ones (y + 1 - j) Ry))

/-- `X`'s cursor on `i` just filled, the head on cell `i - 1` in `x2` -/
def cmpA (Lx : Strm) (x i : Nat) (g : List Bool) (y j : Nat) (Ry : Strm) : Cfg St :=
  cfgL x2 (ones i Lx) (T ::: ones (x + 1 - i) (yR g y j Ry))

/-- one round: `i ≥ 2` moves to `i - 1`, `j < y` to `j + 1` -/
theorem cmp_round {g : List Bool} (hg : Gap g) (Lx Ry : Strm) (x i y j : Nat)
    (hi : 2 ≤ i) (hix : i ≤ x) (hj : 1 ≤ j) (hjy : j < y) :
    Rch (cmpA Lx x i g y j Ry) (cmpA Lx x (i - 1) g y (j + 1) Ry) := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, y + 1 - (j' + 1) = m + 2 := ⟨y - j' - 2, by omega⟩
  unfold cmpA yR
  rw [hm, show i' + 2 - 1 = i' + 1 by omega, show y + 1 - (j' + 1 + 1) = m + 1 by omega,
    show x + 1 - (i' + 1) = (x + 1 - (i' + 2)) + 1 by omega]
  show Rch (cfgL x2 (T ::: T ::: ones i' Lx) _) _
  gL; refine fromL ?_; gR; gR
  have hw : Clean (List.replicate (x + 1 - (i' + 2) + 1) T ++ (g ++ List.replicate (j' + 1) T)) :=
    Clean.rep_append _ (by rw [List.replicate_succ]; exact hg.clean (Clean.replicate j'))
  rw [show T ::: ones (x + 1 - (i' + 2)) (app g (ones (j' + 1) (F ::: ones (m + 2) Ry))) =
    app (List.replicate (x + 1 - (i' + 2) + 1) T ++ (g ++ List.replicate (j' + 1) T)) (F ::: T ::: ones (m + 1) Ry) by
    simp only [app_append, app_replicate, ones_succ]]
  refine Rch.tr (pRL PYP rfl hw _ _) ?_
  gR; gR; gL; gL
  have hw2 : Clean (T :: (List.replicate (x + 1 - (i' + 2) + 1) T ++ (g ++ List.replicate (j' + 1) T)).reverse) := by
    simp only [List.reverse_append, List.reverse_replicate, List.append_assoc]
    exact Clean.one (Clean.rep_append _ (by rw [List.replicate_succ]; exact hg.reverse.clean (Clean.replicate _)))
  refine Rch.tr (pLR PXP rfl hw2 _ _) ?_
  gL
  simp only [List.reverse_cons, List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    List.append_assoc, List.singleton_append, app_append, app_replicate, app_cons, app_nil, ones_succ,
    ones_cons_true]
  fin

theorem cmp_rounds {g : List Bool} (hg : Gap g) (Lx Ry : Strm) (x y : Nat) :
    ∀ k, k + 1 ≤ x → k + 1 ≤ y → Rch (cmpA Lx x x g y 1 Ry) (cmpA Lx x (x - k) g y (1 + k) Ry) := by
  intro k
  induction k with
  | zero => intro _ _; fin
  | succ k ih =>
    intro h1 h2
    refine Rch.tr (ih (by omega) (by omega)) ?_
    have := cmp_round hg Lx Ry x (x - k) y (1 + k) (by omega) (by omega) (by omega) (by omega)
    rwa [show x - k - 1 = x - (k + 1) by omega, show 1 + k + 1 = 1 + (k + 1) by omega] at this

/-- `X` has run out (its cursor was on position 1) -/
theorem cmp_xexh (Lx Ry : Strm) (x : Nat) (g : List Bool) (y j : Nat) :
    Rch (cmpA (F ::: Lx) x 1 g y j Ry) (cfgL xe2 Lx (F ::: ones (x + 2) (yR g y j Ry))) := by
  unfold cmpA
  rw [show x + 1 - 1 = x by omega]
  show Rch (cfgL x2 (T ::: F ::: Lx) _) _
  gL; gL; fin

/-- `Y` has run out (its cursor was on its last position `y`), `X`'s cursor on `i ≥ 2` -/
theorem cmp_yexh {g : List Bool} (hg : Gap g) (Lx Ry : Strm) (x i y : Nat)
    (hi : 2 ≤ i) (hix : i ≤ x) (hy : 1 ≤ y) :
    Rch (cmpA (F ::: F ::: Lx) x i g y y (F ::: Ry))
      (cfgL xq6 Lx (F ::: F ::: ones (x + 2) (app g (ones (y + 2) (F ::: Ry))))) := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  unfold cmpA yR
  rw [show y' + 1 + 1 - (y' + 1) = 1 by omega]
  show Rch (cfgL x2 (T ::: T ::: ones i' (F ::: F ::: Lx)) _) _
  gL; refine fromL ?_; gR; gR
  have hw : Clean (List.replicate (x + 1 - (i' + 2) + 1) T ++ (g ++ List.replicate (y' + 1) T)) :=
    Clean.rep_append _ (by rw [List.replicate_succ]; exact hg.clean (Clean.replicate y'))
  rw [show T ::: ones (x + 1 - (i' + 2)) (app g (ones (y' + 1) (F ::: ones 1 (F ::: Ry)))) =
    app (List.replicate (x + 1 - (i' + 2) + 1) T ++ (g ++ List.replicate (y' + 1) T)) (F ::: T ::: F ::: Ry) by
    simp only [app_append, app_replicate, ones_succ, ones_zero]]
  refine Rch.tr (pRL PYP rfl hw _ _) ?_
  gR; gR; gL; gL
  have hw2 : Clean (T :: (List.replicate (y' + 1) T ++ (g.reverse ++ List.replicate (x + 1 - (i' + 2) + 1) T))) :=
    Clean.one (Clean.rep_append _ (by rw [List.replicate_succ]; exact hg.reverse.clean (Clean.replicate _)))
  rw [show app (List.replicate (x + 1 - (i' + 2) + 1) T ++ (g ++ List.replicate (y' + 1) T)).reverse
      (F ::: T ::: ones i' (F ::: F ::: Lx)) =
    app (List.replicate (y' + 1) T ++ (g.reverse ++ List.replicate (x + 1 - (i' + 2) + 1) T))
      (F ::: T ::: ones i' (F ::: F ::: Lx)) by
    simp only [List.reverse_append, List.reverse_replicate, List.append_assoc]]
  refine Rch.tr (pLR PXQ rfl hw2 _ _) ?_
  gL
  show Rch (cfgL xq4 (T ::: ones i' (F ::: F ::: Lx)) _) _
  sLn (i' + 1); gL; gL
  simp only [List.reverse_cons, List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    List.append_assoc, List.singleton_append, app_append, app_replicate, app_cons, ones_succ, ones_cons_true]
  rw [ones_add, show i' + (x + 1 - (i' + 2)) = x - 1 by omega]
  obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  simp only [Nat.add_sub_cancel, ones_succ, ones_cons_true, app_nil]; fin

/-- **compare**: from `X`'s cursor on its last position (just filled) and `Y`'s on 1 -/
theorem compare {g : List Bool} (hg : Gap g) (Lx Ry : Strm) (x y : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (x ≤ y → Rch (cmpA (F ::: F ::: Lx) x x g y 1 (F ::: Ry))
      (cfgL xe2 (F ::: Lx) (F ::: ones (x + 2) (yR g y x (F ::: Ry))))) ∧
    (y < x → Rch (cmpA (F ::: F ::: Lx) x x g y 1 (F ::: Ry))
      (cfgL xq6 Lx (F ::: F ::: ones (x + 2) (app g (ones (y + 2) (F ::: Ry)))))) := by
  constructor
  · intro h
    refine Rch.tr (cmp_rounds hg _ _ x y (x - 1) (by omega) (by omega)) ?_
    rw [show x - (x - 1) = 1 by omega, show 1 + (x - 1) = x by omega]
    exact cmp_xexh _ _ x g y x
  · intro h
    refine Rch.tr (cmp_rounds hg _ _ x y (y - 1) (by omega) (by omega)) ?_
    rw [show 1 + (y - 1) = y by omega]
    exact cmp_yexh hg Lx Ry x (x - (y - 1)) y (by omega) (by omega) hy

end TM.ABC
