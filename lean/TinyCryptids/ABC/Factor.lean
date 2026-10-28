import TinyCryptids.ABC.Gcd
import TinyCryptids.ABC.Mult
import TinyCryptids.ABC.Nav

/-!
# The factor phase: verdicts of `GCD(D, X)`, `d += 1`

Factor-phase tape: `K 00 D 00 A 00 B 00 C 00 M 00 R`, blank on both sides.  `K` has `k`
cells, `D` holds `d` (hole at position 1 between tests), `A, B, C` hold `a, b, c` (the block
being tested has a marker on cell 1), `M` is one cell, `R` holds `r` with its hole on cell 1.
-/

namespace TM.ABC
open St

local notation "F" => false
local notation "T" => true

/-- a block holding `v`, no hole -/
def Bk (v : Nat) : List Bool := List.replicate (v + 2) true
/-- a block holding `v` with a hole (marker) on cell 1 -/
def Bm (v : Nat) : List Bool := true :: false :: List.replicate v true
def S2 : List Bool := [false, false]

theorem Blk_Bk (v : Nat) : Blk (Bk v) := Blk.one (v + 1)
theorem Blk_M : Blk [true] := Blk.one 0

theorem app_Bk (v : Nat) (s : Strm) : app (Bk v) s = ones (v + 2) s := app_replicate _ _

theorem PEX : ParserR deltaQ EX1 EX2 := ⟨rfl, rfl, rfl⟩
theorem PenF : ParserL deltaQ enF1 enF2 := ⟨rfl, rfl, rfl⟩
theorem PGD : ParserL deltaQ GD1 GD2 := ⟨rfl, rfl, rfl⟩
theorem PenC : ParserL deltaQ enC1 enC2 := ⟨rfl, rfl, rfl⟩
theorem PDH : ParserL deltaQ DH1 DH2 := ⟨rfl, rfl, rfl⟩
theorem PER : ParserL deltaQ ER1 ER2 := ⟨rfl, rfl, rfl⟩
theorem PEQ : ParserL deltaQ EQ1 EQ2 := ⟨rfl, rfl, rfl⟩
theorem PHX : ParserR deltaQ HX1 HX2 := ⟨rfl, rfl, rfl⟩
theorem PhF : ParserL deltaQ hF1 hF2 := ⟨rfl, rfl, rfl⟩
theorem PKC : ParserL deltaQ KC1 KC2 := ⟨rfl, rfl, rfl⟩
theorem PKR : ParserR deltaQ KR1 KR2 := ⟨rfl, rfl, rfl⟩
theorem PhC : ParserL deltaQ hC1 hC2 := ⟨rfl, rfl, rfl⟩
theorem PHR : ParserL deltaQ HR1 HR2 := ⟨rfl, rfl, rfl⟩

/-- the counter `D` after `gcd = 1` (hole on position 2): the hole back on position 1, then
to the marker of `X` (lands two cells right of it, state `en1`) -/
theorem e_to_x {g : List Bool} (hg : Gap g) (Lc X : Strm) (d : Nat) (hd : 2 ≤ d) :
    Rch ⟨E1, F ::: Lc, T ::: T ::: F ::: ones (d - 1) (app g (T ::: F ::: T ::: X))⟩
      ⟨en1, T ::: F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc)), X⟩ := by
  gR; gR; gR
  have hw : Clean (List.replicate (d - 1) T ++ (g ++ [T])) := Clean.rep_append _ (hg.clean Clean.nil)
  have e : ones (d - 1) (app g (T ::: F ::: T ::: X)) =
      app (List.replicate (d - 1) T ++ (g ++ [T])) (F ::: T ::: X) := by
    simp only [app_append, app_replicate, app_cons, app_nil]
  rw [e]
  refine Rch.tr (PEX.find hw _ _) ?_
  gR
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.reverse_replicate, app_append, app_replicate, app_cons, app_nil, List.singleton_append]
  rw [ones_cons_true, ← ones_succ, show d - 1 + 1 = d by omega]; fin

/-- from `X`'s cell 0, left to `D`'s hole (on position 1): `ca1` there -/
theorem gd_back {g : List Bool} (hg : Gap g) (Lc R : Strm) (d : Nat) (hd : 1 ≤ d) :
    Rch (cfgL GD1 (T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))) R)
      ⟨ca1, T ::: F ::: Lc, F ::: app (List.replicate d T ++ g ++ [T]) R⟩ := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hw : Clean (T :: (g.reverse ++ List.replicate (d' + 1) T)) :=
    Clean.one (by rw [List.replicate_succ]; exact hg.reverse.clean (Clean.replicate d'))
  have e : T ::: app g.reverse (ones (d' + 1) (F ::: T ::: F ::: Lc)) =
      app (T :: (g.reverse ++ List.replicate (d' + 1) T)) (F ::: T ::: F ::: Lc) := by
    simp only [app_cons, app_append, app_replicate]
  rw [e]
  refine Rch.tr (pLR PGD rfl hw _ _) ?_
  simp only [List.reverse_cons, List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    List.append_assoc]
  fin

/-- `gcd = 1` on a block `X` followed by a block `Y`: the marker moves to `Y` -/
theorem e_next {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (d v w : Nat) (hd : 2 ≤ d) (hv : 1 ≤ v) :
    Rch ⟨E1, F ::: Lc, T ::: T ::: F ::: ones (d - 1) (cyR (F ::: F ::: T ::: T ::: ones w (F ::: Rc)) v 1 g)⟩
      (gAt ca1 Lc Rc w (g ++ List.replicate (v + 2) T ++ S2) d 1) := by
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  have e0 : cyR (F ::: F ::: T ::: T ::: ones w (F ::: Rc)) (v' + 1) 1 g =
      app g (T ::: F ::: T ::: ones v' (F ::: F ::: T ::: T ::: ones w (F ::: Rc))) := by
    simp only [cyR, show v' + 1 + 1 - 1 = v' + 1 by omega, ones_succ, ones_zero]
  rw [e0]
  refine Rch.tr (e_to_x hg Lc _ d hd) ?_
  sRn v'; gR; gR; gR; gL
  show Rch (cfgL enF1 (T ::: F ::: F ::: ones v' (T ::: F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))))
    (F ::: ones w (F ::: Rc))) _
  have hw : Clean (T :: F :: F :: List.replicate (v' + 1) T) :=
    Clean.one (by rw [List.replicate_succ]; exact Clean.sep (Clean.replicate v'))
  have e1 : T ::: F ::: F ::: ones v' (T ::: F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))) =
      app (T :: F :: F :: List.replicate (v' + 1) T) (F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))) := by
    simp only [app_cons, app_replicate, ones_cons_true, ← ones_succ]
  rw [e1]
  refine Rch.tr (pLR PenF rfl hw _ _) ?_
  gL
  refine Rch.tr (gd_back hg Lc _ d (by omega)) ?_
  unfold gAt cyR S2
  simp only [List.reverse_cons, List.reverse_append, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, app_append,
    app_replicate, app_cons, app_nil, ones_succ, ones_zero, show d + 1 - 1 = d by omega,
    show w + 1 - 1 = w by omega]
  fin

/-- from a cell 0 (a 1) left of which lie a gap and `D` (hole on position 1): a left parser
to `D`'s hole, whose `found` step moves right onto it -/
theorem back_D {p1 p2 q : St} (P : ParserL deltaQ p1 p2) (hf : deltaQ p2 true = some (true, Dir.R, q))
    {g : List Bool} (hg : Gap g) (Lc R : Strm) (d : Nat) (hd : 1 ≤ d) :
    Rch (cfgL p1 (T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))) R)
      ⟨q, T ::: F ::: Lc, F ::: app (List.replicate d T ++ g ++ [T]) R⟩ := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hw : Clean (T :: (g.reverse ++ List.replicate (d' + 1) T)) :=
    Clean.one (by rw [List.replicate_succ]; exact hg.reverse.clean (Clean.replicate d'))
  have e : T ::: app g.reverse (ones (d' + 1) (F ::: T ::: F ::: Lc)) =
      app (T :: (g.reverse ++ List.replicate (d' + 1) T)) (F ::: T ::: F ::: Lc) := by
    simp only [app_cons, app_append, app_replicate]
  rw [e]
  refine Rch.tr (pLR P hf hw _ _) ?_
  simp only [List.reverse_cons, List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    List.append_assoc]
  fin

/-- the same from the first 0 of the gap (left of a block's cell 0) -/
theorem back_D0 {p1 p2 q : St} (P : ParserL deltaQ p1 p2) (hf : deltaQ p2 true = some (true, Dir.R, q))
    {g : List Bool} (hg : Gap g) (Lc R : Strm) (d : Nat) (hd : 1 ≤ d) :
    Rch (cfgL p1 (app g.reverse (ones d (F ::: T ::: F ::: Lc))) R)
      ⟨q, T ::: F ::: Lc, F ::: app (List.replicate d T ++ g) R⟩ := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hw : Clean (g.reverse ++ List.replicate (d' + 1) T) := by
    rw [List.replicate_succ]; exact hg.reverse.clean (Clean.replicate d')
  have e : app g.reverse (ones (d' + 1) (F ::: T ::: F ::: Lc)) =
      app (g.reverse ++ List.replicate (d' + 1) T) (F ::: T ::: F ::: Lc) := by
    simp only [app_append, app_replicate]
  rw [e]
  refine Rch.tr (pLR P hf hw _ _) ?_
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_replicate]
  fin

/-- `gcd > 1`: from `D`'s cell 0 to the marker of `X` (state `hn1`, two cells right of it) -/
theorem h_to_x {g : List Bool} (hg : Gap g) (Lc X : Strm) (d : Nat) :
    Rch ⟨H1, F ::: Lc, T ::: F ::: ones d (app g (T ::: F ::: T ::: X))⟩
      ⟨hn1, T ::: F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc)), X⟩ := by
  gR; gR
  have hw : Clean (List.replicate d T ++ (g ++ [T])) := Clean.rep_append _ (hg.clean Clean.nil)
  have e : ones d (app g (T ::: F ::: T ::: X)) = app (List.replicate d T ++ (g ++ [T])) (F ::: T ::: X) := by
    simp only [app_append, app_replicate, app_cons, app_nil]
  rw [e]
  refine Rch.tr (pRR PHX rfl hw _ _) ?_
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.reverse_replicate, app_append, app_replicate, app_cons, app_nil, List.singleton_append]
  fin

/-- `gcd = 1` on `C` (followed by `M`): `C`'s marker filled, `d += 1` (state `dp1` on `D`'s hole) -/
theorem e_C {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (d v : Nat) (hd : 2 ≤ d) (hv : 1 ≤ v) :
    Rch ⟨E1, F ::: Lc, T ::: T ::: F ::: ones (d - 1) (cyR (F ::: F ::: T ::: F ::: Rc) v 1 g)⟩
      ⟨dp1, T ::: F ::: Lc, F ::: app (List.replicate d T ++ g ++ [T]) (T ::: ones v (F ::: F ::: T ::: F ::: Rc))⟩ := by
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  have e0 : cyR (F ::: F ::: T ::: F ::: Rc) (v' + 1) 1 g =
      app g (T ::: F ::: T ::: ones v' (F ::: F ::: T ::: F ::: Rc)) := by
    simp only [cyR, show v' + 1 + 1 - 1 = v' + 1 by omega, ones_succ, ones_zero]
  rw [e0]
  refine Rch.tr (e_to_x hg Lc _ d hd) ?_
  sRn v'; gR; gR; gR; gL
  show Rch (cfgL enC1 (T ::: F ::: F ::: ones v' (T ::: F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))))
    (F ::: Rc)) _
  have hw : Clean (T :: F :: F :: List.replicate (v' + 1) T) :=
    Clean.one (by rw [List.replicate_succ]; exact Clean.sep (Clean.replicate v'))
  have e1 : T ::: F ::: F ::: ones v' (T ::: F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))) =
      app (T :: F :: F :: List.replicate (v' + 1) T) (F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))) := by
    simp only [app_cons, app_replicate, ones_cons_true, ← ones_succ]
  rw [e1]
  refine Rch.tr (pLR PenC rfl hw _ _) ?_
  gL
  refine Rch.tr (back_D PDH rfl hg Lc _ d (by omega)) ?_
  simp only [List.reverse_cons, List.reverse_append, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, app_append,
    app_replicate, app_cons, app_nil, ones_succ, ones_zero]
  fin

/-- `gcd(d, R) = 1` (`X = R`, the last block): to `D`'s hole, the base of `R := R * d` -/
theorem e_R {g : List Bool} (hg : Gap g) (Lc : Strm) (d r : Nat) (hd : 2 ≤ d) (hr : 1 ≤ r) :
    Rch ⟨E1, F ::: Lc, T ::: T ::: F ::: ones (d - 1) (cyR blank r 1 g)⟩
      ⟨Rba1, T ::: F ::: Lc, F ::: ones d (app g (T ::: F ::: ones r blank))⟩ := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have e0 : cyR blank (r' + 1) 1 g = app g (T ::: F ::: T ::: ones r' (F ::: F ::: F ::: blank)) := by
    simp only [cyR, show r' + 1 + 1 - 1 = r' + 1 by omega, ones_succ, ones_zero, cons_blank]
  rw [e0]
  refine Rch.tr (e_to_x hg Lc _ d hd) ?_
  sRn r'; gR; gR; gL; gL; gL
  have hw : Clean (List.replicate (r' + 1) T) := Clean.replicate _
  have e1 : ones r' (T ::: F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))) =
      app (List.replicate (r' + 1) T) (F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))) := by
    simp only [app_replicate, ← ones_succ']
  rw [e1]
  refine Rch.tr (pLL PER rfl hw _ _) ?_
  refine Rch.tr (back_D0 PEQ rfl hg Lc _ d (by omega)) ?_
  simp only [List.reverse_replicate, app_append, app_replicate, app_cons, ones_succ, ones_zero,
    cons_blank]
  fin

/-- `gcd > 1` on `A` or `B` (followed by a block `Y`): the marker filled, then the `K` check:
`K` has `k + 2` cells: a hit, `ca1` on `D`'s hole (next: `GCD(D, R)`) -/
theorem h_next {g : List Bool} (hg : Gap g) (Rc : Strm) (k d v w : Nat) (hd : 1 ≤ d) (hv : 1 ≤ v) :
    Rch ⟨H1, F ::: F ::: ones (k + 2) blank,
        T ::: F ::: ones d (cyR (F ::: F ::: T ::: T ::: ones w (F ::: Rc)) v 1 g)⟩
      ⟨ca1, T ::: F ::: F ::: ones (k + 2) blank,
        F ::: app (List.replicate d T ++ g ++ [T]) (T ::: ones v (F ::: F ::: T ::: T ::: ones w (F ::: Rc)))⟩ := by
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  have e0 : cyR (F ::: F ::: T ::: T ::: ones w (F ::: Rc)) (v' + 1) 1 g =
      app g (T ::: F ::: T ::: ones v' (F ::: F ::: T ::: T ::: ones w (F ::: Rc))) := by
    simp only [cyR, show v' + 1 + 1 - 1 = v' + 1 by omega, ones_succ, ones_zero]
  rw [e0]
  refine Rch.tr (h_to_x hg _ _ d) ?_
  sRn v'; gR; gR; gR; gL
  show Rch (cfgL hF1 (T ::: F ::: F ::: ones v' (T ::: F ::: T ::: app g.reverse
    (ones d (F ::: T ::: F ::: F ::: ones (k + 2) blank)))) (T ::: ones w (F ::: Rc))) _
  have hw : Clean (T :: F :: F :: List.replicate (v' + 1) T) :=
    Clean.one (by rw [List.replicate_succ]; exact Clean.sep (Clean.replicate v'))
  rw [show T ::: F ::: F ::: ones v' (T ::: F ::: T ::: app g.reverse
      (ones d (F ::: T ::: F ::: F ::: ones (k + 2) blank))) =
      app (T :: F :: F :: List.replicate (v' + 1) T) (F ::: T ::: app g.reverse
      (ones d (F ::: T ::: F ::: F ::: ones (k + 2) blank))) by
    simp only [app_cons, app_replicate, ones_cons_true, ← ones_succ]]
  refine Rch.tr (pLR PhF rfl hw _ _) ?_
  gLc
  refine toL ?_
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hw2 : Clean (T :: (g.reverse ++ List.replicate (d' + 1) T)) :=
    Clean.one (by rw [List.replicate_succ]; exact hg.reverse.clean (Clean.replicate d'))
  rw [show T ::: app g.reverse (ones (d' + 1) (F ::: T ::: F ::: F ::: ones (k + 2) blank)) =
      app (T :: (g.reverse ++ List.replicate (d' + 1) T)) (F ::: T ::: F ::: F ::: ones (k + 2) blank) by
    simp only [app_cons, app_append, app_replicate]]
  refine Rch.tr (pLL PKC rfl hw2 _ _) ?_
  gL; gL; gL
  show Rch (cfgL kc5 (T ::: ones k blank) _) _
  gR
  have hw3 : Clean [T, F, F, T] := Clean.one (Clean.sep Clean.nil)
  simp only [tl_cons, List.reverse_cons, List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
    app_append, app_replicate, app_cons, app_nil, ones_succ]
  refine Rch.tr (pRL PKR rfl hw3 _ _) ?_
  simp only [List.reverse_cons, List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
    app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero]
  fin

theorem h_next_nc {g : List Bool} (hg : Gap g) (Rc : Strm) (d v w : Nat) (hd : 1 ≤ d) (hv : 1 ≤ v) :
    Rch ⟨H1, F ::: F ::: ones 1 blank,
        T ::: F ::: ones d (cyR (F ::: F ::: T ::: T ::: ones w (F ::: Rc)) v 1 g)⟩
      ⟨nc1, F ::: blank, T ::: F ::: F ::: T ::: F :::
        app (List.replicate d T ++ g ++ [T]) (T ::: ones v (F ::: F ::: T ::: T ::: ones w (F ::: Rc)))⟩ := by
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  have e0 : cyR (F ::: F ::: T ::: T ::: ones w (F ::: Rc)) (v' + 1) 1 g =
      app g (T ::: F ::: T ::: ones v' (F ::: F ::: T ::: T ::: ones w (F ::: Rc))) := by
    simp only [cyR, show v' + 1 + 1 - 1 = v' + 1 by omega, ones_succ, ones_zero]
  rw [e0]
  refine Rch.tr (h_to_x hg _ _ d) ?_
  sRn v'; gR; gR; gR; gL
  show Rch (cfgL hF1 (T ::: F ::: F ::: ones v' (T ::: F ::: T ::: app g.reverse
    (ones d (F ::: T ::: F ::: F ::: ones 1 blank)))) (T ::: ones w (F ::: Rc))) _
  have hw : Clean (T :: F :: F :: List.replicate (v' + 1) T) :=
    Clean.one (by rw [List.replicate_succ]; exact Clean.sep (Clean.replicate v'))
  rw [show T ::: F ::: F ::: ones v' (T ::: F ::: T ::: app g.reverse
      (ones d (F ::: T ::: F ::: F ::: ones 1 blank))) =
      app (T :: F :: F :: List.replicate (v' + 1) T) (F ::: T ::: app g.reverse
      (ones d (F ::: T ::: F ::: F ::: ones 1 blank))) by
    simp only [app_cons, app_replicate, ones_cons_true, ← ones_succ]]
  refine Rch.tr (pLR PhF rfl hw _ _) ?_
  gLc
  refine toL ?_
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hw2 : Clean (T :: (g.reverse ++ List.replicate (d' + 1) T)) :=
    Clean.one (by rw [List.replicate_succ]; exact hg.reverse.clean (Clean.replicate d'))
  rw [show T ::: app g.reverse (ones (d' + 1) (F ::: T ::: F ::: F ::: ones 1 blank)) =
      app (T :: (g.reverse ++ List.replicate (d' + 1) T)) (F ::: T ::: F ::: F ::: ones 1 blank) by
    simp only [app_cons, app_append, app_replicate]]
  refine Rch.tr (pLL PKC rfl hw2 _ _) ?_
  gL; gL; gL
  show Rch (cfgL kc5 blank _) _
  rw [← cons_blank]; gR
  simp only [tl_cons, cons_blank, List.reverse_cons, List.reverse_append, List.reverse_reverse,
    List.reverse_replicate, List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append,
    List.cons_append, app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero, tl_blank]
  fin

/-- `gcd > 1` on `C` (followed by `M`): the marker filled; `ca1` on `D`'s hole: `GCD(D, R)` -/
theorem h_C {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (d v : Nat) (hd : 1 ≤ d) (hv : 1 ≤ v) :
    Rch ⟨H1, F ::: Lc, T ::: F ::: ones d (cyR (F ::: F ::: T ::: F ::: Rc) v 1 g)⟩
      ⟨ca1, T ::: F ::: Lc, F ::: app (List.replicate d T ++ g ++ [T]) (T ::: ones v (F ::: F ::: T ::: F ::: Rc))⟩ := by
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  have e0 : cyR (F ::: F ::: T ::: F ::: Rc) (v' + 1) 1 g =
      app g (T ::: F ::: T ::: ones v' (F ::: F ::: T ::: F ::: Rc)) := by
    simp only [cyR, show v' + 1 + 1 - 1 = v' + 1 by omega, ones_succ, ones_zero]
  rw [e0]
  refine Rch.tr (h_to_x hg _ _ d) ?_
  sRn v'; gR; gR; gR; gL
  show Rch (cfgL hC1 (T ::: F ::: F ::: ones v' (T ::: F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))))
    (F ::: Rc)) _
  have hw : Clean (T :: F :: F :: List.replicate (v' + 1) T) :=
    Clean.one (by rw [List.replicate_succ]; exact Clean.sep (Clean.replicate v'))
  rw [show T ::: F ::: F ::: ones v' (T ::: F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))) =
      app (T :: F :: F :: List.replicate (v' + 1) T) (F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))) by
    simp only [app_cons, app_replicate, ones_cons_true, ← ones_succ]]
  refine Rch.tr (pLR PhC rfl hw _ _) ?_
  gL
  refine Rch.tr (back_D PGD rfl hg Lc _ d hd) ?_
  simp only [List.reverse_cons, List.reverse_append, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, app_append,
    app_replicate, app_cons, app_nil, ones_succ, ones_zero]
  fin

/-- `gcd(d, R) > 1` (`X = R`): `d += 1` (state `dp1` on `D`'s hole), `R`'s hole stays -/
theorem h_R {g : List Bool} (hg : Gap g) (Lc : Strm) (d r : Nat) (hd : 1 ≤ d) (hr : 1 ≤ r) :
    Rch ⟨H1, F ::: Lc, T ::: F ::: ones d (cyR blank r 1 g)⟩
      ⟨dp1, T ::: F ::: Lc, F ::: ones d (app g (T ::: F ::: ones r blank))⟩ := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have e0 : cyR blank (r' + 1) 1 g = app g (T ::: F ::: T ::: ones r' (F ::: F ::: F ::: blank)) := by
    simp only [cyR, show r' + 1 + 1 - 1 = r' + 1 by omega, ones_succ, ones_zero, cons_blank]
  rw [e0]
  refine Rch.tr (h_to_x hg _ _ d) ?_
  sRn r'; gR; gR; gL; gL; gL
  have hw : Clean (List.replicate (r' + 1) T) := Clean.replicate _
  have e1 : ones r' (T ::: F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))) =
      app (List.replicate (r' + 1) T) (F ::: T ::: app g.reverse (ones d (F ::: T ::: F ::: Lc))) := by
    simp only [app_replicate, ← ones_succ']
  rw [e1]
  refine Rch.tr (pLL PHR rfl hw _ _) ?_
  refine Rch.tr (back_D0 PDH rfl hg Lc _ d hd) ?_
  simp only [List.reverse_replicate, app_append, app_replicate, app_cons, ones_succ, ones_zero,
    cons_blank]
  fin

/-- a left parser from anywhere left of which lie a clean list `w` and `D` (hole on 1) -/
theorem back_Dw {p1 p2 q : St} (P : ParserL deltaQ p1 p2) (hf : deltaQ p2 true = some (true, Dir.R, q))
    {w : List Bool} (d : Nat) (hw : Clean (w ++ List.replicate d T)) (Lc R : Strm) :
    Rch (cfgL p1 (app w (ones d (F ::: T ::: F ::: Lc))) R)
      ⟨q, T ::: F ::: Lc, F ::: app (List.replicate d T ++ w.reverse) R⟩ := by
  have e : app w (ones d (F ::: T ::: F ::: Lc)) = app (w ++ List.replicate d T) (F ::: T ::: F ::: Lc) := by
    simp only [app_append, app_replicate]
  rw [e]
  refine Rch.tr (pLR P hf hw _ _) ?_
  simp only [List.reverse_append, List.reverse_replicate]
  fin

end TM.ABC