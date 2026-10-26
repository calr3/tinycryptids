import TinyCryptids.Core.Routines
import TinyCryptids.Kurepa.Tac

/-!
# Routines of the design

Tape (`F` = blank): `N 00 L 0 F 0 Q`.

* `N` : cells `0 .. m`, a hole at cell `c` (`1 ≤ c ≤ m`); seen from its right end it is
  `NL m c = ones (m - c) (F ::: ones c blank)`;
* `L` : `lam` cells, during the test a hole walking from right to left;
* `F` : `K` cells, after the marker `m1`; during the copies a cursor;
* `Q` : `q` cells, after the marker `m2`, the copies made so far.
-/

namespace TM.Kurepa
open St

local notation "F" => false

/-- `N` seen from its right end, hole at cell `c` -/
def NL (m c : Nat) : Strm := ones (m - c) (F ::: ones c blank)

/-- the test: `p2` on cell `j` of `L` (all ones), about to make it the hole -/
def TP (m c lam K j : Nat) : Cfg St :=
  ⟨p2, ones j (F ::: F ::: NL m c), ones (lam - j) (F ::: ones K blank)⟩

/-- one unit of the test: the cell `h` of `L` becomes the hole, the N hole moves on, the hole
is filled again and `p2` is on the cell left of it -/
theorem unit_step (m c h : Nat) (R : Strm) (hc1 : 1 ≤ c) (hc : c < m) :
    Rch ⟨p2, ones h (F ::: F ::: NL m c), true ::: true ::: R⟩
      (cfgL p2 (ones h (F ::: F ::: NL m (c + 1))) (true ::: true ::: R)) := by
  obtain ⟨d, hd⟩ : ∃ d, m - c = d + 1 := ⟨m - c - 1, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  unfold NL
  rw [hd, show m - (c' + 1 + 1) = d by omega]
  refine Rch.tr (stepL (δ := delta) (by rfl)) ?_
  show Rch (cfgL PN1 (ones h (F ::: F ::: ones (d + 1) (F ::: ones (c' + 1) blank))) _) _
  sLn h; gL; gL; sLn (d + 1); gL
  gR; gR; gR; sRn d; gR; gR; sRn h; gR; gL0; gL
  fin

theorem unit_wrap (m h : Nat) (R : Strm) (hm : 1 ≤ m) :
    Rch ⟨p2, ones h (F ::: F ::: NL m m), true ::: true ::: R⟩
      (cfgL p2 (ones h (F ::: F ::: NL m 1)) (true ::: true ::: R)) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
  unfold NL
  rw [show d + 1 - (d + 1) = 0 by omega, show d + 1 - 1 = d by omega]
  refine Rch.tr (stepL (δ := delta) (by rfl)) ?_
  show Rch (cfgL PN1 (ones h (F ::: F ::: F ::: ones (d + 1) blank)) _) _
  sLn h; gL; gL; gL
  gR; gR; gL
  show Rch (cfgL s3 (ones (d + 2) blank) (F ::: F ::: ones h (F ::: true ::: R))) _
  sLn (d + 2); gR; gR; gR
  simp only [tl_blank, cons_blank]
  sRn d; gR; gR; sRn h; gR; gL0; gL
  fin

/-- the next position of the N hole -/
def nx (m c : Nat) : Nat := if c < m then c + 1 else 1

theorem unit_any (m c h : Nat) (R : Strm) (hc1 : 1 ≤ c) (hc : c ≤ m) :
    Rch ⟨p2, ones h (F ::: F ::: NL m c), true ::: true ::: R⟩
      (cfgL p2 (ones h (F ::: F ::: NL m (nx m c))) (true ::: true ::: R)) := by
  unfold nx
  split
  · exact unit_step m c h R hc1 (by omega)
  · obtain rfl : c = m := by omega
    exact unit_wrap c h R hc1

theorem test_step (m c lam K j : Nat) (hc1 : 1 ≤ c) (hc : c ≤ m) (hj : j + 2 < lam) :
    Rch (TP m c lam K (j + 1)) (TP m (nx m c) lam K j) := by
  obtain ⟨e, he⟩ : ∃ e, lam - (j + 1) = e + 2 := ⟨lam - j - 3, by omega⟩
  unfold TP
  rw [he, show lam - j = e + 3 by omega]
  exact unit_any m c (j + 1) _ hc1 hc

/-- the test is over: `p2` on the separator left of `L` -/
def TE (m c lam K : Nat) : Cfg St := cfgL p2 (F ::: F ::: NL m c) (ones lam (F ::: ones K blank))

theorem test_last (m c lam K : Nat) (hc1 : 1 ≤ c) (hc : c ≤ m) (hl : 2 ≤ lam) :
    Rch (TP m c lam K 0) (TE m (nx m c) lam K) := by
  obtain ⟨e, rfl⟩ : ∃ e, lam = e + 2 := ⟨lam - 2, by omega⟩
  exact unit_any m c 0 _ hc1 hc


/-! ## end of the test -/

theorem te_halt (m lam K : Nat) : HaltAt (TE m m lam K) := by
  unfold TE NL HaltAt; apply Exists.intro; apply Exists.intro
  rw [show m - m = 0 by omega]
  gL; gL; gL0
  fin

/-- the copy phase: `PG1` right of the N hole at cell `a` -/
def PGc (m a lam K q : Nat) : Cfg St :=
  ⟨PG1, F ::: ones a blank, ones (m - a) (F ::: F ::: ones lam (F ::: ones K (F ::: ones q blank)))⟩

theorem ones_tt (a b : Nat) (X : Strm) : ones a (true ::: ones b (true ::: X)) = ones (a + b + 2) X := by
  rw [← ones_succ', ← ones_succ', ones_add, show a + 1 + (b + 1) = a + b + 2 by omega]

/-- not divisible: fill the N hole, grow N on the left, its hole at cell 1 -/
theorem te_grow (m c lam K : Nat) (hc1 : 1 ≤ c) (hc : c < m) :
    Rch (TE m c lam K) (PGc (m + 1) 1 lam K 0) := by
  obtain ⟨d, hd⟩ : ∃ d, m - c = d + 1 := ⟨m - c - 1, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  unfold TE NL PGc
  rw [hd]
  rw [ones_succ]
  gL; gL; gL; sLn d; gL; sLn (c' + 1); gR
  rw [ones_succ]; gR
  simp only [tl_blank, ones_zero, cons_blank]
  rw [ones_tt, show c' + d + 2 = m + 1 - 1 by omega]; fin


/-! ## the copies -/

theorem ones_cons_blank (s : Nat) : ones s (true ::: blank) = ones (s + 1) blank := (ones_succ' s blank).symm

/-- copy loop: the cursor at `f_b`, the head on the marker `m2` -/
def X (m a lam K b q : Nat) : Cfg St :=
  ⟨x1, ones (K - b - 1) (F ::: ones b (F ::: ones lam (F ::: F ::: NL m a))), F ::: ones q blank⟩

/-- find the marker, put the cursor at `f_0` -/
theorem pg_to_x (m a lam K q : Nat) (hK : 1 ≤ K) : Rch (PGc m a lam K q) (X m a lam K 0 q) := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  unfold PGc X NL
  rw [ones_succ]
  sRn (m - a); gR; gR; sRn lam; gR; gR; sRn k
  rw [show k + 1 - 0 - 1 = k by omega]; fin

/-- copy one cell, not the last one -/
theorem copy_one (m a lam K b q : Nat) (hb : b + 1 < K) :
    Rch (X m a lam K b q) (X m a lam K (b + 1) (q + 1)) := by
  obtain ⟨e, he⟩ : ∃ e, K - b - 1 = e + 1 := ⟨K - b - 2, by omega⟩
  unfold X
  rw [he, show K - (b + 1) - 1 = e by omega]
  gR; sRn q; refine blankR ?_; gL0
  show Rch (cfgL y0 (ones q (F ::: ones (e + 1) (F ::: ones b (F ::: ones lam (F ::: F ::: NL m a)))))
    (true ::: blank)) _
  sLn q; gL; sLn (e + 1); gR; gR; sRn e
  rw [ones_cons_blank]; fin

/-- the last cell: back to the N hole -/
theorem copy_last (m a lam K b q : Nat) (hb : b + 1 = K) (ha : 1 ≤ a) (ha' : a ≤ m) :
    Rch (X m a lam K b q)
      ⟨c1, ones a blank, F ::: ones (m - a) (F ::: F ::: ones lam (F ::: ones K (F ::: ones (q + 1) blank)))⟩ := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  unfold X NL
  rw [show K - b - 1 = 0 by omega, ones_zero]
  gR; sRn q; refine blankR ?_; gL0
  show Rch (cfgL y0 (ones q (F ::: F ::: ones b (F ::: ones lam (F ::: F ::: ones (m - (a' + 1))
    (F ::: ones (a' + 1) blank))))) (true ::: blank)) _
  sLn q; gL; gR; gL0
  show Rch (cfgL z1 (ones (b + 1) (F ::: ones lam (F ::: F ::: ones (m - (a' + 1)) (F ::: ones (a' + 1) blank))))
    (F ::: ones q (true ::: blank))) _
  rw [ones_succ a' blank]
  sLn (b + 1); gL; sLn lam; gL; gL; sLn (m - (a' + 1)); gL; gR
  rw [ones_cons_blank, ← hb]; fin

theorem c_next (m a lam K q : Nat) (ha : a < m) :
    Rch ⟨c1, ones a blank, F ::: ones (m - a) (F ::: F ::: ones lam (F ::: ones K (F ::: ones q blank)))⟩
      (PGc m (a + 1) lam K q) := by
  obtain ⟨e, he⟩ : ∃ e, m - a = e + 1 := ⟨m - a - 1, by omega⟩
  unfold PGc
  rw [he, show m - (a + 1) = e by omega, ones_succ]
  gR; gR; fin

/-- the copy before the merge: the N hole at cell `m` again -/
def PMc (m lam K q : Nat) : Cfg St :=
  ⟨PM1, F ::: ones m blank, F ::: F ::: ones lam (F ::: ones K (F ::: ones q blank))⟩

theorem c_fall (m lam K q : Nat) (hm : 1 ≤ m) :
    Rch ⟨c1, ones m blank, F ::: ones (m - m) (F ::: F ::: ones lam (F ::: ones K (F ::: ones q blank)))⟩
      (PMc m lam K q) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
  unfold PMc
  rw [show d + 1 - (d + 1) = 0 by omega, ones_zero]
  gR; gL0; gR; fin

/-- merge: fill the marker `m1` (`L := L + 1 + F`), `Q` is the new `F`, the test starts -/
theorem merge (m lam K q : Nat) (hK : 1 ≤ K) :
    Rch (PMc m lam K q) (TP m m (lam + 1 + K) q (lam + K - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  unfold PMc TP NL
  rw [ones_succ k]
  gR; gR; sRn lam; gR; gL0; gR
  show Rch ⟨m2, ones (lam + 1) (F ::: F ::: F ::: ones m blank), ones (k + 1) (F ::: ones q blank)⟩ _
  sRn (k + 1); gL0; gL
  rw [ones_add, show m - m = 0 by omega, ones_zero,
    show lam + 1 + (k + 1) - (lam + (k + 1) - 1) = 2 by omega, show k + (lam + 1) = lam + (k + 1) - 1 + 1 by omega]
  fin

end TM.Kurepa
