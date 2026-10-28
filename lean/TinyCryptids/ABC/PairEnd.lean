import TinyCryptids.ABC.Round

/-!
# The end of a pair: erase `R` and `Q`, the next pair, `R := 1`, `d := 2`

At `pe0` the head is on `M`; left of it `K` (one cell), `D` (no hole), `A`, `B`, `C` (no
marker); right of it `R` and possibly `Q` (a list `w` with zero runs of length one or two).
-/

namespace TM.ABC
open St

local notation "F" => false
local notation "T" => true

/-- the tape left of `M` -/
def lM (k d a b c : Nat) : Strm :=
  F ::: F ::: ones (c + 2) (F ::: F ::: ones (b + 2) (F ::: F ::: ones (a + 2) (F ::: F :::
    ones (d + 2) (F ::: F ::: ones k blank))))

/-- the configuration at `pe0`: on `M`, with `w` right of `M`'s separator -/
def peC (k d a b c : Nat) (w : List Bool) : Cfg St := ⟨pe0, lM k d a b c, T ::: F ::: F ::: app w blank⟩

theorem pe_cross {w : List Bool} (hw : Clean12 w) (L : Strm) :
    Rch ⟨pe1, L, app w blank⟩ ⟨pe1, zeros w.length L, blank⟩ := by
  induction hw generalizing L with
  | nil => fin
  | @one l _ ih =>
    show Rch ⟨pe1, L, T ::: app l blank⟩ _
    gR
    refine Rch.tr (ih _) ?_
    rw [List.length_cons, zeros_succ']; fin
  | @z1 l _ ih =>
    show Rch ⟨pe1, L, F ::: T ::: app l blank⟩ _
    gR; gR
    refine Rch.tr (ih _) ?_
    rw [List.length_cons, List.length_cons, zeros_succ', zeros_succ']; fin
  | @z2 l _ ih =>
    show Rch ⟨pe1, L, F ::: F ::: T ::: app l blank⟩ _
    gR; gR; gR
    refine Rch.tr (ih _) ?_
    rw [List.length_cons, List.length_cons, List.length_cons, zeros_succ', zeros_succ', zeros_succ']; fin

/-- erase everything right of `M`, back on `M` -/
theorem pe_erase (k d a b c : Nat) {w : List Bool} (hw : Clean12 (T :: w)) :
    Rch (peC k d a b c (T :: w)) (cfgL eb1 (lM k d a b c) (T ::: blank)) := by
  unfold peC
  gR
  have hw2 : Clean12 (F :: F :: T :: w) := by
    cases hw with | one h => exact Clean12.z2 h
  refine Rch.tr (pe_cross hw2 _) ?_
  refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gL
  show Rch (cfgL pe4 (zeros ((F :: F :: T :: w).length + 2) (T ::: lM k d a b c)) (F ::: blank)) _
  zLn ((F :: F :: T :: w).length + 2)
  gL
  simp only [zeros_blank, cons_blank]
  fin

/-! ## the one-cell-block finder (`MF`, `MW`, `MK`) -/

/-- runs of 1s and separators `00`, each separator followed by a block of at least two cells -/
inductive FC : List Bool → Prop
  | nil : FC []
  | one {l} : FC l → FC (T :: l)
  | sep {l} : FC l → FC (F :: F :: T :: T :: l)

theorem FC.append {l m : List Bool} (hl : FC l) (hm : FC m) : FC (l ++ m) := by
  induction hl with
  | nil => exact hm
  | one _ ih => exact FC.one ih
  | sep _ ih => exact FC.sep ih

theorem FC.rep (n : Nat) : FC (List.replicate n T) := by
  induction n with
  | zero => exact FC.nil
  | succ n ih => exact FC.one ih

/-- a separator and a block of at least two cells, then more -/
theorem FC.sepblk (v : Nat) {m : List Bool} (h : FC m) : FC (F :: F :: List.replicate (v + 2) T ++ m) := by
  show FC (F :: F :: T :: T :: (List.replicate v T ++ m))
  exact FC.sep ((FC.rep v).append h)

structure Finder (p1 p2 p3 p4 : St) : Prop where
  h1 : deltaQ p1 true = some (true, Dir.R, p1)
  h0 : deltaQ p1 false = some (false, Dir.R, p2)
  i1 : deltaQ p2 true = some (true, Dir.R, p1)
  i0 : deltaQ p2 false = some (false, Dir.R, p3)
  j1 : deltaQ p3 true = some (true, Dir.R, p4)
  k1 : deltaQ p4 true = some (true, Dir.R, p1)

theorem Finder.cross {p1 p2 p3 p4 : St} (P : Finder p1 p2 p3 p4) {w : List Bool} (hw : FC w)
    (L R : Strm) : Rch ⟨p1, L, app w R⟩ ⟨p1, app w.reverse L, R⟩ := by
  induction hw generalizing L with
  | nil => fin
  | @one l _ ih =>
    refine Rch.tr (sR P.h1) ?_
    simpa [app_append] using ih (T ::: L)
  | @sep l _ ih =>
    refine Rch.tr (sR P.h0) ?_
    refine Rch.tr (sR P.i0) ?_
    refine Rch.tr (sR P.j1) ?_
    refine Rch.tr (sR P.k1) ?_
    simpa [app_append] using ih (T ::: T ::: F ::: F ::: L)

/-- across `w` to the one-cell block `M`; the head on the 0 right of `M`, in `p4` -/
theorem Finder.find {p1 p2 p3 p4 : St} (P : Finder p1 p2 p3 p4) {w : List Bool} (hw : FC w)
    (L R : Strm) :
    Rch ⟨p1, L, app w (F ::: F ::: T ::: F ::: R)⟩ ⟨p4, T ::: F ::: F ::: app w.reverse L, F ::: R⟩ := by
  refine Rch.tr (P.cross hw L _) ?_
  refine Rch.tr (sR P.h0) ?_
  refine Rch.tr (sR P.i0) ?_
  exact sR P.j1

theorem FMF : Finder MF1 MF2 MF3 MF4 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem FMW : Finder MW1 MW2 MW3 MW4 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem FMK : Finder MK1 MK2 MK3 MK4 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## `R := 1`, to the left end, `d := 2` -/

theorem fl_cross {w : List Bool} (hw : Clean12 w) (s R : Strm) :
    Rch (cfgL fla (app w s) R) (cfgL fla s (app w.reverse R)) := by
  induction hw generalizing R with
  | nil => fin
  | @one l _ ih =>
    show Rch (cfgL fla (T ::: app l s) R) _
    gL
    simpa [app_append] using ih (T ::: R)
  | @z1 l _ ih =>
    show Rch (cfgL fla (F ::: T ::: app l s) R) _
    gL; gL
    simpa [app_append] using ih (T ::: F ::: R)
  | @z2 l _ ih =>
    show Rch (cfgL fla (F ::: F ::: T ::: app l s) R) _
    gL; gL; gL
    simpa [app_append] using ih (T ::: F ::: F ::: R)

/-- to the left end: on the leftmost cell (of `K`), state `dr1` -/
theorem fl_go {v : List Bool} (hv : Clean12 v) (R : Strm) :
    Rch (cfgL fla (app v blank) R) ⟨dr1, blank, app v.reverse R⟩ := by
  refine Rch.tr (fl_cross hv _ R) ?_
  show Rch (cfgL fla (F ::: blank) _) _
  gL
  show Rch (cfgL flb (F ::: blank) _) _
  gL
  show Rch (cfgL flc (F ::: blank) _) _
  gR; gR; gR
  simp only [tl_blank, cons_blank]; fin

/-- `d := 2`: the `K|D` separator moves right until `D` has four cells; then `D`'s hole and
`A`'s marker: the first test of the pair -/
theorem dr_loop (Ra : Strm) : ∀ n k, 1 ≤ k →
    Rch ⟨dr3, F ::: F ::: ones k blank, ones (n + 4) (F ::: F ::: T ::: T ::: Ra)⟩
      (fT (k + n) 2 (F ::: F ::: T ::: F ::: Ra) ca1) := by
  intro n
  induction n with
  | zero =>
    intro k hk
    show Rch ⟨dr3, _, T ::: T ::: T ::: T ::: F ::: F ::: T ::: T ::: Ra⟩ _
    gR; gR; gR; gR; gL; gL; gL; gR; gR; gR; gR; gR; gR; gL
    show Rch (cfgL GD1 (T ::: F ::: F ::: T ::: T ::: F ::: T ::: F ::: F ::: ones k blank) (F ::: Ra)) _
    have hw : Clean (T :: F :: F :: List.replicate 2 T) := Clean.one (Clean.sep (Clean.one Clean.nil))
    refine Rch.tr (pLR PGD rfl hw (F ::: F ::: ones k blank) (F ::: Ra)) ?_
    unfold fT; fin
  | succ n ih =>
    intro k hk
    show Rch ⟨dr3, _, T ::: T ::: T ::: T ::: T ::: ones n (F ::: F ::: T ::: T ::: Ra)⟩ _
    gR; gR; gR; gR; gL; gL; gL; gL; gL; gL
    show Rch (cfgL drM (F ::: ones k blank) _) _
    gR; gR; gR
    have := ih (k + 1) (by omega)
    rw [show k + 1 + n = k + (n + 1) by omega] at this
    exact this

theorem dr_go (Ra : Strm) (k d : Nat) (hk : 1 ≤ k) (hd : 2 ≤ d) :
    Rch ⟨dr1, blank, ones k (F ::: F ::: ones (d + 2) (F ::: F ::: T ::: T ::: Ra))⟩
      (fT (k + d - 2) 2 (F ::: F ::: T ::: F ::: Ra) ca1) := by
  sRn k; gR; gR
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  have := dr_loop Ra n k hk
  rw [show k + (n + 2) - 2 = k + n by omega]
  exact this

/-- after the next pair is on the tape: `R := 1` after `M`, to the left end, `d := 2`, `A`'s
marker; `w` is the tape between `R`'s hole and `K`'s second cell, `K` of `k` cells -/
theorem wr_go (k d a b c : Nat) (hk : 1 ≤ k) (hd : 2 ≤ d) :
    Rch ⟨wr1, F ::: T ::: F ::: F ::: ones (c + 2) (F ::: F ::: ones (b + 2) (F ::: F ::: ones (a + 2)
        (F ::: F ::: ones (d + 2) (F ::: F ::: ones k blank)))), blank⟩
      (stA (k + d - 2) 2 a b c 1) := by
  refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gLc
  refine toL ?_
  have h4 : ∀ v (m : List Bool), Clean m → Clean (F :: F :: List.replicate (v + 2) T ++ m) := by
    intro v m hm
    have := Clean.sepBk v hm; simpa [S2, Bk] using this
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hw : Clean12 (F :: T :: F :: F :: T :: (F :: F :: List.replicate (c + 2) T ++ (F :: F ::
      List.replicate (b + 2) T ++ (F :: F :: List.replicate (a + 2) T ++ (F :: F :: List.replicate (d + 2) T ++
      (F :: F :: List.replicate (k' + 1) T)))))) :=
    Clean12.z1 (Clean12.z2 (Clean12.of_clean (h4 c _ (h4 b _ (h4 a _ (h4 d _
      (Clean.sep (Clean.replicate k'))))))))
  rw [show (F ::: T ::: F ::: F ::: T ::: F ::: F ::: ones (c + 2) (F ::: F ::: ones (b + 2) (F ::: F :::
      ones (a + 2) (F ::: F ::: ones (d + 2) (F ::: F ::: ones (k' + 1) blank))))) =
      app (F :: T :: F :: F :: T :: (F :: F :: List.replicate (c + 2) T ++ (F :: F ::
      List.replicate (b + 2) T ++ (F :: F :: List.replicate (a + 2) T ++ (F :: F :: List.replicate (d + 2) T ++
      (F :: F :: List.replicate (k' + 1) T)))))) blank by
    simp only [List.cons_append, app_cons, app_append, app_replicate]]
  refine Rch.tr (fl_go hw _) ?_
  have := dr_go (ones a (F ::: F ::: ones (b + 2) (F ::: F ::: ones (c + 2) (F ::: F ::: T ::: F ::: F :::
    T ::: F ::: T ::: blank)))) (k' + 1) d (by omega) hd
  simp only [List.reverse_cons, List.reverse_append, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, app_append,
    app_replicate, app_cons, app_nil]
  simp only [stA, fT, fr, blkx, Bm, Bk, S2, List.append_assoc, List.cons_append, List.singleton_append,
    List.nil_append, app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero] at this ⊢
  exact this

/-- `b ≥ 2`: the next pair is `(a + 1, b - 1)` (the `A|B` separator one cell right) -/
theorem next_ab (k d a b c : Nat) (hk : 1 ≤ k) (hd : 2 ≤ d) :
    Rch (cfgL eb1 (lM k d a (b + 2) c) (T ::: blank)) (stA (k + d - 2) 2 (a + 1) (b + 1) c 1) := by
  unfold lM
  gL; gL; sLn (c + 2); gL; gL
  rw [show ones (b + 2 + 2) (F ::: F ::: ones (a + 2) (F ::: F ::: ones (d + 2) (F ::: F ::: ones k blank))) =
    T ::: T ::: T ::: T ::: ones b (F ::: F ::: ones (a + 2) (F ::: F ::: ones (d + 2) (F ::: F ::: ones k blank)))
    from by rw [show b + 2 + 2 = b + 4 by omega]; rfl]
  gL; gL; gL; gL; sLn b; gL
  refine fromL ?_
  gR; gR; rw [ones_cons_true]; gR
  have hw : FC (List.replicate (b + 3) T ++ F :: F :: List.replicate (c + 2) T) :=
    (FC.rep _).append (by simpa using FC.sepblk c FC.nil)
  rw [show ones b (T ::: T ::: T ::: F ::: F ::: ones (c + 2) (F ::: F ::: T ::: blank)) =
    app (List.replicate (b + 3) T ++ F :: F :: List.replicate (c + 2) T) (F ::: F ::: T ::: F ::: blank) by
    simp only [List.cons_append, app_append, app_cons, app_replicate, cons_blank]
    rw [← ones_succ', ← ones_succ', ← ones_succ']]
  refine Rch.tr (FMW.find hw _ _) ?_
  gR
  have := wr_go k d (a + 1) (b + 1) c hk hd
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, app_append,
    app_replicate, app_cons, app_nil, cons_blank] at this ⊢
  rw [show b + 1 + 2 = b + 3 by omega, show a + 1 + 2 = (a + 2) + 1 by omega, ones_succ] at this
  exact this

/-! ## `c += 1`: `A := 1`, `K += 1`, `C += 1`, `B := c` -/

/-- `A := 1`: the `A|B` separator moves left until `A` has three cells -/
theorem a_loop (Ld Rr : Strm) : ∀ n m,
    Rch (cfgL cab (F ::: ones (n + 3) (F ::: F ::: Ld)) (F ::: ones m Rr))
      (cfgL fk2 (F ::: Ld) (F ::: T ::: T ::: T ::: F ::: F ::: ones (m + n) Rr)) := by
  intro n
  induction n with
  | zero =>
    intro m
    show Rch (cfgL cab (F ::: T ::: T ::: T ::: F ::: F ::: Ld) _) _
    gL; gL; gL; gL; gL; fin
  | succ n ih =>
    intro m
    show Rch (cfgL cab (F ::: T ::: T ::: T ::: T ::: ones n (F ::: F ::: Ld)) _) _
    gL; gL; gL; gL
    refine fromL ?_
    gR; gR; gR; gR; gR; gL; gL
    have := ih (m + 1)
    rw [show m + 1 + n = m + (n + 1) by omega] at this
    show Rch (cfgL cab (F ::: ones (n + 3) (F ::: F ::: Ld)) (F ::: ones (m + 1) Rr)) _
    exact this

theorem fk_cross {w : List Bool} (hw : Clean12 w) (s R : Strm) :
    Rch (cfgL fk1 (app w s) R) (cfgL fk1 s (app w.reverse R)) := by
  induction hw generalizing R with
  | nil => fin
  | @one l _ ih =>
    show Rch (cfgL fk1 (T ::: app l s) R) _
    gL
    simpa [app_append] using ih (T ::: R)
  | @z1 l _ ih =>
    show Rch (cfgL fk1 (F ::: T ::: app l s) R) _
    gL; gL
    simpa [app_append] using ih (T ::: F ::: R)
  | @z2 l _ ih =>
    show Rch (cfgL fk1 (F ::: F ::: T ::: app l s) R) _
    gL; gL; gL
    simpa [app_append] using ih (T ::: F ::: F ::: R)

/-- `K += 1`: to the left end, a new cell there; then `MK1` on `K`'s old first cell -/
theorem fk_go (d k : Nat) (R : Strm) (hk : 1 ≤ k) :
    Rch (cfgL fk2 (F ::: ones (d + 2) (F ::: F ::: ones k blank)) R)
      ⟨MK1, T ::: blank, ones k (F ::: F ::: ones (d + 2) (F ::: R))⟩ := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  gL
  rw [show ones (d + 2) (F ::: F ::: ones (k' + 1) blank) =
    T ::: app (List.replicate (d + 1) T ++ F :: F :: List.replicate (k' + 1) T) blank by
    simp only [List.cons_append, app_append, app_cons, app_replicate, ones_succ]]
  gL
  have hw : Clean12 (List.replicate (d + 1) T ++ F :: F :: List.replicate (k' + 1) T) :=
    Clean12.of_clean (Clean.rep_append _ (Clean.sep (Clean.replicate k')))
  refine Rch.tr (fk_cross hw _ _) ?_
  show Rch (cfgL fk1 (F ::: blank) _) _
  gL
  show Rch (cfgL fk2 (F ::: blank) _) _
  gL
  show Rch (cfgL fk3 (F ::: blank) _) _
  gR; gR; gR
  simp only [tl_blank, cons_blank, List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
    app_append, app_replicate, app_cons, app_nil, ones_succ]
  rw [ones_cons_true]; fin

/-- `b = 1`: the next pair is `(1, c)` with `c + 1` (from `(a, 1)`, `a + 1 = c`) -/
theorem next_c (k d a c : Nat) (hk : 1 ≤ k) (hd : 2 ≤ d) (ha : 1 ≤ a) (hac : a + 1 = c) :
    Rch (cfgL eb1 (lM k d a 1 c) (T ::: blank)) (stA (k + 1 + d - 2) 2 1 c (c + 1) 1) := by
  unfold lM
  gL; gL; sLn (c + 2); gL; gL; gL; gL; gL; gL
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  show Rch (cfgL cab (F ::: ones (n + 3) (F ::: F ::: ones (d + 2) (F ::: F ::: ones k blank)))
    (F ::: ones 3 (F ::: F ::: ones (c + 2) (F ::: F ::: T ::: blank)))) _
  refine Rch.tr (a_loop _ _ n 3) ?_
  refine Rch.tr (fk_go d k _ hk) ?_
  have hw : FC (List.replicate k T ++ (F :: F :: List.replicate (d + 2) T ++ (F :: F :: List.replicate (1 + 2) T ++
      (F :: F :: List.replicate (n + 1 + 2) T ++ (F :: F :: List.replicate (c + 2) T))))) :=
    (FC.rep k).append (FC.sepblk d (FC.sepblk 1 (FC.sepblk (n + 1) (by simpa using FC.sepblk c FC.nil))))
  rw [show ones k (F ::: F ::: ones (d + 2) (F ::: F ::: T ::: T ::: T ::: F ::: F ::: ones (3 + n)
      (F ::: F ::: ones (c + 2) (F ::: F ::: T ::: blank)))) =
    app (List.replicate k T ++ (F :: F :: List.replicate (d + 2) T ++ (F :: F :: List.replicate (1 + 2) T ++
      (F :: F :: List.replicate (n + 1 + 2) T ++ (F :: F :: List.replicate (c + 2) T)))))
      (F ::: F ::: T ::: F ::: blank) by
    simp only [List.cons_append, List.append_assoc, app_append, app_cons, app_replicate, cons_blank]
    rw [show 3 + n = n + 1 + 2 by omega]; rfl]
  refine Rch.tr (FMK.find hw _ _) ?_
  gR; refine blankR ?_; gL; gL; gL; gL; gL
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, app_append,
    app_replicate, app_cons, app_nil]
  sLn (c + 2); gL
  refine fromL ?_
  gR; gR
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  rw [show ones (c' + 1 + 2) (T ::: T ::: F ::: F ::: T ::: blank) =
    T ::: ones (c' + 1 + 2 + 1) (F ::: F ::: T ::: blank) by
    rw [show c' + 1 + 2 = c' + 3 by omega, ones_cons_true, ones_cons_true, ← ones_succ, ← ones_succ]]
  gR
  have hw2 : FC (List.replicate (c' + 1 + 2 + 1) T) := FC.rep _
  rw [show ones (c' + 1 + 2 + 1) (F ::: F ::: T ::: blank) =
    app (List.replicate (c' + 1 + 2 + 1) T) (F ::: F ::: T ::: F ::: blank) by
    simp only [app_replicate, cons_blank]]
  refine Rch.tr (FMW.find hw2 _ _) ?_
  gR
  have := wr_go (k + 1) d 1 (c' + 1) (c' + 1 + 1) (by omega) hd
  simp only [List.reverse_replicate, app_replicate, cons_blank, ones_succ] at this ⊢
  obtain rfl : c' = n + 1 := by omega
  simp only [ones_succ, ones_cons_true] at this ⊢
  exact this

/-! ## not coprime: a hit on `A` or `B` at `d = c` (`K` of one cell) -/

/-- fill `D`'s hole, then to `M` -/
theorem nc_go {w : List Bool} (hw : FC w) (R : Strm) :
    Rch ⟨nc1, F ::: blank, T ::: F ::: F ::: T ::: F ::: app w (F ::: F ::: T ::: F ::: R)⟩
      ⟨pe0, F ::: F ::: app w.reverse (T ::: T ::: F ::: F ::: T ::: F ::: blank), T ::: F ::: R⟩ := by
  gR; gR; gR; gR; gR
  refine Rch.tr (FMF.find hw _ _) ?_
  refine Rch.tr (stepL (δ := deltaQ) rfl) ?_
  fin

theorem hitA_nc (d a b c r : Nat) (hd : 2 ≤ d) (ha : 1 ≤ a) (h : Nat.gcd a d ≠ 1) :
    Rch (stA 1 d a b c r) (peC 1 d a b c (Bm r)) := by
  rw [stA_eq]
  have h1 := (gcd_run gap_A (F ::: ones 1 blank) (RcA b c r) a d ha hd).2 h
  simp only [RcA] at h1
  refine Rch.tr h1 ?_
  refine Rch.tr (h_next_nc gap_A (RcB c r) d a b (by omega) ha) ?_
  have hw : FC (List.replicate d T ++ S2 ++ [T] ++ T :: List.replicate a T ++ F :: F :: List.replicate (b + 2) T ++
      F :: F :: List.replicate (c + 2) T) := by
    have := (FC.rep d).append (FC.sepblk a (FC.sepblk b (FC.sepblk c FC.nil)))
    simpa [S2] using this
  have hn := nc_go hw (F ::: app (Bm r) blank)
  simp only [RcB, RcC, S2, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
    List.reverse_cons, List.reverse_append, List.reverse_replicate, List.reverse_nil, app_append,
    app_replicate, app_cons, app_nil, ones_succ, ones_zero, ones_cons_true, cons_blank] at hn ⊢
  refine Rch.tr hn ?_
  unfold peC lM
  simp only [ones_succ, ones_zero, ones_cons_true, cons_blank]
  fin

theorem hitB_nc (d a b c r : Nat) (hd : 2 ≤ d) (hb : 1 ≤ b) (h : Nat.gcd b d ≠ 1) :
    Rch (stB 1 d a b c r) (peC 1 d a b c (Bm r)) := by
  rw [stB_eq]
  have h1 := (gcd_run (gap_B a) (F ::: ones 1 blank) (RcB c r) b d hb hd).2 h
  simp only [RcB] at h1
  refine Rch.tr h1 ?_
  refine Rch.tr (h_next_nc (gap_B a) (RcC r) d b c (by omega) hb) ?_
  have hw : FC (List.replicate d T ++ gB a ++ [T] ++ T :: List.replicate b T ++ F :: F ::
      List.replicate (c + 2) T) := by
    have := (FC.rep d).append (FC.sepblk a (FC.sepblk b (FC.sepblk c FC.nil)))
    simpa [gB, S2, Bk, List.replicate_succ] using this
  have hn := nc_go hw (F ::: app (Bm r) blank)
  simp only [RcC, gB, Bk, S2, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
    List.reverse_cons, List.reverse_append, List.reverse_replicate, List.reverse_nil, app_append,
    app_replicate, app_cons, app_nil, ones_succ, ones_zero, ones_cons_true, cons_blank] at hn ⊢
  refine Rch.tr hn ?_
  unfold peC lM
  simp only [ones_succ, ones_zero, ones_cons_true, cons_blank]
  fin

end TM.ABC
