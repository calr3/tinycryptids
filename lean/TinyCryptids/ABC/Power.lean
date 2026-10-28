import TinyCryptids.ABC.PairEnd
import TinyCryptids.ABC.Compare

/-!
# The pre-test and the power phase

Pre-test: compare `C` with `R`.  `c ≤ R`: the pair is skipped (to `M`, `pe0`); `c > R`: the
power phase, `P := 1` at the left end, `Q := 1` at the right end, `Q := Q * R`, then the loop:
compare `P` with `Q`; `P ≤ Q`: BEEP, `P := P * c`, `Q := Q * R`; `P > Q`: BOOP.
-/

namespace TM.ABC
open St

local notation "F" => false
local notation "T" => true

/-- a run that leaves its first configuration's state continues from its first step -/
theorem Rch.of_step {a b c : Cfg St} (hs : step deltaQ a = some b) (h : Rch a c) (hne : a.q ≠ c.q) :
    Rch b c := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => cases hn; exact absurd rfl hne
  | succ n =>
    have hn : run deltaQ (n + 1) a = some c := hn
    simp only [run, Sys.run, hs] at hn
    exact ⟨n, hn⟩

/-- the stream left of `C`'s cell 0 in the pre-test -/
def lC (d a b : Nat) : Strm :=
  F ::: F ::: ones (b + 2) (F ::: F ::: ones (a + 2) (F ::: F ::: ones (d + 2) (F ::: F ::: T ::: blank)))

/-- the gap between `C` and `R`: `00 M 00` -/
def gCR : List Bool := [F, F, T, F, F]

theorem gap_CR : Gap gCR := Or.inr ⟨[T], Blk_M, rfl⟩

theorem pre_entry (a b c r : Nat) (hc : 2 ≤ c) (hr : 1 ≤ r) :
    Rch ⟨pt1, app (preL c a b c) blank, F ::: ones r blank⟩ (cmpA (lC c a b) c c gCR r 1 (F ::: blank)) := by
  simp only [preL, Bk, S2, List.reverse_cons, List.reverse_append, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, app_append,
    app_replicate, app_cons, app_nil]
  gL0
  show Rch (cfgL pt2 (T ::: F ::: F ::: T ::: F ::: F ::: ones (c + 2) (lC c a b)) _) _
  gL; gL; gL; gL; gL; gL; gL; gL
  unfold cmpA yR gCR
  simp only [cons_blank, show c + 1 - c = 1 by omega, Nat.add_sub_cancel, ones_succ, ones_zero, app_cons, app_nil]
  fin

theorem PSK : ParserR deltaQ SK1 SK2 := ⟨rfl, rfl, rfl⟩

/-- the pre-test fails (`c ≤ r`): fill `R`'s cursor, to `M`: the pair is skipped -/
theorem pre_skip (a b c r : Nat) (hc : 2 ≤ c) (hcr : c ≤ r) :
    Rch (cmpA (lC c a b) c c gCR r 1 (F ::: blank)) (peC 1 c a b c (Bk r)) := by
  refine Rch.tr ((compare gap_CR _ blank c r (by omega) (by omega)).1 hcr) ?_
  gL
  show Rch (cfgL xe3 (T ::: ones (b + 1) (F ::: F ::: ones (a + 2) (F ::: F ::: ones (c + 2) (F ::: F ::: T ::: blank)))) _) _
  refine fromL ?_; gR
  obtain ⟨m, hm⟩ : ∃ m, r + 1 - c = m + 1 := ⟨r - c, by omega⟩
  have hw : Clean ([F, F] ++ List.replicate (c + 2) T ++ gCR ++ List.replicate c T) := by
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [gCR, List.replicate_succ, List.cons_append, List.nil_append, List.append_assoc]
    exact Clean.sep (Clean.one (Clean.one (Clean.rep_append c' (Clean.sep (Clean.sep (Clean.replicate c'))))))
  unfold yR gCR
  rw [hm, show (F ::: F ::: ones (c + 2) (app [F, F, T, F, F] (ones c (F ::: ones (m + 1) (F ::: blank))))) =
    app ([F, F] ++ List.replicate (c + 2) T ++ [F, F, T, F, F] ++ List.replicate c T) (F ::: T ::: ones m (F ::: blank)) by
    simp only [List.cons_append, List.nil_append, List.append_assoc, app_cons, app_append, app_replicate, app_nil,
      ones_succ]]
  refine Rch.tr (pRL PSK rfl hw _ _) ?_
  gL
  simp only [gCR, List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, app_append,
    app_replicate, app_cons, app_nil]
  sLn c; gL; gL
  unfold peC lM
  rw [show (T ::: T ::: ones m (F ::: blank)) = ones (m + 2) blank by
    rw [cons_blank]; rfl, ones_add, show c + (m + 2) = r + 2 by omega]
  simp only [Bk, app_replicate, ones_succ, ones_zero]
  fin

/-! ## the power phase tape -/

/-- the stream left of `R`'s left separator's second cell: `M`, `C`, `B`, `A`, `D`, `K`, then
`P` (value `p`, cursor on its last position) -/
def lbR (a b c p : Nat) : Strm :=
  F ::: T ::: F ::: F ::: ones (c + 2) (F ::: F ::: ones (b + 2) (F ::: F ::: ones (a + 2) (F ::: F :::
    ones (c + 2) (F ::: F ::: T ::: F ::: F ::: T ::: F ::: ones p blank))))

/-- entering `Q := Q * R`: the base hole (cell 1 of `R`) just advanced -/
def qE (a b c r p q : Nat) : Cfg St :=
  ⟨Rba2, T ::: T ::: F ::: lbR a b c p, ones r (Mt.rgt S2 q 0)⟩

/-- between `P` and `Q`: `00 K 00 D 00 A 00 B 00 C 00 M 00 R 00` -/
def gPQ (a b c r : Nat) : List Bool :=
  S2 ++ [T] ++ S2 ++ Bk c ++ S2 ++ Bk a ++ S2 ++ Bk b ++ S2 ++ Bk c ++ S2 ++ [T] ++ S2 ++ Bk r ++ S2

theorem gap_PQ (a b c r : Nat) : Gap (gPQ a b c r) := by
  have h := (((((Blk_M.join (Blk_Bk c)).join (Blk_Bk a)).join (Blk_Bk b)).join (Blk_Bk c)).join Blk_M).join
    (Blk_Bk r)
  exact Or.inr ⟨_, h, by simp [gPQ, S2]⟩

/-- the compare of the loop: `P`'s hole (its last position) just filled, `Q`'s cursor on 1 -/
def loopA (a b c r p q : Nat) : Cfg St :=
  cmpA (F ::: F ::: blank) p p (gPQ a b c r) q 1 (F ::: blank)

theorem PZD' : ParserL deltaQ ZD1 ZD2 := ⟨rfl, rfl, rfl⟩
theorem PRB : ParserL deltaQ RB1 RB2 := ⟨rfl, rfl, rfl⟩
theorem PPX : ParserL deltaQ PX1 PX2 := ⟨rfl, rfl, rfl⟩

/-- `Q := Q * R`, then back to `P`'s cursor: the compare -/
theorem q_mult (a b c r p q : Nat) (hr : 2 ≤ r) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Rch (qE a b c r p q) (loopA a b c r p (q * r)) := by
  have hm := multR gap_A (lbR a b c p) r q hr hq
  have hs : step deltaQ ⟨Rba1, ones 1 (F ::: lbR a b c p), F ::: ones r (Mt.rgt S2 q 0)⟩ =
      some (qE a b c r p q) := rfl
  refine Rch.tr (Rch.of_step hs hm (by intro h; cases h)) ?_
  obtain ⟨n, hn⟩ : ∃ n, q * r = n + 1 := ⟨q * r - 1, by have := Nat.mul_le_mul hq (show 1 ≤ r by omega); omega⟩
  rw [hn, show ones (n + 1) (F ::: T ::: app S2.reverse (ones r (F ::: T ::: F ::: lbR a b c p))) =
    app (List.replicate (n + 1) T) (F ::: T ::: app S2.reverse (ones r (F ::: T ::: F ::: lbR a b c p))) by
    rw [app_replicate]]
  refine Rch.tr (pLL PZD' rfl (Clean.replicate _) _ _) ?_
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
  show Rch (cfgL zd2 (F ::: F ::: T ::: T ::: ones r' (F ::: T ::: F ::: lbR a b c p)) _) _
  gL; gL; gL; gL
  rw [show ones r' (F ::: T ::: F ::: lbR a b c p) = app (List.replicate r' T) (F ::: T ::: F ::: lbR a b c p) by
    rw [app_replicate]]
  refine Rch.tr (pLR PRB rfl (Clean.replicate _) _ _) ?_
  gL
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  have h4 : ∀ v (m : List Bool), Clean m → Clean (F :: F :: (List.replicate (v + 2) T ++ m)) := by
    intro v m hm; have := Clean.sepBk v hm; simpa [S2, Bk] using this
  have hw : Clean ([T, F, F, T, F, F] ++ List.replicate (c + 2) T ++ [F, F] ++ List.replicate (b + 2) T ++ [F, F] ++
      List.replicate (a + 2) T ++ [F, F] ++ List.replicate (c + 2) T ++ [F, F, T, F, F, T]) := by
    simp only [List.cons_append, List.nil_append, List.append_assoc]
    exact Clean.one (Clean.sep (h4 c _ (h4 b _ (h4 a _ (h4 c _ (Clean.sep (Clean.sep Clean.nil)))))))
  show Rch (cfgL PX1 (T ::: F ::: lbR a b c (p' + 1)) _) _
  rw [show (T ::: F ::: lbR a b c (p' + 1)) = app ([T, F, F, T, F, F] ++ List.replicate (c + 2) T ++ [F, F] ++
      List.replicate (b + 2) T ++ [F, F] ++ List.replicate (a + 2) T ++ [F, F] ++ List.replicate (c + 2) T ++
      [F, F, T, F, F, T]) (F ::: T ::: ones p' blank) by
    simp only [lbR, List.cons_append, List.nil_append, List.append_assoc, app_cons, app_append, app_replicate,
      app_nil, ones_succ]]
  refine Rch.tr (pLR PPX rfl hw _ _) ?_
  gLc
  unfold loopA cmpA yR gPQ
  simp only [cons_blank, List.reverse_cons, List.reverse_append, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, app_append, app_replicate,
    app_cons, app_nil, Bk, S2, Mt.rgt, Mt.sep, ones_succ, ones_zero, Nat.add_sub_cancel, hn,
    show p' + 1 + 1 - (p' + 1) = 1 by omega, ones_cons_true]
  exact Reach.refl deltaQ _

theorem blankL {q : St} {R : Strm} {X : Cfg St} (h : Rch (cfgL q (F ::: blank) R) X) :
    Rch (cfgL q blank R) X := by rw [cons_blank] at h; exact h

/-- the pre-test passes (`r < c`): `P := 1` left of `K`, `Q := 1` right of `R`, into `Q := Q * R` -/
theorem pre_pass (a b c r : Nat) (hc : 2 ≤ c) (hr : 1 ≤ r) (hrc : r < c) :
    Rch (cmpA (lC c a b) c c gCR r 1 (F ::: blank)) (qE a b c r 1 1) := by
  refine Rch.tr ((compare gap_CR (ones (b + 2) (F ::: F ::: ones (a + 2) (F ::: F ::: ones (c + 2)
    (F ::: F ::: T ::: blank)))) blank c r (by omega) (by omega)).2 hrc) ?_
  show Rch (cfgL xq6 (T ::: ones (b + 1) _) _) _
  gL; sLn (b + 1); gL; gL
  show Rch (cfgL fl3 (T ::: ones (a + 1) _) _) _
  gL; sLn (a + 1); gL; gL
  show Rch (cfgL fl3 (T ::: ones (c + 1) _) _) _
  gL; sLn (c + 1); gL; gL; gL
  refine blankL ?_; gL; refine blankL ?_; gL; refine blankL ?_; gL; refine blankL ?_; gL
  refine fromL ?_; gR; gR; gR; gR; gR
  unfold gCR
  simp only [ones_succ, ones_cons_true, app_cons, app_nil]
  gR; gR; gR; gR; gR; sRn c; gR; gR; gR; gR; sRn a; gR; gR; gR; gR; sRn b; gR; gR; gR; gR; sRn c
  gR; gR; gR; gR; gR; gR; gR; sRn r; gR
  refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR
  gL0; gLc; gLc; gLc
  refine toL ?_; gL; sLn r; gL; gL
  refine fromL ?_; gR; gR; gR
  unfold qE lbR Mt.rgt Mt.sep
  simp only [S2, ones_succ, ones_zero, ones_cons_true, app_cons, app_nil, tl_blank]
  simp only [cons_blank]
  exact Reach.refl deltaQ _

/-! ## the loop -/

/-- at the BEEP: `xe3` reading the blank left of `P`; `Q`'s cursor on `p` -/
def beepC (a b c r p q : Nat) : Cfg St :=
  cfgL xe3 blank (F ::: F ::: ones (p + 2) (yR (gPQ a b c r) q p (F ::: blank)))

/-- at the BOOP: `xq6` reading the blank left of `P`; `P` and `Q` without holes -/
def boopC (a b c r p q : Nat) : Cfg St :=
  cfgL xq6 blank (F ::: F ::: ones (p + 2) (app (gPQ a b c r) (ones (q + 2) (F ::: blank))))

theorem loop_beep (a b c r p q : Nat) (hp : 1 ≤ p) (hpq : p ≤ q) :
    Rch (loopA a b c r p q) (beepC a b c r p q) := by
  refine Rch.tr ((compare (gap_PQ a b c r) blank blank p q hp (by omega)).1 hpq) ?_
  gL; fin

theorem loop_boop (a b c r p q : Nat) (hq : 1 ≤ q) (hqp : q < p) :
    Rch (loopA a b c r p q) (boopC a b c r p q) :=
  (compare (gap_PQ a b c r) blank blank p q (by omega) hq).2 hqp

/-- between `C` and `P`, read leftwards: `00 B 00 A 00 D 00 K 00` -/
def gCP (a b c : Nat) : List Bool := S2 ++ Bk b ++ S2 ++ Bk a ++ S2 ++ Bk c ++ S2 ++ [T] ++ S2

theorem gap_CP (a b c : Nat) : Gap (gCP a b c) := by
  have h := (((Blk_Bk b).join (Blk_Bk a)).join (Blk_Bk c)).join Blk_M
  exact Or.inr ⟨_, h, by simp [gCP, S2]⟩

/-- right of `C`'s last cell's right neighbour: `0 M 00 R 00 Q` (`Q`'s cursor on cell 1) -/
def lbQ (r q : Nat) : Strm :=
  F ::: T ::: F ::: F ::: ones (r + 2) (F ::: F ::: T ::: F ::: ones q (F ::: F ::: blank))

theorem PQC : ParserR deltaQ QC1 QC2 := ⟨rfl, rfl, rfl⟩
theorem PLZ : ParserR deltaQ LZ1 LZ2 := ⟨rfl, rfl, rfl⟩
theorem PLY : ParserR deltaQ LY1 LY2 := ⟨rfl, rfl, rfl⟩

/-- a right parser across a run of ones, stepping right off the `1` after the hole -/
theorem pRR_ones {p1 p2 q : St} (P : ParserR deltaQ p1 p2) (hf : deltaQ p2 true = some (true, Dir.R, q))
    (n : Nat) (L R : Strm) : Rch ⟨p1, L, ones n (F ::: T ::: R)⟩ ⟨q, T ::: F ::: ones n L, R⟩ := by
  have h := pRR P hf (Clean.replicate n) L R
  rwa [List.reverse_replicate, app_replicate, app_replicate] at h

/-- after the BEEP: `Q`'s cursor back to cell 1, `P := P * c`, then into `Q := Q * R` -/
theorem beep_step (a b c r p q : Nat) (hc : 2 ≤ c) (hp : 1 ≤ p) (hpq : p ≤ q) :
    Rch ⟨bp1, F ::: blank, F ::: F ::: ones (p + 2) (yR (gPQ a b c r) q p (F ::: blank))⟩
      (qE a b c r (p * c) q) := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have hs : step deltaQ (Cfg.mir ⟨Lba1, ones 1 (F ::: lbQ r q), F ::: ones (c' + 1) (Mt.rgt (gCP a b (c' + 1)) p 0)⟩) =
      some ⟨Lba2, ones c' (Mt.rgt (gCP a b (c' + 1)) p 0), T ::: T ::: T ::: F ::: lbQ r q⟩ := rfl
  have hm := Rch.of_step hs (multL (gap_CP a b (c' + 1)) (lbQ r q) (c' + 1) p hc hp) (by intro h; cases h)
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨m, hm'⟩ : ∃ m, q + 1 - (p' + 1) = m + 1 := ⟨q - (p' + 1), by omega⟩
  unfold yR; rw [hm']
  obtain rfl : q = p' + m + 1 := by omega
  gR; gR; sRn (p' + 3)
  unfold gPQ
  simp only [S2, Bk, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append, app_cons]
  show Rch ⟨bp3, T ::: T ::: ones (p' + 1) (F ::: F ::: F ::: blank), _⟩ _
  refine toL ?_; gL; gL; refine fromL ?_; gR
  have hw : Clean ([T, F, F, T, F, F] ++ List.replicate (c' + 3) T ++ [F, F] ++ List.replicate (a + 2) T ++ [F, F] ++
      List.replicate (b + 2) T ++ [F, F] ++ List.replicate (c' + 3) T ++ [F, F, T, F, F] ++ List.replicate (r + 2) T ++
      [F, F] ++ List.replicate (p' + 1) T) := by
    have h4 : ∀ v (m : List Bool), Clean m → Clean (F :: F :: (List.replicate (v + 2) T ++ m)) := by
      intro v m hm; have := Clean.sepBk v hm; simpa [S2, Bk] using this
    simp only [List.cons_append, List.nil_append, List.append_assoc]
    exact Clean.one (Clean.sep (h4 (c' + 1) _ (h4 a _ (h4 b _ (h4 (c' + 1) _ (Clean.sep (h4 r _
      (Clean.sep (Clean.replicate p')))))))))
  have hq := pRL PQC rfl hw (F ::: ones (p' + 1) (F ::: F ::: F ::: blank)) (ones m (F ::: blank))
  simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append, List.reverse_cons,
    List.reverse_append, List.reverse_replicate, List.reverse_nil, app_append, app_replicate, app_cons, app_nil,
    Nat.add_assoc, ones_succ] at hq ⊢
  refine Rch.tr hq ?_
  refine toL ?_; gL; rw [← ones_succ p']; sLn (p' + 1); refine fromL ?_; gR
  simp only [ones_succ, ones_cons_true]
  gR; gLc; gLc; gLc; gLc; gLc
  refine toL ?_; refine Rch.tr (scanL' (q := qc9) rfl (r + 1) _ _) ?_; gL; gL; gL; gL; gL; gL; gL
  simp only [Cfg.mir, cfgL, Mt.rgt, Mt.sep, gCP, lbQ, S2, Bk, List.cons_append, List.nil_append,
    List.append_assoc, List.singleton_append, List.reverse_cons, List.reverse_append, List.reverse_replicate,
    List.reverse_nil, app_append, app_replicate, app_cons, app_nil, Nat.add_assoc, ones_succ, ones_cons_true,
    tl_cons, cons_zero, ones_zero, ones_add, cons_blank, cons_head_tl] at hm ⊢
  refine Rch.tr hm ?_
  refine Rch.tr (pRR_ones PLZ rfl _ _ _) ?_
  have hw2 : Clean ([F, F, T, F, F] ++ List.replicate (c' + 3) T ++ [F, F] ++ List.replicate (a + 2) T ++ [F, F] ++
      List.replicate (b + 2) T ++ [F, F, T] ++ List.replicate c' T) := by
    have h4 : ∀ v (m : List Bool), Clean m → Clean (F :: F :: (List.replicate (v + 2) T ++ m)) := by
      intro v m hm; have := Clean.sepBk v hm; simpa [S2, Bk] using this
    simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    exact Clean.sep (h4 (c' + 1) _ (h4 a _ (h4 b _ (Clean.sep (Clean.replicate c')))))
  have hy := pRL PLY rfl hw2 (T ::: F ::: ones ((p' + 1) * (c' + 1)) blank)
    (F ::: F ::: T ::: F ::: F ::: ones (r + 2) (F ::: F ::: T ::: F ::: ones (p' + (m + 1)) blank))
  simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append, List.reverse_cons,
    List.reverse_append, List.reverse_replicate, List.reverse_nil, app_append, app_replicate, app_cons, app_nil,
    Nat.add_assoc, ones_succ, ones_cons_true] at hy ⊢
  refine Rch.tr hy ?_
  gR; gR; gR; gR; gR; gR; gR; gR; gR
  unfold qE lbR Mt.rgt Mt.sep
  simp only [S2, ones_succ, ones_zero, ones_cons_true, app_cons, app_nil, cons_blank, Nat.add_assoc]
  fin

/-- after the BOOP: erase `P`, then to `M`: the pair is done -/
theorem boop_end (a b c r p q : Nat) :
    Rch ⟨bo1, F ::: blank, F ::: F ::: ones (p + 2) (app (gPQ a b c r) (ones (q + 2) (F ::: blank)))⟩
      (peC 1 c a b c (Bk r ++ S2 ++ Bk q)) := by
  gR; gR; eRn (p + 2)
  unfold gPQ
  simp only [S2, Bk, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append, app_cons,
    app_append, app_replicate, app_nil]
  gR; gR; gR; gR; gR; gR
  have hw : FC (List.replicate (c + 1) T ++ F :: F :: List.replicate (a + 2) T ++ F :: F :: List.replicate (b + 2) T ++
      F :: F :: List.replicate (c + 2) T) := by
    have := (FC.rep (c + 1)).append (FC.sepblk a (FC.sepblk b (FC.sepblk c FC.nil)))
    simpa using this
  have hf := FMF.find hw (T ::: F ::: F ::: T ::: F ::: F ::: zeros (p + 2) (F ::: F ::: F ::: blank))
    (F ::: ones (r + 2) (F ::: F ::: ones (q + 2) (F ::: blank)))
  simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
    List.reverse_cons, List.reverse_append, List.reverse_replicate, List.reverse_nil, app_append,
    app_replicate, app_cons, app_nil] at hf
  refine Rch.tr hf ?_
  refine Rch.tr (stepL (δ := deltaQ) rfl) ?_
  unfold peC lM
  simp only [zeros_blank, cons_blank, app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero,
    ones_cons_true, tl_cons, cons_zero]
  fin

end TM.ABC
