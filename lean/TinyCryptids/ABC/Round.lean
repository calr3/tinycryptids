import TinyCryptids.ABC.Factor

/-!
# One trial divisor `d`: the four `GCD` tests and their outcomes; `d += 1`

`fT k d rest q`: the factor-phase tape with the head on `D`'s hole (position 1), `K` of `k`
cells, `rest` the tape right of `D`.  `fr ma mb mc a b c r`: that tape, with markers on
`A`, `B`, `C` as `ma`, `mb`, `mc` say, and `R` (hole on cell 1) last.
-/

namespace TM.ABC
open St

local notation "F" => false
local notation "T" => true

def fT (k d : Nat) (rest : Strm) (q : St) : Cfg St := ⟨q, T ::: F ::: F ::: ones k blank, F ::: ones d rest⟩

def blkx : Bool → Nat → List Bool
  | true, v => Bm v
  | false, v => Bk v

def fr (ma mb mc : Bool) (a b c r : Nat) : Strm :=
  app (S2 ++ blkx ma a ++ S2 ++ blkx mb b ++ S2 ++ blkx mc c ++ S2 ++ [T] ++ S2 ++ Bm r) blank

def gB (a : Nat) : List Bool := S2 ++ Bk a ++ S2
def gC (a b : Nat) : List Bool := S2 ++ Bk a ++ S2 ++ Bk b ++ S2
def gR (a b c : Nat) : List Bool := S2 ++ Bk a ++ S2 ++ Bk b ++ S2 ++ Bk c ++ S2 ++ [T] ++ S2

theorem Clean.sepBk (v : Nat) {m : List Bool} (h : Clean m) : Clean (S2 ++ (Bk v ++ m)) := by
  simp only [S2, Bk, List.replicate_succ, List.cons_append, List.nil_append]
  exact Clean.sep (Clean.one (Clean.rep_append v h))

theorem gap_A : Gap S2 := Or.inl rfl
theorem gap_B (a : Nat) : Gap (gB a) := Or.inr ⟨Bk a, Blk_Bk a, by simp [gB, S2]⟩
theorem gap_C (a b : Nat) : Gap (gC a b) :=
  Or.inr ⟨Bk a ++ S2 ++ Bk b, by
    have := (Blk_Bk a).join (Blk_Bk b); simpa [S2] using this, by simp [gC, S2]⟩
theorem gap_R (a b c : Nat) : Gap (gR a b c) :=
  Or.inr ⟨Bk a ++ S2 ++ Bk b ++ S2 ++ Bk c ++ S2 ++ [T], by
    have := (((Blk_Bk a).join (Blk_Bk b)).join (Blk_Bk c)).join Blk_M; simpa [S2] using this,
    by simp [gR, S2]⟩

/-- what follows `C`: `00 M 00 R` (as seen from `C`'s right separator's second cell) -/
def RcC (r : Nat) : Strm := F ::: T ::: F ::: F ::: app (Bm r) blank
def RcB (c r : Nat) : Strm := F ::: T ::: T ::: ones c (F ::: RcC r)
def RcA (b c r : Nat) : Strm := F ::: T ::: T ::: ones b (F ::: RcB c r)

theorem PZD : ParserL deltaQ ZD1 ZD2 := ⟨rfl, rfl, rfl⟩
theorem PPT : ParserR deltaQ PT1 PT2 := ⟨rfl, rfl, rfl⟩

/-- after `R := R * d`: from `R`'s last cell (state `ZD1`) to `D`'s hole, `d += 1` (`dp1`) -/
theorem zd_factor (Lc : Strm) (a b c d z : Nat) (hd : 1 ≤ d) (hz : 1 ≤ z) :
    Rch (cfgL ZD1 (ones z (F ::: T ::: app (gR a b c).reverse (ones d (F ::: T ::: F ::: Lc)))) blank)
      ⟨dp1, T ::: F ::: Lc, F ::: app (List.replicate d T ++ gC a b ++ Bk c ++ S2 ++ [T] ++ S2)
        (T ::: F ::: ones z blank)⟩ := by
  obtain ⟨z', rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
  have hw : Clean (List.replicate z' T) := Clean.replicate _
  have e : ones (z' + 1) (F ::: T ::: app (gR a b c).reverse (ones d (F ::: T ::: F ::: Lc))) =
      app (List.replicate (z' + 1) T) (F ::: T ::: app (gR a b c).reverse (ones d (F ::: T ::: F ::: Lc))) := by
    rw [app_replicate]
  rw [e]
  have hw1 : Clean (List.replicate (z' + 1) T) := Clean.replicate _
  refine Rch.tr (pLL PZD rfl hw1 _ _) ?_
  have e2 : app (gR a b c).reverse (ones d (F ::: T ::: F ::: Lc)) =
      F ::: F ::: T ::: F ::: F ::: app (gC a b ++ Bk c).reverse (ones d (F ::: T ::: F ::: Lc)) := by
    simp only [gR, gC, S2, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.append_assoc, List.singleton_append, List.cons_append, app_append, app_cons, app_nil]
  rw [e2]
  gL; gL; gL; gL; gL
  have e3 : app (gC a b ++ Bk c).reverse (ones d (F ::: T ::: F ::: Lc)) =
      app (List.replicate (c + 2) T ++ (gC a b).reverse) (ones d (F ::: T ::: F ::: Lc)) := by
    simp only [Bk, List.reverse_append, List.reverse_replicate, app_append]
  rw [e3]
  have hw2 : Clean (List.replicate (c + 2) T ++ (gC a b).reverse ++ List.replicate d T) := by
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [List.append_assoc, show List.replicate (d' + 1) T = T :: List.replicate d' T from rfl]
    exact Clean.rep_gap (gap_C a b).reverse _ (Clean.replicate d')
  refine Rch.tr (back_Dw PDH rfl d hw2 Lc _) ?_
  simp only [gC, Bk, S2, List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append,
    List.cons_append, app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero]
  fin

/-- `d += 1` (`K` has `k + 2` cells): `K` gives a cell to `D`; `D`'s hole on the new position 1,
`A`'s marker; `ca1` on `D`'s hole -/
theorem next_d (k d : Nat) (Ra : Strm) (hd : 1 ≤ d) :
    Rch (fT (k + 2) d (F ::: F ::: T ::: T ::: Ra) dp1) (fT (k + 1) (d + 1) (F ::: F ::: T ::: F ::: Ra) ca1) := by
  unfold fT
  gL0; gL; gL; gL; gL
  show Rch (cfgL dp6 (T ::: ones k blank) _) _
  gR; gR; gR; gR; gR
  sRn (d + 1)
  gR; gR; gR; gLc
  refine toL ?_
  show Rch (cfgL GD1 (T ::: F ::: F ::: ones (d + 1) (F ::: T ::: F ::: F ::: ones (k + 1) blank)) (F ::: Ra)) _
  have hw : Clean (T :: F :: F :: List.replicate (d + 1) T) :=
    Clean.one (by rw [List.replicate_succ]; exact Clean.sep (Clean.replicate d))
  rw [show (T ::: F ::: F ::: ones (d + 1) (F ::: T ::: F ::: F ::: ones (k + 1) blank)) =
    app (T :: F :: F :: List.replicate (d + 1) T) (F ::: T ::: F ::: F ::: ones (k + 1) blank) by
    simp only [app_cons, app_replicate]]
  refine Rch.tr (pLR PGD rfl hw _ _) ?_
  simp only [List.reverse_cons, List.reverse_replicate, List.reverse_nil, List.nil_append,
    List.append_assoc, List.singleton_append, List.cons_append, app_append, app_replicate, app_cons,
    app_nil, ones_succ]
  fin

/-- the left part of the tape at the pre-test, from `R`'s cell 0 leftwards -/
def preL (d a b c : Nat) : List Bool :=
  (T :: S2 ++ Bk d ++ S2 ++ Bk a ++ S2 ++ Bk b ++ S2 ++ Bk c ++ S2 ++ [T] ++ S2 ++ [T]).reverse

/-- `d = c` was the last divisor (`K` has one cell): the pre-test; `pt1` on `R`'s hole -/
theorem last_d (a b c d r : Nat) (hr : 1 ≤ r) :
    Rch (fT 1 d (fr F F F a b c r) dp1) ⟨pt1, app (preL d a b c) blank, F ::: ones r blank⟩ := by
  unfold fT
  gL0; gL; gL; gL; gL
  show Rch ⟨dp6, blank, F ::: _⟩ _
  gR
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hw : Clean (T :: S2 ++ Bk d ++ S2 ++ Bk a ++ S2 ++ Bk b ++ S2 ++ Bk c ++ S2 ++ [T] ++ S2 ++ [T]) := by
    simp only [List.append_assoc, List.cons_append]
    exact Clean.one (Clean.sepBk d (Clean.sepBk a (Clean.sepBk b (Clean.sepBk c
      (by simp only [S2, List.cons_append, List.nil_append]; exact Clean.sep (Clean.sep Clean.nil))))))
  show Rch ⟨PT1, F ::: blank, T ::: F ::: F ::: T ::: T ::: ones d (fr F F F a b c (r' + 1))⟩ _
  rw [show (T ::: F ::: F ::: T ::: T ::: ones d (fr F F F a b c (r' + 1))) =
    app (T :: S2 ++ Bk d ++ S2 ++ Bk a ++ S2 ++ Bk b ++ S2 ++ Bk c ++ S2 ++ [T] ++ S2 ++ [T])
      (F ::: T ::: ones r' blank) by
    simp only [fr, blkx, Bm, Bk, S2, List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append, app_append, app_replicate, app_cons, app_nil, ones_succ, List.replicate_succ]]
  refine Rch.tr (pRL PPT rfl hw _ _) ?_
  simp only [preL, cons_blank]
  fin

/-! ## the four tests on the factor tape -/

def stA (k d a b c r : Nat) : Cfg St := fT k d (fr T F F a b c r) ca1
def stB (k d a b c r : Nat) : Cfg St := fT k d (fr F T F a b c r) ca1
def stC (k d a b c r : Nat) : Cfg St := fT k d (fr F F T a b c r) ca1
def stR (k d a b c r : Nat) : Cfg St := fT k d (fr F F F a b c r) ca1
def dpC (k d a b c r : Nat) : Cfg St := fT k d (fr F F F a b c r) dp1

theorem stA_eq (k d a b c r : Nat) :
    stA k d a b c r = gAt ca1 (F ::: ones k blank) (RcA b c r) a S2 d 1 := by
  simp only [stA, fT, gAt, cyR, fr, blkx, Bm, Bk, S2, RcA, RcB, RcC, List.append_assoc, List.cons_append,
    List.singleton_append, List.nil_append, app_append, app_replicate, app_cons, app_nil, ones_succ,
    ones_zero, Nat.add_sub_cancel]

theorem stB_eq (k d a b c r : Nat) :
    stB k d a b c r = gAt ca1 (F ::: ones k blank) (RcB c r) b (gB a) d 1 := by
  simp only [stB, fT, gAt, cyR, fr, blkx, Bm, Bk, S2, gB, RcB, RcC, List.append_assoc, List.cons_append,
    List.singleton_append, List.nil_append, app_append, app_replicate, app_cons, app_nil, ones_succ,
    ones_zero, Nat.add_sub_cancel]

theorem stC_eq (k d a b c r : Nat) :
    stC k d a b c r = gAt ca1 (F ::: ones k blank) (RcC r) c (gC a b) d 1 := by
  simp only [stC, fT, gAt, cyR, fr, blkx, Bm, Bk, S2, gC, RcC, List.append_assoc, List.cons_append,
    List.singleton_append, List.nil_append, app_append, app_replicate, app_cons, app_nil, ones_succ,
    ones_zero, Nat.add_sub_cancel]

theorem stR_eq (k d a b c r : Nat) :
    stR k d a b c r = gAt ca1 (F ::: ones k blank) blank r (gR a b c) d 1 := by
  simp only [stR, fT, gAt, cyR, fr, blkx, Bm, Bk, S2, gR, List.append_assoc, List.cons_append,
    List.singleton_append, List.nil_append, app_append, app_replicate, app_cons, app_nil, ones_succ,
    ones_zero, Nat.add_sub_cancel, cons_blank]

theorem pass_A (k d a b c r : Nat) (hd : 2 ≤ d) (ha : 1 ≤ a) (h : Nat.gcd a d = 1) :
    Rch (stA k d a b c r) (stB k d a b c r) := by
  rw [stA_eq, stB_eq]
  refine Rch.tr ((gcd_run gap_A _ _ a d ha hd).1 h) ?_
  have := e_next gap_A (F ::: ones k blank) (RcB c r) d a b hd ha
  simp only [RcA] at *
  rw [show S2 ++ List.replicate (a + 2) T ++ S2 = gB a by simp [gB, Bk]] at this
  exact this

theorem pass_B (k d a b c r : Nat) (hd : 2 ≤ d) (hb : 1 ≤ b) (h : Nat.gcd b d = 1) :
    Rch (stB k d a b c r) (stC k d a b c r) := by
  rw [stB_eq, stC_eq]
  refine Rch.tr ((gcd_run (gap_B a) _ _ b d hb hd).1 h) ?_
  have := e_next (gap_B a) (F ::: ones k blank) (RcC r) d b c hd hb
  simp only [RcB] at *
  rw [show gB a ++ List.replicate (b + 2) T ++ S2 = gC a b by simp [gB, gC, Bk]] at this
  exact this

theorem pass_C (k d a b c r : Nat) (hd : 2 ≤ d) (hc : 1 ≤ c) (h : Nat.gcd c d = 1) :
    Rch (stC k d a b c r) (dpC k d a b c r) := by
  rw [stC_eq]
  refine Rch.tr ((gcd_run (gap_C a b) _ _ c d hc hd).1 h) ?_
  refine Rch.tr (e_C (gap_C a b) (F ::: ones k blank) (F ::: app (Bm r) blank) d c hd hc) ?_
  simp only [dpC, fT, fr, blkx, Bm, Bk, S2, gC, List.append_assoc, List.cons_append,
    List.singleton_append, List.nil_append, app_append, app_replicate, app_cons, app_nil, ones_succ,
    ones_zero]
  fin

theorem hit_A (k d a b c r : Nat) (hd : 2 ≤ d) (ha : 1 ≤ a) (h : Nat.gcd a d ≠ 1) :
    Rch (stA (k + 2) d a b c r) (stR (k + 2) d a b c r) := by
  rw [stA_eq, stR_eq]
  have h1 := (gcd_run gap_A (F ::: ones (k + 2) blank) (RcA b c r) a d ha hd).2 h
  simp only [RcA] at h1
  refine Rch.tr h1 ?_
  refine Rch.tr (h_next gap_A (RcB c r) k d a b (by omega) ha) ?_
  simp only [gAt, cyR, RcB, RcC, gR, Bm, Bk, S2, List.append_assoc, List.cons_append,
    List.singleton_append, List.nil_append, app_append, app_replicate, app_cons, app_nil, ones_succ,
    ones_zero, Nat.add_sub_cancel, cons_blank]
  fin

theorem hit_B (k d a b c r : Nat) (hd : 2 ≤ d) (hb : 1 ≤ b) (h : Nat.gcd b d ≠ 1) :
    Rch (stB (k + 2) d a b c r) (stR (k + 2) d a b c r) := by
  rw [stB_eq, stR_eq]
  have h1 := (gcd_run (gap_B a) (F ::: ones (k + 2) blank) (RcB c r) b d hb hd).2 h
  simp only [RcB] at h1
  refine Rch.tr h1 ?_
  refine Rch.tr (h_next (gap_B a) (RcC r) k d b c (by omega) hb) ?_
  simp only [gAt, cyR, RcC, gB, gR, Bm, Bk, S2, List.append_assoc, List.cons_append,
    List.singleton_append, List.nil_append, app_append, app_replicate, app_cons, app_nil, ones_succ,
    ones_zero, Nat.add_sub_cancel, cons_blank]
  fin

theorem hit_C (k d a b c r : Nat) (hd : 2 ≤ d) (hc : 1 ≤ c) (h : Nat.gcd c d ≠ 1) :
    Rch (stC k d a b c r) (stR k d a b c r) := by
  rw [stC_eq, stR_eq]
  refine Rch.tr ((gcd_run (gap_C a b) _ _ c d hc hd).2 h) ?_
  refine Rch.tr (h_C (gap_C a b) (F ::: ones k blank) (F ::: app (Bm r) blank) d c (by omega) hc) ?_
  simp only [gAt, cyR, gC, gR, Bm, Bk, S2, List.append_assoc, List.cons_append,
    List.singleton_append, List.nil_append, app_append, app_replicate, app_cons, app_nil, ones_succ,
    ones_zero, Nat.add_sub_cancel, cons_blank]
  fin

theorem notnew_R (k d a b c r : Nat) (hd : 2 ≤ d) (hr : 1 ≤ r) (h : Nat.gcd r d ≠ 1) :
    Rch (stR k d a b c r) (dpC k d a b c r) := by
  rw [stR_eq]
  have h1 := (gcd_run (gap_R a b c) (F ::: ones k blank) blank r d hr hd).2 h
  rw [cons_blank] at h1
  refine Rch.tr h1 ?_
  refine Rch.tr (h_R (gap_R a b c) (F ::: ones k blank) d r (by omega) hr) ?_
  simp only [dpC, fT, fr, blkx, gR, Bm, Bk, S2, List.append_assoc, List.cons_append,
    List.singleton_append, List.nil_append, app_append, app_replicate, app_cons, app_nil, ones_succ,
    ones_zero]
  fin

theorem new_R (k d a b c r : Nat) (hd : 2 ≤ d) (hr : 1 ≤ r) (h : Nat.gcd r d = 1) :
    Rch (stR k d a b c r) (dpC k d a b c (r * d)) := by
  rw [stR_eq]
  have h1 := (gcd_run (gap_R a b c) (F ::: ones k blank) blank r d hr hd).1 h
  rw [cons_blank] at h1
  refine Rch.tr h1 ?_
  refine Rch.tr (e_R (gap_R a b c) (F ::: ones k blank) d r hd hr) ?_
  have hm := multR (gap_R a b c) (F ::: ones k blank) d r hd hr
  simp only [Mt.rgt, Mt.sep, ones_zero, cons_blank] at hm
  refine Rch.tr hm ?_
  refine Rch.tr (zd_factor _ a b c d (r * d) (by omega) (Nat.le_trans hr (Nat.le_mul_of_pos_right r (by omega)))) ?_
  simp only [dpC, fT, fr, blkx, gC, Bm, Bk, S2, List.append_assoc, List.cons_append,
    List.singleton_append, List.nil_append, app_append, app_replicate, app_cons, app_nil, ones_succ,
    ones_zero]
  fin

end TM.ABC