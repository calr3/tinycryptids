import TinyCryptids.Pillai.Compare
namespace TM.Pillai
open St

/-! One tuple `(x, y, a, b)`: blocks of `x + 2`, `y + 2`, `a + 2`, `b + 2` cells, then `00 M 00`,
A empty, `0 R` with `R = 1`; x carries the anchor on cell 1. From the setup (`suC`) the run goes
through `a ^ x` (added into A, so `A = 1 + a ^ x`), `b ^ y`, the compare, the clear and back to
the next enumeration step (`en2C`) with the same tuple. -/

/-- `00 M 00`, A empty, `0 R` with `R = 1` -/
def RT : Strm := F ::: F ::: true ::: F ::: F ::: F ::: true ::: blank

/-- the tape right of x -/
def tupR (y a b : Nat) : Strm :=
  F ::: F ::: ones (y + 2) (F ::: F ::: ones (a + 2) (F ::: F ::: ones (b + 2) RT))

/-- state `su0` on x's anchor -/
def suC (x y a b : Nat) : Cfg St := ⟨su0, true ::: blank, F ::: ones x (tupR y a b)⟩

/-- state `en2` on x's cell 2 -/
def en2C (x y a b : Nat) : Cfg St := ⟨en2, F ::: true ::: blank, ones x (tupR y a b)⟩

theorem Clean.sepRep {l : List Bool} (n : Nat) (h : Clean l) : Clean (F :: F :: (rep (n+1) ++ l)) := by
  show Clean (F :: F :: (true :: (rep n ++ l))); exact Clean.sep (Clean.rep_append n h)

theorem PreOK.two : PreOK [F, F] := Or.inl rfl

/-- a right parser that finds a hole next to a separator (three 0s) -/
theorem ParserR.find3 {p1 p2 : St} (P : ParserR deltaQ p1 p2) {w : List Bool} (hw : Clean w)
    (L R : Strm) :
    Rch ⟨p1, L, app w (F ::: F ::: F ::: true ::: R)⟩ ⟨p2, F ::: F ::: F ::: app w.reverse L, true ::: R⟩ := by
  refine Rch.tr (P.cross hw L _) ?_
  refine Rch.tr (stepR (δ := deltaQ) (R := F ::: F ::: F ::: true ::: R) P.h0) ?_
  refine Rch.tr (stepR (δ := deltaQ) (R := F ::: F ::: true ::: R) P.h2) ?_
  exact stepR (δ := deltaQ) (R := F ::: true ::: R) P.h0

/-- the setup: over x and y, the marker goes on a's cell 1, `R = 1` is added into the empty A (the
separator after M and the single 0 before R make three 0s, still a hole), a new `R = 1` is cut,
and the first power starts at the anchor -/
theorem setup (x y a b : Nat) (ha : 1 ≤ a) :
    Rch (suC x y a b)
      (eAtC (pre2 y) x 1 a (rep (b+2) ++ F :: F :: ([true] ++ F :: F :: rep 1)) 1 blank) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  unfold suC tupR RT
  gR; sRn x; gR; gR; sRn (y + 2); gR; gR; gR; gR
  have hw1 : Clean (rep (a' + 1) ++ F :: F :: (rep (b+2) ++ [F, F, true])) :=
    Clean.rep_append _ (Clean.sepRep (b+1) (Clean.sep Clean.nil))
  have e1 : ones (a' + 1) (F ::: F ::: ones (b + 2) (F ::: F ::: true ::: F ::: F ::: F ::: true ::: blank)) =
      app (rep (a' + 1) ++ F :: F :: (rep (b+2) ++ [F, F, true])) (F ::: F ::: F ::: true ::: blank) := by
    simp only [app_append, app_replicate, app_cons, app_nil, List.cons_append, List.nil_append,
      List.append_assoc]
  rw [e1]
  refine Rch.tr (ParserR.find3 PMQ hw1 _ _) ?_
  gL; gR; gR
  refine blankR ?_
  gL; gL
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.reverse_replicate,
    List.nil_append, List.cons_append, List.singleton_append, List.append_assoc, app_append, app_cons,
    app_nil, app_replicate]
  have hw2 : Clean (true :: F :: F :: true :: F :: F :: (rep (b+2) ++ F :: F :: rep (a' + 1))) := by
    refine Clean.one (Clean.sep (Clean.sepRep (b+1) ?_))
    simpa using Clean.sepRep a' Clean.nil
  have e2 : true ::: F ::: F ::: true ::: F ::: F ::: ones (b + 2) (F ::: F :::
      ones (a' + 1) (F ::: true ::: F ::: F ::: ones (y + 2) (F ::: F ::: ones x (F ::: true ::: blank)))) =
      app (true :: F :: F :: true :: F :: F :: (rep (b+2) ++ F :: F :: rep (a' + 1)))
        (F ::: true ::: leftOf (pre2 y) x 1 blank) := by
    simp only [leftOf, pre2, app_append, app_replicate, app_cons, app_nil, List.cons_append,
      List.nil_append, List.append_assoc, Nat.add_sub_cancel]
    rfl
  show Rch (cfgL LF1 (true ::: F ::: F ::: true ::: F ::: F ::: ones (b + 2) (F ::: F :::
      ones (a' + 1) (F ::: true ::: F ::: F ::: ones (y + 2) (F ::: F ::: ones x (F ::: true ::: blank)))))
    (F ::: true ::: blank)) _
  rw [e2]
  refine Rch.tr (PLF.find hw2 _ _) ?_
  gL
  refine Rch.tr (lg_find (PreOK.pre2 y) x 1 blank _ (Nat.le_refl _) (by omega)) ?_
  unfold eAtC rgt sep
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ,
    ones_cons_true, cons_blank]
  fin

theorem PHE : ParserL deltaQ HE1 HE2 := ⟨rfl, rfl, rfl⟩
theorem HH : Home deltaQ H1 H2 H3 H4 H5 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- after the clear: A is written empty and `R = 1 0 1`; the cursor left on a's cell 1 is filled,
and the machine goes home and puts the anchor back on x's cell 1 -/
theorem clear_home (x y a b : Nat) (ha : 1 ≤ a) :
    Rch (clrC (true ::: F ::: F ::: ones (b+2) (leftOf [F, F] a 1
      (F ::: F ::: ones (y + 2) (F ::: F ::: ones (x + 2) blank))))) (en2C x y a b) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  unfold clrC leftOf
  gRb; gRb; gRb; gLb
  gL; gL; gL
  have hw : Clean (true :: F :: F :: (rep (b+2) ++ F :: F :: rep (a' + 1))) :=
    Clean.one (Clean.sepRep (b+1) (by simpa using Clean.sepRep a' Clean.nil))
  have e1 : true ::: F ::: F ::: ones (b+2) (app [F, F] (ones (a' + 1 + 1 - 1) (F ::: ones 1
      (F ::: F ::: ones (y + 2) (F ::: F ::: ones (x + 2) blank))))) =
      app (true :: F :: F :: (rep (b+2) ++ F :: F :: rep (a' + 1))) (F ::: true :::
        (F ::: F ::: ones (y + 2) (F ::: F ::: ones (x + 2) blank))) := by
    simp [app_append, app_replicate, ones_succ]
  rw [e1]
  refine Rch.tr (PHE.find hw _ _) ?_
  gR; gL
  have hw2 : Clean12 (true :: ([F, F] ++ rep (y + 2) ++ F :: F :: rep (x + 1))) := by
    refine Clean12.of_clean ?_
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact Clean.one (Clean.sep (Clean.rep_append (y + 1) (by simpa using Clean.sepRep x Clean.nil)))
  have e2 : true ::: F ::: F ::: ones (y + 2) (F ::: F ::: ones (x + 2) blank) =
      app (true :: ([F, F] ++ rep (y + 2) ++ F :: F :: rep (x + 1))) (true ::: blank) := by
    simp [app_append, app_replicate, ones_succ']
  show Rch (cfgL H1 (true ::: F ::: F ::: ones (y + 2) (F ::: F ::: ones (x + 2) blank)) _) _
  rw [e2]
  refine Rch.tr (HH.go hw2 _) ?_
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_assoc, List.cons_append, List.singleton_append, app_append, app_replicate, app_cons, app_nil]
  rw [ones_succ]
  gR
  unfold en2C tupR RT
  simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, ones_succ]
  fin

theorem pow_pos' {a : Nat} (ha : 1 ≤ a) (E : Nat) : 1 ≤ a ^ E := Nat.pos_pow_of_pos E ha

/-- One tuple: from the setup to the next enumeration step, with the events of the compare of
`A = 1 + a ^ x` with `R = b ^ y`. -/
theorem tuple_check (x y a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Tr (suC x y a b) (zev (1 + a ^ x) (b ^ y)) (en2C x y a b) := by
  have hpa := pow_pos' ha x
  have hpb := pow_pos' hb y
  have hXa : Blk (rep (b+2) ++ F :: F :: ([true] ++ F :: F :: rep 1)) :=
    Blk.cons (b+1) ((Blk.one 0).app_rep 0)
  have s1 := setup x y a b ha
  have p1 := pow_full hXa x y a blank ha
  have n1 := next_base (Blk.one 0) PreOK.two y a b 1 (a ^ x) (F ::: F ::: ones (x + 2) blank) hb
    (Nat.le_refl _) hpa
  have hXb : Blk ([true] ++ F :: F :: rep (1 + a ^ x)) := by
    rw [show 1 + a ^ x = a ^ x + 1 by omega]; exact (Blk.one 0).app_rep _
  have p2 := pow_full hXb y a b (F ::: F ::: ones (x + 2) blank) hb
  have ce := compare_entry [F, F] a b (1 + a ^ x) (b ^ y)
    (F ::: F ::: ones (y + 2) (F ::: F ::: ones (x + 2) blank)) hpb
  have zr := zz (F ::: F ::: ones (b+2) (leftOf [F, F] a 1
    (F ::: F ::: ones (y + 2) (F ::: F ::: ones (x + 2) blank)))) (1 + a ^ x) (b ^ y) 0 0 (by omega) hpb
  have ch := clear_home x y a b ha
  simp only [List.singleton_append] at p1 n1 p2 hXb
  exact Tr.pre (Rch.tr s1 (Rch.tr p1 (Rch.tr n1 (Rch.tr p2 ce)))) (Tr.post zr ch)

end TM.Pillai
