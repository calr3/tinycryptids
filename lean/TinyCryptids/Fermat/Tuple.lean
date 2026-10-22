import TinyCryptids.Fermat.Compare
namespace TM.Fermat
open St

/-- the tape right of the exponent block: `00 B2 00 B3 00 B4 00 M 00 A 0 R` with A empty and
`R = 1` -/
def tailL (a b c : Nat) : List Bool :=
  F :: F :: (rep (a+2) ++ F :: F :: (rep (b+2) ++ F :: F :: (rep (c+2) ++
    [F, F, true, F, F, F, true])))

/-- checkpoint: state `en1` on the anchor (the exponent hole on cell 1) -/
def chk (E a b c : Nat) : Cfg St :=
  ⟨en1, true ::: blank, F ::: ones E (app (tailL a b c) blank)⟩

/-- setup start: state `su0` on the anchor -/
def suC (E a b c : Nat) : Cfg St :=
  ⟨su0, true ::: blank, F ::: ones E (app (tailL a b c) blank)⟩

theorem Clean.sepRep {l : List Bool} (n : Nat) (h : Clean l) : Clean (F :: F :: (rep (n+1) ++ l)) := by
  show Clean (F :: F :: (true :: (rep n ++ l))); exact Clean.sep (Clean.rep_append n h)

theorem PreOK.two : PreOK [F, F] := Or.inl rfl

/-- a right parser that finds a hole next to a separator (three 0s) -/
theorem ParserR.find3 {p1 p2 : St} (P : ParserR delta p1 p2) {w : List Bool} (hw : Clean w)
    (L R : Strm) :
    Rch ⟨p1, L, app w (F ::: F ::: F ::: true ::: R)⟩ ⟨p2, F ::: F ::: F ::: app w.reverse L, true ::: R⟩ := by
  refine Rch.tr (P.cross hw L _) ?_
  refine Rch.tr (stepR (δ := delta) (R := F ::: F ::: F ::: true ::: R) P.h0) ?_
  refine Rch.tr (stepR (δ := delta) (R := F ::: F ::: true ::: R) P.h2) ?_
  exact stepR (δ := delta) (R := F ::: true ::: R) P.h0

/-- the setup: the anchor plays the marker of the next-base step: the marker goes on B2's cell 1,
`R = 1` is added into the empty A (the separator after M and the single 0 before R make three
0s, still a hole), a new `R = 1` is cut, and the first power starts -/
theorem setup (E a b c : Nat) (ha : 1 ≤ a) :
    Rch (suC E a b c)
      (eAtC [F, F] E 1 a (rep (b+2) ++ F :: F :: ((rep (c+2) ++ [F, F, true]) ++ F :: F :: rep 1)) 1) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  unfold suC tailL
  gR; sRn E
  simp only [app_cons, app_append, app_replicate]
  gR; gR; gR; gR
  have hw1 : Clean (rep (a' + 1) ++ F :: F :: (rep (b+2) ++ F :: F :: (rep (c+2) ++ [F, F, true]))) :=
    Clean.rep_append _ (Clean.sepRep (b+1) (Clean.sepRep (c+1) (Clean.sep Clean.nil)))
  have e1 : ones (a' + 1) (F ::: F ::: ones (b + 2) (F ::: F ::: ones (c + 2)
      (F ::: F ::: true ::: F ::: F ::: F ::: true ::: app [] blank))) =
      app (rep (a' + 1) ++ F :: F :: (rep (b+2) ++ F :: F :: (rep (c+2) ++ [F, F, true])))
        (F ::: F ::: F ::: true ::: blank) := by
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
  have hw2 : Clean (true :: F :: F :: true :: F :: F :: (rep (c+2) ++ F :: F :: (rep (b+2) ++
      F :: F :: rep (a' + 1)))) := by
    refine Clean.one (Clean.sep (Clean.sepRep (c+1) (Clean.sepRep (b+1) ?_)))
    simpa using Clean.sepRep a' Clean.nil
  have e2 : true ::: F ::: F ::: true ::: F ::: F ::: ones (c + 2) (F ::: F ::: ones (b + 2) (F ::: F :::
      ones (a' + 1) (F ::: true ::: F ::: F ::: ones E (F ::: true ::: blank)))) =
      app (true :: F :: F :: true :: F :: F :: (rep (c+2) ++ F :: F :: (rep (b+2) ++ F :: F :: rep (a' + 1))))
        (F ::: true ::: leftOf [F, F] E 1) := by
    simp only [leftOf, app_append, app_replicate, app_cons, app_nil, List.cons_append, List.nil_append,
      List.append_assoc, Nat.add_sub_cancel]
    rfl
  show Rch (cfgL LF1 (true ::: F ::: F ::: true ::: F ::: F ::: ones (c + 2) (F ::: F ::: ones (b + 2)
    (F ::: F ::: ones (a' + 1) (F ::: true ::: F ::: F ::: ones E (F ::: true ::: blank)))))
    (F ::: true ::: blank)) _
  rw [e2]
  refine Rch.tr (PLF.find hw2 _ _) ?_
  gL
  refine Rch.tr (lg_find PreOK.two E 1 _ (Nat.le_refl _) (by omega)) ?_
  unfold eAtC rgt sep
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ,
    ones_cons_true, cons_blank]
  fin

theorem PHE : ParserL delta HE1 HE2 := ⟨rfl, rfl, rfl⟩

/-- read leftwards from the last base block: `00 B3 00 B2 00` -/
def preC (a b : Nat) : List Bool := F :: F :: (rep (b+2) ++ F :: F :: (rep (a+2) ++ [F, F]))

/-- after the clear: A is written empty and `R = 1 0 1`, then back to the anchor -/
theorem clear_home (E a b c : Nat) (hE : 1 ≤ E) :
    Rch (clrC (true ::: F ::: F ::: ones (c+2) (leftOf (preC a b) E 1))) (chk E a b c) := by
  unfold clrC
  gRb; gRb; gRb; gLb
  gL; gL; gL
  obtain ⟨e, rfl⟩ : ∃ e, E = e + 1 := ⟨E - 1, by omega⟩
  have hw : Clean (true :: F :: F :: (rep (c+2) ++ preC a b ++ rep (e+1))) := by
    show Clean (true :: F :: F :: (rep (c+2) ++ (F :: F :: (rep (b+2) ++
      F :: F :: (rep (a+2) ++ [F, F]))) ++ rep (e+1)))
    refine Clean.one ?_
    rw [List.append_assoc]
    refine Clean.sepRep (c+1) ?_
    simp only [List.append_assoc, List.cons_append]
    refine Clean.sepRep (b+1) (Clean.sepRep (a+1) ?_)
    simp only [List.nil_append, List.cons_append]
    exact Clean.sep (Clean.replicate e)
  have e1 : true ::: F ::: F ::: ones (c+2) (leftOf (preC a b) (e+1) 1) =
      app (true :: F :: F :: (rep (c+2) ++ preC a b ++ rep (e+1))) (F ::: true ::: blank) := by
    simp [leftOf, preC, app_append, app_replicate, ones_succ]
  rw [e1]
  refine Rch.tr (PHE.find hw _ _) ?_
  gR
  unfold chk tailL preC
  simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, ones_cons_true, ones_succ]
  fin

theorem pow_pos' {a : Nat} (ha : 1 ≤ a) (E : Nat) : 1 ≤ a ^ E := by
  induction E with
  | zero => simp
  | succ n ih => rw [Nat.pow_succ]; exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ ha)

/-- One full check of a tuple: from setup, the machine halts iff `a^E + b^E = c^E`,
and otherwise returns to the checkpoint with the same tuple. -/
theorem tuple_check (E a b c : Nat) (hE : 1 ≤ E) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    (a ^ E + b ^ E = c ^ E → HaltAt (suC E a b c)) ∧
    (a ^ E + b ^ E ≠ c ^ E → Rch (suC E a b c) (chk E a b c)) := by
  have hpa := pow_pos' ha E
  have hpb := pow_pos' hb E
  have hpc := pow_pos' hc E
  have hY : Blk (rep (c+2) ++ [F, F, true]) := Blk.cons (c+1) (Blk.one 0)
  -- base a (A = 1 after the setup)
  have s1 := setup E a b c ha
  have p1 := pow_full (Blk.cons (b+1) (hY.app_rep 0)) PreOK.two E a ha
  have n1 := next_base hY PreOK.two E a b 1 (a ^ E) hb (Nat.le_refl _) hpa
  -- base b
  have hXb : Blk ((rep (c+2) ++ [F, F, true]) ++ F :: F :: rep (1 + a ^ E)) := by
    rw [show 1 + a ^ E = a ^ E + 1 by omega]; exact hY.app_rep _
  have p2 := pow_full hXb (PreOK.two.ext (a+1)) E b hb
  have n2 := next_base (Blk.one 0) (PreOK.two.ext (a+1)) E b c (1 + a ^ E) (b ^ E) hc (by omega) hpb
  simp only [List.append_assoc] at s1 p1 n1 p2
  -- base c
  have hXc : Blk ([true] ++ F :: F :: rep (1 + a ^ E + b ^ E)) := by
    rw [show 1 + a ^ E + b ^ E = (a ^ E + b ^ E) + 1 by omega]; exact (Blk.one 0).app_rep _
  have p3 := pow_full hXc ((PreOK.two.ext (a+1)).ext (b+1)) E c hc
  have ce := compare_entry (preC a b) E c (1 + a ^ E + b ^ E) (c ^ E) hpc
  have zr := zz (F ::: F ::: ones (c+2) (leftOf (preC a b) E 1))
    (1 + a ^ E + b ^ E) (c ^ E) 0 0 (by omega) hpc
  have path : Rch (suC E a b c)
      (Z (sep (true ::: F ::: F ::: ones (c+2) (leftOf (preC a b) E 1))) 0 0 (1 + a ^ E + b ^ E) (c ^ E)) :=
    Rch.tr s1 (Rch.tr p1 (Rch.tr n1 (Rch.tr p2 (Rch.tr n2 (Rch.tr p3 ce)))))
  refine ⟨fun h => HaltAt.back path (zr.1 (by omega)), fun h => ?_⟩
  exact Rch.tr path (Rch.tr (zr.2 (by omega)) (clear_home E a b c hE))

end TM.Fermat
