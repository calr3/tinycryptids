import TinyCryptids.Fermat.Pow
namespace TM.Fermat
open St

/-! After a power: the marker moves to the next base block, R is added into A (the single 0
between them is filled, and a new R = 1 is cut from the end of the block), and the next power
starts at the anchor. -/

theorem PMQ : ParserR delta MQ1 MQ2 := ⟨rfl, rfl, rfl⟩

theorem Blk.app_rep {Y : List Bool} (hY : Blk Y) (α : Nat) :
    Blk (Y ++ F :: F :: List.replicate (α+1) true) := hY.join (Blk.one α)

theorem PreOK.ext {pre : List Bool} (h : PreOK pre) (n : Nat) : PreOK (F :: F :: (rep (n+1) ++ pre)) := by
  rcases h with rfl | ⟨P, hP, rfl⟩
  · exact Or.inr ⟨rep (n+1), Blk.one n, rfl⟩
  · refine Or.inr ⟨rep (n+1) ++ F :: F :: P, Blk.cons n hP, ?_⟩; simp

theorem next_base {Y pre : List Bool} (hY : Blk Y) (hp : PreOK pre)
    (k β β' α r : Nat) (hb' : 1 ≤ β') (ha : 1 ≤ α) (hr : 1 ≤ r) :
    Rch (nbC pre k β (rep (β'+2) ++ F :: F :: (Y ++ F :: F :: rep α)) r)
      (eAtC (F :: F :: (rep (β+2) ++ pre)) k 1 β' (Y ++ F :: F :: rep (α + r)) 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, α = a + 1 := ⟨α - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, β' = b + 1 := ⟨β' - 1, by omega⟩
  unfold nbC
  gR; sRn β
  unfold rgt
  simp only [sep, app_append, app_cons, app_replicate]
  gR; gR; gR; gR
  have hw : Clean (rep (b + 1) ++ F :: F :: (Y ++ F :: F :: rep (a + 1))) :=
    Clean.rep_append _ (hY.clean_sep_append (show Clean (F :: F :: true :: rep a) from
      Clean.sep (Clean.replicate a)))
  have e1 : ones (b + 1) (F ::: F ::: app Y (F ::: F ::: ones (a + 1)
      (F ::: ones (r' + 1) (F ::: ones 0 blank)))) =
      app (rep (b + 1) ++ F :: F :: (Y ++ F :: F :: rep (a + 1))) (F ::: true ::: ones r' (F ::: blank)) := by
    simp [app_append, app_replicate, ones_succ]
  rw [e1]
  refine Rch.tr (PMQ.find hw _ _) ?_
  gL; gR
  show Rch ⟨q1, _, ones (r' + 1) (F ::: blank)⟩ _
  sRn (r' + 1); gL; gL
  have hw2 : Clean (rep (a + r' + 2) ++ F :: F :: (Y.reverse ++ F :: F :: rep (b + 1))) :=
    Clean.rep_append _ (hY.reverse.clean_sep_append
      (show Clean (F :: F :: true :: rep b) from Clean.sep (Clean.replicate b)))
  have e2 : ones r' (true ::: app (rep (b + 1) ++ F :: F :: (Y ++ F :: F :: rep (a + 1))).reverse
      (F ::: true ::: F ::: F ::: ones β (true ::: ones 1 (leftOf pre k 1)))) =
      app (rep (a + r' + 2) ++ F :: F :: (Y.reverse ++ F :: F :: rep (b + 1)))
        (F ::: true ::: leftOf (F :: F :: (rep (β + 2) ++ pre)) k 1) := by
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.reverse_replicate,
      List.nil_append, List.cons_append, List.singleton_append, List.append_assoc, app_append,
      app_cons, app_nil, app_replicate, leftOf]
    rw [ones_cons_true, ← ones_succ, ones_add, show r' + 1 + (a + 1) = a + r' + 2 by omega]
    simp [ones_succ, ones_cons_true]
  show Rch (cfgL LF1 (ones r' (true ::: app (rep (b + 1) ++ F :: F :: (Y ++ F :: F :: rep (a + 1))).reverse
      (F ::: true ::: F ::: F ::: ones β (true ::: ones 1 (leftOf pre k 1))))) _) _
  rw [e2]
  refine Rch.tr (PLF.find hw2 _ _) ?_
  gL
  refine Rch.tr (lg_find (hp.ext (β + 1)) k 1 _ (Nat.le_refl _) (by omega)) ?_
  unfold eAtC
  simp [rgt, sep, app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ,
    ones_cons_true, cons_blank]
  rw [show a + 1 + (r' + 1) = (a + r') + 1 + 1 by omega]; fin

end TM.Fermat
