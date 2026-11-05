import TinyCryptids.ErdosMoser.Pow
namespace TM.ErdosMoser
open St

/-! After a power with the marker on `p + 1 ≥ 2`: the marker moves one cell left, R is added
into A, R = 1 is pushed, and the next power starts at the anchor. -/

theorem PMQ : ParserR delta MQ1 MQ2 := ⟨rfl, rfl, rfl⟩

theorem next_base (k p β a r : Nat) (hp : 1 ≤ p) (hr : 1 ≤ r) :
    Rch (nbC k (p + 1) β (rep (a + 1)) r) (eAtC k 1 p (β + 1) (rep (a + r + 1)) 1) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  unfold nbC
  gL; gL; gR; gR; gR
  have hw : Clean (rep (β + 1) ++ F :: F :: (rep (a + 1) ++ [F, F, true])) :=
    Clean.rep_append _ (Clean.sep (Clean.rep_append a (Clean.sep Clean.nil)))
  have e1 : true ::: ones β (rgt (rep (a + 1)) (r' + 1) 0) =
      app (rep (β + 1) ++ F :: F :: (rep (a + 1) ++ [F, F, true])) (F ::: true ::: ones r' (sep blank)) := by
    simp [rgt, sep, app_append, app_replicate, ones_succ, ones_cons_true]
  rw [e1]
  refine Rch.tr (PMQ.find hw _ _) ?_
  gL; gL
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.reverse_replicate,
    List.nil_append, List.cons_append, List.singleton_append, List.append_assoc, app_append, app_cons,
    app_nil, app_replicate]
  gL; gL; gR
  simp only [tl_cons, ones_succ, Nat.add_eq, Nat.add_zero]
  show Rch ⟨q4, _, ones (r' + 4) (sep blank)⟩ _
  sRn (r' + 4)
  unfold sep
  gL; gL; gL; gL; gL
  have hw2 : Clean (rep (a + r' + 2) ++ F :: F :: rep (β + 2)) :=
    Clean.rep_append _ (Clean.sep (Clean.replicate _))
  have h1 : ∀ X, ones r' (true ::: true ::: ones a X) = ones (a + r' + 2) X := by
    intro X; rw [show true ::: true ::: ones a X = ones (a + 2) X from rfl, ones_add,
      show r' + (a + 2) = a + r' + 2 by omega]
  have h2 : ∀ Y, true ::: ones β (true ::: false ::: Y) = ones (β + 2) (false ::: Y) := by
    intro Y; rw [ones_cons_true]; rfl
  have e2 : ones r' (true ::: true ::: ones a (F ::: F ::: true ::: ones β (true ::: false ::: true ::: ones p' (KL k 1)))) =
      app (rep (a + r' + 2) ++ F :: F :: rep (β + 2)) (F ::: true ::: ones p' (KL k 1)) := by
    rw [h2, h1]; simp [app_append, app_replicate]
  rw [e2]
  refine Rch.tr (PLF.find hw2 _ _) ?_
  gL
  refine Rch.tr (lg_find k 1 p' _ (Nat.le_refl _) (by omega)) ?_
  unfold eAtC
  simp [rgt, sep, app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ,
    ones_cons_true, cons_blank]
  rw [show a + (r' + 1) = (a + r') + 1 by omega, ones_succ]; fin

end TM.ErdosMoser
