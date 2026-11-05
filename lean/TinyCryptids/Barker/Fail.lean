import TinyCryptids.Barker.Check
import TinyCryptids.Barker.Spec

/-!
# A failed check: the next candidate

From `Fc`: unmark `i`, increment the positions as a binary number (last element least
significant, the dummy `0` in front absorbs a carry out and a new dummy is made), and start the
pass for shift 1: `i` on the last but one position, `j` on the last.
-/

namespace TM.Barker
open St

local notation "F" => false
local notation "T" => true

theorem fail_scan (A : List Bool) (x : Bool) (M : List Bool) (z : Bool) :
    Rch (Fc A x M z) ⟨INC, F ::: UL (A ++ x :: M) blank, z ::: blank⟩ := by
  unfold Fc
  cases x <;> cases z
  all_goals
    gL; gL
    refine Rch.tr (keyL (fun b => by cases b <;> rfl) (by rfl) M _ _) ?_
    gL; gR; gR
    refine Rch.tr (keyR (by rfl) (fun b => by cases b <;> rfl) M _ _) ?_
    gR
    rw [UL_append, UL_cons]; fin

theorem carry (E : List Bool) (m : Nat) : ∀ Rt : Strm,
    Rch (cfgL INC (UL (E ++ List.replicate m T) blank) Rt)
      (cfgL INC (UL E blank) (app (U (List.replicate m F)) Rt)) := by
  induction m with
  | zero => intro Rt; simp only [List.replicate, List.append_nil, U_nil, app_nil]; fin
  | succ m ih =>
    intro Rt
    rw [rep_succ', ← List.append_assoc, UL_snoc]
    gL; gL
    refine Rch.tr (ih _) ?_
    rw [rep_succ', appU_snoc]; fin

theorem stop_cons (E0 : List Bool) (e : Bool) (Rt : Strm) :
    Rch (cfgL INC (UL (E0 ++ [e, F]) blank) Rt) ⟨SMp, UL (E0 ++ [e]) blank, app (U [T]) Rt⟩ := by
  rw [show E0 ++ [e, F] = (E0 ++ [e]) ++ [F] by simp, UL_snoc, UL_snoc]
  cases e
  all_goals gL; gL; gL; gR; gR; fin

theorem stop_nil (Rt : Strm) :
    Rch (cfgL INC (UL [F] blank) Rt) ⟨SMp, UL [F] blank, app (U [T]) Rt⟩ := by
  show Rch (cfgL INC (F ::: T ::: blank) Rt) _
  gL; gL; rw [← cons_blank]; gL; rw [← cons_blank]; gR; gR
  simp only [tl_cons, UL_cons, UL_nil, cons_blank, U_cons, U_nil, app_cons, app_nil]; fin

/-- the reversed list: a run of ones, then a zero or the end -/
theorem rev_decomp : ∀ l : List Bool, (∃ m rest, l = List.replicate m T ++ F :: rest) ∨
    ∃ m, l = List.replicate m T
  | [] => Or.inr ⟨0, rfl⟩
  | F :: l => Or.inl ⟨0, l, rfl⟩
  | T :: l => by
    rcases rev_decomp l with ⟨m, rest, h⟩ | ⟨m, h⟩
    · exact Or.inl ⟨m + 1, rest, by rw [h]; rfl⟩
    · exact Or.inr ⟨m + 1, by rw [h]; rfl⟩

theorem rev_rep {α : Type} (m : Nat) (a : α) : (List.replicate m a).reverse = List.replicate m a := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, List.reverse_cons, ih]; exact (rep_succ' m a).symm

theorem finish (G : List Bool) (g z' : Bool) :
    Rch ⟨SMp, UL (G ++ [g]) blank, F ::: z' ::: blank⟩ (P G g [] z' [] 0) := by
  unfold P; rw [UL_snoc]
  show Rch (cfgL SMp (F ::: g ::: T ::: UL G blank) (z' ::: blank)) _
  cases g <;> cases z'
  all_goals gL; gL; gL; rw [Zt_zero]; fin

theorem inc_run (r : List Bool) (z : Bool) : ∃ G g z', G ++ [g, z'] = F :: inc (r ++ [z]) ∧
    Rch ⟨INC, F ::: UL (F :: r) blank, z ::: blank⟩ (P G g [] z' [] 0) := by
  cases z
  · obtain ⟨G, g, hg⟩ := nonempty_snoc (F :: r) (by simp)
    refine ⟨G, g, T, ?_, ?_⟩
    · rw [inc_snoc_false, ← List.cons_append, hg]; simp
    · refine Rch.tr ?_ (finish G g T)
      rw [hg, UL_snoc]
      cases g
      all_goals gL; gL; gL; gR; gR; fin
  · -- carry: the ones at the end of `r` become zeros
    have h0 : Rch ⟨INC, F ::: UL (F :: r) blank, T ::: blank⟩
        (cfgL INC (UL (F :: r) blank) (F ::: F ::: blank)) := by gL; gL; fin
    suffices hm : ∃ G g z', G ++ [g, z'] = F :: inc (r ++ [T]) ∧
        Rch (cfgL INC (UL (F :: r) blank) (F ::: F ::: blank)) (P G g [] z' [] 0) by
      obtain ⟨G, g, z', h1, h2⟩ := hm; exact ⟨G, g, z', h1, Rch.tr h0 h2⟩
    have scan : ∀ (E : List Bool) (m : Nat), Rch ⟨SMp, UL E blank,
        app (U [T]) (app (U (List.replicate m F)) (F ::: F ::: blank))⟩
        ⟨SMp, UL (E ++ T :: List.replicate m F) blank, F ::: F ::: blank⟩ := by
      intro E m
      rw [← appU_append]
      refine Rch.tr (keyR (by rfl) (fun b => by cases b <;> rfl) _ _ _) ?_
      rw [← UL_append]; fin
    rcases rev_decomp r.reverse with ⟨m, rest, h⟩ | ⟨m, h⟩
    · have hr : r = rest.reverse ++ F :: List.replicate m T := by
        rw [← List.reverse_reverse r, h]; simp [rev_rep]
      obtain ⟨G, g, hg⟩ := nonempty_snoc ((F :: rest.reverse) ++ T :: List.replicate m F) (by simp)
      refine ⟨G, g, F, ?_, ?_⟩
      · have e1 : r ++ [T] = rest.reverse ++ F :: List.replicate (m + 1) T := by
          rw [hr, rep_succ']; simp
        rw [e1, inc_replicate, show G ++ [g, F] = (G ++ [g]) ++ [F] by simp, ← hg, rep_succ']; simp
      · refine Rch.tr ?_ (finish G g F)
        rw [← hg, hr, show F :: (rest.reverse ++ F :: List.replicate m T) =
          ((F :: rest.reverse) ++ [F]) ++ List.replicate m T by simp]
        refine Rch.tr (carry _ m _) ?_
        obtain ⟨E0, e, he⟩ := nonempty_snoc (F :: rest.reverse) (by simp)
        rw [he, show E0 ++ [e] ++ [F] = E0 ++ [e, F] by simp]
        refine Rch.tr (stop_cons E0 e _) ?_
        exact scan _ m
    · have hr : r = List.replicate m T := by rw [← List.reverse_reverse r, h, rev_rep]
      obtain ⟨G, g, hg⟩ := nonempty_snoc ([F] ++ T :: List.replicate m F) (by simp)
      refine ⟨G, g, F, ?_, ?_⟩
      · rw [hr, ← rep_succ', inc_all, show G ++ [g, F] = (G ++ [g]) ++ [F] by simp, ← hg]
        simp [rep_succ']
      · refine Rch.tr ?_ (finish G g F)
        rw [← hg, hr, show F :: List.replicate m T = [F] ++ List.replicate m T by rfl]
        refine Rch.tr (carry _ m _) ?_
        refine Rch.tr (stop_nil _) ?_
        exact scan _ m

end TM.Barker
