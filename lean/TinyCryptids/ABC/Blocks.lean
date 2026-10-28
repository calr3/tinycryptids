import TinyCryptids.Core.Lemmas
namespace TM.ABC

/-- Nonempty runs of ones separated by exactly two zeros: `1^a 00 1^b 00 ... 1^c`. -/
inductive Blk : List Bool → Prop
  | one (n : Nat) : Blk (List.replicate (n+1) true)
  | cons (n : Nat) {l : List Bool} : Blk l → Blk (List.replicate (n+1) true ++ false :: false :: l)

theorem Clean.rep_append {l : List Bool} (n : Nat) (h : Clean l) :
    Clean (List.replicate n true ++ l) :=
  (Clean.replicate n).append h

theorem Blk.clean2 {l m : List Bool} (h : Blk l) (hm : Clean m) :
    Clean (l ++ m) ∧ Clean (false :: false :: (l ++ m)) := by
  induction h with
  | one n =>
    refine ⟨Clean.rep_append (n+1) hm, ?_⟩
    rw [List.replicate_succ]; exact Clean.sep (Clean.rep_append n hm)
  | cons n _ ih =>
    rw [List.append_assoc]
    refine ⟨Clean.rep_append (n+1) ih.2, ?_⟩
    rw [List.replicate_succ]; exact Clean.sep (Clean.rep_append n ih.2)

theorem Blk.clean_append {l m : List Bool} (h : Blk l) (hm : Clean m) : Clean (l ++ m) :=
  (h.clean2 hm).1
theorem Blk.clean_sep_append {l m : List Bool} (h : Blk l) (hm : Clean m) :
    Clean (false :: false :: (l ++ m)) := (h.clean2 hm).2

theorem Blk.join {l m : List Bool} (hl : Blk l) (hm : Blk m) :
    Blk (l ++ false :: false :: m) := by
  induction hl with
  | one n => exact Blk.cons n hm
  | cons n _ ih => rw [List.append_assoc]; exact Blk.cons n ih

theorem Blk.reverse {l : List Bool} (h : Blk l) : Blk l.reverse := by
  induction h with
  | one n => rw [List.reverse_replicate]; exact Blk.one n
  | cons n _ ih =>
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.reverse_replicate, List.append_assoc, List.cons_append, List.singleton_append]
    exact Blk.join ih (Blk.one n)


/-- what lies between two blocks: a separator, or separators around hole-less blocks -/
def Gap (g : List Bool) : Prop :=
  g = [false, false] ∨ ∃ P, Blk P ∧ g = false :: false :: (P ++ [false, false])

theorem Gap.clean {g m : List Bool} (h : Gap g) (hm : Clean m) : Clean (g ++ true :: m) := by
  rcases h with rfl | ⟨P, hP, rfl⟩
  · exact Clean.sep hm
  · have := hP.clean_sep_append (m := [false, false] ++ true :: m) (Clean.sep hm)
    simpa using this

theorem Gap.reverse {g : List Bool} (h : Gap g) : Gap g.reverse := by
  rcases h with rfl | ⟨P, hP, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨P.reverse, hP.reverse, by simp⟩

theorem Gap.sep : Gap [false, false] := Or.inl rfl

theorem Gap.rev_head {g : List Bool} (h : Gap g) : ∃ g', g.reverse = false :: g' := by
  rcases h with rfl | ⟨P, _, rfl⟩
  · exact ⟨[false], rfl⟩
  · exact ⟨false :: (P.reverse ++ [false, false]), by simp⟩

theorem Gap.head {g : List Bool} (h : Gap g) : ∃ g', g = false :: g' := by
  rcases h with rfl | ⟨P, _, rfl⟩
  · exact ⟨[false], rfl⟩
  · exact ⟨_, rfl⟩

end TM.ABC
