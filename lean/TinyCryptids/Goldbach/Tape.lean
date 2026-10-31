import TinyCryptids.Goldbach.Machine

/-!
# Steps and walks on list-shaped tapes

A configuration `⟨q, L, R⟩` reads `R 0`; `CL q L R` is the configuration whose head is on `L 0`
(the cell left of the boundary between `L` and `R`), which is where a left move lands.
-/

namespace TMK.Goldbach

open TM (Dir)

abbrev Rch := Reach delta

/-- the head on `L 0` -/
def CL (q : St) (L R : Strm) : Cfg St := ⟨q, tl L, L 0 ∷ R⟩

theorem CL_cons (q : St) (a : Nat) (L R : Strm) : CL q (a ∷ L) R = ⟨q, L, a ∷ R⟩ := rfl

theorem Rch.tr {a b c : Cfg St} (h1 : Rch a b) (h2 : Rch b c) : Rch a c := Reach.trans delta h1 h2

theorem sR {q q' : St} {L R : Strm} {a w : Nat} (h : delta q a = some (w, Dir.R, q')) :
    Rch ⟨q, L, a ∷ R⟩ ⟨q', w ∷ L, R⟩ := stepR (R := a ∷ R) h

theorem sL {q q' : St} {L R : Strm} {a w : Nat} (h : delta q a = some (w, Dir.L, q')) :
    Rch ⟨q, L, a ∷ R⟩ (CL q' L (w ∷ R)) := stepL (R := a ∷ R) h

macro "gR" : tactic => `(tactic| refine Rch.tr (sR (by rfl)) ?_)
macro "gL" : tactic => `(tactic| refine Rch.tr (sL (by rfl)) ?_)
macro "fin" : tactic => `(tactic| exact Reach.refl delta _)

/-- walk right over `l`, writing `f a` on each cell `a` -/
theorem walkR {q : St} (f : Nat → Nat) :
    ∀ (l : List Nat) (L R : Strm), (∀ a ∈ l, delta q a = some (f a, Dir.R, q)) →
      Rch ⟨q, L, lst l R⟩ ⟨q, lst (l.map f).reverse L, R⟩
  | [], L, R, _ => Reach.refl delta _
  | a :: l, L, R, h => by
    refine Rch.tr (sR (h a (List.mem_cons_self _ _))) ?_
    refine Rch.tr (walkR f l _ R (fun b hb => h b (List.mem_cons_of_mem _ hb))) ?_
    simp [lst_append]; fin

/-- walk left over `l` (nearest cell first), writing `f a` on each cell `a` -/
theorem walkL {q : St} (f : Nat → Nat) :
    ∀ (l : List Nat) (L R : Strm), (∀ a ∈ l, delta q a = some (f a, Dir.L, q)) →
      Rch (CL q (lst l L) R) (CL q L (lst (l.map f).reverse R))
  | [], L, R, _ => Reach.refl delta _
  | a :: l, L, R, h => by
    refine Rch.tr (sL (h a (List.mem_cons_self _ _))) ?_
    refine Rch.tr (walkL f l L _ (fun b hb => h b (List.mem_cons_of_mem _ hb))) ?_
    simp [lst_append]; fin

/-- a walk over a run of one symbol -/
theorem runR {q : St} {a w : Nat} (h : delta q a = some (w, Dir.R, q)) (n : Nat) (L R : Strm) :
    Rch ⟨q, L, lst (List.replicate n a) R⟩ ⟨q, lst (List.replicate n w) L, R⟩ := by
  have := walkR (fun _ => w) (List.replicate n a) L R (fun b hb => by
    rw [List.eq_of_mem_replicate hb]; exact h)
  simpa [List.map_replicate, List.reverse_replicate] using this

theorem runL {q : St} {a w : Nat} (h : delta q a = some (w, Dir.L, q)) (n : Nat) (L R : Strm) :
    Rch (CL q (lst (List.replicate n a) L) R) (CL q L (lst (List.replicate n w) R)) := by
  have := walkL (fun _ => w) (List.replicate n a) L R (fun b hb => by
    rw [List.eq_of_mem_replicate hb]; exact h)
  simpa [List.map_replicate, List.reverse_replicate] using this

macro "rRn" n:term : tactic => `(tactic| refine Rch.tr (runR (by rfl) $n _ _) ?_)
macro "rLn" n:term : tactic => `(tactic| refine Rch.tr (runL (by rfl) $n _ _) ?_)

theorem lst_rep_succ' (n a : Nat) (s : Strm) :
    lst (List.replicate (n + 1) a) s = lst (List.replicate n a) (a ∷ s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => show a ∷ lst (List.replicate (n + 1) a) s = a ∷ _; rw [ih]

theorem lst_rep_comm (n a : Nat) (s : Strm) :
    lst (List.replicate n a) (a ∷ s) = a ∷ lst (List.replicate n a) s := by
  rw [← lst_rep_succ']; rfl

theorem lst_rep_add (m n a : Nat) (s : Strm) :
    lst (List.replicate (m + n) a) s = lst (List.replicate m a) (lst (List.replicate n a) s) := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih => rw [Nat.add_right_comm]; show a ∷ _ = a ∷ _; rw [ih]

theorem blank_eq : blank = 0 ∷ blank := cons_blank.symm

end TMK.Goldbach
