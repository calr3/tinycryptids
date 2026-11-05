/-!
# Binary increment of a sequence (last element least significant)
-/

namespace TM.Barker

/-- `+1` on a reversed list (least significant element first) -/
def incR : List Bool → List Bool
  | [] => [true]
  | false :: r => true :: r
  | true :: r => false :: incR r

/-- binary `+1`, the last element least significant; all ones grows by one element -/
def inc (l : List Bool) : List Bool := (incR l.reverse).reverse

theorem inc_nil : inc [] = [true] := rfl
theorem inc_snoc_false (l : List Bool) : inc (l ++ [false]) = l ++ [true] := by
  simp [inc, incR]
theorem inc_snoc_true (l : List Bool) : inc (l ++ [true]) = inc l ++ [false] := by
  simp [inc, incR]

theorem rep_succ' {α : Type} (m : Nat) (a : α) :
    List.replicate (m + 1) a = List.replicate m a ++ [a] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show a :: List.replicate (m + 1) a = (a :: List.replicate m a) ++ [a]; rw [ih]; rfl

theorem inc_replicate (E : List Bool) (m : Nat) :
    inc (E ++ false :: List.replicate m true) = E ++ true :: List.replicate m false := by
  induction m with
  | zero => simpa using inc_snoc_false E
  | succ m ih =>
    rw [rep_succ', ← List.cons_append, ← List.append_assoc, inc_snoc_true, ih,
      rep_succ']; simp

theorem inc_all (n : Nat) : inc (List.replicate n true) = true :: List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ', inc_snoc_true, ih, rep_succ']; rfl

theorem nonempty_snoc (l : List Bool) (h : l ≠ []) : ∃ G g, l = G ++ [g] := by
  induction l with
  | nil => exact absurd rfl h
  | cons c l ih =>
    cases l with
    | nil => exact ⟨[], c, rfl⟩
    | cons d l => obtain ⟨G, g, hg⟩ := ih (by simp); exact ⟨c :: G, g, by rw [hg]; rfl⟩

end TM.Barker
