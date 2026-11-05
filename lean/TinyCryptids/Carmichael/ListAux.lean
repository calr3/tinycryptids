/-!
# List counting lemmas
-/

namespace TinyCryptids

theorem length_le_of_sub {α : Type} [DecidableEq α] :
    ∀ (l m : List α), l.Nodup → (∀ x ∈ l, x ∈ m) → l.length ≤ m.length := by
  intro l
  induction l with
  | nil => intros; simp
  | cons a l ih =>
    intro m hl hsub
    have ha : a ∈ m := hsub a (List.mem_cons_self a l)
    rw [List.nodup_cons] at hl
    have := ih (m.erase a) hl.2 (fun x hx => by
      rw [List.mem_erase_of_ne (fun e => hl.1 (by rw [← e]; exact hx))]
      exact hsub x (List.mem_cons_of_mem a hx))
    rw [List.length_erase_of_mem ha] at this
    have hpos : 0 < m.length := List.length_pos.mpr (fun e => by simp [e] at ha)
    simp only [List.length_cons]; omega

/-- A duplicate-free list inside `m` with at least `m`'s length contains all of `m`. -/
theorem sub_of_length {α : Type} [DecidableEq α] (l m : List α) (hl : l.Nodup)
    (hsub : ∀ x ∈ l, x ∈ m) (hlen : m.length ≤ l.length) : ∀ x ∈ m, x ∈ l := by
  intro x hx
  refine Classical.byContradiction fun hn => ?_
  have := length_le_of_sub l (m.erase x) hl (fun y hy => by
    rw [List.mem_erase_of_ne (fun e => hn (by rw [← e]; exact hy))]; exact hsub y hy)
  rw [List.length_erase_of_mem hx] at this
  have : 0 < m.length := List.length_pos.mpr (fun e => by simp [e] at hx)
  omega

theorem nodup_map_of_inj {α β : Type} {f : α → β} {l : List α} (hl : l.Nodup)
    (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, ih hl.2 (fun x hx y hy => hf x (List.mem_cons_of_mem a hx) y
      (List.mem_cons_of_mem a hy))⟩
    rw [List.mem_map] at h
    obtain ⟨b, hb, hfb⟩ := h
    have := hf a (List.mem_cons_self a l) b (List.mem_cons_of_mem a hb) hfb.symm
    exact hl.1 (this ▸ hb)

theorem range_add (a b : Nat) : List.range (a + b) = List.range a ++ (List.range b).map (a + ·) := by
  induction b with
  | zero => simp
  | succ b ih => rw [← Nat.add_assoc, List.range_succ, ih, List.range_succ, List.map_append,
      List.append_assoc]; rfl

/-- All pairs `(x, y)` with `x < a`, `y < b`. -/
def prodList (a b : Nat) : List (Nat × Nat) := (List.range a).flatMap (fun x => (List.range b).map (x, ·))

theorem mem_prodList {a b x y : Nat} : (x, y) ∈ prodList a b ↔ x < a ∧ y < b := by
  simp [prodList, List.mem_flatMap, List.mem_map, List.mem_range]

theorem length_prodList (a b : Nat) : (prodList a b).length = a * b := by
  induction a with
  | zero => simp [prodList]
  | succ a ih =>
    rw [prodList, List.range_succ, List.flatMap_append, List.length_append] at *
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map,
      List.length_range] at *
    rw [ih, Nat.succ_mul]

theorem nodup_prodList (a b : Nat) : (prodList a b).Nodup := by
  induction a with
  | zero => exact List.Pairwise.nil
  | succ a ih =>
    unfold prodList at *
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine List.pairwise_append.mpr ⟨ih, ?_, ?_⟩
    · exact List.pairwise_map.mpr ((List.nodup_range b).imp (fun h e => h (by simpa using e)))
    · intro u hu w hw e
      rw [List.mem_flatMap] at hu
      obtain ⟨x, hx, hu⟩ := hu
      simp only [List.mem_map, List.mem_range] at hu hw hx
      obtain ⟨y, _, rfl⟩ := hu
      obtain ⟨y', _, rfl⟩ := hw
      simp at e; omega

theorem filter_prodList (a b : Nat) (P Q : Nat → Bool) :
    ((prodList a b).filter (fun xy => P xy.1 && Q xy.2)).length =
      ((List.range a).filter P).length * ((List.range b).filter Q).length := by
  induction a with
  | zero => simp [prodList]
  | succ a ih =>
    rw [prodList, List.range_succ, List.flatMap_append, List.filter_append, List.length_append] at *
    rw [ih, List.filter_append, List.length_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_map,
      List.length_map, List.filter_cons, List.filter_nil]
    by_cases hp : P a = true
    · simp only [hp, if_true, List.length_cons, List.length_nil, Nat.add_mul, Nat.one_mul]
      have e : ((fun xy : Nat × Nat => P xy.1 && Q xy.2) ∘ (a, ·)) = Q := by funext y; simp [hp]
      rw [e]; omega
    · simp only [hp, Bool.false_eq_true, if_false, List.length_nil, Nat.zero_add]
      have : (List.filter ((fun xy : Nat × Nat => P xy.1 && Q xy.2) ∘ (a, ·)) (List.range b)) = [] := by
        rw [List.filter_eq_nil_iff]; intro y _; simp [hp]
      rw [this]; simp

end TinyCryptids
