
/-!
# The search

For `n` and `x` with `n < 4x`, let `a = 4x - n` and `m = nx`. The machine tries
`y = 1, 2, …` while `ay ≤ 2m + 2` and stops at the first `y` with `m < ay` and
`ay - m ∣ my` (`Hit`). Here `ay - m = 4xy - n(x + y)`, the `D` of
`test`, so a hit gives a solution `z = my / D`; a sorted solution has
`n < 4x ≤ 3n` and `D ≤ m`, so it is a hit. -/

namespace TM.ErdosStraus

def test (n x y : Nat) : Bool :=
  decide (4 * (x * y) - n * (x + y) ≠ 0) && decide (n * (x * y) % (4 * (x * y) - n * (x + y)) = 0)

def S (n x y z : Nat) : Prop := 4 * x * y * z = n * (x * y + y * z + z * x)

theorem S_swap12 {n x y z : Nat} (h : S n x y z) : S n y x z := by
  unfold S at *
  rw [Nat.mul_right_comm 4 y x, Nat.mul_comm y x, Nat.mul_comm x z, Nat.mul_comm z y]
  rw [h]; congr 1; omega

theorem S_swap23 {n x y z : Nat} (h : S n x y z) : S n x z y := by
  unfold S at *
  rw [Nat.mul_right_comm (4 * x) z y, Nat.mul_comm z y, Nat.mul_comm x z, Nat.mul_comm y x]
  rw [h]; congr 1; omega

theorem sort3 {n x y z : Nat} (h : S n x y z) :
    ∃ a b c, S n a b c ∧ a ≤ b ∧ b ≤ c ∧ ((a = x ∧ b = y ∧ c = z) ∨ (a = y ∧ b = x ∧ c = z) ∨
      (a = x ∧ b = z ∧ c = y) ∨ (a = y ∧ b = z ∧ c = x) ∨ (a = z ∧ b = x ∧ c = y) ∨
      (a = z ∧ b = y ∧ c = x)) := by
  rcases Nat.le_total x y with hxy | hxy <;> rcases Nat.le_total y z with hyz | hyz <;>
    rcases Nat.le_total x z with hxz | hxz
  all_goals first
    | exact ⟨x, y, z, h, by omega, by omega, by omega⟩
    | exact ⟨y, x, z, S_swap12 h, by omega, by omega, by omega⟩
    | exact ⟨x, z, y, S_swap23 h, by omega, by omega, by omega⟩
    | exact ⟨y, z, x, S_swap23 (S_swap12 h), by omega, by omega, by omega⟩
    | exact ⟨z, x, y, S_swap12 (S_swap23 h), by omega, by omega, by omega⟩
    | exact ⟨z, y, x, S_swap12 (S_swap23 (S_swap12 h)), by omega, by omega, by omega⟩

/-- the right side regrouped -/
theorem rhs_eq (n x y z : Nat) : n * (x * y + y * z + z * x) = n * (x * y) + n * (x + y) * z := by
  rw [Nat.mul_assoc, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_comm z x]; omega

theorem lhs_eq (x y z : Nat) : 4 * x * y * z = 4 * (x * y) * z := by rw [Nat.mul_assoc 4 x y]

theorem sol_of_test {n x y : Nat} (hn : 1 ≤ n) (hx : 1 ≤ x) (hy : 1 ≤ y) (ht : test n x y = true) :
    ∃ z, 1 ≤ z ∧ S n x y z := by
  simp only [test, Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨hD, hm⟩ := ht
  generalize hDd : 4 * (x * y) - n * (x + y) = D at hD hm
  have hz : n * (x * y) / D * D = n * (x * y) := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm)
  have hpos : 0 < n * (x * y) := Nat.mul_pos hn (Nat.mul_pos hx hy)
  refine ⟨n * (x * y) / D, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (n * (x * y) / D) with h0 | h0
    · rw [h0, Nat.zero_mul] at hz; omega
    · exact h0
  · unfold S
    generalize n * (x * y) / D = z at hz
    have key : 4 * (x * y) = D + n * (x + y) := by omega
    rw [lhs_eq, rhs_eq, key, Nat.add_mul, Nat.mul_comm D z, hz]


/-- `y` is a hit for `n, x`. -/
def Hit (n x y : Nat) : Prop :=
  n * x + 1 ≤ (4 * x - n) * y ∧ (4 * x - n) * y ≤ 2 * (n * x) + 2 ∧
    ((4 * x - n) * y - n * x) ∣ n * x * y

instance (n x y : Nat) : Decidable (Hit n x y) := by unfold Hit; infer_instance

theorem D_eq (n x y : Nat) :
    (4 * x - n) * y - n * x = 4 * (x * y) - n * (x + y) := by
  rw [Nat.mul_sub_right_distrib, Nat.mul_add, Nat.mul_assoc]; omega

theorem test_of_hit {n x y : Nat} (hx : n < 4 * x) (h : Hit n x y) : test n x y = true := by
  obtain ⟨h1, _, h3⟩ := h
  have e := D_eq n x y
  rw [e] at h3
  simp only [test, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, ?_⟩
  rw [← Nat.mul_assoc]; exact Nat.mod_eq_zero_of_dvd h3

/-- a sorted solution is a hit -/
theorem hit_of_sorted {n x y z : Nat} (hn : 1 ≤ n) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (h : S n x y z) : n < 4 * x ∧ 4 * x ≤ 3 * n ∧ 1 ≤ y ∧ Hit n x y := by
  unfold S at h
  have hy : 1 ≤ y := by omega
  have hz : 1 ≤ z := by omega
  have hyzp : 0 < y * z := Nat.mul_pos hy hz
  have h1 : x * y ≤ y * z := by rw [Nat.mul_comm x y]; exact Nat.mul_le_mul_left y (by omega)
  have h2 : z * x ≤ y * z := by rw [Nat.mul_comm y z]; exact Nat.mul_le_mul_left z hxy
  have h3 : n * (x * y + y * z + z * x) ≤ n * (3 * (y * z)) := Nat.mul_le_mul_left n (by omega)
  have h4 : (4 * x) * (y * z) ≤ (3 * n) * (y * z) := by
    have e1 : 4 * x * y * z = (4 * x) * (y * z) := by rw [Nat.mul_assoc (4 * x)]
    have e2 : n * (3 * (y * z)) = (3 * n) * (y * z) := by
      rw [← Nat.mul_assoc, Nat.mul_comm n 3]
    omega
  have hxn : 4 * x ≤ 3 * n := by
    rw [Nat.mul_comm (4 * x), Nat.mul_comm (3 * n)] at h4; exact Nat.le_of_mul_le_mul_left h4 hyzp
  rw [lhs_eq, rhs_eq] at h
  have hpos : 0 < n * (x * y) := Nat.mul_pos hn (Nat.mul_pos hx hy)
  have hAB : n * (x + y) * z < 4 * (x * y) * z := by omega
  have hAB' : n * (x + y) < 4 * (x * y) := Nat.lt_of_mul_lt_mul_right hAB
  have e := D_eq n x y
  generalize hDd : 4 * (x * y) - n * (x + y) = D at e
  have key : 4 * (x * y) = D + n * (x + y) := by omega
  rw [key, Nat.add_mul] at h
  have hDz : D * z = n * (x * y) := by omega
  have h5 : D * y ≤ D * z := Nat.mul_le_mul_left D hyz
  have h6 : y * D ≤ y * (n * x) := by
    rw [Nat.mul_comm y D, Nat.mul_comm y, Nat.mul_assoc]; omega
  have h7 : D ≤ n * x := Nat.le_of_mul_le_mul_left h6 hy
  have h8 : n * y < (4 * x) * y := by
    have : n * (x + y) = n * x + n * y := Nat.mul_add n x y
    rw [Nat.mul_assoc]; omega
  have h9 : n < 4 * x := Nat.lt_of_mul_lt_mul_right h8
  refine ⟨h9, hxn, hy, by omega, by omega, ?_⟩
  rw [e, Nat.mul_assoc, ← hDz]; exact Nat.dvd_mul_right D z

/-- `n` has a solution iff some `x` with `n < 4x ≤ 3n` has a hit -/
theorem solvable_iff {n : Nat} (hn : 1 ≤ n) :
    (∃ x y z, 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧ 4 * x * y * z = n * (x * y + y * z + z * x)) ↔
      ∃ x y, n < 4 * x ∧ 4 * x ≤ 3 * n ∧ 1 ≤ y ∧ Hit n x y := by
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, he⟩
    obtain ⟨a, b, c, hS, hab, hbc, hp⟩ := sort3 (show S n x y z from he)
    have ha : 1 ≤ a := by omega
    exact ⟨a, b, hit_of_sorted hn ha hab hbc hS⟩
  · rintro ⟨x, y, hx, _, hy, h⟩
    obtain ⟨z, hz, hS⟩ := sol_of_test hn (by omega) hy (test_of_hit hx h)
    exact ⟨x, y, z, by omega, hy, hz, hS⟩

end TM.ErdosStraus
