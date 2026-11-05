/-!
# Perfect cuboids: the arithmetic behind the machine

* `IsSq n`: `n` is a perfect square.
* The counter S holds `N = k * k + j` with `j ≤ 2 * k` (its hole on cycle cell `j`); `N` is a
  square iff `j = 0` (`sq_iff`). One unit moves it to `adv (k, j)` (`val_adv`).
* A block of `L` cells stands for `v L = L / 2 - 1`.
* `Good (x, y, z)`: the lengths of A, B, C give a perfect cuboid.
* The search order `nxt` (NEXCOM on compositions with parts at least 4) reaches every tuple
  of lengths `≥ 4` from `(4, 4, 4)` (`reached`).
-/

namespace TM.PerfectCuboid

def IsSq (n : Nat) : Prop := ∃ m, m * m = n

/-! ## the counter -/

def Valid (s : Nat × Nat) : Prop := s.2 ≤ 2 * s.1

def val (s : Nat × Nat) : Nat := s.1 * s.1 + s.2

def adv (s : Nat × Nat) : Nat × Nat :=
  if s.2 < 2 * s.1 then (s.1, s.2 + 1) else (s.1 + 1, 0)

theorem adv_valid (s : Nat × Nat) (h : Valid s) : Valid (adv s) := by
  obtain ⟨k, j⟩ := s
  unfold adv Valid at *; simp only at *
  split <;> simp only <;> omega

theorem val_adv (s : Nat × Nat) (h : Valid s) : val (adv s) = val s + 1 := by
  obtain ⟨k, j⟩ := s
  unfold adv val Valid at *; simp only at *
  split
  · simp only; omega
  · simp only
    have : j = 2 * k := by omega
    subst this
    rw [Nat.add_mul, Nat.mul_add]; omega

def advN : Nat → Nat × Nat → Nat × Nat
  | 0, s => s
  | n + 1, s => advN n (adv s)

theorem advN_valid (n : Nat) (s : Nat × Nat) (h : Valid s) : Valid (advN n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih _ (adv_valid s h)

theorem val_advN (n : Nat) (s : Nat × Nat) (h : Valid s) : val (advN n s) = val s + n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => show val (advN n (adv s)) = _; rw [ih _ (adv_valid s h), val_adv s h]; omega

theorem advN_add (m n : Nat) (s : Nat × Nat) : advN (m + n) s = advN n (advN m s) := by
  induction m generalizing s with
  | zero => simp [advN]
  | succ m ih => rw [Nat.add_right_comm]; show advN (m + n) (adv s) = _; rw [ih]; rfl

theorem sq_iff (s : Nat × Nat) (h : Valid s) : IsSq (val s) ↔ s.2 = 0 := by
  obtain ⟨k, j⟩ := s
  unfold Valid val at *; simp only at *
  constructor
  · rintro ⟨m, hm⟩
    rcases Nat.lt_or_ge m (k + 1) with h1 | h1
    · have : m ≤ k := by omega
      have := Nat.mul_le_mul this this
      omega
    · have := Nat.mul_le_mul h1 h1
      rw [Nat.add_mul, Nat.mul_add] at this; omega
  · intro hj; exact ⟨k, by omega⟩

/-- `val` determines a valid counter -/
theorem valid_eq_of_val {s t : Nat × Nat} (hs : Valid s) (ht : Valid t) (h : val s = val t) :
    s = t := by
  obtain ⟨k, j⟩ := s; obtain ⟨l, i⟩ := t
  unfold Valid val at *; simp only at *
  have hkl : k = l := by
    rcases Nat.lt_trichotomy k l with h1 | h1 | h1
    · have : k + 1 ≤ l := h1
      have := Nat.mul_le_mul this this; rw [Nat.add_mul, Nat.mul_add] at this; omega
    · exact h1
    · have : l + 1 ≤ k := h1
      have := Nat.mul_le_mul this this; rw [Nat.add_mul, Nat.mul_add] at this; omega
  subst hkl; ext <;> simp <;> omega

/-! ## blocks and tuples -/

def v (L : Nat) : Nat := L / 2 - 1

abbrev Tup := Nat × Nat × Nat

def Valid3 : Tup → Prop
  | (x, y, z) => 4 ≤ x ∧ 4 ≤ y ∧ 4 ≤ z

/-- the lengths of A, B, C give a perfect cuboid -/
def Good : Tup → Prop
  | (x, y, z) =>
    IsSq (v x * v x + v y * v y) ∧ IsSq (v x * v x + v y * v y + v z * v z) ∧
    IsSq (v z * v z + v x * v x) ∧ IsSq (v y * v y + v z * v z)

def nxt : Tup → Tup
  | (x, y, z) =>
    if 5 ≤ x then (x - 1, y + 1, z)
    else if 5 ≤ y then (y - 1, 4, z + 1)
    else (z + 1, 4, 4)

theorem nxt_valid : ∀ t, Valid3 t → Valid3 (nxt t) := by
  rintro ⟨x, y, z⟩ ⟨hx, hy, hz⟩
  simp only [nxt, Valid3]
  split <;> (try split) <;> omega

def seedT : Tup := (4, 4, 4)

def itr : Nat → Tup → Tup
  | 0, t => t
  | k + 1, t => nxt (itr k t)

theorem tup_eq {a b c d e f : Nat} (h1 : a = d) (h2 : b = e) (h3 : c = f) :
    ((a, b, c) : Tup) = (d, e, f) := by subst h1 h2 h3; rfl

theorem reached : ∀ (x y z : Nat), Valid3 (x, y, z) → ∃ k, itr k seedT = (x, y, z)
  | x, y, z, ⟨hx, hy, hz⟩ => by
    by_cases hy5 : 5 ≤ y
    · obtain ⟨k, hk⟩ := reached (x + 1) (y - 1) z ⟨by omega, by omega, hz⟩
      refine ⟨k + 1, ?_⟩
      show nxt (itr k seedT) = _; rw [hk]; simp only [nxt]
      rw [if_pos (by omega)]; exact tup_eq (by omega) (by omega) rfl
    · by_cases hz5 : 5 ≤ z
      · obtain ⟨k, hk⟩ := reached 4 (x + 1) (z - 1) ⟨Nat.le_refl _, by omega, by omega⟩
        refine ⟨k + 1, ?_⟩
        show nxt (itr k seedT) = _; rw [hk]; simp only [nxt]
        rw [if_neg (by omega), if_pos (by omega)]; exact tup_eq (by omega) (by omega) (by omega)
      · by_cases hx5 : 5 ≤ x
        · obtain ⟨k, hk⟩ := reached 4 4 (x - 1) ⟨Nat.le_refl _, Nat.le_refl _, by omega⟩
          refine ⟨k + 1, ?_⟩
          show nxt (itr k seedT) = _; rw [hk]; simp only [nxt]
          rw [if_neg (by omega), if_neg (by omega)]; exact tup_eq (by omega) (by omega) (by omega)
        · refine ⟨0, ?_⟩; exact tup_eq (by omega) (by omega) (by omega)
termination_by x y z => (x + y + z, z, y)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def, true_and]; omega)

theorem itr_valid (k : Nat) : Valid3 (itr k seedT) := by
  induction k with
  | zero => exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | succ k ih => exact nxt_valid _ ih

/-! ## the statement -/

def PerfectCuboid : Prop :=
  ∃ a b c d e f g : Nat, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ a * a + b * b = d * d ∧
    a * a + c * c = e * e ∧ b * b + c * c = f * f ∧ a * a + b * b + c * c = g * g

theorem v_two (a : Nat) : v (2 * a + 2) = a := by unfold v; omega

theorem good_of_cuboid (a b c d e f g : Nat) (hd : a * a + b * b = d * d)
    (he : a * a + c * c = e * e) (hf : b * b + c * c = f * f) (hg : a * a + b * b + c * c = g * g) :
    Good (2 * a + 2, 2 * b + 2, 2 * c + 2) := by
  simp only [Good, v_two]
  exact ⟨⟨d, hd.symm⟩, ⟨g, hg.symm⟩, ⟨e, by rw [← he, Nat.add_comm]⟩, ⟨f, hf.symm⟩⟩

theorem cuboid_of_good (t : Tup) (hv : Valid3 t) (hg : Good t) : PerfectCuboid := by
  obtain ⟨x, y, z⟩ := t
  obtain ⟨hx, hy, hz⟩ := hv
  obtain ⟨⟨d, hd⟩, ⟨g, hg⟩, ⟨e, he⟩, ⟨f, hf⟩⟩ := hg
  refine ⟨v x, v y, v z, d, e, f, g, by unfold v; omega, by unfold v; omega, by unfold v; omega,
    hd.symm, by rw [he, Nat.add_comm], hf.symm, hg.symm⟩

end TM.PerfectCuboid
