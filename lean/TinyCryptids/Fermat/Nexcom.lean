/-! The search order (NEXCOM on compositions, exponent block minimum 3)
reaches every tuple `(E, a, b, c)` with `E ≥ 3` and `a, b, c ≥ 1`. -/

namespace TM.Fermat

abbrev Tup := Nat × Nat × Nat × Nat

def nxt : Tup → Tup
  | (E, a, b, c) =>
    if 4 ≤ E then (E - 1, a + 1, b, c)
    else if 2 ≤ a then (a + 1, 1, b + 1, c)
    else if 2 ≤ b then (b + 1, 1, 1, c + 1)
    else if 2 ≤ c then (c + 3, 1, 1, 1)
    else (4, 1, 1, 1)

def Valid : Tup → Prop
  | (E, a, b, c) => 3 ≤ E ∧ 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c

def seedT : Tup := (3, 1, 1, 1)

/-- `itr k t` : `k` steps of the search order from `t` -/
def itr : Nat → Tup → Tup
  | 0, t => t
  | k + 1, t => nxt (itr k t)

theorem nxt_valid : ∀ t, Valid t → Valid (nxt t) := by
  rintro ⟨E, a, b, c⟩ ⟨hE, ha, hb, hc⟩
  simp only [nxt, Valid]
  split <;> (try split) <;> (try split) <;> (try split) <;> omega

/-- every valid tuple is reached from the seed -/
theorem reached : ∀ (E a b c : Nat), Valid (E, a, b, c) → ∃ k, itr k seedT = (E, a, b, c)
  | E, a, b, c, ⟨hE, ha, hb, hc⟩ => by
    by_cases ha2 : 2 ≤ a
    · -- predecessor (E+1, a-1, b, c) by an h = 1 step
      obtain ⟨k, hk⟩ := reached (E+1) (a-1) b c ⟨by omega, by omega, hb, hc⟩
      refine ⟨k+1, ?_⟩
      show nxt (itr k seedT) = _; rw [hk]; simp only [nxt]; split <;> (try split) <;> (try split) <;> (try split) <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega
    · by_cases hb2 : 2 ≤ b
      · obtain ⟨k, hk⟩ := reached 3 (E-1) (b-1) c ⟨Nat.le_refl _, by omega, by omega, hc⟩
        refine ⟨k+1, ?_⟩
        show nxt (itr k seedT) = _; rw [hk]; simp only [nxt]; split <;> (try split) <;> (try split) <;> (try split) <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega
      · by_cases hc2 : 2 ≤ c
        · obtain ⟨k, hk⟩ := reached 3 1 (E-1) (c-1) ⟨Nat.le_refl _, Nat.le_refl _, by omega, by omega⟩
          refine ⟨k+1, ?_⟩
          show nxt (itr k seedT) = _; rw [hk]; simp only [nxt]; split <;> (try split) <;> (try split) <;> (try split) <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega
        · by_cases hE5 : 5 ≤ E
          · obtain ⟨k, hk⟩ := reached 3 1 1 (E-3) ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, by omega⟩
            refine ⟨k+1, ?_⟩
            show nxt (itr k seedT) = _; rw [hk]; simp only [nxt]; split <;> (try split) <;> (try split) <;> (try split) <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega
          · by_cases hE4 : E = 4
            · refine ⟨1, ?_⟩; subst hE4; simp [itr, nxt, seedT]; omega
            · refine ⟨0, ?_⟩; simp [itr, seedT]; omega
termination_by E a b c => (E + a + b + c, c, b, a)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def, true_and, and_true]; omega)

end TM.Fermat
