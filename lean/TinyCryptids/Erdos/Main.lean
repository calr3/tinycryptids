import TinyCryptids.Erdos.Round

/-!
# Main theorem: the machine halts iff some `2 ^ n` with `n > 8` has no 2 in base 3

Round `n` starts at `S c (pw n)`, where the counter `c` is the number of `k < n` whose power
`2 ^ k` has no digit 2 in base 3. Below 9 these are `k = 0, 2, 8`, so round 9 starts at
`S 3 (pw 9)`; from there a power with a 2 passes to the next round and one without halts.
-/

namespace TM.Erdos

open TinyCryptids Dig

theorem start_reach : Rch start (S 0 (pw 0)) := by
  have e : ctr 0 = blank := by
    show false ::: false ::: false ::: false ::: blank = blank
    rw [cons_blank, cons_blank, cons_blank, cons_blank]
  have h : start = ⟨St.A, ctr 0, blank⟩ := by rw [e]; rfl
  rw [h]
  exact pass [] [] true (ctr 0)

/-- Rounds 0 to 8: the powers 1, 4 and 256 have no 2 and bring the counter to 3. -/
theorem early : Rch start (S 3 (pw 9)) := by
  refine Rch.tr start_reach ?_
  refine Rch.tr (round_no2 0 (by decide) (ds := pw 0) (by decide)).reach ?_
  refine Rch.tr (round_two 1 (ds := pw 1) (by decide)).reach ?_
  refine Rch.tr (round_no2 1 (by decide) (ds := pw 2) (by decide)).reach ?_
  refine Rch.tr (round_two 2 (ds := pw 3) (by decide)).reach ?_
  refine Rch.tr (round_two 2 (ds := pw 4) (by decide)).reach ?_
  refine Rch.tr (round_two 2 (ds := pw 5) (by decide)).reach ?_
  refine Rch.tr (round_two 2 (ds := pw 6) (by decide)).reach ?_
  refine Rch.tr (round_two 2 (ds := pw 7) (by decide)).reach ?_
  exact (round_no2 2 (by decide) (ds := pw 8) (by decide)).reach

/-- From round 9 on, the machine halts or reaches round `9 + k`. -/
theorem later (k : Nat) : Halts delta (S 3 (pw 9)) ∨ Rch (S 3 (pw 9)) (S 3 (pw (9 + k))) := by
  induction k with
  | zero => exact Or.inr (Reach.refl delta _)
  | succ k ih =>
    rcases ih with h | h
    · exact Or.inl h
    · by_cases h2 : t ∈ pw (9 + k)
      · exact Or.inr (Rch.tr h (round_two 3 h2).reach)
      · exact Or.inl (Reach.halts delta h (round_halt h2))

/-- **Main theorem.** Started on a blank tape, the machine halts if and only if some power
`2 ^ n` with `n > 8` has no digit 2 in base 3 (Erdős conjectured that none does). -/
theorem halts_iff : Halts delta start ↔ ∃ n, 8 < n ∧ 2 ∉ digits3 (2 ^ n) := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have all : ∀ n, 9 ≤ n → t ∈ pw n := by
      intro n hn
      apply Classical.byContradiction; intro h
      exact hno ⟨n, hn, fun h' => h ((two_mem n).1 h')⟩
    have prog : ∀ c, (∃ n, 9 ≤ n ∧ c = S 3 (pw n)) →
        ∃ c', (∃ n, 9 ≤ n ∧ c' = S 3 (pw n)) ∧ Rch1 c c' := by
      rintro c ⟨n, hn, rfl⟩
      exact ⟨S 3 (pw (n + 1)), ⟨n + 1, by omega, rfl⟩, round_two 3 (all n hn)⟩
    exact not_halts_of_progress delta _ prog _ ⟨9, Nat.le_refl _, rfl⟩
      (Sys.Halts.of_reach early hH)
  · rintro ⟨n, hn, h2⟩
    have h2' : t ∉ pw (9 + (n - 9)) := by
      rw [show 9 + (n - 9) = n by omega]; exact fun h => h2 ((two_mem n).2 h)
    refine Reach.halts delta early ?_
    rcases later (n - 9) with h | h
    · exact h
    · exact Reach.halts delta h (round_halt h2')

end TM.Erdos
