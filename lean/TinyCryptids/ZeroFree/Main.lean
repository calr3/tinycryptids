import TinyCryptids.ZeroFree.Round

/-!
# Main theorem: the machine halts iff some `2 ^ n` with `n > 86` has no digit 0

After the scan of `2 ^ n` the machine is at the round start `S c (pw n)`, with `c` = 27 plus
the number of `k ≤ n` whose power `2 ^ k` has no digit 0 (`st`). Up to `n = 86` these are
36 powers, so the counter is 63 at `S 63 (pw 86)`; from there a power with a 0 passes to
the next round, and one without halts (the counter overflows).
-/

namespace TM.ZeroFree

open D

local notation "F" => false

/-- the counter and the digits after the scan of `2 ^ n`, computed -/
def stStep (p : Nat × List D) : Nat × List D :=
  match p with
  | (c, ds) => (if d0 ∈ dbl false ds then c else c + 1, dbl false ds)

def st : Nat → Nat × List D
  | 0 => (28, [d1])
  | n + 1 => stStep (st n)

theorem st_pw (n : Nat) : (st n).2 = pw n := by
  induction n with
  | zero => rfl
  | succ n ih => show (stStep (st n)).2 = _; simp only [stStep, pw, ← ih]

theorem st_le : ∀ n, n < 86 → (st (n + 1)).1 ≤ 63 := by decide

theorem st_86 : (st 86).1 = 63 := by decide

theorem pw_ne (n : Nat) : pw n ≠ [] := by
  intro h; have := pw_num n; rw [h] at this
  have := Nat.two_pow_pos n; simp [num] at *; omega

/-- the seed writes the counter 27 and the separator, and starts the first pass -/
theorem seed : Rch start ⟨St.C1, ctr 27, blank⟩ := by
  have e : ctr 27 = F ::: F ::: true ::: true ::: true ::: true ::: true ::: F ::: true ::: true :::
      true ::: true ::: true ::: blank := by
    rw [show ctr 27 = F ::: F ::: true ::: true ::: true ::: true ::: true ::: F ::: true ::: true :::
      true ::: true ::: true ::: F ::: blank from rfl, cons_blank]
  rw [e]
  unfold start
  refine blankR ?_; zfR; refine blankR ?_; zfR; refine blankR ?_; zfR; refine blankR ?_; zfR
  refine blankR ?_; zfR; refine blankR ?_; zfR; refine blankR ?_; zfR; refine blankR ?_; zfR
  refine blankR ?_; zfR; refine blankR ?_; zfR; refine blankR ?_; zfR; refine blankR ?_; zfR
  refine blankR ?_; zfR
  exact Reach.refl delta _

/-- Rounds 0 to 86. -/
theorem early : ∀ n, n ≤ 86 → Rch start (S (st n).1 (st n).2) := by
  intro n
  induction n with
  | zero => intro _; exact Rch.tr seed first
  | succ n ih =>
    intro hn
    refine Rch.tr (ih (by omega)) ?_
    have hle : (stStep (st n)).1 ≤ 63 := st_le n (by omega)
    have hne := pw_ne n
    rw [← st_pw] at hne
    show Rch _ (S (stStep (st n)).1 (stStep (st n)).2)
    generalize st n = p at hle hne ⊢
    obtain ⟨c, ds⟩ := p
    obtain ⟨d, ds, rfl⟩ : ∃ d ds', ds = d :: ds' := by
      cases ds with
      | nil => exact absurd rfl hne
      | cons d ds' => exact ⟨d, ds', rfl⟩
    simp only [stStep] at hle ⊢
    by_cases h : d0 ∈ dbl false (d :: ds)
    · rw [if_pos h]; exact (round_0 c d ds h).reach
    · rw [if_neg h] at hle ⊢; exact (round_no0 c (by omega) d ds h).reach

theorem start_86 : Rch start (S 63 (pw 86)) := by
  have := early 86 (Nat.le_refl _)
  rw [st_86, st_pw] at this; exact this

theorem round_S (c n : Nat) (h : d0 ∈ pw (n + 1)) : Rch1 (S c (pw n)) (S c (pw (n + 1))) := by
  have hne := pw_ne n
  generalize hp : pw n = ds at hne
  obtain ⟨d, ds', rfl⟩ : ∃ d ds', ds = d :: ds' := by
    cases ds with
    | nil => exact absurd rfl hne
    | cons d ds' => exact ⟨d, ds', rfl⟩
  have e : pw (n + 1) = dbl false (d :: ds') := by rw [← hp]; rfl
  rw [e] at h ⊢
  exact round_0 c d ds' h

theorem halt_S (n : Nat) (h : d0 ∉ pw (n + 1)) : HaltAt (S 63 (pw n)) :=
  round_halt (pw n) h

/-- From round 86 on, the machine halts or reaches round `86 + j`. -/
theorem later (j : Nat) : HaltAt (S 63 (pw 86)) ∨ Rch (S 63 (pw 86)) (S 63 (pw (86 + j))) := by
  induction j with
  | zero => exact Or.inr (Reach.refl delta _)
  | succ j ih =>
    rcases ih with h | h
    · exact Or.inl h
    · by_cases h0 : d0 ∈ pw (86 + j + 1)
      · exact Or.inr (Rch.tr h (round_S 63 (86 + j) h0).reach)
      · exact Or.inl (HaltAt.back h (halt_S _ h0))

/-- With a counterexample, the machine reaches its halting state. -/
theorem haltAt_of (h : ∃ n, 86 < n ∧ ∀ k, 2 ^ n / 10 ^ k ≠ 0 → (2 ^ n / 10 ^ k) % 10 ≠ 0) :
    HaltAt start := by
  obtain ⟨n, hn, h0⟩ := h
  rw [zero_free_iff] at h0
  refine HaltAt.back start_86 ?_
  have e : 86 + (n - 87) + 1 = n := by omega
  rcases later (n - 87) with h | h
  · exact h
  · exact HaltAt.back h (halt_S _ (by rw [e]; exact h0))

/-- **Main theorem.** Started on a blank tape, the design halts if and only if some power
`2 ^ n` with `n > 86` has no decimal digit 0. -/
theorem zero_free_iff_ex :
    (∃ n, 86 < n ∧ ∀ k, 2 ^ n / 10 ^ k ≠ 0 → (2 ^ n / 10 ^ k) % 10 ≠ 0) ↔ ∃ n, 86 < n ∧ d0 ∉ pw n := by
  simp only [zero_free_iff]

theorem halts_iff :
    Halts delta start ↔ ∃ n, 86 < n ∧ ∀ k, 2 ^ n / 10 ^ k ≠ 0 → (2 ^ n / 10 ^ k) % 10 ≠ 0 := by
  rw [zero_free_iff_ex]
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have all : ∀ n, 86 < n → d0 ∈ pw n := by
      intro n hn
      apply Classical.byContradiction; intro h
      exact hno ⟨n, hn, h⟩
    have prog : ∀ c, (∃ n, 86 ≤ n ∧ c = S 63 (pw n)) →
        ∃ c', (∃ n, 86 ≤ n ∧ c' = S 63 (pw n)) ∧ Rch1 c c' := by
      rintro c ⟨n, hn, rfl⟩
      exact ⟨S 63 (pw (n + 1)), ⟨n + 1, by omega, rfl⟩, round_S 63 n (all (n + 1) (by omega))⟩
    exact not_halts_of_progress delta _ prog _ ⟨86, Nat.le_refl _, rfl⟩
      (Sys.Halts.of_reach start_86 hH)
  · intro h; rw [← zero_free_iff_ex] at h; exact (haltAt_of h).halts

end TM.ZeroFree
