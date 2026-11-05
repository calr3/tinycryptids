import TinyCryptids.LehmerTau.Seed
import TinyCryptids.Defs

/-!
# The main theorem

`Sn n` (the start of `n`) halts iff `M = P`, else it reaches `Sn (n + 1)` (`nstep`); the seed
reaches `Sn 2`. With `M = 691 σ₅(n) + 65 σ₁₁(n)` and `P = 252 · 691 · Σ_{i<n} σ₅(i) σ₅(n−i)`,
`M = P` is `τ(n) = 0`; `τ(1) = 1`.
-/

namespace TM.LehmerTau
open St TinyCryptids

local notation "F" => false

/-! ## arithmetic -/

theorem dsum_pow (k n : Nat) : ∀ m, dsum (fun d => d ^ k) n m = sigmaBelow k n m
  | 0 => rfl
  | m + 1 => by simp only [dsum, sigmaBelow, dsum_pow k n m]

theorem dsum_add (f g : Nat → Nat) (n : Nat) : ∀ m, dsum (fun x => f x + g x) n m = dsum f n m + dsum g n m
  | 0 => rfl
  | m + 1 => by
    simp only [dsum, dsum_add f g n m]
    split <;> omega

theorem dsum_mul (c : Nat) (f : Nat → Nat) (n : Nat) : ∀ m, dsum (fun x => c * f x) n m = c * dsum f n m
  | 0 => rfl
  | m + 1 => by
    simp only [dsum, dsum_mul c f n m]
    split <;> simp [Nat.mul_add]

theorem gI_eq (K n i : Nat) : gI K n i = K * (sigma 5 i * sigma 5 (n - i)) := by
  unfold gI sigma
  have h1 : ∀ d, dsum (fun e => d ^ 5 * e ^ 5 * K) (n - i) (n - i) = (d ^ 5 * K) * sigmaBelow 5 (n - i) (n - i) := by
    intro d
    rw [← dsum_pow, ← dsum_mul]
    congr 1; funext e; rw [Nat.mul_right_comm]
  simp only [h1]
  have h2 : (fun d => d ^ 5 * K * sigmaBelow 5 (n - i) (n - i)) =
      (fun d => (K * sigmaBelow 5 (n - i) (n - i)) * d ^ 5) := by
    funext d; ac_rfl
  rw [h2, dsum_mul, dsum_pow]
  rw [Nat.mul_assoc, Nat.mul_comm (sigmaBelow 5 (n - i) (n - i))]

theorem rP_eq (K n : Nat) : ∀ m, rP K n m = K * tauConvBelow n m
  | 0 => rfl
  | m + 1 => by simp only [rP, tauConvBelow, rP_eq K n m, gI_eq, Nat.mul_add]

theorem mM_eq (kA kC n : Nat) : mM kA kC n = kC * sigma 5 n + kA * sigma 11 n := by
  unfold mM sigma
  rw [dsum_add, dsum_mul, dsum_mul, dsum_pow, dsum_pow]

theorem key (n : Nat) : mM 65 691 n = rP (691 * 252) n (n - 1) ↔ tau756 n = 0 := by
  rw [mM_eq, rP_eq]; unfold tau756; omega

/-! ## the machine -/

def Sn2 (n : Nat) : Cfg St := Sn 65 252 691 n

theorem ones_get_add (k i : Nat) (X : Strm) : ones k X (k + i) = X i := by
  induction k with
  | zero => simp [ones]
  | succ k ih => rw [show k + 1 + i = (k + i) + 1 by omega]; exact ih

theorem ones_get_lt (k i : Nat) (X : Strm) (h : i < k) : ones k X i = true := by
  induction k generalizing i with
  | zero => omega
  | succ k ih => cases i with
    | zero => rfl
    | succ i => exact ih i (by omega)

theorem Sn_R (n : Nat) (hn : 2 ≤ n) (i : Nat) (hi : i ≤ n) : (Sn2 n).R (i + 15) = decide (i < n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show ones (m + 1) _ i = _
  by_cases h : i < m + 1
  · rw [ones_get_lt _ _ _ h]; simp [h]
  · obtain ⟨j, rfl⟩ : ∃ j, i = m + 1 + j := ⟨i - (m + 1), by omega⟩
    obtain rfl : j = 0 := by omega
    rw [ones_get_add]; simp

theorem Sn_ne (n : Nat) (hn : 2 ≤ n) : Sn2 n ≠ Sn2 (n + 1) := by
  intro h
  have := congrArg (fun c => c.R (n + 15)) h
  simp only [Sn_R n hn n (Nat.le_refl _), Sn_R (n + 1) (by omega) n (by omega)] at this
  simp at this

theorem reach1_of_ne {a b : Cfg St} (h : Rch a b) (hne : a ≠ b) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem step_n (n : Nat) (hn : 2 ≤ n) :
    (tau756 n = 0 → HaltAt (Sn2 n)) ∧ (tau756 n ≠ 0 → Rch1 (Sn2 n) (Sn2 (n + 1))) := by
  have s := nstep 65 252 691 (by omega) (by omega) (by omega) n hn
  simp only [ne_eq, key] at s
  exact ⟨s.1, fun h => reach1_of_ne (s.2 h) (Sn_ne n hn)⟩

theorem halt_from (n0 : Nat) (h0 : tau756 n0 = 0) : ∀ k n, 2 ≤ n → n0 = n + k → HaltAt (Sn2 n) := by
  intro k
  induction k with
  | zero => intro n hn e; subst e; exact (step_n _ hn).1 h0
  | succ k ih =>
    intro n hn e
    by_cases h : tau756 n = 0
    · exact (step_n n hn).1 h
    · exact HaltAt.back ((step_n n hn).2 h).reach (ih (n + 1) (by omega) (by omega))

theorem tau_one : tau756 1 ≠ 0 := by decide

/-- a counterexample: the machine halts -/
theorem haltAt_of (h : ∃ n, 1 ≤ n ∧ tau756 n = 0) : HaltAt start := by
  obtain ⟨n, h1, h2⟩ := h
  have hn : 2 ≤ n := by
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · exact absurd h2 tau_one
    · exact h
  exact HaltAt.back seed (halt_from n h2 (n - 2) 2 (Nat.le_refl _) (by omega))

theorem no_halt (h : ¬ ∃ n, 1 ≤ n ∧ tau756 n = 0) : ¬ Halts delta (Sn2 2) := by
  refine not_halts_of_progress delta (fun cf => ∃ n, 2 ≤ n ∧ cf = Sn2 n) ?_ _ ⟨2, Nat.le_refl _, rfl⟩
  rintro cf ⟨n, hn, rfl⟩
  exact ⟨Sn2 (n + 1), ⟨n + 1, by omega, rfl⟩, (step_n n hn).2 (fun h0 => h ⟨n, by omega, h0⟩)⟩

/-- **The machine halts iff Lehmer's conjecture fails**: some `n ≥ 1` has `τ(n) = 0`. -/
theorem halts_iff : Halts delta start ↔ ∃ n, 1 ≤ n ∧ tau756 n = 0 := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro h
    exact no_halt h (Sys.Halts.of_reach seed hH)
  · exact fun h => (haltAt_of h).halts

end TM.LehmerTau
