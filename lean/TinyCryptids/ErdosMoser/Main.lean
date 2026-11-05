import TinyCryptids.ErdosMoser.End
import TinyCryptids.Defs
namespace TM.ErdosMoser
open St TinyCryptids

/-! The main loop: one pair `(k, m)` is `m` powers (bases `1, 2, …, m`) and a compare; the pairs
run along the diagonals `k + m = s`. -/

/-- `1^k + 2^k + … + j^k` -/
def sumP (k : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => sumP k j + (j + 1) ^ k

theorem powSum_eq (k : Nat) (hk : 1 ≤ k) : ∀ j, powSum (j + 1) k = sumP k j := by
  intro j
  induction j with
  | zero => simp [powSum, sumP, Nat.zero_pow hk]
  | succ j ih => rw [powSum, ih, sumP]

theorem reach1_of {a b : Cfg St} (h : Rch a b) (hq : a.q ≠ b.q) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero =>
    simp only [Sys.run] at hn
    exact absurd (congrArg Cfg.q (Option.some.inj hn)) hq
  | succ n => exact ⟨n, hn⟩

/-- the powers of one pair: after the power with base `j + 1` -/
theorem powers (k m : Nat) : ∀ j, j + 1 ≤ m →
    Rch (pairC k m) (nbC k (m - j) (j + 1) (rep (sumP k j + 1)) ((j + 1) ^ k)) := by
  intro j
  induction j with
  | zero =>
    intro hm
    have := pow_full (X := rep 1) (Blk.one 0) k m 1 hm (Nat.le_refl _)
    simpa [pairC, sumP] using this
  | succ j ih =>
    intro hm
    refine Rch.tr (ih (by omega)) ?_
    rw [show m - j = (m - (j + 1)) + 1 by omega]
    refine Rch.tr (next_base k (m - (j + 1)) (j + 1) (sumP k j) ((j + 1) ^ k) (by omega)
      (Nat.pos_pow_of_pos _ (by omega))) ?_
    have := pow_full (X := rep (sumP k j + (j + 1) ^ k + 1)) (Blk.one _) k (m - (j + 1)) (j + 1 + 1)
      (by omega) (by omega)
    simpa [sumP] using this

abbrev Pr := Nat × Nat

/-- the next pair along the diagonals -/
def nxt : Pr → Pr
  | (k, m) => if 2 ≤ m then (k + 1, m - 1) else (2, k)

def itr : Nat → Pr → Pr
  | 0, t => t
  | n + 1, t => nxt (itr n t)

def Valid (t : Pr) : Prop := 2 ≤ t.1 ∧ 1 ≤ t.2
def Sol (t : Pr) : Prop := powSum t.2 t.1 = t.2 ^ t.1
def pairT (t : Pr) : Cfg St := pairC t.1 t.2

theorem nxt_valid : ∀ t : Pr, Valid t → Valid (nxt t) := by
  rintro ⟨k, m⟩ ⟨hk, hm⟩
  simp only [nxt]; split <;> simp only [Valid] <;> omega

/-- one pair: halt on a solution, else on to the next pair -/
theorem cycle : ∀ t : Pr, Valid t →
    (Sol t → HaltAt (pairT t)) ∧ (¬ Sol t → Rch1 (pairT t) (pairT (nxt t)))
  | (k, m), ⟨hk, hm⟩ => by
    have h1 := powers k m (m - 1) (by omega)
    rw [show m - (m - 1) = 1 by omega, show m - 1 + 1 = m by omega] at h1
    have h2 := final_start k m (sumP k (m - 1)) (m ^ k) (Nat.pos_pow_of_pos _ (by omega))
    have h3 := zz (ones (m + 2) (KL k 1)) (sumP k (m - 1) + 1) (m ^ k + 1) 1 1 (by omega) (by omega)
    have hs : powSum m k = sumP k (m - 1) := by
      have := powSum_eq k (by omega) (m - 1); rwa [show m - 1 + 1 = m by omega] at this
    simp only [Sol, pairT, hs]
    refine ⟨fun h => HaltAt.back (Rch.tr h1 h2) (h3.1 (by omega)), fun h => ?_⟩
    refine Reach1.trans_reach delta (reach1_of h1 (by simp [pairC, eAtC, nbC, cfgL])) (Rch.tr h2 (Rch.tr (h3.2 (by omega)) ?_))
    simp only [nxt]
    by_cases hm2 : 2 ≤ m
    · rw [if_pos hm2]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
      exact end_shift k m'
    · rw [if_neg hm2]
      obtain rfl : m = 1 := by omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      exact end_reset k'

def seedT : Pr := (2, 2)

def Rd (t : Pr) : Prop := ∃ j, itr j seedT = t

theorem Rd.next {t : Pr} (h : Rd t) : Rd (nxt t) := let ⟨j, hj⟩ := h; ⟨j + 1, by simp [itr, hj]⟩

/-- every pair except `(2, 1)` is reached from `(2, 2)` -/
theorem reached : ∀ s k m, k + m = s → 2 ≤ k → 1 ≤ m → (k, m) ≠ (2, 1) → Rd (k, m) := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    -- the first pair of the diagonal
    have first : 4 ≤ s → Rd (2, s - 2) := by
      intro hs
      by_cases h4 : s = 4
      · subst h4; exact ⟨0, rfl⟩
      · have := (ih (s - 1) (by omega) (s - 2) 1 (by omega) (by omega) (Nat.le_refl _)
          (by simp only [ne_eq, Prod.mk.injEq]; omega)).next
        simpa [nxt] using this
    intro k
    induction k with
    | zero => intro m _ h; omega
    | succ k ihk =>
      intro m hs hk hm hne
      by_cases h2 : k + 1 = 2
      · rw [h2] at hne ⊢
        have : m = s - 2 := by omega
        subst this
        have h1 : s - 2 ≠ 1 := fun h => hne (by rw [h])
        exact first (by omega)
      · have hne' : (k, m + 1) ≠ (2, 1) := by intro h; simp only [Prod.mk.injEq] at h; omega
        have := (ihk (m + 1) (by omega) (by omega) (by omega) hne').next
        simpa [nxt, hm] using this

theorem itr_succ' (t : Pr) : ∀ j, itr (j + 1) t = itr j (nxt t) := by
  intro j; induction j with
  | zero => rfl
  | succ j ih => show nxt (itr (j + 1) t) = nxt (itr j (nxt t)); rw [ih]

theorem itr_valid (t : Pr) (ht : Valid t) : ∀ j, Valid (itr j t) := by
  intro j; induction j with
  | zero => exact ht
  | succ j ih => exact nxt_valid _ ih

theorem halts_if_sol : ∀ K (t : Pr), Valid t → (∃ j, j ≤ K ∧ Sol (itr j t)) → HaltAt (pairT t) := by
  intro K
  induction K with
  | zero =>
    intro t ht ⟨j, hj, hs⟩
    obtain rfl : j = 0 := by omega
    exact (cycle t ht).1 hs
  | succ K ih =>
    intro t ht ⟨j, hj, hs⟩
    by_cases h0 : Sol t
    · exact (cycle t ht).1 h0
    · have hj1 : 1 ≤ j := by
        rcases j with _ | j
        · exact absurd hs h0
        · omega
      have := ih (nxt t) (nxt_valid t ht) ⟨j - 1, by omega, by
        rw [← itr_succ', show j - 1 + 1 = j by omega]; exact hs⟩
      exact HaltAt.back ((cycle t ht).2 h0).reach this

macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))

/-- from the blank tape: K = 2 and M = 1 are written, the end of the pair `(2, 1)`, then `(2, 2)` -/
theorem seed_reach : Rch start (pairT seedT) := by
  unfold start
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  have := end_reset 0
  simp only [clrC, KL, Nat.zero_add] at this
  exact this

/-- If the equation has a solution, the machine reaches its explicit halting state. -/
theorem haltAt_of (h : ∃ k m, 2 ≤ k ∧ 1 ≤ m ∧ powSum m k = m ^ k) : HaltAt start := by
  obtain ⟨k, m, hk, hm, hs⟩ := h
  have hne : (k, m) ≠ (2, 1) := by
    intro h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [powSum] at hs
  obtain ⟨j, hj⟩ := reached _ k m rfl hk hm hne
  exact HaltAt.back seed_reach (halts_if_sol j seedT ⟨by decide, by decide⟩ ⟨j, Nat.le_refl _, by
    rw [hj]; exact hs⟩)

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- **Main theorem.** Started on a blank tape, the 117-state design halts if and only if
`1^k + 2^k + … + (m-1)^k = m^k` has a solution with `k ≥ 2`. -/
theorem halts_iff : Halts delta start ↔ ∃ k m, 2 ≤ k ∧ 1 ≤ m ∧ powSum m k = m ^ k := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have prog : ∀ c, (∃ t, Valid t ∧ c = pairT t) → ∃ c', (∃ t, Valid t ∧ c' = pairT t) ∧ Rch1 c c' := by
      rintro c ⟨t, ht, rfl⟩
      refine ⟨pairT (nxt t), ⟨nxt t, nxt_valid t ht, rfl⟩, (cycle t ht).2 ?_⟩
      intro hs
      obtain ⟨k, m⟩ := t
      exact hno ⟨k, m, ht.1, ht.2, hs⟩
    exact not_halts_of_progress delta _ prog _ ⟨seedT, ⟨by decide, by decide⟩, rfl⟩
      (halts_det hH seed_reach)
  · intro h; exact (haltAt_of h).halts

end TM.ErdosMoser
