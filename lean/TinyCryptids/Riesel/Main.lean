import TinyCryptids.Riesel.Counter

/-!
# Main theorem: the design halts iff no odd k < 509203 is a Riesel number
-/

namespace TM.Riesel

open TinyCryptids
open St

local notation "F" => false

/-! ## checkpoints -/

/-- left of D's separator while `k` is tested: K (`k + 7` cells), its separator, C -/
def XK (k v : Nat) : Strm := ones (k + 7) (F ::: F ::: Cs v)

/-- testing `P = k·2^n - 1`: the mod walk starts with `d = 3` -/
def CK (k n v : Nat) : Cfg St := MW (XK k v) 3 (k * 2 ^ n - 1 - 3) 0 1

/-- the step to `k`: the loop on K (`k + 5` cells), after its first step -/
def KL (k v : Nat) : Cfg St := ⟨s4, F ::: ones (k + 4) (F ::: F ::: Cs v), blank⟩

/-! ## the step to a new k -/

theorem kl_loop (k v : Nat) :
    Rch (KL k v) (cfgL Dm (Cs v) (F ::: F ::: F ::: F ::: ones (k + 5) (F ::: F ::: ones (k + 5) blank))) := by
  have h1 := loop_tail (F ::: Cs v) (k + 4) 0 0
  simp only [ones_zero, cons_blank] at h1
  refine Rch.tr h1 (Rch.tr (loop _ (k + 4) 1 1) ?_)
  rw [show 1 + (k + 4) = k + 5 by omega]
  gL; fin

theorem kl_halt (k : Nat) : HaltAt (KL k 0) := HaltAt.back (kl_loop k 0) (cnt_zero _)

theorem kl_next (k w : Nat) (hk : 5 ≤ k) (hw : w + 1 < 2 ^ 20) : Rch (KL k (w + 1)) (CK k 1 w) := by
  refine Rch.tr (kl_loop k (w + 1)) (Rch.tr (cnt_dec w hw _) (Rch.tr (newk _ (k + 5) (by omega)) ?_))
  refine Rch.tr (loop0 _ _) ?_
  have := dfin (ones (k + 5 + 2) (F ::: F ::: Cs w)) (k + 5 - 9)
  unfold CK XK
  rw [show k * 2 ^ 1 - 1 - 3 = 2 * (k + 5 - 9) + 4 by rw [Nat.pow_one]; omega,
    show k + 7 = k + 5 + 2 by omega]
  exact this

/-! ## one candidate -/

theorem ones_blank_get (a i : Nat) : ones a blank i = decide (i < a) := by
  induction a generalizing i with
  | zero => simp [blank]
  | succ a ih => cases i with
    | zero => show true = _; simp
    | succ i => show ones a blank i = _; rw [ih]; simp

theorem mw_R (X : Strm) (r i : Nat) : (MW X 3 r 0 1).R (i + 8) = decide (i < r) := by
  show ones (r + 1 - 1) blank i = _
  rw [ones_blank_get, Nat.add_sub_cancel]

/-- a run between two different configurations takes at least one step -/
theorem reach1_of_ne {a b : Cfg St} (h : Rch a b) (hne : a ≠ b) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem cand (k n v : Nat) (hk : 5 ≤ k) (hko : k % 2 = 1) (hn : 1 ≤ n) :
    (Prime (k * 2 ^ n - 1) → Rch (CK k n v) (KL (k + 2) v)) ∧
    (¬ Prime (k * 2 ^ n - 1) → Rch1 (CK k n v) (CK k (n + 1) v)) := by
  have h9 := cand_ge k n hk hn
  have hodd := cand_odd k n hko hn
  have t := test (XK k v) (k * 2 ^ n - 1 - 4) 3 (Nat.le_refl _) (fun e h1 h2 => by
    rw [show e = 2 by omega, show 3 + (k * 2 ^ n - 1 - 4) + 1 = k * 2 ^ n - 1 by omega]; omega)
  rw [show 3 + (k * 2 ^ n - 1 - 4) + 1 = k * 2 ^ n - 1 by omega,
    show k * 2 ^ n - 1 - 4 + 1 = k * 2 ^ n - 1 - 3 by omega] at t
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · refine Rch.tr (t.1 hp) (Rch.tr (wipe _ _) ?_)
    unfold XK KL
    gR; fin
  · obtain ⟨d, r, hdr, hd, hr, h⟩ := t.2 hp
    have st := Rch.tr h (Rch.tr (comp_end _ d r hd hr) (Rch.tr (loop0 _ _) (dfin _ _)))
    have e : 2 * (d + r - 3) + 4 = k * 2 ^ (n + 1) - 1 - 3 := by rw [cand_succ k n (by omega)]; omega
    rw [e] at st
    refine reach1_of_ne st fun hc => ?_
    have := congrArg (fun c => c.R (k * 2 ^ n - 1 - 3 + 8)) hc
    simp only [CK] at this
    rw [mw_R, mw_R, cand_succ k n (by omega)] at this
    simp at this; omega

/-! ## the search over n, then over k -/

theorem search (k v : Nat) (hk : 5 ≤ k) (hko : k % 2 = 1) :
    ∀ j n, 1 ≤ n → Prime (k * 2 ^ (n + j) - 1) → Rch (CK k n v) (KL (k + 2) v)
  | 0, n, hn, hp => (cand k n v hk hko hn).1 hp
  | j + 1, n, hn, hp => by
    by_cases h : Prime (k * 2 ^ n - 1)
    · exact (cand k n v hk hko hn).1 h
    · refine Rch.tr ((cand k n v hk hko hn).2 h).reach (search k v hk hko j (n + 1) (by omega) ?_)
      rw [show n + 1 + j = n + (j + 1) by omega]; exact hp

theorem good_reach (k v : Nat) (hk : 5 ≤ k) (hko : k % 2 = 1) (hg : Good k) : Rch (CK k 1 v) (KL (k + 2) v) := by
  obtain ⟨N, hN, hp⟩ := hg
  exact search k v hk hko (N - 1) 1 (Nat.le_refl _) (by rw [show 1 + (N - 1) = N by omega]; exact hp)

theorem bad_loops (k w : Nat) (hk : 5 ≤ k) (hko : k % 2 = 1) (hb : ¬ Good k) : ¬ Halts delta (CK k 1 w) := by
  refine not_halts_of_progress delta (fun c => ∃ n, 1 ≤ n ∧ c = CK k n w) ?_ _ ⟨1, Nat.le_refl _, rfl⟩
  rintro c ⟨n, hn, rfl⟩
  exact ⟨CK k (n + 1) w, ⟨n + 1, by omega, rfl⟩,
    (cand k n w hk hko hn).2 (fun hp => hb ⟨n, hn, hp⟩)⟩

/-- the counter: one decrement for each `k = 5, 7, …, 509201`, then it is 0 -/
def C0 : Nat := 254599

theorem grp_3 : grp 3 blank = ones 3 blank := by simp [grp, ones, cons_blank]

/-- the seed leaves the counter's two leading 0 bits blank -/
theorem cs_c0 : Cs C0 = grp 7 (grp 8 (grp 2 (grp 14 (ones 3 blank)))) := by
  show grp 7 (grp 8 (grp 2 (grp 14 (grp 3 blank)))) = _
  rw [grp_3]

theorem seed_reach : Rch start (KL 5 C0) := by
  unfold start KL
  rw [cs_c0]
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  fin

/-- before the step to `k = 5 + 2i`, if the odd `k` from 5 below it are all good -/
theorem reach_i : ∀ i, i ≤ C0 → (∀ k, k % 2 = 1 → 5 ≤ k → k < 5 + 2 * i → Good k) →
    Rch start (KL (5 + 2 * i) (C0 - i))
  | 0, _, _ => seed_reach
  | i + 1, hi, hg => by
    have ih := reach_i i (by omega) (fun k h1 h2 h3 => hg k h1 h2 (by omega))
    obtain ⟨w, hw⟩ : ∃ w, C0 - i = w + 1 := ⟨C0 - i - 1, by omega⟩
    rw [hw] at ih
    have st := kl_next (5 + 2 * i) w (by omega) (by unfold C0 at hw; omega)
    have g := good_reach (5 + 2 * i) w (by omega) (by omega) (hg _ (by omega) (by omega) (by omega))
    rw [show C0 - (i + 1) = w by omega, show 5 + 2 * (i + 1) = 5 + 2 * i + 2 by omega]
    exact Rch.tr ih (Rch.tr st g)

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- If every odd `k < 509203` has a prime `k·2^n - 1`, the machine reaches its halting state. -/
theorem haltAt_of (h : ∀ k, k % 2 = 1 → k < 509203 → ∃ n, 1 ≤ n ∧ Prime (k * 2 ^ n - 1)) :
    HaltAt start := by
  have := reach_i C0 (Nat.le_refl _) (fun k h1 _ h3 => h k h1 (by unfold C0 at h3; omega))
  rw [Nat.sub_self] at this
  exact HaltAt.back this (kl_halt _)

/-- **Main theorem.** Started on a blank tape, the design halts if and only if every odd
`k < 509203` has some `n ≥ 1` with `k·2^n - 1` prime, i.e. no Riesel number is below 509203. -/
theorem halts_iff :
    Halts delta start ↔ ∀ k, k % 2 = 1 → k < 509203 → ∃ n, 1 ≤ n ∧ Prime (k * 2 ^ n - 1) := by
  constructor
  · intro hH
    have key : ∀ i, i ≤ C0 → ∀ k, k % 2 = 1 → 5 ≤ k → k < 5 + 2 * i → Good k := by
      intro i
      induction i with
      | zero => intro _ k _ _ h; omega
      | succ i ih =>
        intro hi k h1 h2 h3
        by_cases hk : k < 5 + 2 * i
        · exact ih (by omega) k h1 h2 hk
        · obtain rfl : k = 5 + 2 * i := by omega
          have r := reach_i i (by omega) (ih (by omega))
          obtain ⟨w, hw⟩ : ∃ w, C0 - i = w + 1 := ⟨C0 - i - 1, by omega⟩
          rw [hw] at r
          have r2 := Rch.tr r (kl_next (5 + 2 * i) w (by omega) (by unfold C0 at hw; omega))
          apply Classical.byContradiction
          intro hb
          exact bad_loops _ w (by omega) (by omega) hb (halts_det hH r2)
    intro k h1 h2
    rcases Nat.lt_or_ge k 5 with h | h
    · rcases (show k = 1 ∨ k = 3 by omega) with rfl | rfl
      · exact good_one
      · exact good_three
    · exact key C0 (Nat.le_refl _) k h1 h (by unfold C0; omega)
  · intro h; exact (haltAt_of h).halts

end TM.Riesel
