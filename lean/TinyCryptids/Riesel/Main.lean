import TinyCryptids.Riesel.Counter

/-!
# Main theorem: the design halts iff no odd k < 509203 is a Riesel number

For `k = 3, 5, …, 509201` the machine tests `Q = k·2^n - 1` by trial division until one
is prime, then moves on to `k + 2`; after the prime for `k = 509201` it halts.  The seed
region lacks R's cell 0, so the first round is a pseudo-round: its candidate is
`3 + 1 + 1 = 5 = 3·2 - 1`, a prime, which starts `k = 3`.  `k = 1` is not run
(`1·2^2 - 1 = 3` is prime).
-/

namespace TM.Riesel

open TinyCryptids
open St

local notation "F" => false

/-! ## checkpoints -/

/-- left of D's separator while `k` is tested: K (`k + 4` cells), its separator, C -/
def XK (k v : Nat) : Strm := ones (k + 4) (F ::: Cs v)

/-- testing `Q = k·2^n - 1`: the mod walk starts with `d = 3` (hole home), the R hole at cell 0 -/
def CK (k n v : Nat) : Cfg St := MW (XK k v) 3 (k * 2 ^ n - 1 - 4) 3 0

/-- the step to the next `k`: the loop on K (`k + 3` cells) is over; the head on C's lowest marker -/
def KT (k v : Nat) : Cfg St := cfgL t1 (Cs v) (F ::: F ::: ones (k + 3) (F ::: ones (k + 3) blank))

/-! ## the step to a new k -/

theorem kt_halt (k : Nat) : HaltAt (KT k 0) := cnt_zero _

/-- the loop on K, from its last cell -/
theorem kloop (k v : Nat) : Rch (cfgL s1 (ones (k + 3) (F ::: Cs v)) blank) (KT k v) := loop0 _ _

theorem kt_next (k w : Nat) (hk : 5 ≤ k) (hw : w + 1 < 1048576) : Rch (KT k (w + 1)) (CK k 1 w) := by
  refine Rch.tr (cnt_dec w hw _) (Rch.tr (newk _ (k + 3) (by omega)) ?_)
  refine Rch.tr (loop0 _ _) ?_
  have := dfin (ones (k + 3 + 1) (F ::: Cs w)) (k + 3 - 7) (by omega)
  unfold CK XK
  rw [show k * 2 ^ 1 - 1 - 4 = 2 * (k + 3 - 7) + 3 by rw [Nat.pow_one]; omega,
    show k + 4 = k + 3 + 1 by omega]
  exact this

theorem prime5 : Prime (3 + 1 + 1) := by decide

/-- the pseudo-round to `k = 3`: candidate `5`, a prime -/
theorem kt_pseudo_ck (w : Nat) (hw : w + 1 < 1048576) : Rch (KT 3 (w + 1)) (CK 3 1 w) := by
  refine Rch.tr (cnt_dec w hw _) (Rch.tr (newk_pseudo _) ?_)
  refine Rch.tr (loop0 _ 0) ?_
  unfold CK XK
  exact dfin0 _

/-- the seed's step to `k = 3`: its candidate `5 = 3·2 - 1` is a prime; then `k = 5` -/
theorem kt_pseudo (w : Nat) (hw : w + 1 < 1048576) : Rch (KT 3 (w + 1)) (KT 5 w) := by
  refine Rch.tr (kt_pseudo_ck w hw) ?_
  have t := (test (XK 3 w) 1 3 (Nat.le_refl _) (fun e h1 h2 => by
    rw [show e = 2 by omega]; decide)).1 prime5
  refine Rch.tr t (Rch.tr (wipe _ _) ?_)
  rw [show true ::: ones 7 (F ::: Cs w) = ones (5 + 3) (F ::: Cs w) from rfl]
  exact kloop 5 w

/-! ## one candidate -/

theorem ones_blank_get (a i : Nat) : ones a blank i = decide (i < a) := by
  induction a generalizing i with
  | zero => simp [blank]
  | succ a ih => cases i with
    | zero => show true = _; simp
    | succ i => show ones a blank i = _; rw [ih]; simp

theorem mw_R (Y : Strm) (r i : Nat) : (MW Y 3 r 3 0).R (i + 4) = decide (i < r + 1) := by
  show ones (r + 1 - 0) blank i = _
  rw [ones_blank_get, Nat.sub_zero]

/-- a run between two different configurations takes at least one step -/
theorem reach1_of_ne {a b : Cfg St} (h : Rch a b) (hne : a ≠ b) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem cand (k n v : Nat) (hk : 5 ≤ k) (hn : 1 ≤ n) :
    (Prime (k * 2 ^ n - 1) → Rch (CK k n v) (KT (k + 2) v)) ∧
    (¬ Prime (k * 2 ^ n - 1) → Rch1 (CK k n v) (CK k (n + 1) v)) := by
  have hodd := cand_odd k n (by omega) hn
  have hge := cand_ge k n (by omega) hn
  have t := test (XK k v) (k * 2 ^ n - 1 - 4) 3 (Nat.le_refl _) (fun e h1 h2 => by
    rw [show e = 2 by omega, show 3 + (k * 2 ^ n - 1 - 4) + 1 = k * 2 ^ n - 1 by omega]; omega)
  rw [show 3 + (k * 2 ^ n - 1 - 4) + 1 = k * 2 ^ n - 1 by omega] at t
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · refine Rch.tr (t.1 hp) (Rch.tr (wipe _ _) ?_)
    unfold XK
    rw [show true ::: ones (k + 4) (F ::: Cs v) = ones (k + 2 + 3) (F ::: Cs v) from rfl]
    exact kloop (k + 2) v
  · obtain ⟨d, r, hdr, hd, h⟩ := t.2 hp
    have st := Rch.tr h (Rch.tr (comp_end _ d r hd) (Rch.tr (loop0 _ _) (dfin _ _ (by omega))))
    have e : 2 * (d + r - 2) + 3 = k * 2 ^ (n + 1) - 1 - 4 := by rw [cand_succ]; omega
    rw [e] at st
    refine reach1_of_ne st fun hc => ?_
    have := congrArg (fun c => c.R (k * 2 ^ n - 1 - 4 + 1 + 4)) hc
    simp only [CK] at this
    rw [mw_R, mw_R, cand_succ] at this
    simp at this; omega

/-! ## the search over n, then over k -/

theorem search (k v : Nat) (hk : 5 ≤ k) :
    ∀ j n, 1 ≤ n → Prime (k * 2 ^ (n + j) - 1) → Rch (CK k n v) (KT (k + 2) v)
  | 0, n, hn, hp => (cand k n v hk hn).1 hp
  | j + 1, n, hn, hp => by
    by_cases h : Prime (k * 2 ^ n - 1)
    · exact (cand k n v hk hn).1 h
    · refine Rch.tr ((cand k n v hk hn).2 h).reach (search k v hk j (n + 1) (by omega) ?_)
      rw [show n + 1 + j = n + (j + 1) by omega]; exact hp

theorem good_reach (k v : Nat) (hk : 5 ≤ k) (hg : Good k) : Rch (CK k 1 v) (KT (k + 2) v) := by
  obtain ⟨N, hN, hp⟩ := hg
  exact search k v hk (N - 1) 1 (Nat.le_refl _) (by rw [show 1 + (N - 1) = N by omega]; exact hp)

theorem bad_loops (k w : Nat) (hk : 5 ≤ k) (hb : ¬ Good k) : ¬ Halts delta (CK k 1 w) := by
  refine not_halts_of_progress delta (fun c => ∃ n, 1 ≤ n ∧ c = CK k n w) ?_ _ ⟨1, Nat.le_refl _, rfl⟩
  rintro c ⟨n, hn, rfl⟩
  exact ⟨CK k (n + 1) w, ⟨n + 1, by omega, rfl⟩,
    (cand k n w hk hn).2 (fun hp => hb ⟨n, hn, hp⟩)⟩

/-- the counter: one decrement for each tested `k = 3, 5, …, 509201` -/
def C0 : Nat := 254599

/-- the seed writes C (`C0 + 1`) and K, and enters the loop after its first step -/
theorem seed_reach : Rch start (KT 3 (C0 + 1)) := by
  unfold start
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  have := loop_tail (Cs (C0 + 1)) 5 0 0
  simp only [ones_zero, cons_blank] at this
  exact Rch.tr this (loop _ 5 1 1)

/-- before testing `k = 3 + 2i`, if the odd `k` from 3 below it are all good -/
theorem reach_i : ∀ i, i ≤ C0 + 1 → (∀ k, k % 2 = 1 → 3 ≤ k → k < 3 + 2 * i → Good k) →
    Rch start (KT (3 + 2 * i) (C0 + 1 - i))
  | 0, _, _ => seed_reach
  | 1, _, _ => Rch.tr seed_reach (kt_pseudo C0 (by unfold C0; omega))
  | i + 2, hi, hg => by
    have ih := reach_i (i + 1) (by omega) (fun k h1 h2 h3 => hg k h1 h2 (by omega))
    obtain ⟨w, hw⟩ : ∃ w, C0 + 1 - (i + 1) = w + 1 := ⟨C0 - (i + 1), by omega⟩
    rw [hw] at ih
    have st := kt_next (3 + 2 * (i + 1)) w (by omega) (by unfold C0 at hw; omega)
    have g := good_reach (3 + 2 * (i + 1)) w (by omega)
      (hg (3 + 2 * (i + 1)) (by omega) (by omega) (by omega))
    rw [show C0 + 1 - (i + 2) = w by omega,
      show 3 + 2 * (i + 2) = 3 + 2 * (i + 1) + 2 by omega]
    exact Rch.tr ih (Rch.tr st g)

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- If every odd `k < 509203` has a prime `k·2^n - 1`, the machine reaches its halting state. -/
theorem haltAt_of (h : ∀ k, k % 2 = 1 → k < 509203 → ∃ n, 1 ≤ n ∧ Prime (k * 2 ^ n - 1)) :
    HaltAt start := by
  have := reach_i (C0 + 1) (Nat.le_refl _) (fun k h1 _ h3 => h k h1 (by unfold C0 at h3; omega))
  rw [Nat.sub_self] at this
  exact HaltAt.back this (kt_halt _)

/-- **Main theorem.** Started on a blank tape, the design halts if and only if every odd
`k < 509203` has some `n ≥ 1` with `k·2^n - 1` prime, i.e. no Riesel number is below 509203. -/
theorem halts_iff :
    Halts delta start ↔ ∀ k, k % 2 = 1 → k < 509203 → ∃ n, 1 ≤ n ∧ Prime (k * 2 ^ n - 1) := by
  constructor
  · intro hH
    have key : ∀ i, i ≤ C0 → ∀ k, k % 2 = 1 → 3 ≤ k → k < 3 + 2 * i → Good k := by
      intro i
      induction i with
      | zero => intro _ k _ _ h; omega
      | succ i ih =>
        intro hi k h1 h2 h3
        by_cases hk : k < 3 + 2 * i
        · exact ih (by omega) k h1 h2 hk
        · obtain rfl : k = 3 + 2 * i := by omega
          by_cases hi0 : i = 0
          · subst hi0
            exact ⟨1, by omega, prime5⟩
          · have r := reach_i i (by omega) (ih (by omega))
            obtain ⟨w, hw⟩ : ∃ w, C0 + 1 - i = w + 1 := ⟨C0 - i, by omega⟩
            rw [hw] at r
            have r2 := Rch.tr r (kt_next (3 + 2 * i) w (by omega) (by unfold C0 at hw; omega))
            apply Classical.byContradiction
            intro hb
            exact bad_loops (3 + 2 * i) w (by omega) hb (halts_det hH r2)
    intro k h1 h2
    rcases Nat.lt_or_ge k 3 with h | h
    · obtain rfl : k = 1 := by omega
      exact good_one
    · exact key C0 (Nat.le_refl _) k h1 h (by unfold C0; omega)
  · intro h; exact (haltAt_of h).halts

end TM.Riesel
