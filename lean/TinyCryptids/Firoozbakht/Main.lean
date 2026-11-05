import TinyCryptids.Firoozbakht.Prime

/-!
# Main theorem: the design halts iff Firoozbakht's conjecture fails

Checkpoints: `TC e m pre p post` (trial step of the block `p` for the candidate `m`), where
`pre ++ p :: post = pl m` and `e = (pl m).length + 2`.
-/

namespace TM.Firoozbakht

open St TinyCryptids

local notation "F" => false
local notation "T" => true

/-! ## the list of primes -/

theorem pl_filter : ∀ n, pl n = (List.range n).filter (fun p => decide (Prime p))
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, ← pl_filter n]
    by_cases h : Prime n
    · rw [pl_succ_prime h]; simp [h]
    · rw [pl_succ_not h]; simp [h]

theorem primeCount_pl (x : Nat) : primeCount x = (pl (x + 1)).length := by
  rw [pl_filter]; rfl

theorem pl_three : ∀ k, ∃ r, pl (k + 3) = 2 :: r := by
  intro k
  induction k with
  | zero => exact ⟨[], by decide⟩
  | succ k ih =>
    obtain ⟨r, hr⟩ := ih
    by_cases h : Prime (k + 3)
    · exact ⟨r ++ [k + 3], by rw [show k + 1 + 3 = k + 3 + 1 by omega, pl_succ_prime h, hr]; rfl⟩
    · exact ⟨r, by rw [show k + 1 + 3 = k + 3 + 1 by omega, pl_succ_not h, hr]⟩

theorem pl_eq (m : Nat) (hm : 3 ≤ m) : pl m = 2 :: (pl m).tail := by
  obtain ⟨r, hr⟩ := pl_three (m - 3)
  rw [show m - 3 + 3 = m by omega] at hr
  rw [hr]; rfl

/-- the last prime of `pl m` is the prime before `m` -/
theorem pl_last : ∀ m pre p, pl m = pre ++ [p] → Prime p ∧ p < m ∧ ∀ r, p < r → r < m → ¬ Prime r
  | 0, pre, p, h => by simp [pl] at h
  | m + 1, pre, p, h => by
    by_cases hm : Prime m
    · rw [pl_succ_prime hm] at h
      obtain ⟨-, h2⟩ := List.append_inj' h rfl
      simp only [List.cons.injEq, and_true] at h2
      subst h2
      exact ⟨hm, by omega, fun r h1 h2 => by omega⟩
    · rw [pl_succ_not hm] at h
      obtain ⟨h1, h2, h3⟩ := pl_last m pre p h
      refine ⟨h1, by omega, fun r hr1 hr2 => ?_⟩
      rcases Nat.lt_or_ge r m with h | h
      · exact h3 r hr1 h
      · obtain rfl : r = m := by omega
        exact hm

/-- no prime between `p` and `q`: `pl q = pl p ++ [p]` -/
theorem pl_between (p : Nat) (hp : Prime p) : ∀ j, (∀ r, p < r → r < p + 1 + j → ¬ Prime r) →
    pl (p + 1 + j) = pl p ++ [p]
  | 0, _ => pl_succ_prime hp
  | j + 1, h => by
    rw [show p + 1 + (j + 1) = p + 1 + j + 1 by omega,
      pl_succ_not (h _ (by omega) (by omega)), pl_between p hp j (fun r h1 h2 => h r h1 (by omega))]

theorem prime_two : Prime 2 := by decide

theorem reach1_of {a b : Cfg St} (h : Rch a b) (hq : a.q ≠ b.q) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero =>
    simp only [Sys.run] at hn
    exact absurd (congrArg Cfg.q (Option.some.inj hn)) hq
  | succ n => exact ⟨n, hn⟩

/-! ## the transitions -/

/-- the start of the trial pass for `m ≥ 3` -/
def TS (m : Nat) : Cfg St := TC ((pl m).length + 2) m [] 2 (pl m).tail

/-- a good trial checkpoint -/
def GT (m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) : Prop :=
  3 ≤ m ∧ pre ++ p :: post = pl m ∧ ∀ x ∈ pre, ¬ x ∣ m

/-- the counterexample property of a prime `m`, with `pl m = pre ++ [p]` -/
def Bad (m : Nat) (_pre : List Nat) (p : Nat) : Prop :=
  p ^ ((pl m).length + 1) ≤ m ^ (pl m).length

theorem gt_ts (m : Nat) (hm : 3 ≤ m) : GT m [] 2 (pl m).tail :=
  ⟨hm, (pl_eq m hm).symm, by simp⟩

theorem ts_of_mse (m : Nat) (hm : 3 ≤ m) :
    Rch (MSE ((pl (m + 1)).length + 2) m (pl (m + 1))) (TS (m + 1)) := by
  have h := pl_eq (m + 1) (by omega)
  have := next_cand ((pl (m + 1)).length + 2) m 2 (pl (m + 1)).tail (by omega) (by omega)
  rw [← h] at this
  exact this

/-- one trial step -/
theorem trial_step (m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) (hg : GT m pre p post) :
    (p ∣ m → Rch1 (TC ((pl m).length + 2) m pre p post) (TS (m + 1)) ∧ ¬ Prime m) ∧
    (¬ p ∣ m → ∀ q post', post = q :: post' →
      Rch1 (TC ((pl m).length + 2) m pre p post) (TC ((pl m).length + 2) m (pre ++ [p]) q post') ∧
      GT m (pre ++ [p]) q post') ∧
    (¬ p ∣ m → post = [] → Prime m ∧ (Bad m pre p → HaltAt (TC ((pl m).length + 2) m pre p post)) ∧
      (¬ Bad m pre p → Rch1 (TC ((pl m).length + 2) m pre p post) (TS (m + 1)))) := by
  obtain ⟨hm, hl, hx⟩ := hg
  have hpl : p ∈ pl m := by rw [← hl]; simp
  have hp2 := pl_two_le hpl
  have hc := trial_cyc ((pl m).length + 2) m pre p post (by omega) (by omega)
  refine ⟨fun hd => ?_, fun hd q post' hpost => ?_, fun hd hpost => ?_⟩
  · rw [if_pos hd] at hc
    have hnp : ¬ Prime m := fun hpm => (prime_iff_pl m (by omega)).1 hpm p hpl hd
    refine ⟨Reach1.trans_reach delta (reach1_of hc (by simp [TC])) ?_, hnp⟩
    refine Rch.tr (trial_div _ m pre p post (by omega)) ?_
    rw [hl]
    refine Rch.tr (ms_end _ m _ (by omega)) ?_
    have := ts_of_mse m hm
    rwa [pl_succ_not hnp] at this
  · rw [if_neg hd] at hc
    subst hpost
    refine ⟨Reach1.trans_reach delta (reach1_of hc (by simp [TC])) (trial_next _ m pre p q post'), ?_⟩
    refine ⟨hm, by rw [← hl]; simp, fun x hx' => ?_⟩
    rcases List.mem_append.1 hx' with h | h
    · exact hx x h
    · simp at h; subst h; exact hd
  · rw [if_neg hd] at hc
    subst hpost
    have hP : Prime m := by
      rw [prime_iff_pl m (by omega)]
      intro y hy hyd
      rw [← hl] at hy
      rcases List.mem_append.1 hy with h | h
      · exact hx y h hyd
      · simp at h; subst h; exact hd hyd
    have hlen : (pl m).length = pre.length + 1 := by rw [← hl]; simp
    have hs := prime_step ((pl m).length + 2) m pre p (by omega) (by omega) hp2
    rw [show (pl m).length + 2 - 1 = (pl m).length + 1 by omega,
      show (pl m).length + 2 - 2 = (pl m).length by omega] at hs
    refine ⟨hP, fun hb => HaltAt.back hc (hs.1 hb), fun hb => ?_⟩
    refine Reach1.trans_reach delta (reach1_of hc (by simp [TC])) (Rch.tr (hs.2 (by unfold Bad at hb; omega)) ?_)
    have := ts_of_mse m hm
    rw [pl_succ_prime hP, ← hl] at this
    rw [← hl, show (pre ++ [p]).length + 2 + 1 = (pre ++ [p, m]).length + 2 by simp]
    rw [show pre ++ [p] ++ [m] = pre ++ [p, m] by simp] at this
    exact this

/-! ## the seed -/

theorem seed_reach : Rch start (MSE 3 2 [2]) := by
  unfold start
  iterate 17 (refine blankR ?_; gR)
  unfold MSE lft
  simp only [seps, skp, List.replicate, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.singleton_append, List.append_assoc, app_cons, app_nil,
    app_append, cons_blank, tl_blank, ones_succ, ones_zero]
  fin

theorem pl_three' : pl 3 = [2] := by decide

theorem start_reach : Rch start (TS 3) := by
  refine Rch.tr seed_reach ?_
  have h := next_cand 3 2 2 [] (by omega) (by omega)
  unfold TS; rw [pl_three']; exact h

/-! ## the counterexample condition at a prime -/

theorem bad_iff {m : Nat} {pre : List Nat} {p : Nat} (hl : pl m = pre ++ [p]) :
    Bad m pre p ↔ p ^ (primeCount p + 1) ≤ m ^ primeCount p := by
  obtain ⟨hp, hpm, hno⟩ := pl_last m pre p hl
  have h1 := pl_between p hp (m - p - 1) (fun r h1 h2 => hno r h1 (by omega))
  rw [show p + 1 + (m - p - 1) = m by omega] at h1
  have h2 : primeCount p = (pl m).length := by
    rw [primeCount_pl, pl_succ_prime hp, h1]
  rw [h2]; rfl

/-! ## no counterexample: no halting -/

/-- the statement: consecutive primes `p < q` with `p ^ (π(p) + 1) ≤ q ^ π(p)` -/
def Counter : Prop := ∃ p q, Prime p ∧ Prime q ∧ p < q ∧ (∀ r, p < r → r < q → ¬ Prime r) ∧
  p ^ (primeCount p + 1) ≤ q ^ primeCount p

def Good (c : Cfg St) : Prop :=
  ∃ m pre p post, GT m pre p post ∧ c = TC ((pl m).length + 2) m pre p post

theorem progress (hno : ¬ Counter) : ∀ c, Good c → ∃ c', Good c' ∧ Rch1 c c' := by
  rintro c ⟨m, pre, p, post, hg, rfl⟩
  have hs := trial_step m pre p post hg
  by_cases hd : p ∣ m
  · exact ⟨_, ⟨_, _, _, _, gt_ts (m + 1) (by have := hg.1; omega), rfl⟩, (hs.1 hd).1⟩
  · cases post with
    | nil =>
      obtain ⟨hP, -, h2⟩ := hs.2.2 hd rfl
      have hl : pl m = pre ++ [p] := hg.2.1.symm
      have hb : ¬ Bad m pre p := by
        intro hb
        obtain ⟨hp, hpm, hbt⟩ := pl_last m pre p hl
        exact hno ⟨p, m, hp, hP, hpm, hbt, (bad_iff hl).1 hb⟩
      exact ⟨_, ⟨_, _, _, _, gt_ts (m + 1) (by have := hg.1; omega), rfl⟩, h2 hb⟩
    | cons q post' =>
      exact ⟨_, ⟨_, _, _, _, (hs.2.1 hd q post' rfl).2, rfl⟩, (hs.2.1 hd q post' rfl).1⟩

theorem not_halts (hno : ¬ Counter) : ¬ Halts delta start := by
  intro hH
  exact not_halts_of_progress delta Good (progress hno) (TS 3)
    ⟨_, _, _, _, gt_ts 3 (Nat.le_refl _), rfl⟩ (Sys.Halts.of_reach start_reach hH)

/-! ## a counterexample: halting -/

theorem pass_trial (m : Nat)
    (hh : HaltAt (TS (m + 1)) ∨ (Prime m ∧ ∀ pre p, pl m = pre ++ [p] → Bad m pre p)) :
    ∀ k pre p post, post.length = k → GT m pre p post → HaltAt (TC ((pl m).length + 2) m pre p post) := by
  intro k
  induction k with
  | zero =>
    intro pre p post hk hg
    obtain rfl : post = [] := List.eq_nil_of_length_eq_zero hk
    have hs := trial_step m pre p [] hg
    by_cases hd : p ∣ m
    · have ⟨h1, hnp⟩ := hs.1 hd
      rcases hh with h | ⟨hp, _⟩
      · exact HaltAt.back h1.reach h
      · exact absurd hp hnp
    · obtain ⟨-, h1, h2⟩ := hs.2.2 hd rfl
      by_cases hb : Bad m pre p
      · exact h1 hb
      · rcases hh with h | ⟨_, hB⟩
        · exact HaltAt.back (h2 hb).reach h
        · exact absurd (hB pre p hg.2.1.symm) hb
  | succ k ih =>
    intro pre p post hk hg
    have hs := trial_step m pre p post hg
    by_cases hd : p ∣ m
    · have ⟨h1, hnp⟩ := hs.1 hd
      rcases hh with h | ⟨hp, _⟩
      · exact HaltAt.back h1.reach h
      · exact absurd hp hnp
    · cases post with
      | nil => simp at hk
      | cons q post' =>
        have ⟨h1, hg'⟩ := hs.2.1 hd q post' rfl
        exact HaltAt.back h1.reach (ih _ _ _ (by simp at hk; omega) hg')

/-- If Firoozbakht's conjecture fails, the machine reaches its halting state. -/
theorem haltAt_of (h : Counter) : HaltAt start := by
  obtain ⟨p0, q0, hp0, hq0, hlt, hbt, hb⟩ := h
  have h3 : 3 ≤ q0 := by have := hp0.two_le; omega
  have hl : pl q0 = pl p0 ++ [p0] := by
    have := pl_between p0 hp0 (q0 - p0 - 1) (fun r h1 h2 => hbt r h1 (by omega))
    rwa [show p0 + 1 + (q0 - p0 - 1) = q0 by omega] at this
  have hB : ∀ pre p, pl q0 = pre ++ [p] → Bad q0 pre p := by
    intro pre p h
    rw [hl] at h
    obtain ⟨rfl, h2⟩ := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true] at h2
    subst h2
    rw [← hl] at h
    exact (bad_iff (by rw [hl])).2 hb
  suffices H : ∀ d m, q0 - m = d → 3 ≤ m → m ≤ q0 → HaltAt (TS m) from
    HaltAt.back start_reach (H _ 3 rfl (Nat.le_refl _) h3)
  intro d
  induction d with
  | zero =>
    intro m hd' hm hmm
    obtain rfl : m = q0 := by omega
    exact pass_trial m (Or.inr ⟨hq0, hB⟩) _ _ _ _ rfl (gt_ts m hm)
  | succ d ih =>
    intro m hd' hm hmm
    exact pass_trial m (Or.inl (ih (m + 1) (by omega) (by omega) (by omega))) _ _ _ _ rfl (gt_ts m hm)

/-- **Main theorem.** Started on a blank tape, the design halts if and only if there are
consecutive primes `p < q` with `p ^ (π(p) + 1) ≤ q ^ π(p)` (Firoozbakht's conjecture fails). -/
theorem halts_iff : Halts delta start ↔
    ∃ p q, Prime p ∧ Prime q ∧ p < q ∧ (∀ r, p < r → r < q → ¬ Prime r) ∧
      p ^ (primeCount p + 1) ≤ q ^ primeCount p := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    exact not_halts hno hH
  · intro h; exact (haltAt_of h).halts

end TM.Firoozbakht
