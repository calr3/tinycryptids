import TinyCryptids.FeitThompson.Pair

/-!
# Main theorem: the design halts iff the Feit–Thompson conjecture fails

Checkpoints: `TC m pre p post` (trial step of the block `p` for the candidate `m`) and
`PC m pre p post` (pair step of the block `p`), where `pre ++ p :: post = 1 :: pl m`.
-/

namespace TM.FeitThompson

open St TinyCryptids

local notation "F" => false
local notation "T" => true

/-! ## the list of primes -/

theorem pl_three : ∀ k, ∃ r, pl (k + 3) = 2 :: r := by
  intro k
  induction k with
  | zero => exact ⟨[], by decide⟩
  | succ k ih =>
    obtain ⟨r, hr⟩ := ih
    by_cases h : Prime (k + 3)
    · exact ⟨r ++ [k + 3], by rw [show k + 1 + 3 = k + 3 + 1 by omega, pl_succ_prime h, hr]; rfl⟩
    · exact ⟨r, by rw [show k + 1 + 3 = k + 3 + 1 by omega, pl_succ_not h, hr]⟩

/-- the start of the trial pass for `m ≥ 3` -/
def TS (m : Nat) : Cfg St := TC m [1] 2 (pl m).tail

theorem pl_eq (m : Nat) (hm : 3 ≤ m) : pl m = 2 :: (pl m).tail := by
  obtain ⟨r, hr⟩ := pl_three (m - 3)
  rw [show m - 3 + 3 = m by omega] at hr
  rw [hr]; rfl

theorem prime_two : Prime 2 := by decide

theorem pl_two : pl 2 = [] := by decide

theorem reach1_of {a b : Cfg St} (h : Rch a b) (hq : a.q ≠ b.q) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero =>
    simp only [Sys.run] at hn
    exact absurd (congrArg Cfg.q (Option.some.inj hn)) hq
  | succ n => exact ⟨n, hn⟩

/-! ## the transitions -/

/-- a good trial checkpoint -/
def GT (m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) : Prop :=
  3 ≤ m ∧ pre ++ p :: post = 1 :: pl m ∧ pre ≠ [] ∧ ∀ x ∈ pre, x = 1 ∨ ¬ x ∣ m

/-- a good pair checkpoint -/
def GP (m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) : Prop :=
  Prime m ∧ pre ++ p :: post = 1 :: pl m

theorem mem_tail {pre : List Nat} {p : Nat} {post : List Nat} {m x : Nat}
    (h : pre ++ p :: post = 1 :: pl m) (hpre : pre ≠ []) (hx : x ∈ p :: post) : x ∈ pl m := by
  obtain ⟨a, pre', rfl⟩ : ∃ a pre', pre = a :: pre' := by
    cases pre with
    | nil => exact absurd rfl hpre
    | cons a pre' => exact ⟨a, pre', rfl⟩
  simp only [List.cons_append, List.cons.injEq] at h
  rw [← h.2]; simp [hx]

/-- the next candidate after a composite `m` -/
theorem ts_next (m : Nat) (hm : 3 ≤ m) (hc : ¬ Prime m) :
    Rch ⟨ms, app (skp m ++ seps (1 :: pl m) ++ [F, F] ++ [T, F, T]).reverse blank, ones (m - 1) blank⟩
      (TS (m + 1)) := by
  have h := next_cand m 2 (pl m).tail (by omega)
  rw [← pl_eq m hm] at h
  unfold TS; rw [pl_succ_not hc]; exact h

/-- one trial step -/
theorem trial_step (m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) (hg : GT m pre p post) :
    (p ∣ m → Rch1 (TC m pre p post) (TS (m + 1)) ∧ ¬ Prime m) ∧
    (¬ p ∣ m → ∀ q post', post = q :: post' → Rch1 (TC m pre p post) (TC m (pre ++ [p]) q post') ∧
      GT m (pre ++ [p]) q post') ∧
    (¬ p ∣ m → post = [] → Rch1 (TC m pre p post) (PC m pre p []) ∧ GP m pre p []) := by
  obtain ⟨hm, hl, hne, hx⟩ := hg
  have hpl : p ∈ pl m := mem_tail hl hne (by simp)
  have hp2 := pl_two_le hpl
  have hc := trial_cyc m pre p post (by omega) (by omega)
  refine ⟨fun hd => ?_, fun hd q post' hpost => ?_, fun hd hpost => ?_⟩
  · rw [if_pos hd] at hc
    have hnp : ¬ Prime m := fun hpm => (prime_iff_pl m (by omega)).1 hpm p hpl hd
    refine ⟨Reach1.trans_reach delta (reach1_of hc (by simp [TC])) ?_, hnp⟩
    refine Rch.tr (trial_div m pre p post (by omega)) ?_
    rw [hl]; exact ts_next m hm hnp
  · rw [if_neg hd] at hc
    subst hpost
    refine ⟨Reach1.trans_reach delta (reach1_of hc (by simp [TC])) (trial_next m pre p q post'), ?_⟩
    refine ⟨hm, by rw [← hl]; simp, by simp, fun x hx' => ?_⟩
    rcases List.mem_append.1 hx' with h | h
    · exact hx x h
    · simp at h; subst h; exact Or.inr hd
  · rw [if_neg hd] at hc
    subst hpost
    refine ⟨Reach1.trans_reach delta (reach1_of hc (by simp [TC])) (trial_prime m pre p (by omega)), ?_, hl⟩
    rw [prime_iff_pl m (by omega)]
    intro y hy hyd
    have : y ∈ pre ++ [p] := by
      have : y ∈ 1 :: pl m := List.mem_cons_of_mem _ hy
      rw [← hl] at this; simpa using this
    rcases List.mem_append.1 this with h | h
    · rcases hx y h with h1 | h1
      · subst h1; have := pl_two_le hy; omega
      · exact h1 hyd
    · simp at h; subst h; exact hd hyd

theorem gt_ts (m : Nat) (hm : 3 ≤ m) : GT m [1] 2 (pl m).tail :=
  ⟨hm, by rw [pl_eq m hm]; rfl, by simp, by simp⟩

/-- the pair step of `P0`: the next candidate -/
theorem pair_zero (m : Nat) (hp : Prime m) : Rch1 (PC m [] 1 (pl m)) (TS (m + 1)) := by
  have h2 := hp.two_le
  have hps : pl m ++ [m] = 2 :: (pl (m + 1)).tail := by
    rw [← pl_succ_prime hp]; exact pl_eq (m + 1) (by omega)
  exact reach1_of (per_prime m 2 (pl m) _ h2 hps) (by simp [PC, TS, TC])

/-- the pair step of a prime `p < m` -/
theorem pair_trans (m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) (hg : GP m pre p post)
    (hne : pre ≠ []) :
    ∃ pre0 q, pre = pre0 ++ [q] ∧ Prime p ∧ p < m ∧
      (rep m p ∣ rep p m → HaltAt (PC m pre p post)) ∧
      (¬ rep m p ∣ rep p m → Rch1 (PC m pre p post) (PC m pre0 q (p :: post)) ∧ GP m pre0 q (p :: post)) := by
  obtain ⟨hm, hl⟩ := hg
  have hpl : p ∈ pl m := mem_tail hl hne (by simp)
  obtain ⟨hpp, hpm⟩ := (mem_pl m p).1 hpl
  have hp2 := hpp.two_le
  obtain ⟨pre0, q, rfl⟩ : ∃ pre0 q, pre = pre0 ++ [q] := by
    rcases List.eq_nil_or_concat pre with h | ⟨L, b, h⟩
    · exact absurd h hne
    · exact ⟨L, b, by rw [h, List.concat_eq_append]⟩
  obtain ⟨pre', hpre⟩ : ∃ pre', pre0 ++ [q] = 1 :: pre' := by
    cases h : pre0 ++ [q] with
    | nil => simp at h
    | cons a t =>
      rw [h] at hl; simp only [List.cons_append, List.cons.injEq] at hl
      exact ⟨t, by rw [hl.1]⟩
  have hpost : ∀ x ∈ post, 2 ≤ x := fun x hx => pl_two_le (mem_tail hl hne (by simp [hx]))
  have := pair_step m q p pre0 pre' post hpre (by omega) hp2 hpost
  refine ⟨pre0, q, rfl, hpp, hpm, this.1, fun hd => ⟨this.2 hd, hm, ?_⟩⟩
  rw [← hl]; simp

/-! ## the seed -/

theorem seed_reach : Rch start ⟨pw3, F ::: F ::: app (List.replicate 1 T ++ seps [] ++ [F, F] ++ skp 2).reverse
    (F ::: T ::: app (skp 2 ++ seps [] ++ [F, F]).reverse blank), F ::: blank⟩ := by
  unfold start
  iterate 17 (refine blankR ?_; gR)
  simp only [seps, skp, List.replicate, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.singleton_append, List.append_assoc, app_cons, app_nil,
    app_append, cons_blank, tl_blank]
  fin

theorem start_reach : Rch start (TS 3) := by
  refine Rch.tr seed_reach ?_
  have h := pair_h1' 2 [] 1 [] (by omega) (by omega)
  rw [rep_one] at h
  refine Rch.tr h ?_
  exact per_prime_tail 2 2 [] [] (by omega) rfl

/-! ## no counterexample: no halting -/

def Good (c : Cfg St) : Prop :=
  (∃ m pre p post, GT m pre p post ∧ c = TC m pre p post) ∨
  (∃ m pre p post, GP m pre p post ∧ c = PC m pre p post)

theorem gp_nil {m p : Nat} {post : List Nat} (h : GP m [] p post) : p = 1 ∧ post = pl m := by
  have := h.2; simp at this; exact this

theorem progress (hno : ¬ ∃ p m, Prime p ∧ Prime m ∧ p < m ∧ rep m p ∣ rep p m) :
    ∀ c, Good c → ∃ c', Good c' ∧ Rch1 c c' := by
  rintro c (⟨m, pre, p, post, hg, rfl⟩ | ⟨m, pre, p, post, hg, rfl⟩)
  · have hs := trial_step m pre p post hg
    by_cases hd : p ∣ m
    · exact ⟨_, Or.inl ⟨_, _, _, _, gt_ts (m + 1) (by have := hg.1; omega), rfl⟩, (hs.1 hd).1⟩
    · cases post with
      | nil => exact ⟨_, Or.inr ⟨_, _, _, _, (hs.2.2 hd rfl).2, rfl⟩, (hs.2.2 hd rfl).1⟩
      | cons q post' =>
        exact ⟨_, Or.inl ⟨_, _, _, _, (hs.2.1 hd q post' rfl).2, rfl⟩, (hs.2.1 hd q post' rfl).1⟩
  · by_cases hne : pre = []
    · subst hne
      obtain ⟨rfl, rfl⟩ := gp_nil hg
      exact ⟨_, Or.inl ⟨_, _, _, _, gt_ts (m + 1) (by have := hg.1.two_le; omega), rfl⟩,
        pair_zero m hg.1⟩
    · obtain ⟨pre0, q, -, hpp, hpm, -, h2⟩ := pair_trans m pre p post hg hne
      have hnd : ¬ rep m p ∣ rep p m := fun hd => hno ⟨p, m, hpp, hg.1, hpm, hd⟩
      exact ⟨_, Or.inr ⟨_, _, _, _, (h2 hnd).2, rfl⟩, (h2 hnd).1⟩

theorem not_halts (hno : ¬ ∃ p m, Prime p ∧ Prime m ∧ p < m ∧ rep m p ∣ rep p m) :
    ¬ Halts delta start := by
  intro hH
  exact not_halts_of_progress delta Good (progress hno) (TS 3)
    (Or.inl ⟨_, _, _, _, gt_ts 3 (Nat.le_refl _), rfl⟩) (Sys.Halts.of_reach start_reach hH)

/-! ## a counterexample: halting -/

theorem pass_pairs (m : Nat) (hP : Prime m) : ∀ k pre p post, pre.length = k → GP m pre p post →
    (HaltAt (TS (m + 1)) ∨ ∃ x ∈ pre ++ [p], 2 ≤ x ∧ rep m x ∣ rep x m) → HaltAt (PC m pre p post) := by
  intro k
  induction k with
  | zero =>
    intro pre p post hk hg hh
    obtain rfl : pre = [] := List.eq_nil_of_length_eq_zero hk
    obtain ⟨rfl, rfl⟩ := gp_nil hg
    rcases hh with h | ⟨x, hx, h2, _⟩
    · exact HaltAt.back (pair_zero m hP).reach h
    · simp at hx; omega
  | succ k ih =>
    intro pre p post hk hg hh
    have hne : pre ≠ [] := by intro h; subst h; simp at hk
    obtain ⟨pre0, q, rfl, -, -, hdiv, hnd⟩ := pair_trans m pre p post hg hne
    by_cases hd : rep m p ∣ rep p m
    · exact hdiv hd
    · refine HaltAt.back (hnd hd).1.reach (ih pre0 q (p :: post) (by simp at hk; omega) (hnd hd).2 ?_)
      rcases hh with h | ⟨x, hx, h2, h3⟩
      · exact Or.inl h
      · refine Or.inr ⟨x, ?_, h2, h3⟩
        simp only [List.mem_append, List.mem_singleton] at hx ⊢
        rcases hx with (h | h) | h
        · exact Or.inl h
        · exact Or.inr h
        · subst h; exact absurd h3 hd

theorem pass_trial (m : Nat) (hh : HaltAt (TS (m + 1)) ∨ (Prime m ∧ ∃ x ∈ pl m, rep m x ∣ rep x m)) :
    ∀ k pre p post, post.length = k → GT m pre p post → HaltAt (TC m pre p post) := by
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
    · have ⟨h1, hgp⟩ := hs.2.2 hd rfl
      refine HaltAt.back h1.reach (pass_pairs m hgp.1 _ pre p [] rfl hgp ?_)
      rcases hh with h | ⟨_, x, hx, hdx⟩
      · exact Or.inl h
      · refine Or.inr ⟨x, ?_, pl_two_le hx, hdx⟩
        have : x ∈ 1 :: pl m := List.mem_cons_of_mem _ hx
        rw [← hgp.2] at this; simpa using this
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

/-- If some primes `p < m` have `rep m p ∣ rep p m`, the machine reaches its halting state. -/
theorem haltAt_of (h : ∃ p m, Prime p ∧ Prime m ∧ p < m ∧ rep m p ∣ rep p m) : HaltAt start := by
  obtain ⟨p0, m0, hp0, hm0, hlt, hd⟩ := h
  have h3 : 3 ≤ m0 := by have := hp0.two_le; omega
  suffices H : ∀ d m, m0 - m = d → 3 ≤ m → m ≤ m0 → HaltAt (TS m) from
    HaltAt.back start_reach (H _ 3 rfl (Nat.le_refl _) h3)
  intro d
  induction d with
  | zero =>
    intro m hd' hm hmm
    obtain rfl : m = m0 := by omega
    exact pass_trial m (Or.inr ⟨hm0, p0, (mem_pl m p0).2 ⟨hp0, hlt⟩, hd⟩) _ _ _ _ rfl (gt_ts m hm)
  | succ d ih =>
    intro m hd' hm hmm
    exact pass_trial m (Or.inl (ih (m + 1) (by omega) (by omega) (by omega))) _ _ _ _ rfl (gt_ts m hm)

/-- **Main theorem.** Started on a blank tape, the design halts if and only if there are
distinct primes `p`, `q` with `(p^q - 1)/(p - 1) ∣ (q^p - 1)/(q - 1)` (the Feit–Thompson
conjecture fails). -/
theorem halts_iff : Halts delta start ↔ ∃ p q, Prime p ∧ Prime q ∧ p ≠ q ∧ rep p q ∣ rep q p := by
  rw [ft_iff]
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    exact not_halts hno hH
  · intro h; exact (haltAt_of h).halts

end TM.FeitThompson
