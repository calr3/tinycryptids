import TinyCryptids.ABC.Power
import TinyCryptids.ABC.Spec

/-!
# Main theorem: some beep count between boops repeats forever iff the abc conjecture fails

The design enumerates the pairs `(a, c)`, `1 ≤ a < c`, `b = c - a` (`pairAt`). For each pair the
factor loop runs `d = 2, …, c`: at `d = c` a hit on `A` means `gcd(a, b) ≠ 1` (the pair is
skipped); otherwise `R = rad(abc)` (`rfrom_rad`). The pre-test skips the pair if `c ≤ R`;
otherwise the power loop beeps `val c R` times and then boops (`power`). So the run is cut into
segments, one per pair, whose events are `[]` or `val` beeps and a boop (`pair_trace`), and
`repeatsForever_of_segments` with `good_iff` gives the theorem.
-/

namespace TM.ABC
open St TinyCryptids

local notation "F" => false
local notation "T" => true

set_option maxHeartbeats 0 in
theorem deltaQ_eq (q : St) (b : Bool) (h : ¬ (q = xe3 ∧ b = false)) (h' : ¬ (q = xq6 ∧ b = false)) :
    deltaQ q b = delta q b := by
  cases q <;> cases b <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h | exact absurd ⟨rfl, rfl⟩ h'

theorem deltaQ_sub : ∀ q b t, deltaQ q b = some t → delta q b = some t := by
  intro q b t h
  by_cases h1 : q = xe3 ∧ b = false
  · obtain ⟨rfl, rfl⟩ := h1; cases h
  by_cases h2 : q = xq6 ∧ b = false
  · obtain ⟨rfl, rfl⟩ := h2; cases h
  rw [← deltaQ_eq q b h1 h2]; exact h

/-! ## the factor loop -/

theorem dp_next (k d a b c r : Nat) (hd : 1 ≤ d) :
    Rch (dpC (k + 2) d a b c r) (stA (k + 1) (d + 1) a b c r) := by
  have := next_d k d (ones a (app (S2 ++ Bk b ++ S2 ++ Bk c ++ S2 ++ [T] ++ S2 ++ Bm r) blank)) hd
  simp only [dpC, stA, fT, fr, blkx, Bm, Bk, S2, List.append_assoc, List.cons_append, List.singleton_append,
    List.nil_append, app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero] at this ⊢
  exact this

/-- one trial divisor with `K ≥ 2`: the tests, then `R := rstep R d` -/
theorem fround (k d a b c r : Nat) (hd : 2 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hr : 1 ≤ r) :
    Rch (stA (k + 2) d a b c r) (dpC (k + 2) d a b c (rstep a b c r d)) := by
  have hR : (Nat.gcd a d ≠ 1 ∨ Nat.gcd b d ≠ 1 ∨ Nat.gcd c d ≠ 1) →
      Rch (stR (k + 2) d a b c r) (dpC (k + 2) d a b c (rstep a b c r d)) := by
    intro hit
    unfold rstep
    by_cases hg : Nat.gcd r d = 1
    · rw [if_pos ⟨hit, hg⟩]; exact new_R _ _ _ _ _ _ hd hr hg
    · rw [if_neg (fun h => hg h.2)]; exact notnew_R _ _ _ _ _ _ hd hr hg
  by_cases hA : Nat.gcd a d = 1
  · refine Rch.tr (pass_A _ _ _ _ _ _ hd ha hA) ?_
    by_cases hB : Nat.gcd b d = 1
    · refine Rch.tr (pass_B _ _ _ _ _ _ hd hb hB) ?_
      by_cases hC : Nat.gcd c d = 1
      · have e : rstep a b c r d = r := by
          unfold rstep; rw [if_neg]; rintro ⟨h | h | h, _⟩ <;> contradiction
        rw [e]; exact pass_C _ _ _ _ _ _ hd hc hC
      · exact Rch.tr (hit_C _ _ _ _ _ _ hd hc hC) (hR (Or.inr (Or.inr hC)))
    · exact Rch.tr (hit_B _ _ _ _ _ _ hd hb hB) (hR (Or.inr (Or.inl hB)))
  · exact Rch.tr (hit_A _ _ _ _ _ _ hd ha hA) (hR (Or.inl hA))

theorem factor_loop (a b c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    ∀ k d r, d + k = c → 2 ≤ d → 1 ≤ r →
      Rch (stA (k + 1) d a b c r) (stA 1 c a b c (rfrom a b c r d k)) := by
  intro k
  induction k with
  | zero => intro d r h _ _; rw [show d = c by omega]; fin
  | succ k ih =>
    intro d r h hd hr
    refine Rch.tr (fround k d a b c r hd ha hb hc hr) ?_
    refine Rch.tr (dp_next k d a b c _ (by omega)) ?_
    exact ih (d + 1) _ (by omega) (by omega) (rstep_pos hr (by omega))

theorem rfrom_succ (a b c : Nat) : ∀ k r d, rfrom a b c r d (k + 1) = rstep a b c (rfrom a b c r d k) (d + k) := by
  intro k
  induction k with
  | zero => intro r d; rfl
  | succ k ih =>
    intro r d
    show rfrom a b c (rstep a b c r d) (d + 1) (k + 1) = _
    rw [ih]; show rstep a b c (rfrom a b c (rstep a b c r d) (d + 1) k) _ = _
    rw [show d + 1 + k = d + (k + 1) by omega]; rfl

/-- `d = c`, coprime: the tests pass on `A`, `B`, hit `C`; then the pre-test -/
theorem last_cop (a b c r : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : a + b = c) (hr : 1 ≤ r)
    (hg : Nat.gcd a b = 1) :
    Rch (stA 1 c a b c r) ⟨pt1, app (preL c a b c) blank, F ::: ones (rstep a b c r c) blank⟩ := by
  have hA : Nat.gcd a c = 1 := by rw [← hc, gcd_ac]; exact hg
  have hB : Nat.gcd b c = 1 := by rw [← hc, gcd_bc]; exact hg
  have hC : Nat.gcd c c ≠ 1 := by rw [Nat.gcd_self]; omega
  refine Rch.tr (pass_A _ _ _ _ _ _ (by omega) ha hA) ?_
  refine Rch.tr (pass_B _ _ _ _ _ _ (by omega) hb hB) ?_
  refine Rch.tr (hit_C _ _ _ _ _ _ (by omega) (by omega) hC) ?_
  have hd : Rch (stR 1 c a b c r) (dpC 1 c a b c (rstep a b c r c)) := by
    unfold rstep
    by_cases h : Nat.gcd r c = 1
    · rw [if_pos ⟨Or.inr (Or.inr hC), h⟩]; exact new_R _ _ _ _ _ _ (by omega) hr h
    · rw [if_neg (fun h' => h h'.2)]; exact notnew_R _ _ _ _ _ _ (by omega) hr h
  exact Rch.tr hd (last_d a b c c _ (rstep_pos hr (by omega)))

/-! ## one pair -/

/-- the start of the pair `(a, c)`: `K = c - 1`, `d = 2`, `R = 1` -/
def pS (a c : Nat) : Cfg St := stA (c - 1) 2 a (c - a) c 1

theorem pair_next (a c : Nat) {w : List Bool} (ha : 1 ≤ a) (hac : a < c) (hw : Clean12 (T :: w)) :
    Rch (peC 1 c a (c - a) c (T :: w)) (pS (nextPair (a, c)).1 (nextPair (a, c)).2) := by
  refine Rch.tr (pe_erase 1 c a (c - a) c hw) ?_
  by_cases h : a + 1 < c
  · rw [show nextPair (a, c) = (a + 1, c) by simp [nextPair, h]]
    obtain ⟨b', hb'⟩ : ∃ b', c - a = b' + 2 := ⟨c - a - 2, by omega⟩
    rw [hb']
    have := next_ab 1 c a b' c (by omega) (by omega)
    rw [show 1 + c - 2 = c - 1 by omega] at this
    unfold pS; rw [show c - (a + 1) = b' + 1 by omega]; exact this
  · rw [show nextPair (a, c) = (1, c + 1) by simp [nextPair, h]]
    obtain rfl : c = a + 1 := by omega
    rw [show a + 1 - a = 1 by omega]
    have := next_c 1 (a + 1) a (a + 1) (by omega) (by omega) ha rfl
    rw [show 1 + 1 + (a + 1) - 2 = a + 1 by omega] at this
    unfold pS; rw [show a + 1 + 1 - 1 = a + 1 by omega]; exact this

abbrev Tr := Trace delta deltaQ xe3 F xq6 F

theorem Tr.pre {x y z : Cfg St} {es : List Bool} (h : Rch x y) (t : Tr y es z) : Tr x es z := by
  have := (Trace.nil (δ := delta) (qb := xe3) (bb := F) (qo := xq6) (bo := F) h).append t deltaQ_sub
  simpa using this

theorem Tr.post {x y z : Cfg St} {es : List Bool} (t : Tr x es y) (h : Rch y z) : Tr x es z := by
  have := t.append (Trace.nil (δ := delta) (qb := xe3) (bb := F) (qo := xq6) (bo := F) h) deltaQ_sub
  simpa using this

/-- the power loop: after `n` beeps, `P = c ^ n`, `Q = r ^ n`; `val c r - n` more beeps, then the
boop -/
theorem power (a b c r : Nat) (hc : 2 ≤ c) (hr : 2 ≤ r) (hrc : r < c) :
    ∀ j n, n + j = val c r →
      Tr (qE a b c r (c ^ n) (r ^ n)) (List.replicate j true ++ [false])
        (peC 1 c a b c (Bk r ++ S2 ++ Bk (r ^ val c r * r))) := by
  have hv := val_spec (show 1 ≤ r by omega) hrc
  have hcp : ∀ n, 1 ≤ c ^ n := fun n => Nat.pos_pow_of_pos n (by omega)
  have hrp : ∀ n, 1 ≤ r ^ n := fun n => Nat.pos_pow_of_pos n (by omega)
  intro j
  induction j with
  | zero =>
    intro n hn
    obtain rfl : n = val c r := by omega
    refine Tr.pre (q_mult a b c r _ _ hr (hcp _) (hrp _)) ?_
    have hq1 : 1 ≤ r ^ val c r * r := Nat.mul_le_mul (hrp (val c r)) (show 1 ≤ r by omega)
    refine Tr.pre (loop_boop a b c r _ _ hq1 hv.1) ?_
    exact Trace.boop (Reach.refl deltaQ _) rfl rfl rfl (Trace.nil (boop_end a b c r _ _))
  | succ j ih =>
    intro n hn
    have hle : c ^ n ≤ r ^ n * r := hv.2 n (by omega)
    refine Tr.pre (q_mult a b c r _ _ hr (hcp _) (hrp _)) ?_
    refine Tr.pre (loop_beep a b c r _ _ (hcp _) hle) ?_
    refine Trace.beep (Reach.refl deltaQ _) rfl rfl rfl ?_
    refine Tr.pre (beep_step a b c r _ _ hc (hcp _) hle) ?_
    exact ih (n + 1) (by omega)

open Classical in
/-- the events of the pair `(a, c)` -/
noncomputable def evsOf (a c : Nat) : List Bool :=
  if Good a c then List.replicate (val c (rad (a * (c - a) * c))) true ++ [false] else []

theorem rfrom_pos (a b c : Nat) : ∀ k r d, 1 ≤ r → 1 ≤ d → 1 ≤ rfrom a b c r d k := by
  intro k
  induction k with
  | zero => intro r d hr _; exact hr
  | succ k ih => intro r d hr hd; exact ih _ _ (rstep_pos hr hd) (by omega)

theorem pair_trace (a c : Nat) (ha : 1 ≤ a) (hac : a < c) :
    Tr (pS a c) (evsOf a c) (pS (nextPair (a, c)).1 (nextPair (a, c)).2) := by
  obtain ⟨b, rfl⟩ : ∃ b, c = a + b := ⟨c - a, by omega⟩
  have hb : 1 ≤ b := by omega
  have hba : a + b - a = b := by omega
  -- the factor loop up to `d = c - 1`
  have hl := factor_loop a b (a + b) ha hb (by omega) (a + b - 2) 2 1 (by omega) (Nat.le_refl 2) (Nat.le_refl 1)
  rw [show a + b - 2 + 1 = a + b - 1 by omega] at hl
  have hS : pS a (a + b) = stA (a + b - 1) 2 a b (a + b) 1 := by unfold pS; rw [hba]
  rw [hS]
  have hrad : rstep a b (a + b) (rfrom a b (a + b) 1 2 (a + b - 2)) (a + b) = rad (a * b * (a + b)) := by
    rw [← rfrom_rad ha hb rfl]
    have := rfrom_succ a b (a + b) (a + b - 2) 1 2
    rw [show a + b - 2 + 1 = a + b - 1 by omega, show 2 + (a + b - 2) = a + b by omega] at this
    exact this.symm
  generalize rfrom a b (a + b) 1 2 (a + b - 2) = R' at hl hrad
  have hR1 : 1 ≤ R' := by
    apply Classical.byContradiction; intro h
    obtain rfl : R' = 0 := by omega
    have := rad_two_le (n := a * b * (a + b)) (Nat.mul_le_mul (Nat.mul_le_mul ha hb) (show 2 ≤ a + b by omega))
    rw [← hrad] at this
    unfold rstep at this; split at this <;> simp at this
  have hnext : ∀ {w : List Bool}, Clean12 (T :: w) →
      Rch (peC 1 (a + b) a b (a + b) (T :: w)) (pS (nextPair (a, a + b)).1 (nextPair (a, a + b)).2) := by
    intro w hw
    have := pair_next a (a + b) ha (by omega) hw
    rw [hba] at this; exact this
  by_cases hg : Nat.gcd a b = 1
  · have hl2 := last_cop a b (a + b) R' ha hb rfl hR1 hg
    rw [hrad] at hl2
    have hr2 : 2 ≤ rad (a * b * (a + b)) :=
      rad_two_le (Nat.mul_le_mul (Nat.mul_le_mul ha hb) (show 2 ≤ a + b by omega))
    have hpe := pre_entry a b (a + b) _ (by omega) (show 1 ≤ rad (a * b * (a + b)) by omega)
    by_cases hcr : a + b ≤ rad (a * b * (a + b))
    · have hsk := pre_skip a b (a + b) _ (by omega) hcr
      have hev : evsOf a (a + b) = [] := by
        unfold evsOf; rw [if_neg]; rintro ⟨_, h⟩; rw [hba] at h; omega
      rw [hev]
      refine Trace.nil (Rch.tr hl (Rch.tr hl2 (Rch.tr hpe (Rch.tr hsk (hnext ?_)))))
      exact Clean12.one (Clean12.one (Clean12.of_clean (Clean.replicate _)))
    · have hrc : rad (a * b * (a + b)) < a + b := by omega
      have hpp := pre_pass a b (a + b) _ (by omega) (by omega) hrc
      have hpw := power a b (a + b) _ (by omega) hr2 hrc (val (a + b) (rad (a * b * (a + b)))) 0 (by omega)
      have hev : evsOf a (a + b) = List.replicate (val (a + b) (rad (a * b * (a + b)))) true ++ [false] := by
        unfold evsOf; rw [hba, if_pos]; unfold Good; rw [hba]; exact ⟨hg, hrc⟩
      rw [hev]
      refine Tr.pre (Rch.tr hl (Rch.tr hl2 (Rch.tr hpe hpp))) ?_
      refine Tr.post hpw (hnext ?_)
      refine Clean12.of_clean ?_
      show Clean (List.replicate (rad (a * b * (a + b)) + 2) T ++ [F, F] ++ List.replicate (_ + 2) T)
      rw [List.append_assoc]
      exact (Clean.replicate _).append (Clean.sep (Clean.one (Clean.replicate _)))
  · have hnc := hitA_nc (a + b) a b (a + b) R' (by omega) ha (by rw [gcd_ac]; exact hg)
    have hev : evsOf a (a + b) = [] := by
      unfold evsOf; rw [if_neg]; rintro ⟨h, _⟩; rw [hba] at h; exact hg h
    rw [hev]
    refine Trace.nil (Rch.tr hl (Rch.tr hnc (hnext ?_)))
    obtain ⟨R'', rfl⟩ : ∃ R'', R' = R'' + 1 := ⟨R' - 1, by omega⟩
    exact Clean12.one (Clean12.z1 (Clean12.of_clean (Clean.replicate R'')))

/-! ## the run: the seed, then one segment per pair -/

/-- the seed: `K = 1`, `D = 2`, `A = B = 1`, `C = 2`, `M`, then `R := 1`: the pair `(1, 2)` -/
theorem seed : Rch start (pS 1 2) := by
  refine Rch.tr ?_ (wr_go 1 2 1 1 2 (Nat.le_refl 1) (Nat.le_refl 2))
  unfold start
  simp only [ones_succ, ones_zero]
  iterate 27 gRb
  fin

theorem ones_get_lt (a i : Nat) (X : Strm) (h : i < a) : ones a X i = true := by
  induction a generalizing i with
  | zero => omega
  | succ a ih => cases i with
    | zero => rfl
    | succ i => exact ih i (by omega)

theorem ones_get_add (a i : Nat) (X : Strm) : ones a X (a + i) = X i := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih => rw [show a + 1 + i = (a + i) + 1 by omega]; exact ih

theorem ones_get_self (a : Nat) (X : Strm) : ones a X a = X 0 := by
  induction a with
  | zero => rfl
  | succ a ih => exact ih

theorem cons_succ' (b : Bool) (s : Strm) (n : Nat) : (b ::: s) (n + 1) = s n := rfl

theorem pS_ne (a c : Nat) (ha : 1 ≤ a) (hac : a < c) : pS a c ≠ pS (nextPair (a, c)).1 (nextPair (a, c)).2 := by
  intro h
  by_cases h1 : a + 1 < c
  · rw [show nextPair (a, c) = (a + 1, c) by simp [nextPair, h1]] at h
    have := congrArg (fun x : Cfg St => x.R (a + 7)) h
    simp only [pS, stA, fT, fr, blkx, Bm, Bk, S2, List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append, app_cons, app_append, app_replicate, cons_succ', ones_succ, ones_zero] at this
    rw [ones_get_self, show ∀ Y : Strm, (T ::: ones a Y) a = T from fun Y => ones_get_lt (a + 1) a Y (by omega)]
      at this
    exact absurd this (by simp)
  · rw [show nextPair (a, c) = (1, c + 1) by simp [nextPair, h1]] at h
    have := congrArg (fun x : Cfg St => x.L (c - 1 + 3)) h
    simp only [pS, stA, fT, cons_succ', Nat.add_sub_cancel] at this
    rw [ones_get_self, ones_get_lt c (c - 1) blank (by omega)] at this
    exact absurd this (by simp [blank])

theorem pair_trace' (k : Nat) :
    Tr (pS (pairAt k).1 (pairAt k).2) (evsOf (pairAt k).1 (pairAt k).2) (pS (pairAt (k + 1)).1 (pairAt (k + 1)).2) :=
  pair_trace _ _ (pairAt_spec k).1 (pairAt_spec k).2.1

theorem hne : ¬ (xq6 = xe3 ∧ F = F) := fun h => by cases h.1

/-- the beeps and the boops of the run from the start -/
abbrev Bp := BeepsAt delta xe3 F start
abbrev Bo := BeepsAt delta xq6 F start

theorem seg_ex (k n : Nat) (hn : run delta n start = some (pS (pairAt k).1 (pairAt k).2)) :
    ∃ m, run delta (n + m) start = some (pS (pairAt (k + 1)).1 (pairAt (k + 1)).2) ∧
      TM.evs Bp Bo n (n + m) = evsOf (pairAt k).1 (pairAt k).2 :=
  (pair_trace' k).evs deltaQ_sub rfl rfl hne hn

theorem seed_ex : ∃ m, run delta (0 + m) start = some (pS (pairAt 0).1 (pairAt 0).2) ∧
    TM.evs Bp Bo 0 (0 + m) = [] :=
  (Trace.nil seed : Tr start [] (pS 1 2)).evs deltaQ_sub rfl rfl hne rfl

/-- the step at which the `k`-th pair starts -/
noncomputable def TT : (k : Nat) → {n : Nat // run delta n start = some (pS (pairAt k).1 (pairAt k).2)}
  | 0 => ⟨0 + Classical.choose seed_ex, (Classical.choose_spec seed_ex).1⟩
  | k + 1 => ⟨(TT k).1 + Classical.choose (seg_ex k (TT k).1 (TT k).2),
      (Classical.choose_spec (seg_ex k (TT k).1 (TT k).2)).1⟩

noncomputable def Tm (k : Nat) : Nat := (TT k).1

theorem Tm_zero : TM.evs Bp Bo 0 (Tm 0) = [] := (Classical.choose_spec seed_ex).2

theorem Tm_seg (k : Nat) : TM.evs Bp Bo (Tm k) (Tm (k + 1)) = evsOf (pairAt k).1 (pairAt k).2 :=
  (Classical.choose_spec (seg_ex k (TT k).1 (TT k).2)).2

theorem Tm_lt (k : Nat) : Tm k < Tm (k + 1) := by
  show (TT k).1 < (TT k).1 + Classical.choose (seg_ex k (TT k).1 (TT k).2)
  rcases Nat.eq_zero_or_pos (Classical.choose (seg_ex k (TT k).1 (TT k).2)) with e | e
  · exfalso
    have h3 := (Classical.choose_spec (seg_ex k (TT k).1 (TT k).2)).1
    rw [e, Nat.add_zero, (TT k).2] at h3
    exact pS_ne _ _ (pairAt_spec k).1 (pairAt_spec k).2.1 (Option.some.inj h3)
  · omega

theorem Tm_ge (k : Nat) : k ≤ Tm k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => have := Tm_lt k; omega

/-! ## the main theorems -/

/-- The design never halts. -/
theorem never_halts : ¬ Halts delta start := by
  rintro ⟨n, hn⟩
  have := run_none_mono (δ := delta) hn (Tm n - n)
  rw [show n + (Tm n - n) = Tm n by have := Tm_ge n; omega] at this
  have h2 : run delta (Tm n) start = some _ := (TT n).2
  rw [h2] at this; cases this

theorem no_both (n : Nat) : ¬ (Bp n ∧ Bo n) := by
  rintro ⟨⟨c1, h1, q1, -⟩, ⟨c2, h2, q2, -⟩⟩
  rw [h1] at h2; cases h2; rw [q1] at q2; cases q2

/-- **Main theorem.** Started on a blank tape, the design never halts, and some number of beeps
(`xe3` reading 0) between consecutive boops (`xq6` reading 0) occurs infinitely often iff the
abc conjecture is false. -/
theorem repeats_iff : RepeatsForever delta xe3 false xq6 false start ↔ ¬ ABCConjecture := by
  rw [repeatsForever_of_segments delta xe3 F xq6 F start no_both Tm Tm_lt
    (fun k => Good (pairAt k).1 (pairAt k).2)
    (fun k => val (pairAt k).2 (rad ((pairAt k).1 * ((pairAt k).2 - (pairAt k).1) * (pairAt k).2)))
    Tm_zero Tm_seg]
  exact good_iff

end TM.ABC
