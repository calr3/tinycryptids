import TinyCryptids.Carmichael.Round

/-!
# Rounds, windows and the main theorem

`RS0 v M f s p` is the start of the round for `M` in the window of `v`: K/R `(1, M - 1)`,
V's hole on its last slot, the flag `f`, B's hole on slot `p`. The window of `v` runs
`M = 2, 3, …, s + 1` (`p = s + 2 - M`), and stops early at a second `M` with `φ(M) = v`.
-/

namespace TM.Carmichael
open St TinyCryptids

local notation "F" => false

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

def RS0 (v M : Nat) (f : Bool) (s p : Nat) : Cfg St := TK 0 0 0 (M - 2) (VX v 0 (WF f s p))

theorem round (v M : Nat) (f : Bool) (s p : Nat) (hM : 2 ≤ M) :
    Rch (RS0 v M f s p) ⟨EC1, PostL (M - 2), VX v (totient M) (WF f s p)⟩ := by
  have := sweep M v hM (WF f s p) (M - 2) 1 (by omega) (Nat.le_refl 1)
  rw [cp_one hM, show M - 1 - 1 = M - 2 by omega] at this; exact this

theorem next_eq (v M : Nat) (f : Bool) (s p : Nat) (hM : 2 ≤ M) :
    TK 0 0 0 (M - 1) (VX v 0 (WF f s (p + 1))) = RS0 v (M + 1) f s (p + 1) := by
  unfold RS0; rw [show M + 1 - 2 = M - 1 by omega]

/-- the first match: set the flag, next round -/
theorem r_first (v M s p : Nat) (hM : 2 ≤ M) (hp : 2 ≤ p) (hps : p ≤ s) (h : totient M = v) :
    Rch1 (RS0 v M false s p) (RS0 v (M + 1) true s (p - 1)) := by
  refine Reach.trans_reach1 delta (round v M false s p hM) ?_
  rw [h]
  refine Reach1.trans_reach delta (cross_match _ _ _) ?_
  unfold WF
  cR; cR
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  rw [show q + 2 - 1 = q + 1 by omega, ← next_eq v M true s q hM]
  exact advance F1s rfl true v M q s hM hps

/-- the first match in the last round: HALT -/
theorem r_first_halt (v M s : Nat) (hM : 2 ≤ M) (h : totient M = v) : HaltAt (RS0 v M false s 1) := by
  refine HaltAt.back (round v M false s 1 hM) ?_
  rw [h]
  refine HaltAt.back (cross_match _ _ _).reach ?_
  unfold WF Bst
  refine ⟨?L, ?R, ?h⟩
  case h =>
    cR; cR
    rw [Nat.sub_self, ones_zero]
    refine Rch.tr (stepL (δ := delta) rfl) ?_
    exact Reach.refl delta _

/-- a second match: the next v -/
theorem r_second (v M s p : Nat) (hM : 2 ≤ M) (hp : 1 ≤ p) (hps : p ≤ s) (h : totient M = v) :
    Rch1 (RS0 v M true s p) (Start (v + 1) (s + 4 * v + 7)) := by
  refine Reach.trans_reach1 delta (round v M true s p hM) ?_
  rw [h]
  exact Reach1.trans_reach delta (cross_match _ _ _) (rebuild2 v (M - 2) s p hp hps)

/-- no match: next round -/
theorem r_none (v M : Nat) (f : Bool) (s p : Nat) (hM : 2 ≤ M) (hp : 2 ≤ p) (hps : p ≤ s)
    (h : totient M ≠ v) : Rch1 (RS0 v M f s p) (RS0 v (M + 1) f s (p - 1)) := by
  refine Reach.trans_reach1 delta (round v M f s p hM) ?_
  refine Reach1.trans_reach delta (cross_nomatch _ _ _ h _) ?_
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  rw [show q + 2 - 1 = q + 1 by omega, ← next_eq v M f s q hM]
  unfold WF
  cases f
  · cR; cR; exact advance F0s rfl false v M q s hM hps
  · cR; cR; exact advance F1s rfl true v M q s hM hps

/-- no match in the last round, one match before: HALT -/
theorem r_none_halt (v M s : Nat) (hM : 2 ≤ M) (h : totient M ≠ v) : HaltAt (RS0 v M true s 1) := by
  refine HaltAt.back (round v M true s 1 hM) ?_
  refine HaltAt.back (cross_nomatch _ _ _ h _).reach ?_
  unfold WF Bst
  refine ⟨?L, ?R, ?h⟩
  case h =>
    cR; cR
    rw [Nat.sub_self, ones_zero]
    refine Rch.tr (stepL (δ := delta) rfl) ?_
    exact Reach.refl delta _

/-- no match in the window: the next v -/
theorem r_none_end (v M s : Nat) (hM : 2 ≤ M) (hs : 1 ≤ s) (h : totient M ≠ v) :
    Rch1 (RS0 v M false s 1) (Start (v + 1) (s + 4 * v + 7)) := by
  refine Reach.trans_reach1 delta (round v M false s 1 hM) ?_
  refine Reach1.trans_reach delta (cross_nomatch _ _ _ h _) ?_
  unfold WF
  cR; cR
  exact rebuild1 v (M - 2) s hs

theorem nm_mono (v : Nat) : ∀ a b, a ≤ b → nm v a ≤ nm v b := by
  intro a b hab
  induction b with
  | zero => rw [show a = 0 by omega]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with h | h
    · rw [h]; exact Nat.le_refl _
    · rw [nm_succ]; have := ih (by omega); omega

/-- The window of `v`: rounds `M, …, s + 1` from round `M`, the flag set iff one `M' < M`
matches. -/
theorem loop (v s : Nat) (hs : 1 ≤ s) : ∀ n M, M + n = s + 1 → 2 ≤ M → nm v (M - 1) ≤ 1 →
    (nm v (s + 1) = 1 → HaltAt (RS0 v M (decide (nm v (M - 1) = 1)) s (s + 2 - M))) ∧
    (nm v (s + 1) ≠ 1 →
      Rch1 (RS0 v M (decide (nm v (M - 1) = 1)) s (s + 2 - M)) (Start (v + 1) (s + 4 * v + 7))) := by
  intro n
  induction n with
  | zero =>
    intro M hM hM2 hle
    have e := nm_succ v (M - 1)
    rw [show M - 1 + 1 = M by omega] at e
    rw [show s + 1 = M by omega, show s + 2 - M = 1 by omega]
    by_cases ht : totient M = v
    · rw [if_pos ht] at e
      by_cases hf : nm v (M - 1) = 1
      · rw [decide_eq_true hf]
        exact ⟨fun h => by omega, fun _ => r_second v M s 1 hM2 (Nat.le_refl 1) hs ht⟩
      · rw [decide_eq_false hf]
        exact ⟨fun _ => r_first_halt v M s hM2 ht, fun h => by omega⟩
    · rw [if_neg ht] at e
      by_cases hf : nm v (M - 1) = 1
      · rw [decide_eq_true hf]
        exact ⟨fun _ => r_none_halt v M s hM2 ht, fun h => by omega⟩
      · rw [decide_eq_false hf]
        exact ⟨fun h => by omega, fun _ => r_none_end v M s hM2 hs ht⟩
  | succ n ih =>
    intro M hM hM2 hle
    have e := nm_succ v (M - 1)
    rw [show M - 1 + 1 = M by omega] at e
    have hmono := nm_mono v M (s + 1) (by omega)
    have ih' := ih (M + 1) (by omega) (by omega)
    rw [show M + 1 - 1 = M by omega, show s + 2 - (M + 1) = s + 2 - M - 1 by omega] at ih'
    by_cases ht : totient M = v
    · rw [if_pos ht] at e
      by_cases hf : nm v (M - 1) = 1
      · rw [decide_eq_true hf]
        exact ⟨fun h => by omega, fun _ => r_second v M s (s + 2 - M) hM2 (by omega) (by omega) ht⟩
      · rw [decide_eq_false hf]
        have hM1 : nm v M = 1 := by omega
        rw [decide_eq_true hM1] at ih'
        have ih'' := ih' (by omega)
        have step := r_first v M s (s + 2 - M) hM2 (by omega) (by omega) ht
        exact ⟨fun h => HaltAt.back step.reach (ih''.1 h), fun h => Sys.Reach1.trans step (ih''.2 h)⟩
    · rw [if_neg ht, Nat.add_zero] at e
      rw [e] at ih'
      have ih'' := ih' (by omega)
      have step := r_none v M (decide (nm v (M - 1) = 1)) s (s + 2 - M) hM2 (by omega) (by omega) ht
      exact ⟨fun h => HaltAt.back step.reach (ih''.1 h), fun h => Sys.Reach1.trans step (ih''.2 h)⟩

theorem window (v s : Nat) (hv : 2 ≤ v) (hs : 1 ≤ s) :
    (nm v (s + 1) = 1 → HaltAt (Start v s)) ∧
    (nm v (s + 1) ≠ 1 → Rch1 (Start v s) (Start (v + 1) (s + 4 * v + 7))) := by
  have := loop v s hs (s - 1) 2 (by omega) (Nat.le_refl 2) (by rw [nm_one hv]; omega)
  rw [nm_one hv, show s + 2 - 2 = s by omega] at this
  exact this

/-! ## the main theorem -/

/-- the window sizes: `s = 11` for `v = 2`, growing by `4v + 7` -/
def sz : Nat → Nat
  | 0 => 11
  | n + 1 => sz n + 4 * (n + 2) + 7

theorem sz_bound : ∀ n, 2 * ((n + 2) * (n + 2)) ≤ sz n + 1 := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    show 2 * ((n + 3) * (n + 3)) ≤ sz n + 4 * (n + 2) + 7 + 1
    have : (n + 3) * (n + 3) = (n + 2) * (n + 2) + 2 * n + 5 := by
      simp only [Nat.add_mul, Nat.mul_add]; omega
    omega

theorem sz_pos (n : Nat) : 1 ≤ sz n := by
  cases n <;> simp [sz] <;> omega

theorem reach (n : Nat) : HaltAt start ∨ Rch start (Start (n + 2) (sz n)) := by
  induction n with
  | zero => exact Or.inr seed
  | succ n ih =>
    rcases ih with h | h
    · exact Or.inl h
    · have w := window (n + 2) (sz n) (by omega) (sz_pos n)
      by_cases hn : nm (n + 2) (sz n + 1) = 1
      · exact Or.inl (HaltAt.back h (w.1 hn))
      · exact Or.inr (Rch.tr h (w.2 hn).reach)

theorem W_bound (v : Nat) (hv : 2 ≤ v) : 2 * (v * v) ≤ sz (v - 2) + 1 := by
  have := sz_bound (v - 2); rw [show v - 2 + 2 = v by omega] at this; exact this

/-- With a counterexample, the machine reaches its halting state. -/
theorem haltAt_of (h : ∃ m, 1 ≤ m ∧ ∀ n, n ≠ m → totient n ≠ totient m) : HaltAt start := by
  rw [exists_iff (fun v => sz (v - 2) + 1) W_bound] at h
  obtain ⟨v, hv, h⟩ := h
  rcases reach (v - 2) with hh | hr
  · exact hh
  · rw [show v - 2 + 2 = v by omega] at hr
    exact HaltAt.back hr ((window v (sz (v - 2)) hv (sz_pos _)).1 h)

/-- **Main theorem.** Started on a blank tape, the design halts if and only if Carmichael's
totient conjecture fails. -/
theorem halts_iff :
    Halts delta start ↔ ∃ m, 1 ≤ m ∧ ∀ n, n ≠ m → totient n ≠ totient m := by
  constructor
  · intro hH
    rw [exists_iff (fun v => sz (v - 2) + 1) W_bound]
    apply Classical.byContradiction
    intro hno
    have all : ∀ n, nm (n + 2) (sz n + 1) ≠ 1 := by
      intro n h; exact hno ⟨n + 2, by omega, by rw [show n + 2 - 2 = n by omega]; exact h⟩
    have prog : ∀ c, (∃ n, c = Start (n + 2) (sz n)) → ∃ c', (∃ n, c' = Start (n + 2) (sz n)) ∧ Rch1 c c' := by
      rintro c ⟨n, rfl⟩
      exact ⟨Start (n + 3) (sz (n + 1)), ⟨n + 1, rfl⟩,
        (window (n + 2) (sz n) (by omega) (sz_pos n)).2 (all n)⟩
    exact not_halts_of_progress delta _ prog _ ⟨0, rfl⟩ (Sys.Halts.of_reach seed hH)
  · intro h; exact (haltAt_of h).halts

end TM.Carmichael
