import TinyCryptids.FermatPrimes.Round
import TinyCryptids.FermatPrimes.Spec

/-!
# Main theorem: the design halts iff some Fermat number `2 ^ 2 ^ n + 1`, `n ≥ 5`, is prime

Candidate `m` (odd, `m ≥ 5`) starts at `CS m g j`: the walk for `d = 3`, with the counter
(`j` cells) `g + 1` blanks right of R. A pass (`FP m`: `m` prime, `m - 1` a power of 2)
reaches `PassCfg (m - 1) g' j`; there the counter loses a cell, or the machine halts if it
was the last one. Any other candidate reaches `CS (m + 2) g' j`. The start passes `m = 3`
and reaches `CS 5 1 5`; the passes up to 65537 are 5, 17, 257, 65537 (`fp_small`), so the run
reaches `CS 65539 g 1`, and from there it halts at the first pass, if there is one.
-/

namespace TM.FermatPrimes

open TinyCryptids
open St

local notation "F" => false

/-- the start of candidate `m`: the walk for `d = 3`, `r = m - 4`, the counter (`j` cells)
after `g + 1` blanks -/
def CS (m g j : Nat) : Cfg St := WS 3 (m - 4) (zeros g (ones j blank))

/-- after the walk for `d` (with `m = d + r + 1`) the D hole is on cell `r % d`; `d` divides
`m` or `m - 1` iff that is D's last or first cell -/
theorem fail_iff (d r : Nat) (hd : 3 ≤ d) :
    ¬ Good (d + r + 1) d ↔ (r % d + 1 = d ∨ r % d = 0) := by
  have e := Nat.div_add_mod r d
  have hc := Nat.mod_lt r (show d > 0 by omega)
  generalize r % d = c at e hc
  generalize r / d = q at e
  have h1 : (d + r + 1) % d = (c + 1) % d := by
    rw [show d + r + 1 = d * (q + 1) + (c + 1) by rw [Nat.mul_add]; omega, Nat.mul_add_mod]
  have h2 : (d + r + 1 - 1) % d = c % d := by
    rw [show d + r + 1 - 1 = d * (q + 1) + c by rw [Nat.mul_add]; omega, Nat.mul_add_mod]
  unfold Good
  rw [h1, h2, Nat.mod_eq_of_lt hc]
  constructor
  · intro h
    apply Classical.byContradiction; intro hno
    exact h ⟨by rw [Nat.mod_eq_of_lt (by omega)]; omega, by omega⟩
  · rintro (h | h) ⟨ha, hb⟩
    · rw [h, Nat.mod_self] at ha; exact ha rfl
    · exact hb h

/-! ## trial division of one candidate -/

/-- the round for `d` (`r = 2 t + 1`, `m = d + r + 1`), every odd `e < d` already passed:
the run reaches the pass if every odd `e` with `d ≤ e ≤ m - 2` passes, and the next candidate
otherwise -/
theorem test : ∀ t d g j, 3 ≤ d → d % 2 = 1 →
    (∀ e, 3 ≤ e → e < d → e % 2 = 1 → Good (d + 2 * t + 2) e) →
    ((∀ e, d ≤ e → e + 2 ≤ d + 2 * t + 2 → e % 2 = 1 → Good (d + 2 * t + 2) e) →
      ∃ g', Rch (WS d (2 * t + 1) (zeros g (ones j blank))) (PassCfg (d + 2 * t + 1) g' j)) ∧
    (¬ (∀ e, d ≤ e → e + 2 ≤ d + 2 * t + 2 → e % 2 = 1 → Good (d + 2 * t + 2) e) →
      ∃ g', Rch (WS d (2 * t + 1) (zeros g (ones j blank))) (CS (d + 2 * t + 4) g' j)) := by
  intro t
  induction t with
  | zero =>
    intro d g j hd hdo _
    have w := Rch.tr (walk_all d 1 (zeros g (ones j blank)) (by omega)) (walk_end d 0 (1 % d) _)
    have hc : 1 % d = 1 := Nat.mod_eq_of_lt (by omega)
    have hf := fail_iff d 1 hd
    rw [hc] at w hf
    by_cases hg : Good (d + 2 * 0 + 2) d
    · have h1 : 1 + 1 ≠ d := fun h => hf.2 (Or.inl h) hg
      have := Rch.tr w (check_ok d 0 1 _ (Nat.le_refl _) (by omega))
      refine ⟨fun _ => ⟨g + 1, ?_⟩, fun hn => absurd (fun e h1 h2 h3 => by
        rw [show e = d by omega]; exact hg) hn⟩
      unfold PassCfg; rw [show d + 2 * 0 + 1 = d + 1 by omega]; exact this
    · have hc1 : 1 + 1 = d := by
        rcases hf.1 hg with h | h
        · exact h
        · omega
      omega
  | succ t ih =>
    intro d g j hd hdo hbelow
    have hc := Nat.mod_lt (2 * (t + 1) + 1) (show d > 0 by omega)
    have w := Rch.tr (walk_all d (2 * (t + 1) + 1) (zeros g (ones j blank)) (by omega))
      (walk_end d (2 * (t + 1)) ((2 * (t + 1) + 1) % d) _)
    have hf := fail_iff d (2 * (t + 1) + 1) hd
    rw [show d + (2 * (t + 1) + 1) + 1 = d + 2 * (t + 1) + 2 by omega] at hf
    generalize (2 * (t + 1) + 1) % d = c at w hf hc
    by_cases hg : Good (d + 2 * (t + 1) + 2) d
    · -- d passes: d := d + 2
      have h1 : c + 1 ≠ d := fun h => hf.2 (Or.inl h) hg
      have h2 : c ≠ 0 := fun h => hf.2 (Or.inr h) hg
      have st := Rch.tr w (check_ok d _ _ _ (by omega) (by omega))
      rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega] at st
      have st2 := Rch.tr st (shift d (2 * t + 1) (F ::: zeros g (ones j blank)) (by omega))
      have h := ih (d + 2) (g + 1) j (by omega) (by omega) (fun e h1 h2 h3 => by
        rw [show d + 2 + 2 * t + 2 = d + 2 * (t + 1) + 2 by omega]
        rcases Nat.lt_or_ge e d with he | he
        · exact hbelow e h1 he h3
        · rw [show e = d by omega]; exact hg)
      rw [show d + 2 + 2 * t + 2 = d + 2 * (t + 1) + 2 by omega,
        show d + 2 + 2 * t + 1 = d + 2 * (t + 1) + 1 by omega,
        show d + 2 + 2 * t + 4 = d + 2 * (t + 1) + 4 by omega] at h
      refine ⟨fun hall => ?_, fun hn => ?_⟩
      · obtain ⟨g', hg'⟩ := h.1 fun e h1 h2 h3 => hall e (by omega) h2 h3
        exact ⟨g', Rch.tr st2 hg'⟩
      · obtain ⟨g', hg'⟩ := h.2 fun hall => hn fun e h1 h2 h3 => by
          rcases Nat.lt_or_ge e (d + 2) with he | he
          · rw [show e = d by omega]; exact hg
          · exact hall e he h2 h3
        exact ⟨g', Rch.tr st2 hg'⟩
    · -- d divides m or m - 1: fail
      have hfail : ∃ g', Rch (WS d (2 * (t + 1) + 1) (zeros g (ones j blank)))
          (CS (d + 2 * (t + 1) + 4) g' j) := by
        refine ⟨g + 1, ?_⟩
        rcases hf.1 hg with h | h
        · obtain rfl : d = c + 1 := by omega
          have := Rch.tr w (check_last c (2 * (t + 1)) _)
          have r := rebuild (c + 1) (2 * (t + 1) + 1) (F ::: zeros g (ones j blank)) (by omega) (by omega)
          unfold CS
          rw [show c + 1 + 2 * (t + 1) + 4 - 4 = c + 1 + (2 * (t + 1) + 1) - 1 by omega]
          exact Rch.tr this r
        · subst h
          have := Rch.tr w (check_first d (2 * (t + 1)) _ (by omega))
          have r := rebuild (d - 1) (2 * (t + 1) + 2) (F ::: zeros g (ones j blank)) (by omega) (by omega)
          unfold CS
          rw [show d + 2 * (t + 1) + 4 - 4 = d - 1 + (2 * (t + 1) + 2) - 1 by omega]
          exact Rch.tr this r
      exact ⟨fun hall => absurd (hall d (Nat.le_refl _) (by omega) hdo) hg, fun _ => hfail⟩

theorem cand_fp (m g j : Nat) (hm : 5 ≤ m) (ho : m % 2 = 1) (h : FP m) :
    ∃ g', Rch (CS m g j) (PassCfg (m - 1) g' j) := by
  have t := test ((m - 5) / 2) 3 g j (Nat.le_refl _) rfl (fun e h1 h2 _ => by omega)
  rw [show 3 + 2 * ((m - 5) / 2) + 2 = m by omega, show 2 * ((m - 5) / 2) + 1 = m - 4 by omega,
    show 3 + 2 * ((m - 5) / 2) + 1 = m - 1 by omega] at t
  exact t.1 fun e h1 h2 h3 => (fp_iff' m hm ho).1 h e (by omega) h2 h3

theorem cand_not (m g j : Nat) (hm : 5 ≤ m) (ho : m % 2 = 1) (h : ¬ FP m) :
    ∃ g', Rch (CS m g j) (CS (m + 2) g' j) := by
  have t := test ((m - 5) / 2) 3 g j (Nat.le_refl _) rfl (fun e h1 h2 _ => by omega)
  rw [show 3 + 2 * ((m - 5) / 2) + 2 = m by omega, show 2 * ((m - 5) / 2) + 1 = m - 4 by omega,
    show 3 + 2 * ((m - 5) / 2) + 4 = m + 2 by omega] at t
  exact t.2 fun hall => h ((fp_iff' m hm ho).2 fun e h1 h2 h3 => hall e h1 h2 h3)

/-- a pass with more than one counter cell: the next candidate -/
theorem after_pass (n g j : Nat) (hn : 2 ≤ n) : Rch (PassCfg n g (j + 2)) (CS (n + 3) (g + 1) (j + 1)) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  refine Rch.tr (pass_more d g j (by omega)) ?_
  have := rebuild (d - 1) 2 (zeros (g + 1) (ones (j + 1) blank)) (by omega) (by omega)
  unfold CS
  rw [show d + 1 + 3 - 4 = d - 1 + 2 - 1 by omega]
  exact this

/-- a passing candidate with more than one counter cell left: the counter loses a cell -/
theorem cand_pass (m g j : Nat) (hm : 5 ≤ m) (ho : m % 2 = 1) (h : FP m) :
    ∃ g', Rch (CS m g (j + 2)) (CS (m + 2) g' (j + 1)) := by
  obtain ⟨g', hg'⟩ := cand_fp m g (j + 2) hm ho h
  have := after_pass (m - 1) g' j (by omega)
  rw [show m - 1 + 3 = m + 2 by omega] at this
  exact ⟨g' + 1, Rch.tr hg' this⟩

/-- candidates `a, a + 2, …, b - 2` that do not pass, with the counter unchanged -/
theorem fails (a j : Nat) (ha : 5 ≤ a) (ho : a % 2 = 1) :
    ∀ k g, (∀ i, i < k → ¬ FP (a + 2 * i)) → ∃ g', Rch (CS a g j) (CS (a + 2 * k) g' j) := by
  intro k
  induction k with
  | zero => intro g _; exact ⟨g, Reach.refl delta _⟩
  | succ k ih =>
    intro g h
    obtain ⟨g1, h1⟩ := ih g fun i hi => h i (by omega)
    obtain ⟨g2, h2⟩ := cand_not (a + 2 * k) g1 j (by omega) (by omega) (h k (by omega))
    exact ⟨g2, Rch.tr h1 (by rw [show a + 2 * (k + 1) = a + 2 * k + 2 by omega]; exact h2)⟩

/-- the passes 5, 17, 257 and 65537 leave one counter cell for candidate 65539 -/
theorem reach_big : ∃ g, Rch start (CS 65539 g 1) := by
  have s1 := Rch.tr seed (after_pass 2 0 4 (by omega))
  -- 5 passes
  obtain ⟨g1, h1⟩ := cand_pass 5 1 3 (by omega) rfl fp_5
  -- 7 .. 15 fail, 17 passes
  obtain ⟨g2, h2⟩ := fails 7 4 (by omega) rfl 5 g1 fun i hi hf => by
    rcases (fp_small (7 + 2 * i) (by omega) (by omega)).1 hf with h | h | h <;> omega
  obtain ⟨g3, h3⟩ := cand_pass 17 g2 2 (by omega) rfl ((fp_small 17 (by omega) (by omega)).2 (Or.inl rfl))
  -- 19 .. 255 fail, 257 passes
  obtain ⟨g4, h4⟩ := fails 19 3 (by omega) rfl 119 g3 fun i hi hf => by
    rcases (fp_small (19 + 2 * i) (by omega) (by omega)).1 hf with h | h | h <;> omega
  obtain ⟨g5, h5⟩ := cand_pass 257 g4 1 (by omega) rfl ((fp_small 257 (by omega) (by omega)).2 (Or.inr (Or.inl rfl)))
  -- 259 .. 65535 fail, 65537 passes
  obtain ⟨g6, h6⟩ := fails 259 2 (by omega) rfl 32639 g5 fun i hi hf => by
    rcases (fp_small (259 + 2 * i) (by omega) (by omega)).1 hf with h | h | h <;> omega
  obtain ⟨g7, h7⟩ := cand_pass 65537 g6 0 (by omega) rfl ((fp_small 65537 (by omega) (by omega)).2 (Or.inr (Or.inr rfl)))
  exact ⟨g7, Rch.tr s1 (Rch.tr h1 (Rch.tr h2 (Rch.tr h3 (Rch.tr h4 (Rch.tr h5 (Rch.tr h6 h7))))))⟩

/-! ## the main theorem -/

theorem ones_get_lt (a i : Nat) (X : Strm) (h : i < a) : ones a X i = true := by
  induction a generalizing i with
  | zero => omega
  | succ a ih => cases i with
    | zero => rfl
    | succ i => exact ih i (by omega)

theorem ones_get_self (a : Nat) (X : Strm) : ones a X a = X 0 := by
  induction a with
  | zero => rfl
  | succ a ih => exact ih

theorem CS_ne (m g g' j : Nat) (hm : 5 ≤ m) : CS m g j ≠ CS (m + 2) g' j := by
  intro h
  have := congrArg (fun c => c.R (m - 4)) h
  simp only [CS, WS, W, Nat.sub_zero, show m + 2 - 4 = m - 4 + 2 by omega] at this
  rw [ones_get_self, ones_get_lt _ _ _ (by omega)] at this
  exact absurd this (by simp)

/-- a run between two different configurations takes at least one step -/
theorem reach1_of_ne {a b : Cfg St} (h : Rch a b) (hne : a ≠ b) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- If some `m > 65537` passes, the machine reaches its explicit halting state. -/
theorem haltAt_of (h : ∃ m, 65537 < m ∧ FP m) : HaltAt start := by
  obtain ⟨N, hN, hfp⟩ := h
  have hNo := hfp.odd (by omega)
  obtain ⟨g0, h0⟩ := reach_big
  suffices H : ∀ k m g, 65539 ≤ m → m % 2 = 1 → m + 2 * k = N → HaltAt (CS m g 1) from
    HaltAt.back h0 (H ((N - 65539) / 2) 65539 g0 (Nat.le_refl _) rfl (by omega))
  intro k
  induction k with
  | zero =>
    intro m g _ _ h; subst h
    obtain ⟨g', hg'⟩ := cand_fp m g 1 (by omega) hNo (by simpa using hfp)
    exact HaltAt.back hg' (pass_halt _ _)
  | succ k ih =>
    intro m g hm ho h
    by_cases hp : FP m
    · obtain ⟨g', hg'⟩ := cand_fp m g 1 (by omega) ho hp
      exact HaltAt.back hg' (pass_halt _ _)
    · obtain ⟨g', hg'⟩ := cand_not m g 1 (by omega) ho hp
      exact HaltAt.back hg' (ih (m + 2) g' (by omega) (by omega) (by omega))

/-- **Main theorem.** Started on a blank tape, the design halts if and only if some Fermat
number `2 ^ 2 ^ n + 1` with `n ≥ 5` is prime (`F_4 = 65537` is not the last Fermat prime). -/
theorem halts_iff : Halts delta start ↔ ∃ n, 5 ≤ n ∧ Prime (2 ^ 2 ^ n + 1) := by
  rw [fp_big_iff]
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    obtain ⟨g0, h0⟩ := reach_big
    have prog : ∀ c, (∃ m g, 65539 ≤ m ∧ m % 2 = 1 ∧ c = CS m g 1) →
        ∃ c', (∃ m g, 65539 ≤ m ∧ m % 2 = 1 ∧ c' = CS m g 1) ∧ Rch1 c c' := by
      rintro c ⟨m, g, hm, ho, rfl⟩
      obtain ⟨g', hg'⟩ := cand_not m g 1 (by omega) ho (fun hp => hno ⟨m, by omega, hp⟩)
      exact ⟨CS (m + 2) g' 1, ⟨m + 2, g', by omega, by omega, rfl⟩, reach1_of_ne hg' (CS_ne m g g' 1 (by omega))⟩
    exact not_halts_of_progress delta _ prog _ ⟨65539, g0, Nat.le_refl _, rfl, rfl⟩ (halts_det hH h0)
  · intro h; exact (haltAt_of h).halts

end TM.FermatPrimes
