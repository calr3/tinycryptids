import TinyCryptids.Legendre.Round
import TinyCryptids.Legendre.Spec

/-!
# Main theorem: the design halts iff Legendre's conjecture fails
-/

namespace TM.Legendre

open TinyCryptids
open St

attribute [local instance] Classical.propDecidable

/-! ## testing one number -/

/-- the mod walk after `j` of its `r` steps -/
theorem mw_upto (X : Strm) (d r : Nat) (hd : 1 ≤ d) :
    ∀ j, 1 ≤ j → j ≤ r → Rch (MW X d r 0 1) (MW X d r ((j - 1) % d) j) := by
  intro j hj hjr
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Nat.zero_mod]; fin
    refine Rch.tr (ih hj0 (by omega)) ?_
    have := mw_step X d r ((j - 1) % d) j (Nat.mod_lt _ (by omega)) hj0 (by omega)
    have ms := mod_succ (j - 1) d
    rw [show j - 1 + 1 = j by omega] at ms
    rw [show j + 1 - 1 = j by omega]
    by_cases hw : (j - 1) % d + 1 < d
    · rw [ms.1 hw]; rw [Nat.mod_eq_of_lt hw] at this; exact this
    · have h2 : (j - 1) % d + 1 = d := by have := Nat.mod_lt (j - 1) (show d > 0 by omega); omega
      rw [ms.2 h2]; rw [h2, Nat.mod_self] at this; exact this

/-- trial division of `m = d + r` by `d, d+1, …`, no divisor below `d` -/
theorem test (q k : Nat) (f : Bool) (hk : k < q) : ∀ r d, 2 ≤ d →
    (∀ e, 2 ≤ e → e < d → (d + r) % e ≠ 0) →
    (Prime (d + r) → Rch (SHT (QX q k f) d r) (AQ q k true (d + r) 0)) ∧
    (¬ Prime (d + r) → ∃ d' r', d' + r' = d + r ∧ 2 ≤ d' ∧
      Rch (SHT (QX q k f) d r) (AQ q k f d' r')) := by
  intro r
  induction r with
  | zero =>
    intro d hd hno
    refine ⟨fun _ => Rch.tr (tail_zero _ d) (prime_path q k f d hk (by omega)), fun hp => ?_⟩
    exact absurd ⟨hd, fun e h1 h2 => hno e h2 h1⟩ hp
  | succ r ih =>
    intro d hd hno
    have walk := Rch.tr (tail_more (QX q k f) d (r + 1) (by omega) (by omega))
      (mw_upto _ d (r + 1) (by omega) (r + 1) (by omega) (Nat.le_refl _))
    rw [show r + 1 - 1 = r by omega] at walk
    have ms := mod_succ r d
    have hlt := Nat.mod_lt r (show d > 0 by omega)
    by_cases hw : r % d + 1 < d
    · -- d does not divide m: shift and go on with d + 1
      have hnd : (d + (r + 1)) % d ≠ 0 := by rw [add_mod_self_left', ms.1 hw]; omega
      have step := Rch.tr walk (Rch.tr (mw_last_nodiv _ d (r + 1) _ (by omega) hw)
        (shift _ d (r + 1) (by omega)))
      rw [show r + 1 - 1 = r by omega] at step
      have := ih (d + 1) (by omega) (fun e h1 h2 => by
        rw [show d + 1 + r = d + (r + 1) by omega]
        rcases Nat.lt_or_ge e d with h | h
        · exact hno e h1 h
        · rw [show e = d by omega]; exact hnd)
      rw [show d + 1 + r = d + (r + 1) by omega] at this
      exact ⟨fun hp => Rch.tr step (this.1 hp), fun hp => by
        obtain ⟨d', r', h1, h2, h3⟩ := this.2 hp
        exact ⟨d', r', h1, h2, Rch.tr step h3⟩⟩
    · -- d divides m: composite
      have h2 : r % d + 1 = d := by omega
      have hdv : (d + (r + 1)) % d = 0 := by rw [add_mod_self_left', ms.2 h2]
      rw [show r % d = d - 1 by omega] at walk
      have st := Rch.tr walk (mw_last_div q k f d (r + 1) (by omega) (by omega) hk)
      refine ⟨fun hp => absurd hdv (hp.2 d (by omega) hd), fun _ => ⟨d, r + 1, rfl, hd, st⟩⟩

/-- configuration before testing `m` (the `k`-th number of the interval) -/
def CS (q k : Nat) (f : Bool) (m : Nat) : Cfg St := SHT (QX q k f) 2 (m - 2)

/-- test `m`, then go on: to the next number, the next interval, or halt -/
theorem cand (q k : Nat) (f : Bool) (m : Nat) (hm : 2 ≤ m) (hk : k < q) :
    let f' := f || (if Prime m then true else false)
    (k + 1 < q → Rch (CS q k f m) (CS q (k + 1) f' (m + 1))) ∧
    (k + 1 = q → f' = true → Rch (CS q k f m) (CS (q + 2) 0 false (m + 1))) ∧
    (k + 1 = q → f' = false → HaltAt (CS q k f m)) := by
  intro f'
  have t := test q k f hk (m - 2) 2 (Nat.le_refl _) (fun e h1 h2 => by omega)
  rw [show 2 + (m - 2) = m by omega] at t
  have hreach : ∃ d r, d + r = m ∧ 2 ≤ d ∧ Rch (CS q k f m) (AQ q k f' d r) := by
    unfold CS
    by_cases hp : Prime m
    · have : f' = true := by simp [f', hp]
      rw [this]; exact ⟨m, 0, rfl, hm, t.1 hp⟩
    · have : f' = f := by simp [f', hp]
      rw [this]; exact t.2 hp
  obtain ⟨d, r, hdr, hd, hr⟩ := hreach
  refine ⟨fun h => Rch.tr hr ?_, fun h hf => Rch.tr hr ?_, fun h hf => HaltAt.back hr ?_⟩
  · have := qadv_next q k f' d r h hd
    unfold CS; rw [show m + 1 - 2 = d + r - 1 by omega]; exact this
  · rw [hf]
    have := qadv_end_next q k d r h hd
    unfold CS; rw [show m + 1 - 2 = d + r - 1 by omega]; exact this
  · rw [hf]; exact qadv_end_halt q k d r h

/-! ## one interval -/

theorem ones_blank_get (a i : Nat) : ones a blank i = decide (i < a) := by
  induction a generalizing i with
  | zero => simp [blank]
  | succ a ih => cases i with
    | zero => show true = _; simp
    | succ i => show ones a blank i = _; rw [ih]; simp

/-- a run between two different configurations takes at least one step -/
theorem reach1_of_ne {a b : Cfg St} (h : Rch a b) (hne : a ≠ b) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

/-- from the `k`-th number of the interval `[b, b + q)` -/
theorem ival (b q : Nat) (hb : 2 ≤ b) : ∀ j k f, q - k = j + 1 → k < q →
    ((f = true ∨ ∃ i, k ≤ i ∧ i < q ∧ Prime (b + i)) →
      Rch (CS q k f (b + k)) (CS (q + 2) 0 false (b + q))) ∧
    ((f = false ∧ ∀ i, k ≤ i → i < q → ¬ Prime (b + i)) → HaltAt (CS q k f (b + k))) := by
  intro j
  induction j with
  | zero =>
    intro k f h hk
    have c := cand q k f (b + k) (by omega) hk
    simp only at c
    refine ⟨fun hs => ?_, fun ⟨hf, hn⟩ => ?_⟩
    · rw [show b + q = b + k + 1 by omega]
      apply c.2.1 (by omega)
      rcases hs with hs | ⟨i, h1, h2, hp⟩
      · simp [hs]
      · obtain rfl : i = k := by omega
        simp [hp]
    · apply c.2.2 (by omega)
      simp [hf, hn k (Nat.le_refl _) hk]
  | succ j ih =>
    intro k f h hk
    have c := cand q k f (b + k) (by omega) hk
    simp only at c
    have st := c.1 (by omega)
    have := ih (k + 1) (f || if Prime (b + k) then true else false) (by omega) (by omega)
    rw [show b + (k + 1) = b + k + 1 by omega] at this
    refine ⟨fun hs => Rch.tr st (this.1 ?_), fun ⟨hf, hn⟩ => HaltAt.back st (this.2 ⟨?_, ?_⟩)⟩
    · rcases hs with hs | ⟨i, h1, h2, hp⟩
      · left; simp [hs]
      · by_cases hik : i = k
        · subst hik; left; simp [hp]
        · right; exact ⟨i, by omega, h2, hp⟩
    · simp [hf, hn k (Nat.le_refl _) hk]
    · exact fun i h1 h2 => hn i (by omega) h2

/-- start of interval `n`: about to test `n²` -/
def IS (n : Nat) : Cfg St := CS (2 * n + 1) 0 false (n * n)

theorem IS_ne (n : Nat) (hn : 2 ≤ n) : IS n ≠ IS (n + 1) := by
  intro h
  have hsq : n * n + (2 * n + 1) = (n + 1) * (n + 1) := (sq_succ n).symm
  have hle : 4 ≤ n * n := Nat.mul_le_mul hn hn
  have := congrArg (fun c => c.R (n * n)) h
  simp only [IS, CS, SHT, ones_blank_get] at this
  rw [← hsq] at this
  simp at this; omega

theorem interval (n : Nat) (hn : 2 ≤ n) :
    (LegendreFails n → HaltAt (IS n)) ∧ (¬ LegendreFails n → Rch1 (IS n) (IS (n + 1))) := by
  have hle : 4 ≤ n * n := Nat.mul_le_mul hn hn
  have iv := ival (n * n) (2 * n + 1) (by omega) (2 * n) 0 false (by omega) (by omega)
  rw [Nat.add_zero] at iv
  rw [fails_iff n hn]
  refine ⟨fun h => iv.2 ⟨rfl, fun i _ h2 => h i h2⟩, fun h => ?_⟩
  have hs : ∃ i, 0 ≤ i ∧ i < 2 * n + 1 ∧ Prime (n * n + i) := by
    apply Classical.byContradiction; intro hno
    exact h (fun i hi hp => hno ⟨i, Nat.zero_le _, hi, hp⟩)
  have := iv.1 (Or.inr hs)
  have hsq := sq_succ n
  refine reach1_of_ne ?_ (IS_ne n hn)
  unfold IS; rw [hsq, show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by omega]; exact this

/-! ## the main theorem -/

/-- the seed: the interval for n = 1 starts at m = 2 (k = 1); 2 and 3 are prime -/
theorem start_reach : Rch start (IS 2) := by
  refine Rch.tr seed_reach (Rch.tr (prime_path 3 1 false 2 (by omega) (by omega)) ?_)
  have h1 := qadv_next 3 1 true 2 0 (by omega) (Nat.le_refl _)
  refine Rch.tr h1 ?_
  have t := test 3 2 true (by omega) 1 2 (Nat.le_refl _) (fun e h1 h2 => by omega)
  have : ∃ d r, d + r = 3 ∧ 2 ≤ d ∧ Rch (SHT (QX 3 (1 + 1) true) 2 (2 + 0 - 1)) (AQ 3 2 true d r) := by
    by_cases hp : Prime (2 + 1)
    · exact ⟨3, 0, rfl, by omega, t.1 hp⟩
    · exact t.2 hp
  obtain ⟨d, r, hdr, hd, hr⟩ := this
  refine Rch.tr hr ?_
  have := qadv_end_next 3 2 d r (by omega) hd
  unfold IS CS; rw [show d + r - 1 = 2 * 2 - 2 by omega] at this; exact this

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- If Legendre's conjecture fails, the machine reaches its explicit halting state. -/
theorem haltAt_of_fails (h : ∃ n, LegendreFails n) : HaltAt start := by
  obtain ⟨N, hN⟩ := h
  have h2 : 2 ≤ N := by
    have := hN.1
    rcases Nat.lt_or_ge N 2 with h | h
    · obtain rfl : N = 1 := by omega
      exact absurd hN not_fails_one
    · exact h
  suffices H : ∀ k n, 2 ≤ n → n + k = N → HaltAt (IS n) from HaltAt.back start_reach (H (N - 2) 2 (by omega) (by omega))
  intro k
  induction k with
  | zero => intro n _ h; subst h; exact (interval _ (by omega)).1 hN
  | succ k ih =>
    intro n hn h
    by_cases hf : LegendreFails n
    · exact (interval n hn).1 hf
    · exact HaltAt.back ((interval n hn).2 hf).reach (ih (n + 1) (by omega) (by omega))

/-- **Main theorem.** Started on a blank tape, the design halts if and only if
Legendre's conjecture is false. -/
theorem halts_iff :
    Halts delta start ↔ ∃ n, 1 ≤ n ∧ ∀ p, n ^ 2 < p → p < (n + 1) ^ 2 → ¬ Prime p := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have prog : ∀ c, (∃ n, 2 ≤ n ∧ c = IS n) → ∃ c', (∃ n, 2 ≤ n ∧ c' = IS n) ∧ Rch1 c c' := by
      rintro c ⟨n, hn, rfl⟩
      exact ⟨IS (n + 1), ⟨n + 1, by omega, rfl⟩, (interval n hn).2 (fun hf => hno ⟨n, hf⟩)⟩
    exact not_halts_of_progress delta _ prog _ ⟨2, Nat.le_refl _, rfl⟩ (halts_det hH start_reach)
  · intro h; exact (haltAt_of_fails h).halts

end TM.Legendre
