import TinyCryptids.Oppermann.Round
import TinyCryptids.Oppermann.Spec

/-!
# Main theorem: the design halts iff Oppermann's conjecture fails
-/

namespace TM.Oppermann

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

/-- configuration before testing `m`, the `i`-th number of interval `q` (hole at cell `2i + 1`) -/
def CS (q i : Nat) (f : Bool) (m : Nat) : Cfg St := SHT (QX q (2 * i) f) 2 (m - 2)

/-- test `m`, then go on: to the next number, the next interval, or halt. Interval `q` has `c`
numbers, `q = 2c - 1` or `q = 2c`. -/
theorem cand (q c i : Nat) (f : Bool) (m : Nat) (hm : 2 ≤ m) (hq : q + 1 = 2 * c ∨ q = 2 * c)
    (hi : i < c) :
    let f' := f || (if Prime m then true else false)
    (i + 1 < c → Rch (CS q i f m) (CS q (i + 1) f' (m + 1))) ∧
    (i + 1 = c → f' = true → Rch (CS q i f m) (CS (q + 1) 0 false (m + 1))) ∧
    (i + 1 = c → f' = false → HaltAt (CS q i f m)) := by
  intro f'
  have hk : 2 * i < q := by omega
  have t := test q (2 * i) f hk (m - 2) 2 (Nat.le_refl _) (fun e h1 h2 => by omega)
  rw [show 2 + (m - 2) = m by omega] at t
  have hreach : ∃ d r, d + r = m ∧ 2 ≤ d ∧ Rch (CS q i f m) (AQ q (2 * i) f' d r) := by
    unfold CS
    by_cases hp : Prime m
    · have : f' = true := by simp [f', hp]
      rw [this]; exact ⟨m, 0, rfl, hm, t.1 hp⟩
    · have : f' = f := by simp [f', hp]
      rw [this]; exact t.2 hp
  obtain ⟨d, r, hdr, hd, hr⟩ := hreach
  refine ⟨fun h => Rch.tr hr ?_, fun h hf => Rch.tr hr ?_, fun h hf => HaltAt.back hr ?_⟩
  · have := qadv_next q (2 * i) f' d r (by omega) hd
    unfold CS; rw [show m + 1 - 2 = d + r - 1 by omega, show 2 * (i + 1) = 2 * i + 2 by omega]
    exact this
  · rw [hf] at hr ⊢
    have := Rch.tr (qadv_end q (2 * i) true d r (by omega)) (ie_next q d r hd)
    unfold CS; rw [show m + 1 - 2 = d + r - 1 by omega]; exact this
  · rw [hf]; exact HaltAt.back (qadv_end q (2 * i) false d r (by omega)) (ie_halt q d r)

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

/-- from the `i`-th number of the interval `[b, b + c)` (held by a Q of `q + 2` cells) -/
theorem ival (b q c : Nat) (hb : 2 ≤ b) (hq : q + 1 = 2 * c ∨ q = 2 * c) : ∀ j i f, c - i = j + 1 →
    i < c →
    ((f = true ∨ ∃ x, i ≤ x ∧ x < c ∧ Prime (b + x)) →
      Rch (CS q i f (b + i)) (CS (q + 1) 0 false (b + c))) ∧
    ((f = false ∧ ∀ x, i ≤ x → x < c → ¬ Prime (b + x)) → HaltAt (CS q i f (b + i))) := by
  intro j
  induction j with
  | zero =>
    intro i f h hi
    have c' := cand q c i f (b + i) (by omega) hq hi
    simp only at c'
    refine ⟨fun hs => ?_, fun ⟨hf, hn⟩ => ?_⟩
    · rw [show b + c = b + i + 1 by omega]
      apply c'.2.1 (by omega)
      rcases hs with hs | ⟨x, h1, h2, hp⟩
      · simp [hs]
      · obtain rfl : x = i := by omega
        simp [hp]
    · apply c'.2.2 (by omega)
      simp [hf, hn i (Nat.le_refl _) hi]
  | succ j ih =>
    intro i f h hi
    have c' := cand q c i f (b + i) (by omega) hq hi
    simp only at c'
    have st := c'.1 (by omega)
    have := ih (i + 1) (f || if Prime (b + i) then true else false) (by omega) (by omega)
    rw [show b + (i + 1) = b + i + 1 by omega] at this
    refine ⟨fun hs => Rch.tr st (this.1 ?_), fun ⟨hf, hn⟩ => HaltAt.back st (this.2 ⟨?_, ?_⟩)⟩
    · rcases hs with hs | ⟨x, h1, h2, hp⟩
      · left; simp [hs]
      · by_cases hix : x = i
        · subst hix; left; simp [hp]
        · right; exact ⟨x, by omega, h2, hp⟩
    · simp [hf, hn i (Nat.le_refl _) hi]
    · exact fun x h1 h2 => hn x (by omega) h2

/-- the whole interval `[b, b + c)` from its start -/
theorem ival0 (b q c : Nat) (hb : 2 ≤ b) (hq : q + 1 = 2 * c ∨ q = 2 * c) (hc : 1 ≤ c) :
    ((∃ x, x < c ∧ Prime (b + x)) → Rch (CS q 0 false b) (CS (q + 1) 0 false (b + c))) ∧
    ((∀ x, x < c → ¬ Prime (b + x)) → HaltAt (CS q 0 false b)) := by
  have iv := ival b q c hb hq (c - 1) 0 false (by omega) (by omega)
  rw [Nat.add_zero] at iv
  exact ⟨fun ⟨x, h1, h2⟩ => iv.1 (Or.inr ⟨x, Nat.zero_le _, h1, h2⟩),
    fun h => iv.2 ⟨rfl, fun x _ h2 => h x h2⟩⟩

/-- start of the interval `[n², n² + n)` -/
def IB (n : Nat) : Cfg St := CS (2 * n) 0 false (n * n)

theorem IB_ne (n : Nat) (hn : 2 ≤ n) : IB n ≠ IB (n + 1) := by
  intro h
  have hsq := sq_succ n
  have := le_sq n hn
  have := congrArg (fun c => c.R (n * n)) h
  simp only [IB, CS, SHT, ones_blank_get] at this
  rw [hsq] at this
  simp at this; omega

/-- the two intervals `[n², n² + n)` and `[n² + n, (n + 1)²)` -/
theorem interval (n : Nat) (hn : 2 ≤ n) :
    ((FB n ∨ FA (n + 1)) → HaltAt (IB n)) ∧ (¬ FB n → ¬ FA (n + 1) → Rch1 (IB n) (IB (n + 1))) := by
  have hle := le_sq n hn
  have hsq := sq_succ n
  have i1 := ival0 (n * n) (2 * n) n (by omega) (Or.inr rfl) (by omega)
  have i2 := ival0 (n * n + n) (2 * n + 1) (n + 1) (by omega) (Or.inl (by omega)) (by omega)
  have ea : (n + 1) * (n + 1) - (n + 1) = n * n + n := by omega
  rw [FB_iff n hn, FA_iff (n + 1) (by omega), ea]
  have nb : (¬ ∀ i, i < n → ¬ Prime (n * n + i)) → ∃ x, x < n ∧ Prime (n * n + x) := fun h =>
    Classical.byContradiction fun h' => h fun i hi hp => h' ⟨i, hi, hp⟩
  have na : (¬ ∀ i, i < n + 1 → ¬ Prime (n * n + n + i)) → ∃ x, x < n + 1 ∧ Prime (n * n + n + x) :=
    fun h => Classical.byContradiction fun h' => h fun i hi hp => h' ⟨i, hi, hp⟩
  refine ⟨fun h => ?_, fun hb ha => ?_⟩
  · by_cases hb : ∀ i, i < n → ¬ Prime (n * n + i)
    · exact i1.2 hb
    · rcases h with h | h
      · exact absurd h hb
      · exact HaltAt.back (i1.1 (nb hb)) (i2.2 h)
  · refine reach1_of_ne ?_ (IB_ne n hn)
    have := Rch.tr (i1.1 (nb hb)) (i2.1 (na ha))
    unfold IB
    rw [hsq, show 2 * (n + 1) = 2 * n + 1 + 1 by omega, show n * n + (2 * n + 1) = n * n + n + (n + 1) by omega]
    exact this

/-! ## the main theorem -/

/-- the seed: the interval `[2, 4)` starts at m = 2; 2 and 3 are prime -/
theorem start_reach : Rch start (IB 2) := by
  refine Rch.tr seed_reach (Rch.tr (prime_path 3 0 false 2 (by omega) (by omega)) ?_)
  refine Rch.tr (qadv_next 3 0 true 2 0 (by omega) (Nat.le_refl _)) ?_
  have c' := cand 3 2 1 true 3 (by omega) (Or.inl rfl) (by omega)
  exact c'.2.1 rfl (by simp)

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- the statement's counterexamples, as an `n` whose `IB n` round fails -/
theorem fails_shift (h : ∃ n, 2 ≤ n ∧ (FA n ∨ FB n)) : ∃ n, 2 ≤ n ∧ (FB n ∨ FA (n + 1)) := by
  obtain ⟨n, hn, h | h⟩ := h
  · rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by omega
      exact absurd h not_FA_two
    · exact ⟨n - 1, by omega, Or.inr (by rw [show n - 1 + 1 = n by omega]; exact h)⟩
  · exact ⟨n, hn, Or.inl h⟩

/-- If Oppermann's conjecture fails, the machine reaches its explicit halting state. -/
theorem haltAt_of (h : ∃ n, 2 ≤ n ∧ (FA n ∨ FB n)) : HaltAt start := by
  obtain ⟨N, hN2, hN⟩ := fails_shift h
  suffices H : ∀ k n, 2 ≤ n → n + k = N → HaltAt (IB n) from
    HaltAt.back start_reach (H (N - 2) 2 (by omega) (by omega))
  intro k
  induction k with
  | zero => intro n hn h; subst h; exact (interval _ hn).1 hN
  | succ k ih =>
    intro n hn h
    by_cases hf : FB n ∨ FA (n + 1)
    · exact (interval n hn).1 hf
    · exact HaltAt.back ((interval n hn).2 (fun h => hf (Or.inl h)) (fun h => hf (Or.inr h))).reach
        (ih (n + 1) (by omega) (by omega))

/-- **Main theorem.** Started on a blank tape, the design halts if and only if
Oppermann's conjecture is false. -/
theorem halts_iff : Halts delta start ↔
    ∃ n, 2 ≤ n ∧ ((∀ p, n * n - n < p → p < n * n → ¬ Prime p) ∨
      (∀ p, n * n < p → p < n * n + n → ¬ Prime p)) := by
  show _ ↔ ∃ n, 2 ≤ n ∧ (FA n ∨ FB n)
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have prog : ∀ c, (∃ n, 2 ≤ n ∧ c = IB n) → ∃ c', (∃ n, 2 ≤ n ∧ c' = IB n) ∧ Rch1 c c' := by
      rintro c ⟨n, hn, rfl⟩
      obtain ⟨hb, ha⟩ : ¬ FB n ∧ ¬ FA (n + 1) := by
        refine ⟨fun h => hno ⟨n, hn, Or.inr h⟩, fun h => hno ⟨n + 1, by omega, Or.inl h⟩⟩
      exact ⟨IB (n + 1), ⟨n + 1, by omega, rfl⟩, (interval n hn).2 hb ha⟩
    exact not_halts_of_progress delta _ prog _ ⟨2, Nat.le_refl _, rfl⟩ (halts_det hH start_reach)
  · intro h; exact (haltAt_of h).halts

end TM.Oppermann
