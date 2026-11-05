import TinyCryptids.Carmichael.Tac
import TinyCryptids.Carmichael.Spec

/-!
# The coprimality test, the count and the sweep

Tape (left to right): `1 K 00 1 R 00 V 1 00 f 0 B 1`. `K` has `k` slots, `R` has `r` slots,
each with one hole (a single `0`).

    TK a b j e X : `KA` on K's hole, `a` slots left of it and `b` right of it
                   (`k = a + b + 1`); R's hole has `j` slots left and `e` right
                   (`r = j + e + 1`); `X` is the rest of the tape, from the separator
                   after R.
-/

namespace TM.Carmichael
open St TinyCryptids

local notation "F" => false

def TK (a b j e : Nat) (X : Strm) : Cfg St :=
  ⟨KA, ones (a + 1) blank, F ::: ones b (F ::: F ::: ones (j + 1) (F ::: ones e X))⟩

theorem tick (a b j e : Nat) (X : Strm) : Rch (TK a (b + 1) j (e + 1) X) (TK (a + 1) b (j + 1) e X) := by
  unfold TK
  cR; cR
  refine Rch.tr (scanR (δ := delta) rfl b _ _) ?_
  cR; cR; cR
  refine Rch.tr (scanR (δ := delta) rfl j _ _) ?_
  cR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL GK1 (true ::: ones j (true ::: F ::: F ::: ones b (F ::: true ::: ones (a + 1) blank)))
    (F ::: ones e X)) _
  rw [ones_cons_true]
  refine Rch.tr (scanL (δ := delta) (n := j + 2) rfl _ _) ?_
  cL; cL
  refine Rch.tr (scanL (δ := delta) rfl b _ _) ?_
  exact Reach.refl delta _

/-- a tick in which R's hole wraps from its last slot to its first -/
theorem tickW (a b j : Nat) (Y : Strm) :
    Rch (TK a (b + 1) j 0 (F ::: Y)) (TK (a + 1) b 0 j (F ::: Y)) := by
  unfold TK
  cR; cR
  refine Rch.tr (scanR (δ := delta) rfl b _ _) ?_
  cR; cR; cR
  refine Rch.tr (scanR (δ := delta) rfl j _ _) ?_
  cR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL RW (true ::: ones j (true ::: F ::: F ::: ones b (F ::: true ::: ones (a + 1) blank)))
    (F ::: Y)) _
  rw [ones_cons_true]
  refine Rch.tr (scanL (δ := delta) (n := j + 2) rfl _ _) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  cR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL GK1 (true ::: F ::: F ::: ones b (F ::: true ::: ones (a + 1) blank))
    (F ::: ones j (F ::: Y))) _
  cL; cL; cL
  refine Rch.tr (scanL (δ := delta) rfl b _ _) ?_
  exact Reach.refl delta _

/-- the cells left of b2 after a test: b1 (the hole), R's start, the separator, K with
`a + 1` slots and its hole on a1, K's start -/
def PostL (a : Nat) : Strm := F ::: true ::: F ::: F ::: ones a (F ::: true ::: blank)

/-- a wrap of K's hole with R's hole on b1: coprime -/
theorem wrapC (a e : Nat) (X : Strm) :
    Rch (TK a 0 0 e X) ⟨CV1, PostL a, ones e X⟩ := by
  unfold TK
  cR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL KW (ones (a + 2) blank) (F ::: F ::: ones 1 (F ::: ones e X))) _
  refine Rch.tr (scanL (δ := delta) rfl (a + 2) _ _) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  cR; cR
  refine Rch.tr (scanR (δ := delta) rfl a _ _) ?_
  cR; cR; cR; cR
  rw [tl_blank, cons_blank]; exact Reach.refl delta _

/-- a wrap of K's hole, R's hole not at its ends: the walk goes on -/
theorem wrapM (a j e : Nat) (X : Strm) :
    Rch (TK a 0 (j + 1) (e + 1) X) (TK 0 a (j + 2) e X) := by
  unfold TK
  cR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL KW (ones (a + 2) blank) (F ::: F ::: ones (j + 2) (F ::: ones (e + 1) X))) _
  refine Rch.tr (scanL (δ := delta) rfl (a + 2) _ _) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  cR; cR
  refine Rch.tr (scanR (δ := delta) rfl a _ _) ?_
  cR; cR; cR; cR
  refine Rch.tr (scanR (δ := delta) rfl j _ _) ?_
  cR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL GK1 (true ::: ones j (true ::: true ::: F ::: F ::: ones a (F ::: true ::: F ::: tl blank)))
    (F ::: ones e X)) _
  rw [ones_cons_true, ones_cons_true, tl_blank, cons_blank]
  refine Rch.tr (scanL (δ := delta) (n := j + 3) rfl _ _) ?_
  cL; cL
  refine Rch.tr (scanL (δ := delta) rfl a _ _) ?_
  exact Reach.refl delta _

/-- a wrap of K's hole with R's hole on its last slot: not coprime -/
theorem wrapN (a j : Nat) (Y : Strm) :
    Rch (TK a 0 (j + 1) 0 (F ::: Y)) ⟨EC1, PostL a, ones (j + 1) (F ::: Y)⟩ := by
  unfold TK
  cR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL KW (ones (a + 2) blank) (F ::: F ::: ones (j + 2) (F ::: ones 0 (F ::: Y)))) _
  refine Rch.tr (scanL (δ := delta) rfl (a + 2) _ _) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  cR; cR
  refine Rch.tr (scanR (δ := delta) rfl a _ _) ?_
  cR; cR; cR; cR
  refine Rch.tr (scanR (δ := delta) rfl j _ _) ?_
  cR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL CW (true ::: ones j (true ::: true ::: F ::: F ::: ones a (F ::: true ::: F ::: tl blank)))
    (F ::: Y)) _
  rw [ones_cons_true, ones_cons_true, tl_blank, cons_blank]
  refine Rch.tr (scanL (δ := delta) (n := j + 3) rfl _ _) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  cR; cR
  exact Reach.refl delta _

theorem mod_succ_eq (x r : Nat) (hr : 1 ≤ r) :
    (x + 1) % r = if x % r + 1 = r then 0 else x % r + 1 := by
  have h1 := Nat.mod_lt x (by omega : r > 0)
  have h2 := Nat.div_add_mod x r
  split
  · rw [show x + 1 = r * (x / r + 1) by rw [Nat.mul_succ]; omega]; exact Nat.mul_mod_right _ _
  · rw [show x + 1 = (x % r + 1) + r * (x / r) by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]

/-- a tick, R's hole at position `j` of `r` -/
theorem tickg (a b j r : Nat) (hj : j < r) (Y : Strm) :
    Rch (TK a (b + 1) j (r - 1 - j) (F ::: Y))
      (TK (a + 1) b ((j + 1) % r) (r - 1 - (j + 1) % r) (F ::: Y)) := by
  rcases Nat.lt_or_ge (j + 1) r with h | h
  · rw [Nat.mod_eq_of_lt h, show r - 1 - j = (r - 1 - (j + 1)) + 1 by omega]
    exact tick a b j _ _
  · rw [show j + 1 = r by omega, Nat.mod_self, show r - 1 - j = 0 by omega,
      show r - 1 - 0 = j by omega]
    exact tickW a b j Y

theorem ticks (r : Nat) (Y : Strm) : ∀ b a j, j < r →
    Rch (TK a b j (r - 1 - j) (F ::: Y)) (TK (a + b) 0 ((j + b) % r) (r - 1 - (j + b) % r) (F ::: Y)) := by
  intro b
  induction b with
  | zero => intro a j hj; rw [Nat.add_zero, Nat.add_zero, Nat.mod_eq_of_lt hj]; exact Reach.refl delta _
  | succ b ih =>
    intro a j hj
    refine Rch.tr (tickg a b j r hj Y) ?_
    have := ih (a + 1) ((j + 1) % r) (Nat.mod_lt _ (by omega))
    rw [Nat.mod_add_mod, show j + 1 + b = j + (b + 1) by omega,
      show a + 1 + b = a + (b + 1) by omega] at this
    exact this

/-- the outcome of the test of `(k, r)` -/
def Res (k r : Nat) (Y : Strm) : Cfg St :=
  if Nat.gcd k r = 1 then ⟨CV1, PostL (k - 1), ones (r - 1) (F ::: Y)⟩
  else ⟨EC1, PostL (k - 1), ones (r - 1) (F ::: Y)⟩

/-- the start of stride `q`: K's hole on a1, R's hole at `(q - 1) k mod r` -/
def SS (k r q : Nat) (Y : Strm) : Cfg St :=
  TK 0 (k - 1) ((q - 1) * k % r) (r - 1 - (q - 1) * k % r) (F ::: Y)

theorem stride (k r q : Nat) (hk : 1 ≤ k) (hr : 1 ≤ r) (hq : 1 ≤ q) (Y : Strm) :
    (hitC k r q → Rch (SS k r q Y) ⟨CV1, PostL (k - 1), ones (r - 1) (F ::: Y)⟩) ∧
    (hitN k r q → ¬ hitC k r q → Rch (SS k r q Y) ⟨EC1, PostL (k - 1), ones (r - 1) (F ::: Y)⟩) ∧
    (¬ hitC k r q → ¬ hitN k r q → Rch (SS k r q Y) (SS k r (q + 1) Y)) := by
  have hj := Nat.mod_lt ((q - 1) * k) (by omega : r > 0)
  generalize hjq : (q - 1) * k % r = jq at hj
  have hqk : q * k % r = (jq + (k - 1) + 1) % r := by
    rw [show jq + (k - 1) + 1 = jq + k by omega, ← hjq, Nat.mod_add_mod,
      show (q - 1) * k + k = q * k by
        rw [← Nat.succ_mul, show (q - 1).succ = q by omega]]
  rw [mod_succ_eq _ r hr] at hqk
  have hx := Nat.mod_lt (jq + (k - 1)) (by omega : r > 0)
  generalize hj' : (jq + (k - 1)) % r = j' at hqk hx
  have hrun : Rch (SS k r q Y) (TK (k - 1) 0 j' (r - 1 - j') (F ::: Y)) := by
    unfold SS; rw [hjq]
    have := ticks r Y (k - 1) 0 jq hj
    rwa [Nat.zero_add, hj'] at this
  have hS : SS k r (q + 1) Y = TK 0 (k - 1) (q * k % r) (r - 1 - q * k % r) (F ::: Y) := by
    unfold SS; rw [Nat.add_sub_cancel]
  unfold hitC hitN
  rcases Nat.eq_zero_or_pos j' with h0 | h0
  · subst h0
    refine ⟨fun _ => Rch.tr hrun ?_, fun _ hc => absurd ?_ hc, fun hc _ => absurd ?_ hc⟩
    · have := wrapC (k - 1) (r - 1 - 0) (F ::: Y); rwa [Nat.sub_zero] at this
    all_goals
      rcases Nat.lt_or_ge r 2 with h | h
      · obtain rfl : r = 1 := by omega
        simp [hqk]
      · rw [hqk, if_neg (by omega), Nat.mod_eq_of_lt h]
  · obtain ⟨j, rfl⟩ : ∃ j, j' = j + 1 := ⟨j' - 1, by omega⟩
    rcases Nat.lt_or_ge (j + 1 + 1) r with hl | hl
    · rw [if_neg (by omega)] at hqk
      refine ⟨fun hc => absurd hc ?_, fun hn => absurd hn ?_, fun _ _ => Rch.tr hrun ?_⟩
      · rw [hqk, Nat.mod_eq_of_lt (by omega : 1 < r)]; omega
      · rw [hqk]; omega
      · rw [hS, hqk, show r - 1 - (j + 1) = (r - 1 - (j + 2)) + 1 by omega]
        exact wrapM (k - 1) j _ _
    · rw [if_pos (by omega)] at hqk
      have hr2 : 1 < r := by omega
      refine ⟨fun hc => absurd hc ?_, fun _ _ => Rch.tr hrun ?_, fun _ hn => absurd hqk hn⟩
      · rw [hqk, Nat.mod_eq_of_lt hr2]; omega
      · rw [show r - 1 - (j + 1) = 0 by omega]
        have := wrapN (k - 1) j Y
        rw [show j + 1 = r - 1 by omega] at this ⊢; exact this

theorem strides (k r : Nat) (hk : 1 ≤ k) (hr : 1 ≤ r) (Y : Strm) : ∀ n q, q + n = r → 1 ≤ q →
    (∀ i, 1 ≤ i → i < q → ¬ hitC k r i ∧ ¬ hitN k r i) → Rch (SS k r q Y) (Res k r Y) := by
  have hit : ∀ q, 1 ≤ q → (∀ i, 1 ≤ i → i < q → ¬ hitC k r i ∧ ¬ hitN k r i) →
      (hitC k r q ∨ hitN k r q) → Rch (SS k r q Y) (Res k r Y) := by
    intro q hq hfirst hh
    have fh := first_hit hr hq hfirst
    have st := stride k r q hk hr hq Y
    unfold Res
    by_cases hC : hitC k r q
    · rw [if_pos (fh.1 hC)]; exact st.1 hC
    · have hN : hitN k r q := hh.resolve_left hC
      rw [if_neg (fh.2 hN hC)]; exact st.2.1 hN hC
  intro n
  induction n with
  | zero =>
    intro q hq hq1 hfirst
    exact hit q hq1 hfirst (Or.inr (by rw [show q = r by omega]; exact hitN_r k r))
  | succ n ih =>
    intro q hq hq1 hfirst
    by_cases hh : hitC k r q ∨ hitN k r q
    · exact hit q hq1 hfirst hh
    · have hC : ¬ hitC k r q := fun h => hh (Or.inl h)
      have hN : ¬ hitN k r q := fun h => hh (Or.inr h)
      refine Rch.tr ((stride k r q hk hr hq1 Y).2.2 hC hN) (ih (q + 1) (by omega) (by omega) ?_)
      intro i hi1 hi
      rcases Nat.lt_or_ge i q with h | h
      · exact hfirst i hi1 h
      · rw [show i = q by omega]; exact ⟨hC, hN⟩

/-- the test of `(k, r)`, from both holes on their first slots -/
theorem test (k r : Nat) (hk : 1 ≤ k) (hr : 1 ≤ r) (Y : Strm) :
    Rch (TK 0 (k - 1) 0 (r - 1) (F ::: Y)) (Res k r Y) := by
  have := strides k r hk hr Y (r - 1) 1 (by omega) (Nat.le_refl 1) (fun i h1 h2 => by omega)
  unfold SS at this; simpa using this

/-! ## the count in V -/

/-- V's `v + 1` slots after `c` coprime pairs: the hole on slot `v + 1 - c`, none once `c > v` -/
def Vst (v c : Nat) (Z : Strm) : Strm := if c ≤ v then ones (v - c) (F ::: ones c Z) else ones (v + 1) Z

/-- from the separator after R: V, its end cell, `0 0`, then `W` (the flag cell onwards) -/
def VX (v c : Nat) (W : Strm) : Strm := F ::: F ::: Vst v c (true ::: F ::: F ::: W)

theorem back (a e m : Nat) (R : Strm) :
    Rch (cfgL BK1 (ones m (F ::: F ::: ones e (PostL a))) R) ⟨EC1, PostL a, ones e (F ::: F ::: ones m R)⟩ := by
  refine Rch.tr (scanL (δ := delta) rfl m _ _) ?_
  cL; cL
  refine Rch.tr (scanL (δ := delta) rfl e _ _) ?_
  exact stepR (δ := delta) rfl

/-- a coprime pair: V's hole one slot left (none once it falls off) -/
theorem coprime (a e v c : Nat) (W : Strm) :
    Rch ⟨CV1, PostL a, ones e (VX v c W)⟩ ⟨EC1, PostL a, ones e (VX v (c + 1) W)⟩ := by
  unfold VX Vst
  refine Rch.tr (scanR (δ := delta) rfl e _ _) ?_
  cR; cR
  rcases Nat.lt_trichotomy c v with h | rfl | h
  · rw [if_pos (by omega), if_pos (by omega)]
    obtain ⟨d, hd⟩ : ∃ d, v - c = d + 1 := ⟨v - c - 1, by omega⟩
    rw [hd, show v - (c + 1) = d by omega]
    refine Rch.tr (scanR (δ := delta) rfl (d + 1) _ _) ?_
    cR
    rw [ones_cons_true]
    refine Rch.tr (stepL (δ := delta) rfl) ?_
    show Rch (cfgL CV5 (F ::: ones (d + 1) (F ::: F ::: ones e (PostL a))) (true ::: ones c (F ::: F ::: W))) _
    cL; cL
    have := back a e d (F ::: true ::: true ::: ones c (F ::: F ::: W))
    rw [show ones (c + 1) (true ::: F ::: F ::: W) = true ::: true ::: ones c (F ::: F ::: W) by
      rw [ones_succ, ones_cons_true]]
    exact this
  · rw [if_pos (Nat.le_refl c), if_neg (by omega), Nat.sub_self]
    cR
    rw [ones_cons_true]
    refine Rch.tr (stepL (δ := delta) rfl) ?_
    show Rch (cfgL CV5 (F ::: F ::: F ::: ones e (PostL a)) (true ::: ones c (F ::: F ::: W))) _
    cL; cL; cL
    refine Rch.tr (scanL (δ := delta) rfl e _ _) ?_
    rw [show ones (c + 1) (true ::: F ::: F ::: W) = true ::: true ::: ones c (F ::: F ::: W) by
      rw [ones_succ, ones_cons_true]]
    exact stepR (δ := delta) rfl
  · rw [if_neg (by omega), if_neg (by omega)]
    rw [← ones_succ']
    refine Rch.tr (scanR (δ := delta) (n := v + 2) rfl _ _) ?_
    cR
    refine Rch.tr (stepL (δ := delta) rfl) ?_
    show Rch (cfgL CVS (F ::: ones (v + 2) (F ::: F ::: ones e (PostL a))) (F ::: W)) _
    cL
    have := back a e (v + 2) (F ::: F ::: W)
    simpa [ones_succ'] using this

/-- the test of `(k, r)` and the count -/
theorem test_count (k r v c : Nat) (hk : 1 ≤ k) (hr : 1 ≤ r) (W : Strm) :
    Rch (TK 0 (k - 1) 0 (r - 1) (VX v c W))
      ⟨EC1, PostL (k - 1), ones (r - 1) (VX v (c + if Nat.gcd k r = 1 then 1 else 0) W)⟩ := by
  have ht := test k r hk hr (F ::: Vst v c (true ::: F ::: F ::: W))
  unfold Res at ht
  by_cases h : Nat.gcd k r = 1
  · rw [if_pos h] at ht ⊢
    exact Rch.tr ht (coprime (k - 1) (r - 1) v c W)
  · rw [if_neg h] at ht ⊢; exact ht

/-- the separator one cell right: `(k, r + 1) → (k + 1, r)` -/
theorem shift (a e : Nat) (X : Strm) : Rch ⟨EC1, PostL a, ones (e + 1) X⟩ (TK 0 (a + 1) 0 e X) := by
  unfold PostL TK
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  cL; cL; cL; cL
  refine Rch.tr (scanL (δ := delta) rfl a _ _) ?_
  rw [ones_cons_true]; exact Reach.refl delta _

/-- the tests of `k, k + 1, …, M - 1` against `M - k`, …, `1` -/
theorem sweep (M v : Nat) (hM : 2 ≤ M) (W : Strm) : ∀ n k, k + n = M - 1 → 1 ≤ k →
    Rch (TK 0 (k - 1) 0 (M - k - 1) (VX v (cp M k) W)) ⟨EC1, PostL (M - 2), VX v (totient M) W⟩ := by
  intro n
  induction n with
  | zero =>
    intro k hk hk1
    have := test_count k (M - k) v (cp M k) hk1 (by omega) W
    rw [gcd_sub (by omega), ← cp_succ, show k + 1 = M by omega, cp_self,
      show M - k - 1 = 0 by omega, show k - 1 = M - 2 by omega] at this
    rw [show M - k - 1 = 0 by omega, show k - 1 = M - 2 by omega]; exact this
  | succ n ih =>
    intro k hk hk1
    have := test_count k (M - k) v (cp M k) hk1 (by omega) W
    rw [gcd_sub (by omega), ← cp_succ, show M - k - 1 = (M - (k + 1) - 1) + 1 by omega] at this
    rw [show M - k - 1 = (M - (k + 1) - 1) + 1 by omega]
    refine Rch.tr this (Rch.tr (shift _ _ _) ?_)
    have := ih (k + 1) (by omega) (by omega)
    rwa [show k + 1 - 1 = k - 1 + 1 by omega] at this

/-! ## round end -/

/-- `(M - 1, 1) → (1, M)`, from R's hole -/
theorem reset (M : Nat) (hM : 2 ≤ M) (Z : Strm) :
    Rch (cfgL RS1 (PostL (M - 2)) (F ::: F ::: Z)) (TK 0 0 0 (M - 1) (F ::: F ::: Z)) := by
  unfold PostL TK
  cL; cL; cL; cL
  refine Rch.tr (scanL (δ := delta) rfl (M - 2) _ _) ?_
  cL; cL
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  cR; cR
  show Rch ⟨RS10, _, ones (M - 2) (true ::: true ::: true ::: true ::: F ::: F ::: Z)⟩ _
  rw [ones_cons_true, ones_cons_true, ones_cons_true, ones_cons_true]
  cR; cR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  cL; cL; cL
  rw [show M - 1 = (M - 2) + 1 by omega]
  exact Reach.refl delta _

/-- B: `s` slots, the hole on slot `p` (`1 ≤ p ≤ s`), its end cell -/
def Bst (s p : Nat) : Strm := ones (p - 1) (F ::: ones (s - p) (true ::: blank))

/-- from the flag cell: the flag, `0`, B -/
def WF (f : Bool) (s p : Nat) : Strm := f ::: F ::: Bst s p

/-- left of the flag cell, after the round end: `0 0`, V's end, V (no hole), `0 0`, then
K/R `(a + 1, 1)` -/
def L1 (v a : Nat) : Strm := F ::: F ::: true ::: ones (v + 1) (F ::: F ::: PostL a)

theorem ones_tt (a b : Nat) (X : Strm) : ones a (true ::: true ::: ones b X) = ones (a + b + 2) X := by
  rw [← ones_succ', ← ones_succ', ones_add, show a + 1 + 1 + b = a + b + 2 by omega]

theorem cross_match (a v : Nat) (W : Strm) : Rch1 ⟨EC1, PostL a, VX v v W⟩ ⟨MF, L1 v a, W⟩ := by
  unfold VX Vst; rw [if_pos (Nat.le_refl v), Nat.sub_self, ones_zero]
  refine Reach1.trans_reach delta (stepR1 (δ := delta) rfl) ?_
  cR; cR
  rw [← ones_succ']
  refine Rch.tr (scanR (δ := delta) (n := v + 1) rfl _ _) ?_
  cR; cR
  simp only [L1, ones_succ, ones_cons_true]; exact Reach.refl delta _

theorem cross_nomatch (a v c : Nat) (hc : c ≠ v) (W : Strm) :
    Rch1 ⟨EC1, PostL a, VX v c W⟩ ⟨NF, L1 v a, W⟩ := by
  unfold VX Vst
  refine Reach1.trans_reach delta (stepR1 (δ := delta) rfl) ?_
  rcases Nat.lt_or_ge c v with h | h
  · rw [if_pos (by omega)]
    obtain ⟨d, hd⟩ : ∃ d, v - c = d + 1 := ⟨v - c - 1, by omega⟩
    rw [hd]
    cR; cR
    refine Rch.tr (scanR (δ := delta) rfl d _ _) ?_
    cR
    simp only [ones_cons_true]
    refine Rch.tr (stepL (δ := delta) rfl) ?_
    refine Rch.tr (stepR (δ := delta) rfl) ?_
    show Rch ⟨NV1, true ::: true ::: ones d (F ::: F ::: PostL a), ones (c + 1) (F ::: F ::: W)⟩ _
    refine Rch.tr (scanR (δ := delta) (n := c + 1) rfl _ _) ?_
    cR; cR
    rw [ones_tt, show c + 1 + d + 2 = v + 2 by omega]
    exact Reach.refl delta _
  · rw [if_neg (by omega)]
    cR; cR
    rw [← ones_succ']
    refine Rch.tr (scanR (δ := delta) (n := v + 1) rfl _ _) ?_
    cR; cR
    simp only [L1, ones_succ, ones_cons_true]; exact Reach.refl delta _

/-- B's hole one slot left, back to R's hole, place V's hole on slot `v + 1`, and reset K/R -/
theorem advance (q : St) (hq : delta q true = some (true, Dir.R, BA1)) (f : Bool) (v M p s : Nat)
    (hM : 2 ≤ M) (hp : p + 2 ≤ s) :
    Rch ⟨q, F ::: f ::: L1 v (M - 2), Bst s (p + 2)⟩ (TK 0 0 0 (M - 1) (VX v 0 (WF f s (p + 1)))) := by
  unfold Bst L1
  rw [show p + 2 - 1 = p + 1 by omega]
  refine Rch.tr (sR hq) ?_
  refine Rch.tr (scanR (δ := delta) rfl p _ _) ?_
  rw [ones_cons_true]
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  cL
  refine Rch.tr (scanL (δ := delta) rfl p _ _) ?_
  cases f <;>
  · cL; cL; cL; cL; cL; cL
    refine Rch.tr (scanL (δ := delta) rfl v _ _) ?_
    cL; cL
    refine Rch.tr (reset M hM _) ?_
    unfold VX Vst WF Bst
    rw [if_pos (Nat.zero_le v), Nat.sub_zero, ones_zero, show p + 1 - 1 = p by omega,
      show s - (p + 1) = (s - (p + 2)) + 1 by omega]
    exact Reach.refl delta _

/-! ## next v: K/R back to `(1, 1)` -/

theorem zfin (n : Nat) (R : Strm) :
    Rch (cfgL E3 blank (zeros n (true ::: F ::: R))) ⟨KA, ones 1 blank, F ::: R⟩ := by
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (scanR0 (δ := delta) rfl n _ _) ?_
  cR
  rw [tl_blank, cons_blank, zeros_blank]; exact Reach.refl delta _

/-- erase what is left of K, from the cell left of the new K start -/
theorem erase_blank (R : Strm) : Rch (cfgL E1 blank (true ::: F ::: R)) ⟨KA, ones 1 blank, F ::: R⟩ := by
  refine Rch.tr (stepL' (δ := delta) (s := blank) rfl) ?_
  refine Rch.tr (stepL' (δ := delta) (s := tl blank) rfl) ?_
  rw [tl_blank, tl_blank]
  have := zfin 2 R
  simp only [zeros, Nat.add_eq, Nat.add_zero] at this
  exact this

theorem erase_one (R : Strm) :
    Rch (cfgL E1 (true ::: blank) (true ::: F ::: R)) ⟨KA, ones 1 blank, F ::: R⟩ := by
  cL
  refine Rch.tr (stepL' (δ := delta) (s := blank) rfl) ?_
  refine Rch.tr (stepL' (δ := delta) (s := tl blank) rfl) ?_
  rw [tl_blank, tl_blank]
  have := zfin 3 R
  simp only [zeros] at this
  exact this

theorem erase_ones (x : Nat) (R : Strm) :
    Rch (cfgL E1 (ones x (F ::: true ::: blank)) (true ::: F ::: R)) ⟨KA, ones 1 blank, F ::: R⟩ := by
  refine Rch.tr (eraseL (δ := delta) rfl x _ _) ?_
  cL; cL
  refine Rch.tr (stepL' (δ := delta) (s := blank) rfl) ?_
  refine Rch.tr (stepL' (δ := delta) (s := tl blank) rfl) ?_
  rw [tl_blank, tl_blank]
  have := zfin (4 + x) R
  rw [← zeros_add] at this
  exact this

/-- K/R `(a + 1, 1)` (or nothing, at the seed) becomes `(1, 1)` -/
theorem kr_init (a : Nat) (Z : Strm) :
    Rch (cfgL EI1 (PostL a) (F ::: F ::: Z)) (TK 0 0 0 0 (F ::: F ::: Z)) := by
  unfold PostL TK
  cL; cL; cL; cL
  rcases a with _ | _ | x
  · cL; cL; exact erase_blank _
  · cL; cL; exact erase_one _
  · cL; cL; exact erase_ones x _

theorem kr_init_blank (Z : Strm) : Rch (cfgL EI1 blank (F ::: F ::: Z)) (TK 0 0 0 0 (F ::: F ::: Z)) := by
  unfold TK
  refine Rch.tr (stepL' (δ := delta) (s := blank) rfl) ?_
  refine Rch.tr (stepL' (δ := delta) (s := tl blank) rfl) ?_
  refine Rch.tr (stepL' (δ := delta) (s := tl (tl blank)) rfl) ?_
  refine Rch.tr (stepL' (δ := delta) (s := tl (tl (tl blank))) rfl) ?_
  refine Rch.tr (stepL' (δ := delta) (s := tl (tl (tl (tl blank)))) rfl) ?_
  refine Rch.tr (stepL' (δ := delta) (s := tl (tl (tl (tl (tl blank))))) rfl) ?_
  simp only [tl_blank]
  exact erase_blank _

/-! ## next v: B grows by 4 per slot of V -/

/-- left of B's first slot during the growth: `0 0 0 0`, V's end, V (`w` slots, the cursor
hole on slot `u`), `0 0`, then K/R -/
def LG (w u : Nat) (KR : Strm) : Strm :=
  F ::: F ::: F ::: F ::: true ::: ones (w - u) (F ::: ones (u - 1) (F ::: F ::: KR))

/-- append `1 1 0 1` to B; the head ends on the second appended cell, going left -/
theorem append (j m : Nat) (L : Strm) :
    Rch ⟨GX, ones j L, ones m (true ::: blank)⟩ (cfgL GB1 (ones (j + m + 3) L) (F ::: true ::: blank)) := by
  rw [← ones_succ']
  refine Rch.tr (scanR (δ := delta) rfl (m + 1) _ _) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  simp only [tl_blank]
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  simp only [tl_blank, tl_cons]
  show Rch ⟨GB1, true ::: ones (m + 1) (ones j L), true ::: F ::: true ::: blank⟩ _
  rw [ones_add, show j + m + 3 = (m + 1 + j) + 1 + 1 by omega]
  exact Reach.refl delta _

/-- back to the cursor, one slot left, and to B again -/
theorem grow_back (n w u : Nat) (KR : Strm) (hu : 2 ≤ u) (huw : u ≤ w) :
    Rch (cfgL GB1 (ones n (LG w u KR)) (F ::: true ::: blank)) ⟨GX, LG w (u - 1) KR, Bst (n + 1) (n + 1)⟩ := by
  unfold LG Bst
  obtain ⟨d, rfl⟩ : ∃ d, w = u + d := ⟨w - u, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, u = t + 2 := ⟨u - 2, by omega⟩
  rw [show t + 2 + d - (t + 2) = d by omega, show t + 2 - 1 = t + 1 by omega,
    show t + 2 + d - (t + 1) = d + 1 by omega, show t + 1 - 1 = t by omega,
    show n + 1 - 1 = n by omega, Nat.sub_self]
  refine Rch.tr (scanL (δ := delta) rfl n _ _) ?_
  cL; cL; cL; cL
  refine Rch.tr (scanL (δ := delta) (n := d + 1) rfl _ _) ?_
  cL
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  show Rch ⟨GR1, F ::: ones t (F ::: F ::: KR), ones (d + 2) (F ::: F ::: F ::: F ::: ones n (F ::: true ::: blank))⟩ _
  refine Rch.tr (scanR (δ := delta) rfl (d + 2) _ _) ?_
  cR; cR; cR; cR
  exact Reach.refl delta _

/-- the cursor falls off V: V's hole on its last slot `w`, then to K/R -/
theorem grow_last (n w : Nat) (KR : Strm) (hw : 1 ≤ w) :
    Rch (cfgL GB1 (ones n (LG w 1 KR)) (F ::: true ::: blank))
      (cfgL EI1 KR (F ::: F ::: ones (w - 1) (F ::: true ::: F ::: F ::: F ::: F ::: Bst (n + 1) (n + 1)))) := by
  unfold LG Bst
  obtain ⟨d, rfl⟩ : ∃ d, w = d + 1 := ⟨w - 1, by omega⟩
  rw [show d + 1 - 1 = d by omega, show n + 1 - 1 = n by omega, Nat.sub_self, ones_zero]
  refine Rch.tr (scanL (δ := delta) rfl n _ _) ?_
  cL; cL; cL; cL
  refine Rch.tr (scanL (δ := delta) (n := d + 1) rfl _ _) ?_
  cL
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  show Rch ⟨GD1, F ::: F ::: KR, ones (d + 2) (F ::: F ::: F ::: F ::: ones n (F ::: true ::: blank))⟩ _
  refine Rch.tr (scanR (δ := delta) rfl (d + 2) _ _) ?_
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  cL; cL
  refine Rch.tr (scanL (δ := delta) rfl d _ _) ?_
  cL; cL
  rw [Nat.sub_self]; exact Reach.refl delta _

/-- fill B's hole on the way to its end -/
theorem fill (n p : Nat) (hp : 1 ≤ p) (hpn : p ≤ n) (L : Strm) :
    Rch ⟨GX, L, Bst n p⟩ ⟨GX, ones p L, ones (n - p) (true ::: blank)⟩ := by
  unfold Bst
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  refine Rch.tr (scanR (δ := delta) rfl q _ _) ?_
  cR
  rw [ones_cons_true]
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  exact Reach.refl delta _

/-- the configuration after the growth, before K/R is reset -/
def EIc (w n : Nat) (KR : Strm) : Cfg St :=
  cfgL EI1 KR (F ::: F ::: ones (w - 1) (F ::: true ::: F ::: F ::: F ::: F ::: Bst n n))

theorem grow (w : Nat) (KR : Strm) : ∀ u, 1 ≤ u → u ≤ w → ∀ j m,
    Rch ⟨GX, ones j (LG w u KR), ones m (true ::: blank)⟩ (EIc w (j + m + 4 * u) KR) := by
  intro u
  induction u with
  | zero => intro h; omega
  | succ u ih =>
    intro _ huw j m
    refine Rch.tr (append j m _) ?_
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · subst h0
      exact grow_last (j + m + 3) w KR (by omega)
    · refine Rch.tr (grow_back (j + m + 3) w (u + 1) KR (by omega) huw) ?_
      rw [Nat.add_sub_cancel]
      refine Rch.tr (fill _ _ (by omega) (Nat.le_refl _) _) ?_
      have := ih h0 (by omega) (j + m + 3 + 1) 0
      rw [show j + m + 3 + 1 + 0 + 4 * u = j + m + 4 * (u + 1) by omega] at this
      rw [Nat.sub_self]; exact this

/-- V gains a slot (the cursor hole) at its end; B loses its first slot -/
theorem vg (v a : Nat) (R : Strm) :
    Rch (cfgL VG1 (F ::: F ::: L1 v a) (F ::: R)) ⟨GX, LG (v + 2) (v + 2) (PostL a), R⟩ := by
  unfold L1 LG
  cL; cL; cL; cL
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  cR; cR; cR; cR; cR
  rw [Nat.sub_self, show v + 2 - 1 = v + 1 by omega]
  exact Reach.refl delta _

/-- a window starts: K/R `(1, 1)`, V's hole on its last slot, the flag 0, B's hole on its
last slot -/
def Start (v s : Nat) : Cfg St := TK 0 0 0 0 (VX v 0 (WF false s s))

theorem finish (v a n : Nat) : Rch (EIc (v + 2) n (PostL a)) (Start (v + 1) n) := by
  unfold EIc Start VX Vst WF
  rw [if_pos (Nat.zero_le _), Nat.sub_zero, ones_zero, show v + 2 - 1 = v + 1 by omega]
  exact kr_init a _

/-- the window is over without a match: next v -/
theorem rebuild1 (v a s : Nat) (hs : 1 ≤ s) :
    Rch ⟨F0s, F ::: false ::: L1 v a, Bst s 1⟩ (Start (v + 1) (s + 4 * v + 7)) := by
  unfold Bst
  rw [Nat.sub_self, ones_zero]
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  refine Rch.tr (vg v a _) ?_
  refine Rch.tr (grow (v + 2) (PostL a) (v + 2) (by omega) (Nat.le_refl _) 0 (s - 1)) ?_
  rw [show 0 + (s - 1) + 4 * (v + 2) = s + 4 * v + 7 by omega]
  exact finish v a _

/-- a second match: next v -/
theorem rebuild2 (v a s p : Nat) (hp : 1 ≤ p) (hps : p ≤ s) :
    Rch ⟨MF, L1 v a, true ::: F ::: Bst s p⟩ (Start (v + 1) (s + 4 * v + 7)) := by
  cR; cR
  unfold Bst
  rcases Nat.lt_or_ge p 2 with h | h
  · obtain rfl : p = 1 := by omega
    rw [Nat.sub_self, ones_zero]
    refine Rch.tr (stepL (δ := delta) rfl) ?_
    refine Rch.tr (vg v a _) ?_
    refine Rch.tr (grow (v + 2) (PostL a) (v + 2) (by omega) (Nat.le_refl _) 0 (s - 1)) ?_
    rw [show 0 + (s - 1) + 4 * (v + 2) = s + 4 * v + 7 by omega]
    exact finish v a _
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
    rw [show q + 2 - 1 = q + 1 by omega]
    refine Rch.tr (stepL (δ := delta) rfl) ?_
    refine Rch.tr (vg v a _) ?_
    have hf := fill (s - 1) (q + 1) (by omega) (by omega) (LG (v + 2) (v + 2) (PostL a))
    unfold Bst at hf
    rw [show q + 1 - 1 = q by omega, show s - 1 - (q + 1) = s - (q + 2) by omega] at hf
    refine Rch.tr hf ?_
    refine Rch.tr (grow (v + 2) (PostL a) (v + 2) (by omega) (Nat.le_refl _) (q + 1) (s - (q + 2))) ?_
    rw [show q + 1 + (s - (q + 2)) + 4 * (v + 2) = s + 4 * v + 7 by omega]
    exact finish v a _

/-- the seed: V `1 1 1`, then the next-v routine grows it to 3 slots and B to 11 -/
theorem seed : Rch start (Start 2 11) := by
  unfold start
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  simp only [tl_blank, tl_cons]
  cR
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  -- GX on the blank: the first append
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  simp only [tl_blank, tl_cons]
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  simp only [tl_blank, tl_cons]
  have h1 := grow_back 2 3 3 blank (by omega) (by omega)
  have h2 := fill 3 3 (by omega) (by omega) (LG 3 2 blank)
  have h3 := grow 3 blank 2 (by omega) (by omega) 3 0
  have h4 := kr_init_blank (ones 2 (F ::: true ::: F ::: F ::: F ::: F ::: Bst 11 11))
  have e : LG 3 3 blank = F ::: F ::: F ::: F ::: true ::: F ::: true ::: true ::: blank := by
    unfold LG; simp only [Nat.reduceSub, ones_zero, cons_blank]; rfl
  rw [e] at h1
  simp only [Nat.reduceSub, Nat.reduceAdd] at h1
  refine Rch.tr h1 ?_
  refine Rch.tr h2 (Rch.tr h3 ?_)
  unfold EIc
  refine Rch.tr h4 ?_
  unfold Start VX Vst WF
  exact Reach.refl delta _

end TM.Carmichael
