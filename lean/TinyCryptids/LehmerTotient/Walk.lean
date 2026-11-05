import TinyCryptids.LehmerTotient.Tac
import TinyCryptids.Carmichael.Spec

/-!
# The coprimality test and the sweep (`../carmichael`'s, on this machine)

Tape (left to right): `1 K 00 1 R 00 Y`. `K` has `k` slots, `R` has `r` slots, each with one
hole (a single `0`); `Y` is the pair `D 00 P`.

    TK a b j e X : `KA` on K's hole, `a` slots left of it and `b` right of it
                   (`k = a + b + 1`); R's hole has `j` slots left and `e` right
                   (`r = j + e + 1`); `X` is the rest of the tape, from the separator
                   after R.
-/

namespace TM.LehmerTotient
open St TinyCryptids
open TM.Carmichael (hitC hitN first_hit hitN_r)

local notation "F" => false

def TK (a b j e : Nat) (X : Strm) : Cfg St :=
  ⟨KA, ones (a + 1) blank, F ::: ones b (F ::: F ::: ones (j + 1) (F ::: ones e X))⟩

theorem tick (a b j e : Nat) (X : Strm) : Rch (TK a (b + 1) j (e + 1) X) (TK (a + 1) b (j + 1) e X) := by
  unfold TK
  gR; gR
  refine Rch.tr (scanR (δ := delta) rfl b _ _) ?_
  gR; gR; gR
  refine Rch.tr (scanR (δ := delta) rfl j _ _) ?_
  gR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL GK1 (true ::: ones j (true ::: F ::: F ::: ones b (F ::: true ::: ones (a + 1) blank)))
    (F ::: ones e X)) _
  rw [ones_cons_true]
  refine Rch.tr (scanL (δ := delta) (n := j + 2) rfl _ _) ?_
  gL; gL
  refine Rch.tr (scanL (δ := delta) rfl b _ _) ?_
  exact Reach.refl delta _

/-- a tick in which R's hole wraps from its last slot to its first -/
theorem tickW (a b j : Nat) (Y : Strm) :
    Rch (TK a (b + 1) j 0 (F ::: Y)) (TK (a + 1) b 0 j (F ::: Y)) := by
  unfold TK
  gR; gR
  refine Rch.tr (scanR (δ := delta) rfl b _ _) ?_
  gR; gR; gR
  refine Rch.tr (scanR (δ := delta) rfl j _ _) ?_
  gR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL RW (true ::: ones j (true ::: F ::: F ::: ones b (F ::: true ::: ones (a + 1) blank)))
    (F ::: Y)) _
  rw [ones_cons_true]
  refine Rch.tr (scanL (δ := delta) (n := j + 2) rfl _ _) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  gR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL GK1 (true ::: F ::: F ::: ones b (F ::: true ::: ones (a + 1) blank))
    (F ::: ones j (F ::: Y))) _
  gL; gL; gL
  refine Rch.tr (scanL (δ := delta) rfl b _ _) ?_
  exact Reach.refl delta _

/-- the cells left of b2 after a test: b1 (the hole), R's start, the separator, K with
`a + 1` slots and its hole on a1, K's start -/
def PostL (a : Nat) : Strm := F ::: true ::: F ::: F ::: ones a (F ::: true ::: blank)

/-- a wrap of K's hole with R's hole on b1: coprime -/
theorem wrapC (a e : Nat) (X : Strm) :
    Rch (TK a 0 0 e X) ⟨CV1, PostL a, ones e X⟩ := by
  unfold TK
  gR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL KW (ones (a + 2) blank) (F ::: F ::: ones 1 (F ::: ones e X))) _
  refine Rch.tr (scanL (δ := delta) rfl (a + 2) _ _) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  gR; gR
  refine Rch.tr (scanR (δ := delta) rfl a _ _) ?_
  gR; gR; gR; gR
  rw [tl_blank, cons_blank]; exact Reach.refl delta _

/-- a wrap of K's hole, R's hole not at its ends: the walk goes on -/
theorem wrapM (a j e : Nat) (X : Strm) :
    Rch (TK a 0 (j + 1) (e + 1) X) (TK 0 a (j + 2) e X) := by
  unfold TK
  gR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL KW (ones (a + 2) blank) (F ::: F ::: ones (j + 2) (F ::: ones (e + 1) X))) _
  refine Rch.tr (scanL (δ := delta) rfl (a + 2) _ _) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  gR; gR
  refine Rch.tr (scanR (δ := delta) rfl a _ _) ?_
  gR; gR; gR; gR
  refine Rch.tr (scanR (δ := delta) rfl j _ _) ?_
  gR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL GK1 (true ::: ones j (true ::: true ::: F ::: F ::: ones a (F ::: true ::: F ::: tl blank)))
    (F ::: ones e X)) _
  rw [ones_cons_true, ones_cons_true, tl_blank, cons_blank]
  refine Rch.tr (scanL (δ := delta) (n := j + 3) rfl _ _) ?_
  gL; gL
  refine Rch.tr (scanL (δ := delta) rfl a _ _) ?_
  exact Reach.refl delta _

/-- a wrap of K's hole with R's hole on its last slot: not coprime -/
theorem wrapN (a j : Nat) (Y : Strm) :
    Rch (TK a 0 (j + 1) 0 (F ::: Y)) ⟨EC1, PostL a, ones (j + 1) (F ::: Y)⟩ := by
  unfold TK
  gR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL KW (ones (a + 2) blank) (F ::: F ::: ones (j + 2) (F ::: ones 0 (F ::: Y)))) _
  refine Rch.tr (scanL (δ := delta) rfl (a + 2) _ _) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  gR; gR
  refine Rch.tr (scanR (δ := delta) rfl a _ _) ?_
  gR; gR; gR; gR
  refine Rch.tr (scanR (δ := delta) rfl j _ _) ?_
  gR
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  show Rch (cfgL CW (true ::: ones j (true ::: true ::: F ::: F ::: ones a (F ::: true ::: F ::: tl blank)))
    (F ::: Y)) _
  rw [ones_cons_true, ones_cons_true, tl_blank, cons_blank]
  refine Rch.tr (scanL (δ := delta) (n := j + 3) rfl _ _) ?_
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  gR; gR
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

/-- the separator one cell right: `(k, r + 1) → (k + 1, r)` -/
theorem shift (a e : Nat) (X : Strm) : Rch ⟨EC1, PostL a, ones (e + 1) X⟩ (TK 0 (a + 1) 0 e X) := by
  unfold PostL TK
  refine Rch.tr (stepL (δ := delta) rfl) ?_
  gL; gL; gL; gL
  refine Rch.tr (scanL (δ := delta) rfl a _ _) ?_
  rw [ones_cons_true]; exact Reach.refl delta _


/-- `(M - 1, 1) → (1, M)`, from R's hole; then on R's slot 2 -/
theorem reset (M : Nat) (hM : 2 ≤ M) (Z : Strm) :
    Rch (cfgL RS1 (PostL (M - 2)) (F ::: F ::: Z)) ⟨PU1, PostL 0, ones (M - 1) (F ::: F ::: Z)⟩ := by
  unfold PostL
  gL; gL; gL; gL
  refine Rch.tr (scanL (δ := delta) rfl (M - 2) _ _) ?_
  gL; gL
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  gR; gR
  show Rch ⟨RS10, _, ones (M - 2) (true ::: true ::: true ::: true ::: F ::: F ::: Z)⟩ _
  rw [ones_cons_true, ones_cons_true, ones_cons_true, ones_cons_true]
  gR; gR; gR
  rw [tl_blank, show M - 1 = (M - 2) + 1 by omega]; fin

end TM.LehmerTotient
