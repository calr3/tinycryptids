import TinyCryptids.Beal.Tac
import TinyCryptids.Carmichael.Spec

/-!
# The coprimality walk

Blocks a and b (`β_a = a + b + 1`, `β_b = j + e + 1` walk positions, on cells `2 ..`):
`TK a b j e La Rb` has H_a with `a` positions to its left and `b` to its right, H_b with
`j` and `e`; the head is just left of H_b in state `GK1`, at the start of a tick.
The ticks and wraps are proved here; `stride`, `strides` and `test` follow
`TinyCryptids/Carmichael/Round.lean`.
-/

namespace TM.Beal
open St TM.Carmichael

def TK (a b j e : Nat) (La Rb : Strm) : Cfg St :=
  cfgL GK1 (ones (j + 2) (F ::: F ::: ones (b + 1) (F ::: ones (a + 2) (F ::: F ::: La))))
    (F ::: ones (e + 1) (F ::: F ::: Rb))

theorem tick (a b j e : Nat) (La Rb : Strm) :
    Rch (TK a (b + 1) j (e + 1) La Rb) (TK (a + 1) b (j + 1) e La Rb) := by
  unfold TK
  sLn (j + 2); gL; gL
  rw [show b + 1 + 1 = b + 2 by rfl]
  sLn (b + 2)
  gR; gR; gL; gR
  sRn (b + 1); gR; gR
  sRn (j + 2); gR; gR; gL; gL
  fin

/-- a tick in which H_b wraps from its last position to its first -/
theorem tickW (a b j : Nat) (La Rb : Strm) :
    Rch (TK a (b + 1) j 0 La Rb) (TK (a + 1) b 0 j La Rb) := by
  unfold TK
  sLn (j + 2); gL; gL
  rw [show b + 1 + 1 = b + 2 by rfl]
  sLn (b + 2)
  gR; gR; gL; gR
  sRn (b + 1); gR; gR
  sRn (j + 2); gR; gR; gL
  sLn (j + 4)
  gR; gR; gR; gL
  fin

/-- the coprime exit: state `t1` on b's cell 3, H_a on a's first position -/
def CopC (a e : Nat) (La Rb : Strm) : Cfg St :=
  ⟨t1, ones 3 (F ::: F ::: ones (a + 1) (F ::: ones 2 (F ::: F ::: La))), ones (e + 1) (F ::: F ::: Rb)⟩

/-- H_a wraps with H_b on its first position: coprime -/
theorem wrapC (a e : Nat) (La Rb : Strm) : Rch (TK a 0 0 e La Rb) (CopC a e La Rb) := by
  unfold TK CopC
  sLn 2; gL; gL
  sLn 1
  gR; gR; gL
  sLn (a + 4)
  gR; gR; gR; gR
  sRn (a + 1); gR; gR; gR; gR; gR
  fin

/-- H_a wraps, H_b not on its first or last position: the walk goes on -/
theorem wrapM (a j e : Nat) (La Rb : Strm) :
    Rch (TK a 0 (j + 1) (e + 1) La Rb) (TK 0 a (j + 2) e La Rb) := by
  unfold TK
  sLn (j + 3); gL; gL
  sLn 1
  gR; gR; gL
  sLn (a + 4)
  gR; gR; gR; gR
  sRn (a + 1); gR; gR; gR; gR; gR
  sRn j; gR; gR; gL; gL
  simp only [ones_cons_true, ones_succ, tl_cons, Nat.zero_add]; fin

/-- the not-coprime exit: state `HE1` on b's last cell, H_b gone, H_a on a's first position -/
def NcC (a j : Nat) (La Rb : Strm) : Cfg St :=
  cfgL HE1 (ones (j + 5) (F ::: F ::: ones (a + 1) (F ::: ones 2 (F ::: F ::: La)))) (F ::: F ::: Rb)

/-- H_a wraps with H_b on its last position: not coprime -/
theorem wrapN (a j : Nat) (La Rb : Strm) :
    Rch (TK a 0 (j + 1) 0 La Rb) (NcC a j La Rb) := by
  unfold TK NcC
  sLn (j + 3); gL; gL
  sLn 1
  gR; gR; gL
  sLn (a + 4)
  gR; gR; gR; gR
  sRn (a + 1); gR; gR; gR; gR; gR
  sRn j; gR; gR; gL
  show Rch (cfgL HE1 (true ::: true ::: ones j (true ::: true ::: true ::: F ::: F ::: ones (a + 1)
    (F ::: true ::: true ::: F ::: tl (F ::: F ::: La)))) (F ::: F ::: Rb)) _
  simp only [ones_cons_true, ones_succ, tl_cons]; fin

theorem mod_succ_eq' (x r : Nat) (hr : 1 ≤ r) :
    (x + 1) % r = if x % r + 1 = r then 0 else x % r + 1 := by
  have h1 := Nat.mod_lt x (by omega : r > 0)
  have h2 := Nat.div_add_mod x r
  split
  · rw [show x + 1 = r * (x / r + 1) by rw [Nat.mul_succ]; omega]; exact Nat.mul_mod_right _ _
  · rw [show x + 1 = (x % r + 1) + r * (x / r) by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]

/-- a tick, R's hole at position `j` of `r` -/
theorem tickg (a b j r : Nat) (hj : j < r) (La Rb : Strm) :
    Rch (TK a (b + 1) j (r - 1 - j) La Rb)
      (TK (a + 1) b ((j + 1) % r) (r - 1 - (j + 1) % r) La Rb) := by
  rcases Nat.lt_or_ge (j + 1) r with h | h
  · rw [Nat.mod_eq_of_lt h, show r - 1 - j = (r - 1 - (j + 1)) + 1 by omega]
    exact tick a b j _ _ _
  · rw [show j + 1 = r by omega, Nat.mod_self, show r - 1 - j = 0 by omega,
      show r - 1 - 0 = j by omega]
    exact tickW a b j La Rb

theorem ticks (r : Nat) (La Rb : Strm) : ∀ b a j, j < r →
    Rch (TK a b j (r - 1 - j) La Rb) (TK (a + b) 0 ((j + b) % r) (r - 1 - (j + b) % r) La Rb) := by
  intro b
  induction b with
  | zero => intro a j hj; rw [Nat.add_zero, Nat.add_zero, Nat.mod_eq_of_lt hj]; exact Reach.refl delta _
  | succ b ih =>
    intro a j hj
    refine Rch.tr (tickg a b j r hj La Rb) ?_
    have := ih (a + 1) ((j + 1) % r) (Nat.mod_lt _ (by omega))
    rw [Nat.mod_add_mod, show j + 1 + b = j + (b + 1) by omega,
      show a + 1 + b = a + (b + 1) by omega] at this
    exact this

/-- the outcome of the test of `(k, r)` -/
def Res (k r : Nat) (La Rb : Strm) : Cfg St :=
  if Nat.gcd k r = 1 then CopC (k - 1) (r - 1) La Rb else NcC (k - 1) (r - 2) La Rb

/-- the start of stride `q`: H_a on its first position, H_b at `(q - 1) k mod r` -/
def SS (k r q : Nat) (La Rb : Strm) : Cfg St :=
  TK 0 (k - 1) ((q - 1) * k % r) (r - 1 - (q - 1) * k % r) La Rb

theorem stride (k r q : Nat) (hk : 1 ≤ k) (hr : 1 ≤ r) (hq : 1 ≤ q) (La Rb : Strm) :
    (hitC k r q → Rch (SS k r q La Rb) (CopC (k - 1) (r - 1) La Rb)) ∧
    (hitN k r q → ¬ hitC k r q → Rch (SS k r q La Rb) (NcC (k - 1) (r - 2) La Rb)) ∧
    (¬ hitC k r q → ¬ hitN k r q → Rch (SS k r q La Rb) (SS k r (q + 1) La Rb)) := by
  have hj := Nat.mod_lt ((q - 1) * k) (by omega : r > 0)
  generalize hjq : (q - 1) * k % r = jq at hj
  have hqk : q * k % r = (jq + (k - 1) + 1) % r := by
    rw [show jq + (k - 1) + 1 = jq + k by omega, ← hjq, Nat.mod_add_mod,
      show (q - 1) * k + k = q * k by
        rw [← Nat.succ_mul, show (q - 1).succ = q by omega]]
  rw [mod_succ_eq' _ r hr] at hqk
  have hx := Nat.mod_lt (jq + (k - 1)) (by omega : r > 0)
  generalize hj' : (jq + (k - 1)) % r = j' at hqk hx
  have hrun : Rch (SS k r q La Rb) (TK (k - 1) 0 j' (r - 1 - j') La Rb) := by
    unfold SS; rw [hjq]
    have := ticks r La Rb (k - 1) 0 jq hj
    rwa [Nat.zero_add, hj'] at this
  have hS : SS k r (q + 1) La Rb = TK 0 (k - 1) (q * k % r) (r - 1 - q * k % r) La Rb := by
    unfold SS; rw [Nat.add_sub_cancel]
  unfold hitC hitN
  rcases Nat.eq_zero_or_pos j' with h0 | h0
  · subst h0
    refine ⟨fun _ => Rch.tr hrun ?_, fun _ hc => absurd ?_ hc, fun hc _ => absurd ?_ hc⟩
    · have := wrapC (k - 1) (r - 1 - 0) La Rb; rwa [Nat.sub_zero] at this
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
        exact wrapM (k - 1) j _ _ _
    · rw [if_pos (by omega)] at hqk
      have hr2 : 1 < r := by omega
      refine ⟨fun hc => absurd hc ?_, fun _ _ => Rch.tr hrun ?_, fun _ hn => absurd hqk hn⟩
      · rw [hqk, Nat.mod_eq_of_lt hr2]; omega
      · rw [show r - 1 - (j + 1) = 0 by omega]
        have := wrapN (k - 1) j La Rb
        rw [show r - 2 = j by omega]; exact this

theorem strides (k r : Nat) (hk : 1 ≤ k) (hr : 1 ≤ r) (La Rb : Strm) : ∀ n q, q + n = r → 1 ≤ q →
    (∀ i, 1 ≤ i → i < q → ¬ hitC k r i ∧ ¬ hitN k r i) → Rch (SS k r q La Rb) (Res k r La Rb) := by
  have hit : ∀ q, 1 ≤ q → (∀ i, 1 ≤ i → i < q → ¬ hitC k r i ∧ ¬ hitN k r i) →
      (hitC k r q ∨ hitN k r q) → Rch (SS k r q La Rb) (Res k r La Rb) := by
    intro q hq hfirst hh
    have fh := first_hit hr hq hfirst
    have st := stride k r q hk hr hq La Rb
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
      refine Rch.tr ((stride k r q hk hr hq1 La Rb).2.2 hC hN) (ih (q + 1) (by omega) (by omega) ?_)
      intro i hi1 hi
      rcases Nat.lt_or_ge i q with h | h
      · exact hfirst i hi1 h
      · rw [show i = q by omega]; exact ⟨hC, hN⟩

/-- the test of `(k, r)`, from both holes on their first positions -/
theorem test (k r : Nat) (hk : 1 ≤ k) (hr : 1 ≤ r) (La Rb : Strm) :
    Rch (TK 0 (k - 1) 0 (r - 1) La Rb) (Res k r La Rb) := by
  have := strides k r hk hr La Rb (r - 1) 1 (by omega) (Nat.le_refl 1) (fun i h1 h2 => by omega)
  unfold SS at this; simpa using this

end TM.Beal
