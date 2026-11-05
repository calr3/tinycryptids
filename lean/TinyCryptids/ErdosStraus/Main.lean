import TinyCryptids.ErdosStraus.NStep
import TinyCryptids.ErdosStraus.Spec

/-!
# Main theorem: the design halts iff the Erdős–Straus conjecture is false
-/

namespace TM.ErdosStraus

open St

local notation "F" => false
local notation "T" => true

/-! ## the y counter -/

theorem kc1 {m W : Nat} (h : W ≤ m + 1) : kc m W = m + 2 - W := by unfold kc; exact if_pos h
theorem kc2 {m W : Nat} (h : ¬ W ≤ m + 1) : kc m W = 1 := by unfold kc; exact if_neg h
theorem ke1 {m W : Nat} (h : W ≤ m + 1) : ke m W = W + 1 := by unfold ke; exact if_pos h
theorem ke2 {m W : Nat} (h : ¬ W ≤ m + 1) : ke m W = 2 * m + 3 - W := by unfold ke; exact if_neg h
theorem kd1 {m W : Nat} (h : W ≤ m + 1) : kd m W = 2 := by unfold kd; exact if_pos h
theorem kd2 {m W : Nat} (h : ¬ W ≤ m + 1) : kd m W = W - m + 1 := by unfold kd; exact if_neg h

theorem k_lap1 {m W : Nat} (h : W ≤ m) :
    2 ≤ kc m W ∧ kc m (W + 1) = kc m W - 1 ∧ ke m (W + 1) = ke m W + 1 ∧ kd m (W + 1) = kd m W ∧
      1 ≤ ke m W := by
  rw [kc1 (by omega), kc1 (by omega), ke1 (by omega), ke1 (by omega), kd1 (by omega), kd1 (by omega)]
  omega

theorem k_lap2 {m W : Nat} (h1 : m + 1 ≤ W) (h2 : W ≤ 2 * m + 1) :
    kc m W = 1 ∧ kc m (W + 1) = 1 ∧ 2 ≤ ke m W ∧ ke m (W + 1) = ke m W - 1 ∧
      kd m (W + 1) = kd m W + 1 := by
  rcases Nat.lt_or_ge (m + 1) W with h | h
  · rw [kc2 (W := W) (by omega), kc2 (W := W + 1) (by omega), ke2 (W := W) (by omega),
      ke2 (W := W + 1) (by omega), kd2 (W := W) (by omega), kd2 (W := W + 1) (by omega)]
    omega
  · rw [kc1 (W := W) (by omega), kc2 (W := W + 1) (by omega), ke1 (W := W) (by omega),
      ke2 (W := W + 1) (by omega), kd1 (W := W) (by omega), kd2 (W := W + 1) (by omega)]
    omega

theorem k_stop {m : Nat} : kc m (2 * m + 2) = 1 ∧ ke m (2 * m + 2) = 1 ∧ kd m (2 * m + 2) = m + 3 := by
  rw [kc2 (m := m) (W := 2 * m + 2) (by omega), ke2 (m := m) (W := 2 * m + 2) (by omega),
    kd2 (m := m) (W := 2 * m + 2) (by omega)]; omega

theorem k_pos (m W : Nat) (hW : W ≤ 2 * m + 2) : 1 ≤ kc m W ∧ 1 ≤ ke m W ∧ 2 ≤ kd m W := by
  by_cases h : W ≤ m + 1
  · rw [kc1 h, ke1 h, kd1 h]; omega
  · rw [kc2 h, ke2 h, kd2 h]; omega

/-- the y counter at `W` -/
abbrev KW (m W : Nat) (P : Strm) : Strm := KD' (kc m W) (ke m W) (kd m W) P

/-- one unit (`W ≤ 2m + 1`) -/
theorem unitW (n a m i W : Nat) (P : Strm) (hi : 1 ≤ i) (hia : i ≤ a) (ha : a ≤ 2 * n)
    (hn : 2 ≤ n) (hm : 1 ≤ m) (hW : W ≤ 2 * m + 1) :
    Rch (CU a i (RR n a m (KW m W P))) (AC a i (RR n a m (KW m (W + 1) P))) := by
  rcases Nat.lt_or_ge m W with h | h
  · obtain ⟨c1, c2, e2, e3, d3⟩ := k_lap2 (m := m) (W := W) (by omega) hW
    have := unit2 n a m i (ke m W) (kd m W) P hi hia ha hn hm e2
    unfold KW; rw [c1, c2, e3, d3]; exact this
  · obtain ⟨c2, c3, e3, d3, e1⟩ := k_lap1 (m := m) (W := W) h
    have := unit1 n a m i (kc m W) (ke m W) (kd m W) P hi hia ha hn hm c2 e1
    unfold KW; rw [c3, e3, d3]; exact this

/-- the units from cursor `i` on: all of them (`W' ≤ 2m + 2`), or the stop -/
theorem cloop (n a m p : Nat) (ha : 1 ≤ a) (ha2 : a ≤ 2 * n) (hn : 2 ≤ n) (hm : 1 ≤ m) :
    ∀ k i W, i + k = a → 1 ≤ i → W ≤ 2 * m + 2 →
      (W + k + 1 ≤ 2 * m + 2 →
        Rch (CU a i (RR n a m (KW m W (ones (p + 1) blank))))
          ⟨F1, F ::: F ::: ones (a + 1) blank, RR n a m (KW m (W + k + 1) (ones (p + 1) blank))⟩) ∧
      (2 * m + 2 < W + k + 1 → Rch (CU a i (RR n a m (KW m W (ones (p + 1) blank)))) (G (Lb n a) n m)) := by
  intro k
  induction k with
  | zero =>
    intro i W hk hi hW
    obtain rfl : i = a := by omega
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact Rch.tr (unitW n i m i W _ hi (Nat.le_refl _) ha2 hn hm (by omega)) (ac_last _ _)
    · obtain rfl : W = 2 * m + 2 := by omega
      obtain ⟨c1, e1, d1⟩ := k_stop (m := m)
      have := stop n i m i p hi (Nat.le_refl _) ha2 hn hm
      unfold KW; rw [c1, e1, d1]; exact this
  | succ k ih =>
    intro i W hk hi hW
    refine ⟨fun h => ?_, fun h => ?_⟩
    · refine Rch.tr (unitW n a m i W _ hi (by omega) ha2 hn hm (by omega)) ?_
      refine Rch.tr (ac_next a i _ (by omega)) ?_
      have := (ih (i + 1) (W + 1) (by omega) (by omega) (by omega)).1 (by omega)
      rw [show W + 1 + k + 1 = W + (k + 1) + 1 by omega] at this
      exact this
    · rcases Nat.lt_or_ge W (2 * m + 2) with hl | hl
      · refine Rch.tr (unitW n a m i W _ hi (by omega) ha2 hn hm (by omega)) ?_
        refine Rch.tr (ac_next a i _ (by omega)) ?_
        exact (ih (i + 1) (W + 1) (by omega) (by omega) (by omega)).2 (by omega)
      · obtain rfl : W = 2 * m + 2 := by omega
        obtain ⟨c1, e1, d1⟩ := k_stop (m := m)
        have := stop n a m i p hi (by omega) ha2 hn hm
        unfold KW; rw [c1, e1, d1]; exact this

/-- `(x + 1) % d` from `x % d` (`../OddPerfect/Spec.lean`) -/
theorem mod_succ (x d : Nat) :
    (x % d + 1 < d → (x + 1) % d = x % d + 1) ∧ (x % d + 1 = d → (x + 1) % d = 0) := by
  have e := Nat.div_add_mod x d
  constructor
  · intro h
    have : x + 1 = d * (x / d) + (x % d + 1) := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt h]
  · intro h
    have : x + 1 = d * (x / d + 1) := by rw [Nat.mul_add]; omega
    rw [this, Nat.mul_mod_right]

/-! ## one y step -/

/-- a y step starts with the y counter at `W` and `P` holding `p` -/
def YC (n a m W p : Nat) : Cfg St := YP (LN n a) m 1 (kc m W) (ke m W) (kd m W) p

/-- `P += M` and the `a` units, up to the end of the units (or the stop) -/
theorem ystep_units (n a m W p : Nat) (hn : 2 ≤ n) (ha : 1 ≤ a) (ha2 : a ≤ 2 * n) (hm : 2 ≤ m)
    (hW : W ≤ 2 * m + 2) :
    (W + a ≤ 2 * m + 2 → Rch (YC n a m W p)
      ⟨F1, F ::: F ::: ones (a + 1) blank, RR n a m (KW m (W + a) (ones (p + m + 1) blank))⟩) ∧
    (2 * m + 2 < W + a → Rch (YC n a m W p) (G (Lb n a) n m)) := by
  obtain ⟨c1, e1, d1⟩ := k_pos m W hW
  have st : Rch (YC n a m W p) (CU a 1 (RR n a m (KW m W (ones (p + m + 1) blank)))) :=
    Rch.tr (pmloop _ m _ _ _ p (by omega) c1 e1 (by omega)) (consume_start n a m _ _ _ (p + m) ha ha2)
  have cl := cloop n a m (p + m) ha ha2 hn (by omega) (a - 1) 1 W (by omega) (Nat.le_refl _) hW
  rw [show W + (a - 1) + 1 = W + a by omega] at cl
  exact ⟨fun h => Rch.tr st (cl.1 h), fun h => Rch.tr st (cl.2 h)⟩

theorem ystep_lap1 (n a m W p : Nat) (hn : 2 ≤ n) (ha : 1 ≤ a) (ha2 : a ≤ 2 * n) (hm : 2 ≤ m)
    (hW : W ≤ 2 * m + 2) (h : W + a ≤ m) : Rch (YC n a m W p) (YC n a m (W + a) (p + m)) := by
  refine Rch.tr ((ystep_units n a m W p hn ha ha2 hm hW).1 (by omega)) ?_
  obtain ⟨c2, -, -, -, e1⟩ := k_lap1 (m := m) (W := W + a) h
  exact lap1_next n a m _ _ _ (p + m) ha2 hn (by omega) c2 e1

/-- second lap: the test `W + a - m ∣ p + m` -/
theorem ystep_test (n a m W p : Nat) (hn : 2 ≤ n) (ha : 1 ≤ a) (ha2 : a ≤ 2 * n) (hm : 2 ≤ m)
    (hW : W ≤ 2 * m + 2) (h1 : m + 1 ≤ W + a) (h2 : W + a ≤ 2 * m + 2) :
    ((W + a - m) ∣ (p + m) → Rch (YC n a m W p) (G (Ld (n + 1) 0) (n + 1) 0)) ∧
    (¬ (W + a - m) ∣ (p + m) → Rch (YC n a m W p) (YC n a m (W + a) (p + m))) := by
  have st := (ystep_units n a m W p hn ha ha2 hm hW).1 h2
  have hc : kc m (W + a) = 1 := by
    by_cases hh : W + a ≤ m + 1
    · rw [kc1 hh]; omega
    · exact kc2 hh
  have hd : kd m (W + a) = (W + a - m) + 1 := by
    by_cases hh : W + a ≤ m + 1
    · rw [kd1 hh]; omega
    · rw [kd2 hh]
  have he : 1 ≤ ke m (W + a) := (k_pos m (W + a) h2).2.1
  unfold KW at st
  rw [hc, hd] at st
  have ts := test_setup n a m (ke m (W + a)) (W + a - m) (p + m) ha2 hn (by omega) (by omega) (by omega)
  have wk := walk1 (KY n a m (ke m (W + a))) (W + a - m) (p + m - 1) (by omega) (by omega)
  have ms := mod_succ (p + m - 1) (W + a - m)
  have hlt := Nat.mod_lt (p + m - 1) (show W + a - m > 0 by omega)
  rw [show p + m - 1 + 1 = p + m by omega] at ms
  refine ⟨fun hdv => ?_, fun hdv => ?_⟩
  · have h0 := Nat.mod_eq_zero_of_dvd hdv
    have home : (p + m - 1) % (W + a - m) + 1 = W + a - m := by
      rcases Nat.lt_or_ge ((p + m - 1) % (W + a - m) + 1) (W + a - m) with hl | hl
      · have := ms.1 hl; omega
      · omega
    rw [home] at wk
    exact Rch.tr st (Rch.tr ts (Rch.tr wk (nstep n a m _ _ _ ha ha2 (by omega) (by omega) he)))
  · have nh : (p + m - 1) % (W + a - m) + 1 < W + a - m := by
      rcases Nat.lt_or_ge ((p + m - 1) % (W + a - m) + 1) (W + a - m) with hl | hl
      · exact hl
      · exact absurd (Nat.dvd_of_mod_eq_zero (ms.2 (by omega))) hdv
    refine Rch.tr st (Rch.tr ts (Rch.tr wk ?_))
    have := test_fail n a m (ke m (W + a)) (W + a - m) (p + m - 1) _ (by omega) (by omega) nh
    unfold YC
    rw [hc, hd, show p + m - 1 + 1 = p + m by omega] at *
    exact this

theorem ystep_stop (n a m W p : Nat) (hn : 2 ≤ n) (ha : 1 ≤ a) (ha2 : a ≤ 2 * n) (hm : 2 ≤ m)
    (hW : W ≤ 2 * m + 2) (h : 2 * m + 2 < W + a) : Rch (YC n a m W p) (G (Lb n a) n m) :=
  (ystep_units n a m W p hn ha ha2 hm hW).2 h

/-! ## the y loop -/

/-- the y loop for `a`, `m` from step `j + 1` (`W = a j`, `p = m j`): a hit at some `y > j`
leads to the next `n`, no hit to the next `x` -/
theorem yloop (n a m : Nat) (hn : 2 ≤ n) (ha : 1 ≤ a) (ha2 : a ≤ 2 * n) (hm : 2 ≤ m) :
    ∀ f j, 2 * m + 2 - a * j < f → a * j ≤ 2 * m + 2 →
      ((∃ y, j < y ∧ m + 1 ≤ a * y ∧ a * y ≤ 2 * m + 2 ∧ (a * y - m) ∣ m * y) →
        Rch (YC n a m (a * j) (m * j)) (G (Ld (n + 1) 0) (n + 1) 0)) ∧
      ((¬ ∃ y, j < y ∧ m + 1 ≤ a * y ∧ a * y ≤ 2 * m + 2 ∧ (a * y - m) ∣ m * y) →
        Rch (YC n a m (a * j) (m * j)) (G (Lb n a) n m)) := by
  intro f
  induction f with
  | zero => intro j h; omega
  | succ f ih =>
    intro j hf hW
    have e1 : a * (j + 1) = a * j + a := Nat.mul_succ a j
    have e2 : m * (j + 1) = m * j + m := Nat.mul_succ m j
    have next : a * (j + 1) ≤ 2 * m + 2 → ¬ (m + 1 ≤ a * (j + 1) ∧ (a * (j + 1) - m) ∣ m * (j + 1)) →
        Rch (YC n a m (a * j) (m * j)) (YC n a m (a * (j + 1)) (m * (j + 1))) := by
      intro hle hno
      rw [e1, e2]
      rcases Nat.lt_or_ge (a * j + a) (m + 1) with hl | hl
      · exact ystep_lap1 n a m _ _ hn ha ha2 hm hW (by omega)
      · rw [e1, e2] at hno
        exact (ystep_test n a m _ _ hn ha ha2 hm hW hl (by omega)).2 (fun hd => hno ⟨hl, hd⟩)
    have ihj := ih (j + 1)
    have hf' : a * (j + 1) ≤ 2 * m + 2 → 2 * m + 2 - a * (j + 1) < f := by rw [e1]; omega
    refine ⟨fun hex => ?_, fun hno => ?_⟩
    · obtain ⟨y, hy, h1, h2, h3⟩ := hex
      by_cases hit : m + 1 ≤ a * (j + 1) ∧ a * (j + 1) ≤ 2 * m + 2 ∧ (a * (j + 1) - m) ∣ m * (j + 1)
      · obtain ⟨g1, g2, g3⟩ := hit
        rw [e1] at g1 g2; rw [e1, e2] at g3
        exact (ystep_test n a m _ _ hn ha ha2 hm hW g1 g2).1 g3
      · have hy1 : j + 1 < y := by
          rcases Nat.lt_or_ge (j + 1) y with h | h
          · exact h
          · obtain rfl : y = j + 1 := by omega
            exact absurd ⟨h1, h2, h3⟩ hit
        have hmono : a * (j + 1) ≤ a * y := Nat.mul_le_mul_left a (by omega)
        refine Rch.tr (next (by omega) (fun h => hit ⟨h.1, by omega, h.2⟩)) ?_
        exact (ihj (hf' (by omega)) (by omega)).1 ⟨y, hy1, h1, h2, h3⟩
    · rcases Nat.lt_or_ge (2 * m + 2) (a * (j + 1)) with hs | hs
      · rw [e1] at hs
        exact ystep_stop n a m _ _ hn ha ha2 hm hW hs
      · refine Rch.tr (next hs (fun h => hno ⟨j + 1, by omega, h.1, hs, h.2⟩)) ?_
        exact (ihj (hf' hs) hs).2 (fun ⟨y, hy, h⟩ => hno ⟨y, by omega, h⟩)

/-! ## the x loop -/

/-- the x step for `x ≥ 1` starts: `U = 4(x - 1)`, `m = n(x - 1)` -/
def Gx (n x : Nat) : Cfg St :=
  if 4 * (x - 1) ≤ n then G (Ld n (4 * (x - 1))) n (n * (x - 1))
  else G (Lb n (4 * (x - 1) - n)) n (n * (x - 1))

theorem YS_eq (n a m : Nat) : YS n a m 0 0 = YC n a m 0 0 := by
  unfold YS YC YP
  rw [KD_eq]
  rfl

theorem nx_succ (n x : Nat) (hx : 1 ≤ x) : n * (x - 1) + n = n * x := by
  obtain ⟨k, rfl⟩ : ∃ k, x = k + 1 := ⟨x - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.mul_succ]

theorem xs_debt (n x : Nat) (hn : 2 ≤ n) (hx : 1 ≤ x) (h : 4 * x ≤ n) : Rch (Gx n x) (Gx n (x + 1)) := by
  unfold Gx
  rw [if_pos (by omega), if_pos (by omega), show x + 1 - 1 = x by omega]
  refine Rch.tr (nloop _ n _ (by omega)) ?_
  have := debt_move n (4 * (x - 1)) (n * (x - 1) + n) (by omega)
  rw [show 4 * (x - 1) + 4 = 4 * x by omega, nx_succ n x hx] at this
  rw [nx_succ n x hx]; exact this

theorem xs_y (n x : Nat) (hn : 2 ≤ n) (hx : 1 ≤ x) (h1 : n < 4 * x) (h2 : 4 * x ≤ 3 * n) :
    Rch (Gx n x) (YC n (4 * x - n) (n * x) 0 0) := by
  have hm : 1 ≤ n * x := Nat.mul_pos (by omega) hx
  rw [← YS_eq]
  unfold Gx
  by_cases hd : 4 * (x - 1) ≤ n
  · rw [if_pos hd]
    refine Rch.tr (nloop _ n _ (by omega)) ?_
    have := cross_move n (4 * (x - 1)) (n * (x - 1) + n) hd (by omega) hn (by rw [nx_succ n x hx]; exact hm)
    rw [nx_succ n x hx, show 4 * (x - 1) + 4 - n = 4 * x - n by omega] at this
    rw [nx_succ n x hx]; exact this
  · rw [if_neg hd]
    refine Rch.tr (nloop _ n _ (by omega)) ?_
    have := b_move n (4 * (x - 1) - n) (n * (x - 1) + n) (by omega) (by rw [nx_succ n x hx]; exact hm)
    rw [nx_succ n x hx, show 4 * (x - 1) - n + 4 = 4 * x - n by omega] at this
    rw [nx_succ n x hx]; exact this

theorem xs_halt (n x : Nat) (hn : 2 ≤ n) (hx : 1 ≤ x) (h1 : 4 * (x - 1) ≤ 3 * n) (h2 : 3 * n < 4 * x) :
    HaltAt (Gx n x) := by
  unfold Gx
  rw [if_neg (by omega)]
  refine HaltAt.back (nloop _ n _ (by omega)) ?_
  exact b_halt n _ _ (by omega) (by omega)

/-- no hit for `x`: the y loop ends at the next x -/
theorem G_next (n x : Nat) (hx : 1 ≤ x) (h1 : n < 4 * x) :
    G (Lb n (4 * x - n)) n (n * x) = Gx n (x + 1) := by
  unfold Gx
  rw [if_neg (by omega), show x + 1 - 1 = x by omega]

/-- the x loop: a hit for some `x' ≥ x` leads to the next `n`, otherwise the machine halts -/
theorem xloop (n : Nat) (hn : 2 ≤ n) :
    ∀ f x, 3 * n + 4 - 4 * x < f → 1 ≤ x → 4 * (x - 1) ≤ 3 * n →
      ((∃ x' y, x ≤ x' ∧ n < 4 * x' ∧ 4 * x' ≤ 3 * n ∧ 1 ≤ y ∧ Hit n x' y) →
        Rch (Gx n x) (G (Ld (n + 1) 0) (n + 1) 0)) ∧
      ((¬ ∃ x' y, x ≤ x' ∧ n < 4 * x' ∧ 4 * x' ≤ 3 * n ∧ 1 ≤ y ∧ Hit n x' y) → HaltAt (Gx n x)) := by
  intro f
  induction f with
  | zero => intro x h; omega
  | succ f ih =>
    intro x hf hx hU
    rcases Nat.lt_or_ge (3 * n) (4 * x) with hb | hb
    · -- past the bound: no hit, halt
      refine ⟨fun ⟨x', y, h1, h2, h3, _⟩ => by omega, fun _ => xs_halt n x hn hx hU hb⟩
    rcases Nat.lt_or_ge n (4 * x) with hp | hp
    · -- a y loop
      have hm : 2 ≤ n * x := Nat.le_trans hn (Nat.le_mul_of_pos_right n hx)
      have yl := yloop n (4 * x - n) (n * x) hn (by omega) (by omega) hm (2 * (n * x) + 3) 0 (by omega)
        (by omega)
      simp only [Nat.mul_zero] at yl
      have ihx := ih (x + 1) (by omega) (by omega) (by omega)
      have st := xs_y n x hn hx hp hb
      by_cases hhit : ∃ y, 0 < y ∧ n * x + 1 ≤ (4 * x - n) * y ∧ (4 * x - n) * y ≤ 2 * (n * x) + 2 ∧
          ((4 * x - n) * y - n * x) ∣ n * x * y
      · exact ⟨fun _ => Rch.tr st (yl.1 hhit), fun hno => absurd ⟨x, by
          obtain ⟨y, hy, h⟩ := hhit; exact ⟨y, Nat.le_refl _, hp, hb, hy, h⟩⟩ hno⟩
      · have nx := Rch.tr st (yl.2 hhit)
        rw [G_next n x hx hp] at nx
        refine ⟨fun ⟨x', y, h1, h2, h3, h4, h5⟩ => ?_, fun hno => ?_⟩
        · rcases Nat.lt_or_ge x x' with hl | hl
          · exact Rch.tr nx (ihx.1 ⟨x', y, hl, h2, h3, h4, h5⟩)
          · obtain rfl : x' = x := by omega
            exact absurd ⟨y, h4, h5⟩ hhit
        · exact HaltAt.back nx (ihx.2 (fun ⟨x', y, h1, h⟩ => hno ⟨x', y, by omega, h⟩))
    · -- debt
      have ihx := ih (x + 1) (by omega) (by omega) (by omega)
      have st := xs_debt n x hn hx hp
      refine ⟨fun ⟨x', y, h1, h2, h3, h4, h5⟩ => ?_, fun hno => ?_⟩
      · exact Rch.tr st (ihx.1 ⟨x', y, by omega, h2, h3, h4, h5⟩)
      · exact HaltAt.back st (ihx.2 (fun ⟨x', y, h1, h⟩ => hno ⟨x', y, by omega, h⟩))

/-! ## one `n` and the main theorem -/

/-- the x step of `x = 1` for `n` -/
def C (n : Nat) : Cfg St := G (Ld n 0) n 0

theorem Gx_one (n : Nat) : Gx n 1 = C n := by
  unfold Gx C
  rw [if_pos (by omega)]
  simp

/-- a hit for `n` -/
def Found (n : Nat) : Prop := ∃ x y, n < 4 * x ∧ 4 * x ≤ 3 * n ∧ 1 ≤ y ∧ Hit n x y

theorem reach1_of_ne {a b : Cfg St} (h : Rch a b) (hne : a ≠ b) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem ones_get (a : Nat) (s : Strm) (i : Nat) (h : i < a) : ones a s i = true := by
  induction a generalizing i with
  | zero => omega
  | succ a ih => cases i with
    | zero => rfl
    | succ i => exact ih i (by omega)

theorem ones_get_end (a : Nat) (s : Strm) : ones a s a = s 0 := by
  induction a with
  | zero => rfl
  | succ a ih => exact ih

theorem C_ne (n : Nat) : C n ≠ C (n + 1) := by
  intro e
  have := congrFun (congrArg Cfg.R e) (n + 1)
  simp only [C, G] at this
  rw [ones_get_end, ones_get _ _ _ (by omega)] at this
  exact Bool.false_ne_true this

theorem cycle (n : Nat) (hn : 2 ≤ n) :
    (Found n → Rch1 (C n) (C (n + 1))) ∧ (¬ Found n → HaltAt (C n)) := by
  have xl := xloop n hn (3 * n + 5) 1 (by omega) (Nat.le_refl _) (by omega)
  rw [Gx_one] at xl
  refine ⟨fun ⟨x, y, h⟩ => reach1_of_ne (xl.1 ⟨x, y, by omega, h⟩) (C_ne n),
    fun hno => xl.2 (fun ⟨x, y, _, h⟩ => hno ⟨x, y, h⟩)⟩

theorem start_reach : Rch start (C 2) := Rch.tr seed_reach (nstep_tail 1 1 (Nat.le_refl _) (by omega))

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

theorem found_iff {n : Nat} (hn : 1 ≤ n) :
    ¬ Found n ↔ ∀ x y z, 1 ≤ x → 1 ≤ y → 1 ≤ z → 4 * x * y * z ≠ n * (x * y + y * z + z * x) := by
  unfold Found
  rw [← solvable_iff hn]
  constructor
  · intro h x y z hx hy hz he; exact h ⟨x, y, z, hx, hy, hz, he⟩
  · rintro h ⟨x, y, z, hx, hy, hz, he⟩; exact h x y z hx hy hz he

/-- If some `n ≥ 2` has no solution, the machine reaches its explicit halting state. -/
theorem haltAt_of (h : ∃ n, 2 ≤ n ∧ ∀ x y z, 1 ≤ x → 1 ≤ y → 1 ≤ z →
    4 * x * y * z ≠ n * (x * y + y * z + z * x)) : HaltAt start := by
  obtain ⟨n, hn, hno⟩ := h
  have hF : ¬ Found n := (found_iff (by omega)).2 hno
  suffices H : ∀ k m, 2 ≤ m → m + k = n → HaltAt (C m) from
    HaltAt.back start_reach (H (n - 2) 2 (Nat.le_refl _) (by omega))
  intro k
  induction k with
  | zero => intro m hm h; obtain rfl : m = n := by omega
            exact (cycle m hm).2 hF
  | succ k ih =>
    intro m hm h
    by_cases hf : Found m
    · exact HaltAt.back ((cycle m hm).1 hf).reach (ih (m + 1) (by omega) (by omega))
    · exact (cycle m hm).2 hf

/-- **Main theorem.** Started on a blank tape, the design halts if and only if the
Erdős–Straus conjecture is false: some `n ≥ 2` has no `4/n = 1/x + 1/y + 1/z`. -/
theorem halts_iff : Halts delta start ↔
    ∃ n, 2 ≤ n ∧ ∀ x y z, 1 ≤ x → 1 ≤ y → 1 ≤ z → 4 * x * y * z ≠ n * (x * y + y * z + z * x) := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have all : ∀ m, 2 ≤ m → Found m := by
      intro m hm
      apply Classical.byContradiction
      intro hf
      exact hno ⟨m, hm, (found_iff (by omega)).1 hf⟩
    have prog : ∀ c, (∃ m, 2 ≤ m ∧ c = C m) → ∃ c', (∃ m, 2 ≤ m ∧ c' = C m) ∧ Rch1 c c' := by
      rintro c ⟨m, hm, rfl⟩
      exact ⟨C (m + 1), ⟨m + 1, by omega, rfl⟩, (cycle m hm).1 (all m hm)⟩
    exact not_halts_of_progress delta _ prog _ ⟨2, Nat.le_refl _, rfl⟩ (halts_det hH start_reach)
  · intro h; exact (haltAt_of h).halts

end TM.ErdosStraus
