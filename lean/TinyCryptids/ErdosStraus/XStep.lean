import TinyCryptids.Core.Lemmas
import TinyCryptids.ErdosStraus.Tac

/-!
# The x step on the tape

Tape (`F` = blank): `A 00 R 00 N 00 M 00 K`, then blank.

* `A` : `a + 1` cells; `R` : in the debt phase `2n + 3` cells with a hole at cell
  `2n + 1 - 2U`, after it `2n + 3 - a` cells; `N` : `n + 1` cells; `M` : `m + 1`; `K` : `m + 4`.

Left of `N` the tape is read from `R`'s last cell: `Ld n U` (debt) or `Lb n a`.
-/

namespace TM.ErdosStraus

open St

local notation "F" => false
local notation "T" => true

/-- `R` and `A` from `R`'s last cell, debt phase: the hole at cell `2n + 1 - 2U` -/
def Ld (n U : Nat) : Strm := ones (2 * U + 1) (F ::: ones (2 * n + 1 - 2 * U) (F ::: F ::: T ::: blank))

/-- `R` and `A` from `R`'s last cell, `a ≥ 1` -/
def Lb (n a : Nat) : Strm := ones (2 * n + 3 - a) (F ::: F ::: ones (a + 1) blank)

/-- the start of the x step: the head on `N`'s cell 0 -/
def G (Y : Strm) (n m : Nat) : Cfg St :=
  ⟨g6, F ::: F ::: Y, ones (n + 1) (F ::: F ::: ones (m + 1) (F ::: F ::: ones (m + 4) blank))⟩

/-- the N loop with the cursor on cell `c` (`c - 1` cells copied) -/
def CB (Y : Strm) (n m c : Nat) : Cfg St :=
  ⟨cb1, F ::: ones c (F ::: F ::: Y),
    ones (n - c) (F ::: F ::: ones (m + c) (F ::: F ::: ones (m + c + 3) blank))⟩

/-- after the N loop: on `N`'s last cell, going left -/
def QS (Y : Strm) (n m : Nat) : Cfg St :=
  cfgL q1 (ones (n + 1) (F ::: F ::: Y)) (F ::: F ::: ones (m + 1) (F ::: F ::: ones (m + 4) blank))

theorem g_start (Y : Strm) (n m : Nat) (hn : 1 ≤ n) : Rch (G Y n m) (CB Y n m 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold G CB
  gR; gR
  rw [show k + 1 - 1 = k by omega, show m + 1 + 3 = m + 4 by omega]
  fin

/-- one copy: `M` and `K` one cell longer; back to the cursor -/
theorem cb_step (Y : Strm) (n m c : Nat) (h1 : 1 ≤ c) (hc : c ≤ n) :
    Rch (CB Y n m c)
      (⟨ca1, ones c (F ::: F ::: Y), F ::: ones (n - c) (F ::: F ::: ones (m + c + 1)
        (F ::: F ::: ones (m + c + 4) blank))⟩) := by
  unfold CB
  sRn (n - c); gR; gR
  sRn (m + c); gR; gR
  rw [show m + c + 3 = (m + c + 2) + 1 by omega, ones_succ]
  gR
  sRn (m + c + 2)
  refine blankR ?_; gR; refine blankR ?_; gL
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  show Rch (cfgL CL1 (ones (m + c' + 1 + 3) (F ::: F ::: ones (m + c' + 1 + 1) (F ::: F :::
    ones (n - (c' + 1)) (F ::: T ::: ones c' (F ::: F ::: Y))))) (T ::: blank)) _
  sLn (m + c' + 1 + 3); gL; gL; sLn (m + c' + 1 + 1); gL; gL; sLn (n - (c' + 1)); gL; gR
  rw [show ones (m + c' + 1 + 3) (T ::: blank) = ones (m + c' + 1 + 4) blank by
    rw [← ones_succ']]
  fin

theorem cb_next (Y : Strm) (n m c : Nat) (h1 : 1 ≤ c) (hc : c < n) :
    Rch (CB Y n m c) (CB Y n m (c + 1)) := by
  refine Rch.tr (cb_step Y n m c h1 (by omega)) ?_
  obtain ⟨k, hk⟩ : ∃ k, n - c = k + 1 := ⟨n - c - 1, by omega⟩
  rw [hk]
  gR; gR
  unfold CB
  rw [show n - (c + 1) = k by omega, show m + (c + 1) = m + c + 1 by omega,
    show m + c + 1 + 3 = m + c + 4 by omega]
  fin

theorem cb_last (Y : Strm) (n m : Nat) (h1 : 1 ≤ n) : Rch (CB Y n m n) (QS Y n (m + n)) := by
  refine Rch.tr (cb_step Y n m n h1 (Nat.le_refl _)) ?_
  rw [Nat.sub_self]
  gR; gL
  unfold QS
  rw [show m + n + 1 + 3 = m + n + 4 by omega]
  fin

/-- the N loop: `M` and `K` grow by `n` -/
theorem nloop (Y : Strm) (n m : Nat) (h1 : 1 ≤ n) : Rch (G Y n m) (QS Y n (m + n)) := by
  refine Rch.tr (g_start Y n m h1) ?_
  suffices H : ∀ k c, c + k = n → 1 ≤ c → Rch (CB Y n m c) (QS Y n (m + n)) from H (n - 1) 1 (by omega) (Nat.le_refl _)
  intro k
  induction k with
  | zero => intro c h hc; obtain rfl : c = n := by omega
            exact cb_last Y c m hc
  | succ k ih => intro c h hc; exact Rch.tr (cb_next Y n m c hc (by omega)) (ih (c + 1) (by omega) (by omega))

/-! ## the four units of `U` -/

/-- debt, no crossing: the hole of `R` moves 8 cells left; back to `N`'s cell 0 -/
theorem debt_move (n U m : Nat) (h : U + 4 ≤ n) : Rch (QS (Ld n U) n m) (G (Ld n (U + 4)) n m) := by
  obtain ⟨j, hj⟩ : ∃ j, 2 * n + 1 - 2 * U = j + 9 := ⟨2 * n - 8 - 2 * U, by omega⟩
  unfold QS Ld
  rw [hj]
  sLn (n + 1); gL; gL; sLn (2 * U + 1); gL; gR; gL
  gL; gL; gL; gL; gL; gL; gL; gR
  show Rch ⟨gd1, F ::: ones (j + 1) (F ::: F ::: T ::: blank),
    ones 7 (T ::: ones (2 * U + 1) (F ::: F ::: ones (n + 1) (F ::: F ::: ones (m + 1)
      (F ::: F ::: ones (m + 4) blank))))⟩ _
  rw [← ones_succ', ones_add]
  sRn (7 + 1 + (2 * U + 1)); gR; gR
  unfold G
  rw [show 2 * n + 1 - 2 * (U + 4) = j + 1 by omega, show 2 * (U + 4) + 1 = 7 + 1 + (2 * U + 1) by omega]
  fin

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

/-- the state after the first of `s` separator moves -/
def sS : Nat → St | 1 => Z1 | 2 => S1 | 3 => S2 | _ => S3

/-- the separator moves after the first (`s - 1` more fills), then the two zeros -/
theorem sfill (s a r : Nat) (Z : Strm) (h1 : 1 ≤ s) (hs : s ≤ 4) (hr : s ≤ r) :
    Rch ⟨sS s, T ::: ones (a + 1) blank,
        F ::: ones r (F ::: F ::: Z)⟩
      ⟨H1, F ::: F ::: ones (a + s + 1) blank, ones (r - s) (F ::: F ::: Z)⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, r = s + k := ⟨r - s, by omega⟩
  rw [show s + k - s = k by omega]
  rcases (by omega : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4) with rfl | rfl | rfl | rfl
  · rw [show 1 + k = k + 1 by omega]; gR; gR; fin
  · rw [show 2 + k = k + 1 + 1 by omega]; gR; gR; gR; fin
  · rw [show 3 + k = k + 1 + 1 + 1 by omega]; gR; gR; gR; gR; fin
  · rw [show 4 + k = k + 1 + 1 + 1 + 1 by omega]; gR; gR; gR; gR; gR; fin

/-- four moves on an `R` of three cells: halt -/
theorem sfill_over (a : Nat) (Z : Strm) :
    HaltAt ⟨S3, T ::: ones (a + 1) blank, F ::: ones 3 (F ::: F ::: Z)⟩ :=
  ⟨_, _, by gR; gR; gR; gR; gR; fin⟩

/-- the check of `R`'s remaining cells -/
theorem hcheck (L Z : Strm) (r : Nat) :
    (3 ≤ r → Rch ⟨H1, L, ones r (F ::: F ::: Z)⟩ ⟨su1, ones 3 L, ones (r - 3) (F ::: F ::: Z)⟩) ∧
    (r < 3 → HaltAt ⟨H1, L, ones r (F ::: F ::: Z)⟩) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
    rw [show k + 3 - 3 = k by omega]; gR; gR; gR; fin
  · rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
    · exact ⟨_, _, by gR; fin⟩
    · exact ⟨_, _, by gR; gR; fin⟩
    · exact ⟨_, _, by gR; gR; gR; fin⟩

/-- a right step, also on the blank part of the tape -/
macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))

/-! ## the y loop's configuration -/

/-- `K 00 D 00 Z` for `W` units of the y counter (`m ≥ 1`): first lap (`W ≤ m + 1`) the hole of
`K` on cell `m + 2 - W`, `D = 11`; second lap the hole on cell 1, `K` has `2m + 5 - W` cells and
`D` has `W - m + 1` -/
def KD (m W : Nat) (Z : Strm) : Strm :=
  if W ≤ m + 1 then ones (m + 2 - W) (F ::: ones (W + 1) (F ::: F ::: T ::: T ::: F ::: F ::: Z))
  else T ::: F ::: ones (2 * m + 3 - W) (F ::: F ::: ones (W - m + 1) (F ::: F ::: Z))

/-- `N`, `R`, `A` from `N`'s last cell -/
def LN (n a : Nat) : Strm := ones (n + 1) (F ::: F ::: Lb n a)

/-- a y step starts: the `M` cursor on cell 1, `P` has `p + 1` cells -/
def YS (n a m W p : Nat) : Cfg St :=
  ⟨ce1, F ::: T ::: F ::: F ::: LN n a, ones (m - 1) (F ::: F ::: KD m W (ones (p + 1) blank))⟩

theorem KD_lap1 (m W : Nat) (Z : Strm) (h : W ≤ m + 1) :
    KD m W Z = ones (m + 2 - W) (F ::: ones (W + 1) (F ::: F ::: T ::: T ::: F ::: F ::: Z)) := by
  simp [KD, h]

theorem KD_lap2 (m W : Nat) (Z : Strm) (h : m + 1 ≤ W) :
    KD m W Z = T ::: F ::: ones (2 * m + 3 - W) (F ::: F ::: ones (W - m + 1) (F ::: F ::: Z)) := by
  rcases Nat.lt_or_ge (m + 1) W with h' | h'
  · simp [KD, show ¬ W ≤ m + 1 by omega]
  · obtain rfl : W = m + 1 := by omega
    simp only [KD, Nat.le_refl, if_true, show m + 2 - (m + 1) = 1 by omega,
      show 2 * m + 3 - (m + 1) = m + 1 + 1 by omega, show m + 1 - m + 1 = 2 by omega]
    rfl

/-- set up the y loop: to the end, the hole of `K` on its last-but-one cell, `D = 11`, `P = 1`;
then from the right to `M`'s cell 1 -/
theorem setup (n a m r : Nat) (hr : r + 3 = 2 * n + 3 - a) (hm : 1 ≤ m) :
    Rch ⟨su1, ones 3 (F ::: F ::: ones (a + 1) blank),
        ones r (F ::: F ::: ones (n + 1) (F ::: F ::: ones (m + 1) (F ::: F ::: ones (m + 4) blank)))⟩
      (YS n a m 0 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  sRn r; gR; gR; gR; sRn n; gR; gR; gR; sRn (k + 1); gR; gR; gR
  sRn (k + 4)
  refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gL
  gL; gL; gL; gR; gR; gR; gRb; gRb; gRb; gRb; gRb
  refine blankR ?_; gL
  gL; gL; gL; gL; gL; gL; gL; gL; gL
  rw [← ones_succ' (k + 1), ← ones_succ' (k + 1)]
  sLn (k + 1 + 1); gL; gL; sLn (k + 1 + 1); gR; gR; gR
  unfold YS LN Lb
  rw [KD_lap1 (k + 1) 0 _ (by omega), ← hr, ones_add r 3, show k + 1 - 1 = k by omega,
    show k + 1 + 2 - 0 = k + 2 + 1 by omega, ones_succ' (k + 2), ones_succ' n,
    show k + 1 + 1 = k + 2 by omega]
  fin

/-- after the debt phase: to the separator `A | R`, the first of the four moves -/
theorem b_start (n a m : Nat) :
    Rch (QS (Lb n a) n m) ⟨S3, T ::: ones (a + 1) blank, F ::: ones (2 * n + 3 - a)
      (F ::: F ::: ones (n + 1) (F ::: F ::: ones (m + 1) (F ::: F ::: ones (m + 4) blank)))⟩ := by
  unfold QS Lb
  sLn (n + 1); gL; gL; sLn (2 * n + 3 - a); gL; gR
  fin

theorem b_move (n a m : Nat) (h : a + 4 ≤ 2 * n) (hm : 1 ≤ m) :
    Rch (QS (Lb n a) n m) (YS n (a + 4) m 0 0) := by
  refine Rch.tr (b_start n a m) ?_
  refine Rch.tr (sfill 4 a (2 * n + 3 - a) _ (by omega) (by omega) (by omega)) ?_
  refine Rch.tr ((hcheck _ _ (2 * n + 3 - a - 4)).1 (by omega)) ?_
  exact setup n (a + 4) m _ (by omega) hm

theorem b_halt (n a m : Nat) (h1 : a ≤ 2 * n) (h2 : 2 * n < a + 4) : HaltAt (QS (Lb n a) n m) := by
  refine HaltAt.back (b_start n a m) ?_
  rcases Nat.lt_or_ge (2 * n + 3 - a) 4 with hr | hr
  · rw [show 2 * n + 3 - a = 3 by omega]; exact sfill_over a _
  · refine HaltAt.back (sfill 4 a (2 * n + 3 - a) _ (by omega) (by omega) hr) ?_
    exact (hcheck _ _ (2 * n + 3 - a - 4)).2 (by omega)

/-- the crossing: `U ≤ n < U + 4`, the hole falls off `R` at unit `n - U + 1`; the other units
are separator moves -/
theorem cross_move (n U m : Nat) (hU : U ≤ n) (hU' : n < U + 4) (hn : 2 ≤ n) (hm : 1 ≤ m) :
    Rch (QS (Ld n U) n m) (YS n (U + 4 - n) m 0 0) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = U + t := ⟨n - U, by omega⟩
  have fin4 : ∀ s, 1 ≤ s → s ≤ 4 → s = U + 4 - (U + t) →
      Rch ⟨sS s, T ::: ones 1 blank, F ::: ones (2 * (U + t) + 3) (F ::: F ::: ones (U + t + 1)
        (F ::: F ::: ones (m + 1) (F ::: F ::: ones (m + 4) blank)))⟩ (YS (U + t) (U + 4 - (U + t)) m 0 0) := by
    intro s h1 h4 hs
    refine Rch.tr (sfill s 0 _ _ h1 h4 (by omega)) ?_
    refine Rch.tr ((hcheck _ _ (2 * (U + t) + 3 - s)).1 (by omega)) ?_
    rw [show 0 + s + 1 = U + 4 - (U + t) + 1 by omega]
    exact setup (U + t) _ m _ (by omega) hm
  unfold QS Ld
  sLn (U + t + 1); gL; gL; sLn (2 * U + 1); gL
  rw [show 2 * (U + t) + 1 - 2 * U = 2 * t + 1 by omega]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
  · gR; gL; gL; gL; gR
    have := fin4 4 (by omega) (by omega) (by omega)
    rw [show 2 * (U + 0) + 3 = 1 + 1 + (2 * U + 1) by omega, ← ones_add, ← ones_add] at this
    exact this
  · gR; gL; gL; gL; gL; gL; gR
    have := fin4 3 (by omega) (by omega) (by omega)
    rw [show 2 * (U + 1) + 3 = 3 + 1 + (2 * U + 1) by omega, ← ones_add, ← ones_add] at this
    exact this
  · gR; gL; gL; gL; gL; gL; gL; gL; gR
    have := fin4 2 (by omega) (by omega) (by omega)
    rw [show 2 * (U + 2) + 3 = 5 + 1 + (2 * U + 1) by omega, ← ones_add, ← ones_add] at this
    exact this
  · gR; gL; gL; gL; gL; gL; gL; gL; gL; gL; gR
    have := fin4 1 (by omega) (by omega) (by omega)
    rw [show 2 * (U + 3) + 3 = 7 + 1 + (2 * U + 1) by omega, ← ones_add, ← ones_add] at this
    exact this

end TM.ErdosStraus
