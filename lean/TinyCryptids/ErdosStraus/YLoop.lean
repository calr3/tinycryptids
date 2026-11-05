import TinyCryptids.ErdosStraus.XStep

/-!
# The y loop on the tape

`K 00 D 00 P` is `KD' c e d (ones (p + 1) blank)`: `K` has `c + e + 1` cells with its hole on
cell `c`, `D` has `d` cells, `P` has `p + 1`. In the first lap a unit moves the hole one cell
left (`c - 1`, `e + 1`); in the second (`c = 1`) it moves the separator `K | D` one cell left
(`e - 1`, `d + 1`), and with `e = 1` (`K = 1 0 1`) the y loop is over.
-/

namespace TM.ErdosStraus

open St

local notation "F" => false
local notation "T" => true

def KD' (c e d : Nat) (Z : Strm) : Strm := ones c (F ::: ones e (F ::: F ::: ones d (F ::: F ::: Z)))

def kc (m W : Nat) : Nat := if W ≤ m + 1 then m + 2 - W else 1
def ke (m W : Nat) : Nat := if W ≤ m + 1 then W + 1 else 2 * m + 3 - W
def kd (m W : Nat) : Nat := if W ≤ m + 1 then 2 else W - m + 1

theorem KD_eq (m W : Nat) (Z : Strm) : KD m W Z = KD' (kc m W) (ke m W) (kd m W) Z := by
  unfold KD KD' kc ke kd
  by_cases h : W ≤ m + 1
  · simp only [h, if_true]; rfl
  · simp only [h, if_false]; rfl

/-- `P += M` with the `M` cursor on cell `j` (`X`: `N`, `R`, `A` from `N`'s last cell) -/
def YP (X : Strm) (m j c e d p : Nat) : Cfg St :=
  ⟨ce1, F ::: ones j (F ::: F ::: X), ones (m - j) (F ::: F ::: KD' c e d (ones (p + 1) blank))⟩

/-- one cell onto `P`'s end, back to the `M` cursor -/
theorem pm_step (X : Strm) (m j c e d p : Nat) (h1 : 1 ≤ j) (hj : j ≤ m) (hc : 1 ≤ c) (he : 1 ≤ e)
    (hd : 1 ≤ d) :
    Rch (YP X m j c e d p)
      ⟨mc1, ones j (F ::: F ::: X), F ::: ones (m - j) (F ::: F ::: KD' c e d (ones (p + 2) blank))⟩ := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  unfold YP KD'
  sRn (m - j); gR; gR; gR; sRn c'; gR; gR; sRn e'; gR; gR; gR; sRn d'; gR; gR; gR; sRn p
  refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gL; gL; gL
  rw [← ones_succ' p, ← ones_succ' d', ← ones_succ' e', ← ones_succ' c']
  sLn (p + 1); gL; gL; sLn (d' + 1); gL; gL; sLn (e' + 1); gL; gL; sLn c'; gL; gL; sLn (m - j)
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  gL; gR
  rw [show ones (p + 1) (T ::: F ::: F ::: blank) = ones (p + 2) blank by
    rw [← ones_succ' (p + 1)]; simp only [cons_blank]]
  rw [← ones_succ' c']
  fin

theorem pm_next (X : Strm) (m j c e d p : Nat) (h1 : 1 ≤ j) (hj : j < m) (hc : 1 ≤ c) (he : 1 ≤ e)
    (hd : 1 ≤ d) : Rch (YP X m j c e d p) (YP X m (j + 1) c e d (p + 1)) := by
  refine Rch.tr (pm_step X m j c e d p h1 (by omega) hc he hd) ?_
  obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
  rw [hk]
  gR; gR
  unfold YP
  rw [show m - (j + 1) = k by omega]
  fin

/-- `P += M` is done: on `M`'s last cell, going left -/
def UL (X : Strm) (m c e d p : Nat) : Cfg St :=
  cfgL u1 (ones (m + 1) (F ::: F ::: X)) (F ::: F ::: KD' c e d (ones (p + 1) blank))

theorem pm_last (X : Strm) (m c e d p : Nat) (h1 : 1 ≤ m) (hc : 1 ≤ c) (he : 1 ≤ e) (hd : 1 ≤ d) :
    Rch (YP X m m c e d p) (UL X m c e d (p + 1)) := by
  refine Rch.tr (pm_step X m m c e d p h1 (Nat.le_refl _) hc he hd) ?_
  rw [Nat.sub_self]
  gR; gL
  fin

/-- `P += M` -/
theorem pmloop (X : Strm) (m c e d p : Nat) (h1 : 1 ≤ m) (hc : 1 ≤ c) (he : 1 ≤ e) (hd : 1 ≤ d) :
    Rch (YP X m 1 c e d p) (UL X m c e d (p + m)) := by
  suffices H : ∀ k j q, j + k = m → 1 ≤ j → q + 1 = p + j →
      Rch (YP X m j c e d q) (UL X m c e d (p + m)) from H (m - 1) 1 p (by omega) (Nat.le_refl _) rfl
  intro k
  induction k with
  | zero =>
    intro j q h hj hq; obtain rfl : j = m := by omega
    have := pm_last X j c e d q h1 hc he hd
    rw [show q + 1 = p + j by omega] at this; exact this
  | succ k ih =>
    intro j q h hj hq
    exact Rch.tr (pm_next X m j c e d q hj (by omega) hc he hd) (ih (j + 1) (q + 1) (by omega) (by omega) (by omega))

/-! ## the consume loop: `W += a` -/

/-- right of `A`: `R`, `N`, `M` and `Z` (`K 00 D 00 P`) -/
def RR (n a m : Nat) (Z : Strm) : Strm :=
  ones (2 * n + 3 - a) (F ::: F ::: ones (n + 1) (F ::: F ::: ones (m + 1) (F ::: F ::: Z)))

/-- a unit starts: the `A` cursor on cell `i`, the head right of it -/
def CU (a i : Nat) (Z : Strm) : Cfg St := ⟨f1, F ::: ones i blank, ones (a - i) (F ::: F ::: Z)⟩

theorem blankL {q : St} {R : Strm} {X : Cfg St} (h : Rch (cfgL q (F ::: blank) R) X) :
    Rch (cfgL q blank R) X := h

theorem consume_start (n a m c e d p : Nat) (ha : 1 ≤ a) (h2 : a ≤ 2 * n) :
    Rch (UL (LN n a) m c e d p) (CU a 1 (RR n a m (KD' c e d (ones (p + 1) blank)))) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * n + 3 - a = r + 1 := ⟨2 * n + 2 - a, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  unfold UL LN Lb CU RR
  rw [hr]
  sLn (m + 1); gL; gL; gL; sLn n; gL; gL; gL; sLn r; gL; gL; gL; sLn (a' + 1)
  refine blankL ?_; gL; refine blankL ?_; gL
  show Rch ⟨u3, blank, F ::: _⟩ _
  rw [← ones_succ' (a' + 1)]
  gR; gR; gR; gR; gR
  rw [show a' + 1 - 1 = a' by omega, ← ones_succ' r, ← ones_succ' n]
  simp only [cons_blank]
  fin

/-- a unit is done: back on the `A` cursor -/
def AC (a i : Nat) (Z : Strm) : Cfg St := ⟨ac1, ones i blank, F ::: ones (a - i) (F ::: F ::: Z)⟩

/-- first lap: the hole of `K` one cell left -/
theorem unit1 (n a m i c e d : Nat) (P : Strm) (hi : 1 ≤ i) (hia : i ≤ a) (ha : a ≤ 2 * n)
    (hn : 2 ≤ n) (hm : 1 ≤ m) (hc : 2 ≤ c) (he : 1 ≤ e) :
    Rch (CU a i (RR n a m (KD' c e d P))) (AC a i (RR n a m (KD' (c - 1) (e + 1) d P))) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * n + 3 - a = r + 2 := ⟨2 * n + 1 - a, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  unfold CU AC RR KD'
  rw [hr]
  sRn (a - i); gR; gR; gR; gR; sRn r; gR; gR; gR; gR; sRn n'; gR; gR; gR; gR; sRn m'
  gR; gR; gR; gR; sRn c'; gR; gL; gL
  rw [← ones_succ' c', ← ones_succ' (c' + 1), ← ones_succ' m', ← ones_succ' (m' + 1), ← ones_succ' n',
    ← ones_succ' (n' + 1), ← ones_succ' r, ← ones_succ' (r + 1)]
  gL
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  sLn (c' + 1); gL; gL; sLn (m' + 1 + 1); gL; gL; sLn (n' + 1 + 1); gL; gL; sLn (r + 1 + 1); gL; gL
  sLn (a - (i' + 1)); gL; gR
  rw [show c' + 2 - 1 = c' + 1 by omega]
  fin

/-- left of `K`'s cell 2 in the second lap: `K`'s cells 1, 0, then `M`, `N`, `R`, `A` with its
cursor on cell `i` -/
def KL (n a m i : Nat) : Strm :=
  F ::: T ::: F ::: F ::: ones (m + 1) (F ::: F ::: ones (n + 1) (F ::: F ::: ones (2 * n + 3 - a)
    (F ::: F ::: ones (a - i) (F ::: ones i blank))))

/-- second lap: the finder meets the hole on `K`'s cell 1 -/
theorem lap2_find (n a m i e d : Nat) (P : Strm) (hia : i ≤ a) (ha : a ≤ 2 * n)
    (hn : 2 ≤ n) (hm : 1 ≤ m) :
    Rch (CU a i (RR n a m (KD' 1 e d P))) ⟨l1, KL n a m i, ones e (F ::: F ::: ones d (F ::: F ::: P))⟩ := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * n + 3 - a = r + 2 := ⟨2 * n + 1 - a, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold CU RR KD' KL
  rw [hr]
  sRn (a - i); gR; gR; gR; gR; sRn r; gR; gR; gR; gR; sRn n'; gR; gR; gR; gR; sRn m'
  gR; gR; gR; gR
  rw [← ones_succ' m', ← ones_succ' (m' + 1), ← ones_succ' n', ← ones_succ' (n' + 1), ← ones_succ' r,
    ← ones_succ' (r + 1)]
  fin

/-- second lap: the separator `K | D` one cell left -/
theorem unit2 (n a m i e d : Nat) (P : Strm) (hi : 1 ≤ i) (hia : i ≤ a) (ha : a ≤ 2 * n)
    (hn : 2 ≤ n) (hm : 1 ≤ m) (he : 2 ≤ e) :
    Rch (CU a i (RR n a m (KD' 1 e d P))) (AC a i (RR n a m (KD' 1 (e - 1) (d + 1) P))) := by
  refine Rch.tr (lap2_find n a m i e d P hia ha hn hm) ?_
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
  sRn (e' + 2); gL; gL; gR; gR; gR; gL
  show Rch (cfgL AK1 (F ::: F ::: ones (e' + 1) (KL n a m i)) (T ::: ones d (F ::: F ::: P))) _
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  unfold KL
  gL; gL; sLn (e' + 1); gL; gL; gL; gL; sLn (m + 1); gL; gL; sLn (n + 1); gL; gL; sLn (2 * n + 3 - a)
  gL; gL; sLn (a - (i' + 1)); gL; gR
  unfold AC RR KD'
  rw [show e' + 2 - 1 = e' + 1 by omega]
  fin

/-- `K = 1 0 1`: the y loop is over. `K := K 00 D` less four cells, `P` erased, the `A`
cursor filled; on to `N`'s cell 0 for the next x -/
theorem stop (n a m i p : Nat) (hi : 1 ≤ i) (hia : i ≤ a) (ha : a ≤ 2 * n) (hn : 2 ≤ n) (hm : 1 ≤ m) :
    Rch (CU a i (RR n a m (KD' 1 1 (m + 3) (ones (p + 1) blank)))) (G (Lb n a) n m) := by
  refine Rch.tr (lap2_find n a m i 1 (m + 3) _ hia ha hn hm) ?_
  gR; gL; gL; gR; gR; gR; gR
  sRn (m + 3); gR; gR
  refine Rch.tr (eraseR (δ := delta) (q := x6) rfl (p + 1) _ _) ?_
  refine blankR ?_; gL
  show Rch (cfgL x7 (F ::: zeros p (F ::: F ::: ones (m + 3) (T ::: T ::: T ::: T ::: tl (KL n a m i))))
    (F ::: blank)) _
  rw [zeros_cons_false, zeros_cons_false]
  gL; gL; gL; zLn p
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [show m' + 1 + 3 = m' + 4 from rfl]
  gL; gL; gL; gL
  unfold KL
  simp only [cons_blank, zeros_blank, tl_cons]
  rw [← ones_succ' m', ← ones_succ' (m' + 1), ← ones_succ' (m' + 1 + 1), ← ones_succ' (m' + 1 + 1 + 1),
    ← ones_succ' (m' + 1 + 1 + 1 + 1)]
  sLn (m' + 1 + 1 + 1 + 1 + 1); gL; gL; sLn (m' + 2); gL; gL; sLn (n + 1); gL; gL; sLn (2 * n + 3 - a); gL; gL
  sLn (a - (i' + 1)); gL; gR; gR
  sRn (a - (i' + 1)); gR; gR; sRn (2 * n + 3 - a); gR; gR
  unfold G Lb
  rw [show (T ::: T ::: tl (ones (i' + 1) blank)) = ones (i' + 2) blank from rfl, ones_add,
    show a - (i' + 1) + (i' + 2) = a + 1 by omega]
  fin

theorem ac_next (a i : Nat) (Z : Strm) (hi : i < a) : Rch (AC a i Z) (CU a (i + 1) Z) := by
  obtain ⟨k, hk⟩ : ∃ k, a - i = k + 1 := ⟨a - i - 1, by omega⟩
  unfold AC CU
  rw [hk, show a - (i + 1) = k by omega]
  gR; gR; fin

/-- all units done: the finder starts on `R`'s cell 0 -/
theorem ac_last (a : Nat) (Z : Strm) : Rch (AC a a Z) ⟨F1, F ::: F ::: ones (a + 1) blank, Z⟩ := by
  unfold AC
  rw [Nat.sub_self]
  gR; gR; gR; fin

/-- first lap: the next y step (`P += M` from `M`'s cell 1) -/
theorem lap1_next (n a m c e d p : Nat) (ha : a ≤ 2 * n) (hn : 2 ≤ n) (hm : 1 ≤ m) (hc : 2 ≤ c)
    (he : 1 ≤ e) :
    Rch ⟨F1, F ::: F ::: ones (a + 1) blank, RR n a m (KD' c e d (ones (p + 1) blank))⟩
      (YP (LN n a) m 1 c e d p) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * n + 3 - a = r + 2 := ⟨2 * n + 1 - a, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  unfold RR KD' YP LN Lb
  rw [hr]
  sRn (r + 2); gR; gR; gR; gR; sRn n'; gR; gR; gR; gR; sRn m'; gR; gR; gR; gR; sRn c'; gR; gL; gL
  rw [← ones_succ' c', ← ones_succ' (c' + 1), ← ones_succ' m', ← ones_succ' (m' + 1), ← ones_succ' n',
    ← ones_succ' (n' + 1)]
  gL; sLn (c' + 1); gL; gL; sLn (m' + 1 + 1); gR; gR; gR
  rw [show m' + 1 - 1 = m' by omega, ← ones_succ' (c' + 1)]
  unfold KD'
  fin

end TM.ErdosStraus
