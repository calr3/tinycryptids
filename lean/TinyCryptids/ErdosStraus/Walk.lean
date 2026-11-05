import TinyCryptids.Core.Routines
import TinyCryptids.ErdosStraus.YLoop

/-!
# The mod walk on `D 00 P` (`../OddPerfect/Round.lean`, the same states)

`D` has `d + 1` cells, its hole steps cyclically over cells `1 … d` (home: cell `d`); `P` has
`r + 2` cells and its hole counts the steps. The walk ends with `D`'s hole home iff
`d ∣ r + 1`. Here the setup does the walk's first step by hand: the walk starts at
`MW Y d r 1 1`.
-/

namespace TM.ErdosStraus

open St

local notation "F" => false
local notation "T" => true

theorem PPR : ParserR delta PR1 PR2 := by constructor <;> rfl
theorem PPM : ParserL delta PM1 PM2 := by constructor <;> rfl

/-- a right parser across `a` ones and three 0s: the third is the hole -/
theorem ParserR.find3 {p1 p2 : St} (P : ParserR delta p1 p2) (a : Nat) (L X : Strm) :
    Rch ⟨p1, L, ones a (F ::: F ::: F ::: true ::: X)⟩ ⟨p2, F ::: F ::: F ::: ones a L, true ::: X⟩ := by
  refine Rch.tr (scanR P.h1 a L _) ?_
  refine Rch.tr (stepR (δ := delta) (R := F ::: F ::: F ::: true ::: X) P.h0) ?_
  refine Rch.tr (stepR (δ := delta) (R := F ::: F ::: true ::: X) P.h2) ?_
  exact stepR (δ := delta) (R := F ::: true ::: X) P.h0

/-- a left parser across `a` ones and three 0s: the third is the hole -/
theorem ParserL.find3 {p1 p2 : St} (P : ParserL delta p1 p2) (a : Nat) (s R : Strm) :
    Rch (cfgL p1 (ones a (F ::: F ::: F ::: true ::: s)) R)
      (cfgL p2 (true ::: s) (F ::: F ::: F ::: ones a R)) := by
  refine Rch.tr (scanL P.h1 a _ R) ?_
  refine Rch.tr (stepL' (δ := delta) (s := F ::: F ::: F ::: true ::: s) P.h0) ?_
  refine Rch.tr (stepL' (δ := delta) (s := F ::: F ::: true ::: s) P.h2) ?_
  exact stepL' (δ := delta) (s := F ::: true ::: s) P.h0

/-- a right parser across `a` ones, a separator and `j` ones to a hole (`j = 0`: the hole
is next to the separator) -/
theorem ParserR.findS {p1 p2 : St} (P : ParserR delta p1 p2) (L X : Strm) (a j : Nat) :
    Rch ⟨p1, L, ones a (F ::: F ::: ones j (F ::: true ::: X))⟩
      ⟨p2, F ::: ones j (F ::: F ::: ones a L), true ::: X⟩ := by
  rcases j with _ | j
  · exact ParserR.find3 P a L X
  · exact P.find2 a j L X

/-- a left parser across `a` ones, a separator and `b` ones to a hole -/
theorem ParserL.findS {p1 p2 : St} (P : ParserL delta p1 p2) (s R : Strm) (a b : Nat) :
    Rch (cfgL p1 (ones a (F ::: F ::: ones b (F ::: true ::: s))) R)
      (cfgL p2 (true ::: s) (F ::: ones b (F ::: F ::: ones a R))) := by
  rcases b with _ | b
  · exact ParserL.find3 P a s R
  · exact P.find2 a b s R

/-- mod walk: about to advance the D hole (at cell `h`); the R hole is at cell `j` -/
def MW (Y : Strm) (d r h j : Nat) : Cfg St :=
  ⟨ma1, ones h (F ::: Y), F ::: ones (d - h) (F ::: F ::: ones j (F ::: ones (r + 1 - j) blank))⟩

/-- the walk is over: back on D's last cell (the home), D hole at cell `h`, R without hole -/
def E3 (Y : Strm) (d r h : Nat) : Cfg St :=
  cfgL e3 (ones (d - h) (F ::: ones h (F ::: Y))) (F ::: F ::: ones (r + 2) blank)

/-! ## mod walk -/

/-- advance the D hole: from cell `h` to cell `h % d + 1`, then the right parser starts -/
theorem dadv (Y Z : Strm) (d h : Nat) (h1 : 1 ≤ h) (hd : h ≤ d) :
    Rch ⟨ma1, ones h (F ::: Y), F ::: ones (d - h) (F ::: Z)⟩
      ⟨PR1, F ::: ones (h % d + 1) (F ::: Y), ones (d - (h % d + 1)) (F ::: Z)⟩ := by
  rcases Nat.lt_or_ge h d with hl | hl
  · obtain ⟨k, rfl⟩ : ∃ k, d = h + k + 1 := ⟨d - h - 1, by omega⟩
    rw [Nat.mod_eq_of_lt hl, show h + k + 1 - h = k + 1 by omega,
      show h + k + 1 - (h + 1) = k by omega]
    gR; gR; fin
  · obtain rfl : h = d := by omega
    obtain ⟨e, rfl⟩ : ∃ e, h = e + 1 := ⟨h - 1, by omega⟩
    rw [Nat.mod_self, Nat.sub_self, show e + 1 - (0 + 1) = e by omega]
    gR; gL
    show Rch (cfgL mw1 (ones (e + 2) (F ::: Y)) (F ::: Z)) _
    sLn (e + 2); gR; gR; gR
    fin

/-- one round of the walk, the R hole not at its last cell -/
theorem mw_step (Y : Strm) (d r h j : Nat) (h1 : 1 ≤ h) (hh : h ≤ d) (hj : j < r) :
    Rch (MW Y d r h j) (MW Y d r (h % d + 1) (j + 1)) := by
  obtain ⟨m, hm⟩ : ∃ m, r + 1 - j = m + 2 := ⟨r - 1 - j, by omega⟩
  have hh' : h % d + 1 ≤ d := Nat.mod_lt h (by omega)
  unfold MW
  rw [hm, show r + 1 - (j + 1) = m + 1 by omega]
  refine Rch.tr (dadv Y _ d h h1 hh) ?_
  refine Rch.tr (ParserR.findS PPR _ _ _ j) ?_
  gL; gR; gR; gL; gL
  rw [show ones j (F ::: F ::: ones (d - (h % d + 1)) (F ::: ones (h % d + 1) (F ::: Y))) =
    ones j (F ::: F ::: ones (d - (h % d + 1)) (F ::: true ::: ones (h % d) (F ::: Y))) from rfl]
  refine Rch.tr (ParserL.findS PPM _ _ (j + 1) _) ?_
  gR
  fin

theorem mod_succ' (x d : Nat) : (x % d + 1) % d = (x + 1) % d := by
  rw [Nat.add_mod x 1 d, Nat.add_mod (x % d) 1 d, Nat.mod_mod]

/-- the walk from the D hole on cell `h` and the P hole on cell `j0` -/
theorem mw_from (Y : Strm) (d r : Nat) (hd : 1 ≤ d) :
    ∀ k h j0, 1 ≤ h → h ≤ d → j0 + k ≤ r →
      Rch (MW Y d r h j0) (MW Y d r ((h + k - 1) % d + 1) (j0 + k))
  | 0, h, j0, h1, hh, _ => by
    rw [show h + 0 - 1 = h - 1 by omega, Nat.mod_eq_of_lt (by omega), show h - 1 + 1 = h by omega]; fin
  | k + 1, h, j0, h1, hh, hk => by
    refine Rch.tr (mw_step Y d r h j0 h1 hh (by omega)) ?_
    have := mw_from Y d r hd k (h % d + 1) (j0 + 1) (by omega) (Nat.mod_lt _ (by omega)) (by omega)
    have e : (h % d + 1 + k - 1) % d = (h + (k + 1) - 1) % d := by
      rw [show h % d + 1 + k - 1 = h % d + k by omega, show h + (k + 1) - 1 = h + k by omega,
        Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [e, show j0 + 1 + k = j0 + (k + 1) by omega] at this
    exact this

/-- the last round: the R hole falls off, back to D's last cell -/
theorem mw_last (Y : Strm) (d r h : Nat) (h1 : 1 ≤ h) (hh : h ≤ d) :
    Rch (MW Y d r h r) (E3 Y d r (h % d + 1)) := by
  have hh' : h % d + 1 ≤ d := Nat.mod_lt h (by omega)
  unfold MW E3
  rw [show r + 1 - r = 0 + 1 by omega]
  refine Rch.tr (dadv Y _ d h h1 hh) ?_
  refine Rch.tr (ParserR.findS PPR _ _ _ r) ?_
  gL; gR; gR; refine blankR ?_; gL
  show Rch (cfgL e1 (ones (r + 2) (F ::: F ::: ones (d - (h % d + 1)) (F ::: ones (h % d + 1) (F ::: Y))))
    (F ::: blank)) _
  sLn (r + 2); gL; gL
  rw [cons_blank]; fin

/-- the whole walk from `MW Y d r 1 1` (`r ≥ 1`): `D`'s hole ends on cell `r % d + 1` -/
theorem walk1 (Y : Strm) (d r : Nat) (hd : 1 ≤ d) (hr : 1 ≤ r) :
    Rch (MW Y d r 1 1) (E3 Y d r (r % d + 1)) := by
  refine Rch.tr (mw_from Y d r hd (r - 1) 1 1 (Nat.le_refl _) hd (by omega)) ?_
  have := mw_last Y d r ((1 + (r - 1) - 1) % d + 1) (by omega) (Nat.mod_lt _ (by omega))
  rw [mod_succ', show 1 + (r - 1) - 1 + 1 = r by omega] at this
  rw [show 1 + (r - 1) = r by omega]
  rw [show 1 + (r - 1) - 1 = r - 1 by omega] at this
  exact this

/-- left of `D` in the second lap: the separator, `K` (hole on cell 1), `M`, `N`, `R`, `A` -/
def KY (n a m e : Nat) : Strm := F ::: ones e (F ::: T ::: F ::: F ::: ones (m + 1) (F ::: F ::: LN n a))

/-- second lap after the units: the finder meets the hole on `K`'s cell 1; the walk's first
step by hand (`D`'s hole on cell 1, `P`'s on cell 1) -/
theorem test_setup (n a m e d p : Nat) (ha : a ≤ 2 * n) (hn : 2 ≤ n) (hm : 1 ≤ m) (hd : 1 ≤ d)
    (hp : 2 ≤ p) :
    Rch ⟨F1, F ::: F ::: ones (a + 1) blank, RR n a m (KD' 1 e (d + 1) (ones (p + 1) blank))⟩
      (MW (KY n a m e) d (p - 1) 1 1) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * n + 3 - a = r + 2 := ⟨2 * n + 1 - a, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  unfold RR KD'
  rw [hr]
  sRn (r + 2); gR; gR; gR; gR; sRn n'; gR; gR; gR; gR; sRn m'; gR; gR; gR; gR
  sRn e; gR; gR; gR; gR; sRn d'; gR; gR; gR; gR; gL; gL
  gL; gL; gL; sLn d'; gL; gR
  unfold MW KY LN Lb
  rw [show p' + 2 - 1 = p' + 1 by omega, show p' + 1 + 1 - 1 = p' + 1 by omega,
    show d' + 1 - 1 = d' by omega, hr, ← ones_succ' m', ← ones_succ' (m' + 1), ← ones_succ' n',
    ← ones_succ' (n' + 1)]
  fin

/-- not a divisor: fill `D`'s hole, back to `M`'s cell 1: the next y step -/
theorem test_fail (n a m e d r h : Nat) (hm : 1 ≤ m) (h1 : 1 ≤ h) (hh : h < d) :
    Rch (E3 (KY n a m e) d r h) (YP (LN n a) m 1 1 e (d + 1) (r + 1)) := by
  obtain ⟨k, hk⟩ : ∃ k, d - h = k + 1 := ⟨d - h - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold E3 KY
  rw [hk]
  gL; sLn k; gL; sLn h; gL; gL; sLn e; gL; gL; gL; gL; sLn (m' + 1 + 1); gR; gR; gR
  have eD : ∀ X : Strm, ones h (T ::: ones k (T ::: X)) = ones (d + 1) X := by
    intro X
    rw [← ones_succ' k, ← ones_succ' h, ones_add, show h + 1 + (k + 1) = d + 1 by omega]
  rw [eD]
  unfold YP KD'
  rw [show m' + 1 - 1 = m' by omega]
  fin

end TM.ErdosStraus
