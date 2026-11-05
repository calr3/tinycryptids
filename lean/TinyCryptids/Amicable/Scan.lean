import TinyCryptids.Core.Routines
import TinyCryptids.Amicable.Tac
import TinyCryptids.Amicable.Spec

/-!
# The scan of one number: `../OddPerfect`'s mod walk and shift, the left add

Tape (`F` = blank) during the scan of `x`:

    A 0 0 D 0 0 R 0 Z

* `D` : `d + 1` cells, the candidate `d`; during the mod walk its hole is at cell `h`,
  `1 ≤ h ≤ d`, its home is cell `d`;
* `R` : `r + 2` cells, `x = d + r + 1`; during the walk with a hole at cell `j ≤ r`;
* `A` (read leftwards from the cell three left of D) is the accumulator `ones b (F ::: W)`:
  each unit fills its hole and makes the next cell left (`W 0`) the hole: `ones (b + 1) (F ::: tl W)`;
* right of R: one blank, then `Z` (blank in pass 1, `0 N` in pass 2).

Configurations take the contents left of D's separator as a stream `Y` (here `F ::: A`).
-/

namespace TM.Amicable

open St TinyCryptids

local notation "F" => false
local notation "T" => true

theorem PPR : ParserR deltaNB PR1 PR2 := by constructor <;> rfl
theorem PPM : ParserL deltaNB PM1 PM2 := by constructor <;> rfl
theorem PPA : ParserR deltaNB PA1 PA2 := by constructor <;> rfl

/-- a right parser across `a` ones and three 0s: the third is the hole -/
theorem ParserR.find3 {p1 p2 : St} (P : ParserR deltaNB p1 p2) (a : Nat) (L X : Strm) :
    Rch ⟨p1, L, ones a (F ::: F ::: F ::: true ::: X)⟩ ⟨p2, F ::: F ::: F ::: ones a L, true ::: X⟩ := by
  refine Rch.tr (scanR P.h1 a L _) ?_
  refine Rch.tr (stepR (δ := deltaNB) (R := F ::: F ::: F ::: true ::: X) P.h0) ?_
  refine Rch.tr (stepR (δ := deltaNB) (R := F ::: F ::: true ::: X) P.h2) ?_
  exact stepR (δ := deltaNB) (R := F ::: true ::: X) P.h0

/-- a left parser across `a` ones and three 0s: the third is the hole -/
theorem ParserL.find3 {p1 p2 : St} (P : ParserL deltaNB p1 p2) (a : Nat) (s R : Strm) :
    Rch (cfgL p1 (ones a (F ::: F ::: F ::: true ::: s)) R)
      (cfgL p2 (true ::: s) (F ::: F ::: F ::: ones a R)) := by
  refine Rch.tr (scanL P.h1 a _ R) ?_
  refine Rch.tr (stepL' (δ := deltaNB) (s := F ::: F ::: F ::: true ::: s) P.h0) ?_
  refine Rch.tr (stepL' (δ := deltaNB) (s := F ::: F ::: true ::: s) P.h2) ?_
  exact stepL' (δ := deltaNB) (s := F ::: true ::: s) P.h0

/-- a right parser across `a` ones, a separator and `j` ones to a hole -/
theorem ParserR.findS {p1 p2 : St} (P : ParserR deltaNB p1 p2) (L X : Strm) (a j : Nat) :
    Rch ⟨p1, L, ones a (F ::: F ::: ones j (F ::: true ::: X))⟩
      ⟨p2, F ::: ones j (F ::: F ::: ones a L), true ::: X⟩ := by
  rcases j with _ | j
  · exact ParserR.find3 P a L X
  · exact P.find2 a j L X

/-- a left parser across `a` ones, a separator and `b` ones to a hole -/
theorem ParserL.findS {p1 p2 : St} (P : ParserL deltaNB p1 p2) (s R : Strm) (a b : Nat) :
    Rch (cfgL p1 (ones a (F ::: F ::: ones b (F ::: true ::: s))) R)
      (cfgL p2 (true ::: s) (F ::: ones b (F ::: F ::: ones a R))) := by
  rcases b with _ | b
  · exact ParserL.find3 P a s R
  · exact P.find2 a b s R

/-! ## configurations -/

/-- mod walk: about to advance the D hole (at cell `h`); the R hole is at cell `j` -/
def MW (Y Z : Strm) (d r h j : Nat) : Cfg St :=
  ⟨ma1, ones h (F ::: Y), F ::: ones (d - h) (F ::: F ::: ones j (F ::: ones (r + 1 - j) (F ::: Z)))⟩

/-- the walk is over: back on D's last cell (the home), D hole at cell `h`, R without hole -/
def E3 (Y Z : Strm) (d r h : Nat) : Cfg St :=
  cfgL e3 (ones (d - h) (F ::: ones h (F ::: Y))) (F ::: F ::: ones (r + 2) (F ::: Z))

/-- the shift starts on the first separator cell, D without hole to its left -/
def SEP (Y Z : Strm) (d r : Nat) : Cfg St :=
  ⟨f2, ones (d + 1) (F ::: Y), F ::: F ::: ones (r + 2) (F ::: Z)⟩

/-- the scan of `x` is over: D has `x` cells, then four 0s -/
def RE (Y Z : Strm) (x : Nat) : Cfg St := ⟨f6, F ::: F ::: F ::: F ::: ones x (F ::: Y), F ::: Z⟩

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
theorem mw_step (Y Z : Strm) (d r h j : Nat) (h1 : 1 ≤ h) (hh : h ≤ d) (hj : j < r) :
    Rch (MW Y Z d r h j) (MW Y Z d r (h % d + 1) (j + 1)) := by
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

/-- the walk after `j` of its `r + 1` rounds, from the D hole home and the R hole at cell 0 -/
theorem mw_upto (Y Z : Strm) (d r : Nat) (hd : 1 ≤ d) :
    ∀ j, j ≤ r → Rch (MW Y Z d r d 0) (MW Y Z d r ((d + j - 1) % d + 1) j)
  | 0, _ => by
    rw [show d + 0 - 1 = d - 1 by omega, Nat.mod_eq_of_lt (by omega), show d - 1 + 1 = d by omega]; fin
  | j + 1, hj => by
    refine Rch.tr (mw_upto Y Z d r hd j (by omega)) ?_
    have := mw_step Y Z d r ((d + j - 1) % d + 1) j (by omega) (Nat.mod_lt _ (by omega)) (by omega)
    rw [mod_succ', show d + j - 1 + 1 = d + (j + 1) - 1 by omega] at this
    exact this

/-- the last round: the R hole falls off, back to D's last cell -/
theorem mw_last (Y Z : Strm) (d r h : Nat) (h1 : 1 ≤ h) (hh : h ≤ d) :
    Rch (MW Y Z d r h r) (E3 Y Z d r (h % d + 1)) := by
  have hh' : h % d + 1 ≤ d := Nat.mod_lt h (by omega)
  unfold MW E3
  rw [show r + 1 - r = 0 + 1 by omega]
  refine Rch.tr (dadv Y _ d h h1 hh) ?_
  refine Rch.tr (ParserR.findS PPR _ _ _ r) ?_
  gL; gR; gR; gL
  show Rch (cfgL e1 (ones (r + 2) (F ::: F ::: ones (d - (h % d + 1)) (F ::: ones (h % d + 1) (F ::: Y))))
    (F ::: Z)) _
  sLn (r + 2); gL; gL
  fin

/-- the whole walk: `r + 1` rounds; the D hole ends at cell `r % d + 1` (home iff `d ∣ r + 1`) -/
theorem walk (Y Z : Strm) (d r : Nat) (hd : 1 ≤ d) :
    Rch (MW Y Z d r d 0) (E3 Y Z d r (r % d + 1)) := by
  refine Rch.tr (mw_upto Y Z d r hd r (Nat.le_refl _)) ?_
  have := mw_last Y Z d r ((d + r - 1) % d + 1) (by omega) (Nat.mod_lt _ (by omega))
  rw [mod_succ', show d + r - 1 + 1 = d + r by omega, Nat.add_mod_left] at this
  exact this

/-! ## the shift -/

/-- the first separator cell becomes D's new home, R loses its cell 0 and gets its hole at its
new cell 0; then the walk for `d + 1` -/
theorem shift (Y Z : Strm) (d r : Nat) : Rch (SEP Y Z d (r + 1)) (MW Y Z (d + 1) r (d + 1) 0) := by
  unfold SEP MW
  gR; gR; gR; gR; gL
  show Rch (cfgL PM2 (F ::: F ::: F ::: F ::: ones (d + 1) (F ::: Y)) _) _
  gL; gL; gL; gL; gR
  rw [Nat.sub_self, Nat.sub_zero]
  fin

/-- the same with R of two cells: `r` becomes 0 and the scan is over -/
theorem shift_end (Y Z : Strm) (d : Nat) : Rch (SEP Y Z d 0) (RE Y Z (d + 1)) := by
  unfold SEP RE
  gR; gR; gR; gR
  fin

/-- the D hole is not home: fill it, then to the separator -/
theorem fill_hole (Y Z : Strm) (d r h : Nat) (hh : h < d) : Rch (E3 Y Z d r h) (SEP Y Z d r) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = h + k + 1 := ⟨d - h - 1, by omega⟩
  unfold E3 SEP
  rw [show h + k + 1 - h = k + 1 by omega]
  gL
  show Rch (cfgL f1 (ones k (F ::: ones h (F ::: Y))) _) _
  sLn k; gR
  rw [← ones_succ']
  sRn (k + 1)
  show Rch ⟨f2, ones (k + 1) (ones (h + 1) (F ::: Y)), _⟩ _
  rw [ones_add, show k + 1 + (h + 1) = h + k + 1 + 1 by omega]
  fin

/-! ## the add: `d` units into the accumulator left of D -/

/-- `k` cells dropped from the front of a stream -/
def tln : Nat → Strm → Strm
  | 0, V => V
  | k + 1, V => tln k (tl V)

/-- the accumulator `[1^a] hole [1^b]`, read leftwards from its right end; with `a = 0` the hole
is the blank beyond it -/
def ACC (a b : Nat) : Strm := ones b (F ::: ones a blank)

theorem tln_ones (a : Nat) : ∀ k, tln k (ones a blank) = ones (a - k) blank
  | 0 => by rw [Nat.sub_zero]; rfl
  | k + 1 => by
    show tln k (tl (ones a blank)) = _
    rcases a with _ | a
    · have : tl (ones 0 blank) = ones 0 blank := rfl
      rw [this, tln_ones 0 k, Nat.zero_sub, Nat.zero_sub]
    · have : tl (ones (a + 1) blank) = ones a blank := rfl
      rw [this, tln_ones a k, show a + 1 - (k + 1) = a - k by omega]

/-- adding: the D hole at cell `c` (moving down), the head on it, `Q` right of D -/
def AD (A : Strm) (d c : Nat) (Q : Strm) : Cfg St :=
  cfgL a1 (F ::: ones c (F ::: F ::: A)) (ones (d - c) Q)

theorem w_step (s R : Strm) : Rch (cfgL W s R) ⟨PA1, F ::: tl s, R⟩ := by
  unfold cfgL
  cases h : s 0
  · exact sR (by rfl)
  · exact sR (by rfl)

/-- one unit: from the new D hole (cell `c`) left to the accumulator's hole (two 0s, then
`b` ones), fill it, the next cell becomes the hole, back to the D hole -/
theorem add_unit (b c k : Nat) (V Q : Strm) :
    Rch (cfgL Z1 (ones c (F ::: F ::: ones b (F ::: V))) (F ::: ones (k + 1) Q))
      (AD (ones (b + 1) (F ::: tl V)) (c + k + 1) c Q) := by
  sLn c; gL; gL
  show Rch (cfgL Z3 (ones b (F ::: V)) _) _
  sLn b; gL
  refine Rch.tr (w_step _ _) ?_
  show Rch ⟨PA1, F ::: tl V, ones (b + 1) (F ::: F ::: ones c (F ::: T ::: ones k Q))⟩ _
  refine Rch.tr (ParserR.findS PPA _ _ (b + 1) c) ?_
  gL
  unfold AD
  rw [show c + k + 1 - c = k + 1 by omega]
  fin

/-- the D hole one cell down, and one unit -/
theorem add_step (b d c : Nat) (V Q : Strm) (hc : c + 1 ≤ d) :
    Rch (AD (ones b (F ::: V)) d (c + 1) Q) (AD (ones (b + 1) (F ::: tl V)) d c Q) := by
  unfold AD
  gL; gL
  have := add_unit b c (d - c - 1) V Q
  rw [show c + (d - c - 1) + 1 = d by omega] at this
  rw [show d - (c + 1) = d - c - 1 by omega]
  exact this

/-- all units: the D hole from cell `c` down to cell 0 -/
theorem add_all (d : Nat) (Q : Strm) :
    ∀ c b V, c ≤ d → Rch (AD (ones b (F ::: V)) d c Q) (AD (ones (b + c) (F ::: tln c V)) d 0 Q)
  | 0, b, V, _ => by fin
  | c + 1, b, V, hc => by
    refine Rch.tr (add_step b d c V Q (by omega)) ?_
    have := add_all d Q c (b + 1) (tl V) (by omega)
    rw [show b + 1 + c = b + (c + 1) by omega] at this
    exact this

/-- the D hole falls off cell 0: D without hole, on to its right end -/
theorem add_end (A Q : Strm) (d : Nat) : Rch (AD A d 0 Q) ⟨f2, ones (d + 1) (F ::: F ::: A), Q⟩ := by
  unfold AD
  gL; gR
  rw [Nat.sub_zero, show T ::: ones d Q = ones (d + 1) Q from rfl]
  sRn (d + 1)
  fin

/-- the add from `a2` on D's cell `c` (D's cells `0 … c` and `k` more ones after the head's
right neighbour): `c + 1` units, then on to the end of D -/
theorem add_from (b c k : Nat) (V Q : Strm) :
    Rch (cfgL a2 (ones (c + 1) (F ::: F ::: ones b (F ::: V))) (T ::: ones k Q))
      ⟨f2, ones (c + k + 2) (F ::: F ::: ones (b + c + 1) (F ::: tln (c + 1) V)), Q⟩ := by
  gL
  refine Rch.tr (add_unit b c k V Q) ?_
  refine Rch.tr (add_all (c + k + 1) Q c (b + 1) (tl V) (by omega)) ?_
  refine Rch.tr (add_end _ Q (c + k + 1)) ?_
  rw [show b + 1 + c = b + c + 1 by omega]
  fin

/-- `d` divides: `d` units into the accumulator, then on to the separator -/
theorem add (a b d r : Nat) (Z : Strm) (hd : 1 ≤ d) :
    Rch (E3 (F ::: ACC a b) Z d r d) (SEP (F ::: ACC (a - d) (b + d)) Z d r) := by
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  unfold E3
  rw [Nat.sub_self]
  gL
  have := add_from b c 0 (ones a blank) (F ::: F ::: ones (r + 2) (F ::: Z))
  rw [tln_ones] at this
  exact this

/-- test `d` (`x = d + r + 1`): the walk, then if `d ∣ x` add `d`; on to the separator -/
theorem dstep (a b d r : Nat) (Z : Strm) (hd : 1 ≤ d) :
    Rch (MW (F ::: ACC a b) Z d r d 0)
      (SEP (F ::: ACC (a - (if (r + 1) % d = 0 then d else 0))
        (b + (if (r + 1) % d = 0 then d else 0))) Z d r) := by
  refine Rch.tr (walk _ _ d r hd) ?_
  have ms := mod_succ r d
  have hlt := Nat.mod_lt r (show d > 0 by omega)
  by_cases hw : r % d + 1 < d
  · rw [if_neg (by rw [ms.1 hw]; omega), Nat.sub_zero, Nat.add_zero]
    exact fill_hole _ _ d r _ hw
  · have h2 : r % d + 1 = d := by omega
    rw [if_pos (ms.2 h2), h2]
    exact add a b d r Z hd

/-- the scan of `x` from the candidate `d`: every proper divisor `≥ d` is added -/
theorem scan_from (x a b : Nat) (Z : Strm) :
    ∀ r d, x = d + r + 1 → 1 ≤ d →
      Rch (MW (F ::: ACC (a - divSumBelow x (d - 1)) (b + divSumBelow x (d - 1))) Z d r d 0)
        (RE (F ::: ACC (a - properDivSum x) (b + properDivSum x)) Z x)
  | r, d, hx, hd => by
    refine Rch.tr (dstep _ _ d r Z hd) ?_
    have st := divSumBelow_step x d hd (by omega)
    rw [show x - d = r + 1 by omega] at st
    rw [Nat.sub_sub, Nat.add_assoc, st]
    rcases r with _ | r
    · refine Rch.tr (shift_end _ Z d) ?_
      rw [properDivSum_eq x (by omega), show x - 1 = d by omega, show d + 1 = x by omega]
      fin
    · refine Rch.tr (shift _ Z d r) ?_
      have := scan_from x a b Z r (d + 1) (by omega) (by omega)
      rw [Nat.add_sub_cancel] at this
      exact this

/-- the whole scan of `x ≥ 2`: `properDivSum x` units into the accumulator -/
theorem scan (x a b : Nat) (Z : Strm) (hx : 2 ≤ x) :
    Rch (MW (F ::: ACC a b) Z 1 (x - 2) 1 0)
      (RE (F ::: ACC (a - properDivSum x) (b + properDivSum x)) Z x) := by
  have := scan_from x a b Z (x - 2) 1 (by omega) (Nat.le_refl _)
  simpa [divSumBelow] using this

end TM.Amicable
