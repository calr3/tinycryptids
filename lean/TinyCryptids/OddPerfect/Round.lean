import TinyCryptids.Core.Routines
import TinyCryptids.OddPerfect.Tac
import TinyCryptids.OddPerfect.Spec

/-!
# One round on the tape

Tape (`F` = blank):

    T 00 D 00 R

* `T` : `L + 1` cells (cells `0 … L`, `L = n + 2` in the round for `n`), a hole at cell
  `u + 1`, `u ≤ L - 1`: the counter `u`.  Seen from its right end it is `TX L u`.
* `D` : `d + 1` cells (cells `0 … d`), the candidate `d`; during the mod walk its hole is at
  cell `h`, `1 ≤ h ≤ d`, and its home is cell `d`, the last one (as in `../Sierpinski`);
* `R` : `r + 2` cells, `n = d + r + 1`; during the walk with a hole at cell `j ≤ r`.

Configurations take the contents left of D's separator as a stream `Y`; in a round it is
`F ::: TX L u` (the other separator cell, then T).
-/

namespace TM.OddPerfect

open St

local notation "F" => false

theorem PPR : ParserR delta PR1 PR2 := by constructor <;> rfl
theorem PPM : ParserL delta PM1 PM2 := by constructor <;> rfl
theorem PPT : ParserL delta PT1 PT2 := by constructor <;> rfl
theorem PPA : ParserR delta PA1 PA2 := by constructor <;> rfl
theorem PPC : ParserL delta PC1 PC2 := by constructor <;> rfl
theorem PPZ : ParserR delta PZ1 PZ2 := by constructor <;> rfl

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

/-! ## configurations -/

/-- T seen from its right end: `L + 1` cells, the hole at cell `u + 1` -/
def TX (L u : Nat) : Strm := ones (L - 1 - u) (F ::: ones (u + 1) blank)

/-- mod walk: about to advance the D hole (at cell `h`); the R hole is at cell `j` -/
def MW (Y : Strm) (d r h j : Nat) : Cfg St :=
  ⟨ma1, ones h (F ::: Y), F ::: ones (d - h) (F ::: F ::: ones j (F ::: ones (r + 1 - j) blank))⟩

/-- the walk is over: back on D's last cell (the home), D hole at cell `h`, R without hole -/
def E3 (Y : Strm) (d r h : Nat) : Cfg St :=
  cfgL e3 (ones (d - h) (F ::: ones h (F ::: Y))) (F ::: F ::: ones (r + 2) blank)

/-- adding `d` to T: the D hole at cell `c` (moving down), the head on it -/
def AD (L u d r c : Nat) : Cfg St :=
  cfgL a1 (F ::: ones c (F ::: F ::: TX L u)) (ones (d - c) (F ::: F ::: ones (r + 2) blank))

/-- the round for `n` is over: D has `n` cells and its home, R is a single hole -/
def RE (Y : Strm) (n : Nat) : Cfg St := ⟨f6, F ::: F ::: F ::: F ::: ones n (F ::: Y), blank⟩

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

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

/-- the walk after `j` of its `r + 1` rounds, from the D hole home and the R hole at cell 0 -/
theorem mw_upto (Y : Strm) (d r : Nat) (hd : 1 ≤ d) :
    ∀ j, j ≤ r → Rch (MW Y d r d 0) (MW Y d r ((d + j - 1) % d + 1) j)
  | 0, _ => by
    rw [show d + 0 - 1 = d - 1 by omega, Nat.mod_eq_of_lt (by omega), show d - 1 + 1 = d by omega]; fin
  | j + 1, hj => by
    refine Rch.tr (mw_upto Y d r hd j (by omega)) ?_
    have := mw_step Y d r ((d + j - 1) % d + 1) j (by omega) (Nat.mod_lt _ (by omega)) (by omega)
    rw [mod_succ', show d + j - 1 + 1 = d + (j + 1) - 1 by omega] at this
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

/-- the whole walk: `r + 1` rounds; the D hole ends at cell `r % d + 1` (home iff `d ∣ r + 1`) -/
theorem walk (Y : Strm) (d r : Nat) (hd : 1 ≤ d) :
    Rch (MW Y d r d 0) (E3 Y d r (r % d + 1)) := by
  refine Rch.tr (mw_upto Y d r hd r (Nat.le_refl _)) ?_
  have := mw_last Y d r ((d + r - 1) % d + 1) (by omega) (Nat.mod_lt _ (by omega))
  rw [mod_succ', show d + r - 1 + 1 = d + r by omega, Nat.add_mod_left] at this
  exact this

/-! ## the shift -/

/-- a right step, also on the blank part of the tape -/
macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))

/-- the shift starts on the first separator cell, D without hole to its left -/
def SEP (Y : Strm) (d r : Nat) : Cfg St := ⟨f2, ones (d + 1) (F ::: Y), F ::: F ::: ones (r + 2) blank⟩

/-- the first separator cell becomes D's new home, R loses its cell 0 and gets its hole at its
new cell 0; then the walk for `d + 1` -/
theorem shift (Y : Strm) (d r : Nat) : Rch (SEP Y d (r + 1)) (MW Y (d + 1) r (d + 1) 0) := by
  unfold SEP MW
  gR; gR; gR; gR; gL
  show Rch (cfgL PM2 (F ::: F ::: F ::: F ::: ones (d + 1) (F ::: Y)) _) _
  gL; gL; gL; gL; gR
  rw [Nat.sub_self, Nat.sub_zero]
  fin

/-- the same with R of two cells: `r` becomes 0 and the round is over -/
theorem shift_end (Y : Strm) (d : Nat) : Rch (SEP Y d 0) (RE Y (d + 1)) := by
  unfold SEP RE
  gR; gR; gR; gR
  fin

/-- the D hole is not home: fill it, then to the separator -/
theorem fill_hole (Y : Strm) (d r h : Nat) (hh : h < d) : Rch (E3 Y d r h) (SEP Y d r) := by
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

/-! ## adding `d` to T -/

theorem TX_eq (L u : Nat) : TX L u = ones (L - 1 - u) (F ::: true ::: ones u blank) := rfl

/-- one unit: the left parser from the new D hole (at cell `c`) to the T hole, advance it
(it stays on T's last cell: saturation), and the right parser back to the D hole -/
theorem add_unit (L u d r c : Nat) (hL : 1 ≤ L) (hu : u ≤ L - 1) (hc : c + 1 ≤ d) :
    Rch (cfgL PT1 (ones c (F ::: F ::: TX L u)) (F ::: true ::: ones (d - c - 1) (F ::: F ::: ones (r + 2) blank)))
      (AD L (min (u + 1) (L - 1)) d r c) := by
  rw [TX_eq]
  refine Rch.tr (ParserL.findS PPT _ _ c (L - 1 - u)) ?_
  gR; gR
  unfold AD
  rcases Nat.lt_or_ge u (L - 1) with hl | hl
  · obtain ⟨k, hk⟩ : ∃ k, L - 1 - u = k + 1 := ⟨L - 2 - u, by omega⟩
    rw [hk, show min (u + 1) (L - 1) = u + 1 by omega, TX_eq, show L - 1 - (u + 1) = k by omega]
    gR
    show Rch ⟨PA1, F ::: ones (u + 2) blank, ones k (F ::: F ::: ones c (F ::: true ::: ones (d - c - 1)
      (F ::: F ::: ones (r + 2) blank)))⟩ _
    refine Rch.tr (ParserR.findS PPA _ _ k c) ?_
    gL
    rw [show d - c = d - c - 1 + 1 by omega]
    fin
  · obtain rfl : u = L - 1 := by omega
    rw [Nat.sub_self, show min (L - 1 + 1) (L - 1) = L - 1 by omega, TX_eq, Nat.sub_self]
    gL; gR
    show Rch ⟨PA1, F ::: ones (L - 1 + 1) blank, F ::: F ::: ones c (F ::: true ::: ones (d - c - 1)
      (F ::: F ::: ones (r + 2) blank))⟩ _
    refine Rch.tr (ParserR.findS PPA _ _ 0 c) ?_
    gL
    rw [show d - c = d - c - 1 + 1 by omega]
    fin

/-- the D hole one cell down, and one unit -/
theorem add_step (L u d r c : Nat) (hL : 1 ≤ L) (hu : u ≤ L - 1) (hc : c + 1 ≤ d) :
    Rch (AD L u d r (c + 1)) (AD L (min (u + 1) (L - 1)) d r c) := by
  unfold AD
  gL; gL
  rw [show d - (c + 1) = d - c - 1 by omega]
  exact add_unit L u d r c hL hu hc

/-- the walk ended with the D hole home: the first unit -/
theorem add_first (L u d r : Nat) (hL : 1 ≤ L) (hu : u ≤ L - 1) (hd : 1 ≤ d) :
    Rch (E3 (F ::: TX L u) d r d) (AD L (min (u + 1) (L - 1)) d r (d - 1)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  unfold E3
  rw [Nat.sub_self]
  gL; gL
  have := add_unit L u (e + 1) r e hL hu (by omega)
  rw [show e + 1 - e - 1 = 0 by omega] at this
  rw [show e + 1 - 1 = e by omega]
  exact this

/-- all units: the D hole from cell `c` down to cell 0 -/
theorem add_all (L d r : Nat) (hL : 1 ≤ L) :
    ∀ c u, c ≤ d → u ≤ L - 1 → Rch (AD L u d r c) (AD L (min (u + c) (L - 1)) d r 0)
  | 0, u, _, hu => by rw [show min (u + 0) (L - 1) = u by omega]; fin
  | c + 1, u, hc, hu => by
    refine Rch.tr (add_step L u d r c hL hu (by omega)) ?_
    have := add_all L d r hL c (min (u + 1) (L - 1)) (by omega) (by omega)
    rw [show min (min (u + 1) (L - 1) + c) (L - 1) = min (u + (c + 1)) (L - 1) by omega] at this
    exact this

/-- the D hole falls off cell 0: D without hole, on to the separator -/
theorem add_end (L u d r : Nat) : Rch (AD L u d r 0) (SEP (F ::: TX L u) d r) := by
  unfold AD SEP
  gL; gR
  rw [Nat.sub_zero, show true ::: ones d (F ::: F ::: ones (r + 2) blank) =
    ones (d + 1) (F ::: F ::: ones (r + 2) blank) from rfl]
  sRn (d + 1)
  fin

/-- `d` divides: T gets `d` more (saturated at `L - 1`), then on to the separator -/
theorem add (L u d r : Nat) (hL : 1 ≤ L) (hu : u ≤ L - 1) (hd : 1 ≤ d) :
    Rch (E3 (F ::: TX L u) d r d) (SEP (F ::: TX L (min (u + d) (L - 1))) d r) := by
  refine Rch.tr (add_first L u d r hL hu hd) ?_
  refine Rch.tr (add_all L d r hL (d - 1) _ (by omega) (by omega)) ?_
  rw [show min (min (u + 1) (L - 1) + (d - 1)) (L - 1) = min (u + d) (L - 1) by omega]
  exact add_end _ _ _ _

/-! ## the round end -/

local notation "T" => true

/-- R's new cells (six, written from the right), back over D, its cell 1 marked -/
theorem re_fill (Y : Strm) (n : Nat) (hn : 1 ≤ n) :
    Rch (RE Y n) (cfgL PC1 (T ::: F ::: Y) (F ::: ones (n + 4) blank)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold RE
  refine blankR ?_; gR; refine blankR ?_
  show Rch (cfgL h1 (F ::: F ::: F ::: F ::: F ::: F ::: ones (m + 1) (F ::: Y)) blank) _
  gL; gL; gL; gL; gL; gL; gL
  sLn m
  rw [show T ::: T ::: T ::: T ::: T ::: T ::: T ::: blank = ones 7 blank from rfl, ones_add,
    show m + 7 = (m + 5) + 1 + 1 by omega, ones_succ, ones_succ]
  show Rch ⟨k1, Y, F ::: _⟩ _
  gR; gR; gL
  rw [show m + 1 + 4 = m + 5 by omega]
  fin

/-- the check: the left parser to the T hole; two cells after it read `1 0` iff `u + 2 = L`
(halt); otherwise the hole is filled and the head is somewhere in T going left -/
theorem check (L u : Nat) (Z : Strm) (hL : 1 ≤ L) (hu : u ≤ L - 1) :
    (u + 2 = L → HaltAt (cfgL PC1 (T ::: F ::: F ::: TX L u) (F ::: Z))) ∧
    (u + 2 ≠ L → ∃ a b, a + b = L + 1 ∧
      Rch (cfgL PC1 (T ::: F ::: F ::: TX L u) (F ::: Z))
        (cfgL z1 (ones a blank) (ones b (F ::: F ::: T ::: F ::: Z)))) := by
  have st : Rch (cfgL PC1 (T ::: F ::: F ::: TX L u) (F ::: Z))
      ⟨x2, T ::: T ::: ones u blank, ones (L - 1 - u) (F ::: F ::: T ::: F ::: Z)⟩ := by
    rw [TX_eq]
    refine Rch.tr (ParserL.findS PPC _ _ 1 (L - 1 - u)) ?_
    gR; gR; fin
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show L - 1 - u = 1 by omega] at st
    refine HaltAt.back st ⟨T ::: T ::: ones u blank, T ::: F ::: F ::: T ::: F ::: Z, ?_⟩
    gR; gL; fin
  · rcases Nat.lt_or_ge (u + 2) L with hl | hl
    · obtain ⟨k, hk⟩ : ∃ k, L - 1 - u = k + 2 := ⟨L - 3 - u, by omega⟩
      rw [hk] at st
      refine ⟨u + 3, k + 1, ?_, Rch.tr st ?_⟩
      · omega
      · gR; gL; fin
    · rw [show L - 1 - u = 0 by omega] at st
      refine ⟨u + 2, 0, ?_, Rch.tr st ?_⟩
      · omega
      · gL; fin

/-- T: two more cells on the left (the new hole at cell 1); back right to the mark (D's cell
1): D := 1 with its home at cell 1, the separator, R's hole at R's cell 0 -/
theorem reset (a b : Nat) (X : Strm) :
    Rch (cfgL z1 (ones a blank) (ones b (F ::: F ::: T ::: F ::: T ::: T ::: T ::: X)))
      ⟨f6, F ::: F ::: F ::: F ::: T ::: F ::: F ::: ones (a + b) (F ::: T ::: blank), X⟩ := by
  sLn a
  rw [ones_add]
  show Rch (cfgL z1 (F ::: blank) _) _
  gL
  show Rch (cfgL z2 (F ::: blank) _) _
  gR; gR
  rw [show T ::: F ::: T ::: T ::: T ::: X = ones 1 (F ::: T ::: T ::: T ::: X) from rfl]
  show Rch ⟨PZ1, F ::: T ::: blank, _⟩ _
  refine Rch.tr (ParserR.findS PPZ _ _ (a + b) 1) ?_
  gR; gR; gR
  fin

/-- the round end for `n ≥ 1`: halt iff the T hole is at cell `n + 1` (`u = n`); otherwise
the round for `n + 2` starts (`d = 1`, the T counter 0) -/
theorem round_end (n u : Nat) (hn : 1 ≤ n) (hu : u ≤ n + 1) :
    (u = n → HaltAt (RE (F ::: TX (n + 2) u) n)) ∧
    (u ≠ n → Rch (RE (F ::: TX (n + 2) u) n) (MW (F ::: TX (n + 4) 0) 1 n 1 0)) := by
  have f := re_fill (F ::: TX (n + 2) u) n hn
  have c := check (n + 2) u (ones (n + 4) blank) (by omega) (by omega)
  refine ⟨fun h => HaltAt.back f (c.1 (by omega)), fun h => ?_⟩
  obtain ⟨a, b, hab, st⟩ := c.2 (by omega)
  refine Rch.tr f (Rch.tr st ?_)
  rw [show ones (n + 4) blank = T ::: T ::: T ::: ones (n + 1) blank from rfl]
  refine Rch.tr (reset a b _) ?_
  rw [hab, show ones (n + 1) blank = T ::: ones n blank from rfl]
  gL
  show Rch (cfgL PM2 (F ::: F ::: F ::: F ::: T ::: F ::: F ::: ones (n + 2 + 1) (F ::: T ::: blank)) _) _
  gL; gL; gL; gL; gR
  show Rch ⟨ma1, T ::: F ::: F ::: ones (n + 2 + 1) (F ::: T ::: blank), F ::: F ::: F ::: F ::: T ::: ones n blank⟩ _
  unfold MW TX
  rw [Nat.sub_self, Nat.sub_zero, Nat.sub_zero, show n + 4 - 1 = n + 2 + 1 by omega]
  fin

/-! ## the seed and one candidate -/

/-- the seed writes `T = 10` (hole on its last cell), `00`, D's cell 0: the end of a pseudo-round
`n = -1`; the round end turns it into the end of the (empty) round for `n = 1` -/
theorem seed_reach : Rch start (RE (F ::: TX 3 0) 1) := by
  unfold start
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; refine blankR ?_
  show Rch (cfgL h1 (F ::: F ::: F ::: F ::: T ::: F ::: F ::: F ::: T ::: blank) blank) _
  gL; gL; gL; gL; gL
  show Rch ⟨k1, F ::: F ::: T ::: blank, F ::: _⟩ _
  gR; gR; gL
  have c := (check 1 0 (T ::: T ::: T ::: blank) (Nat.le_refl _) (by omega)).2 (by omega)
  obtain ⟨a, b, hab, st⟩ := c
  refine Rch.tr st (Rch.tr (reset a b blank) ?_)
  rw [hab]
  fin

/-- test `d` (`n = d + r + 1`): the walk, then if `d ∣ n` add `d` to T; on to the separator -/
theorem dstep (L u d r : Nat) (hL : 1 ≤ L) (hu : u ≤ L - 1) (hd : 1 ≤ d) :
    Rch (MW (F ::: TX L u) d r d 0)
      (SEP (F ::: TX L (if (r + 1) % d = 0 then min (u + d) (L - 1) else u)) d r) := by
  refine Rch.tr (walk _ d r hd) ?_
  have ms := mod_succ r d
  have hlt := Nat.mod_lt r (show d > 0 by omega)
  by_cases hw : r % d + 1 < d
  · rw [if_neg (by rw [ms.1 hw]; omega)]
    exact fill_hole _ d r _ hw
  · have h2 : r % d + 1 = d := by omega
    rw [if_pos (ms.2 h2), h2]
    exact add L u d r hL hu hd

end TM.OddPerfect
