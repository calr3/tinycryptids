import TinyCryptids.Core.Routines
import TinyCryptids.Riesel.Tac
import TinyCryptids.Riesel.Spec

/-!
# The mod walk

Tape (`F` = blank):

    C 0 K 0 D 00 R

* `D` : `d + 1` cells (cells `0 … d`), the trial divisor `d`, with a hole at cell `h`,
  `1 ≤ h ≤ d`; its home is cell `d`, the last one;
* `R` : `r + 2` cells, `P = d + r + 1`, during the mod walk with a hole at cell `j ≤ r`.

Configurations take the contents left of D's separator as a stream `Y`
(nearest cell first): K, its separator and C.  One round of the walk advances the D hole
(from cell `d` it wraps to cell 1) and then the R hole; after `r + 1` rounds the R hole
falls off and the D hole is home iff `d ∣ r + 1`, i.e. iff `d ∣ P`.
-/

namespace TM.Riesel
open St

local notation "F" => false

theorem PPR : ParserR delta PR1 PR2 := by constructor <;> rfl
theorem PPM : ParserL delta PM1 PM2 := by constructor <;> rfl

/-- a right parser across `a` ones and three 0s: the third is the hole -/
theorem PPR.find3 (a : Nat) (L X : Strm) :
    Rch ⟨PR1, L, ones a (F ::: F ::: F ::: true ::: X)⟩ ⟨PR2, F ::: F ::: F ::: ones a L, true ::: X⟩ := by
  sRn a; gR; gR; gR; fin

/-- a left parser across `a` ones and three 0s: the third is the hole -/
theorem PPM.find3 (a : Nat) (s R : Strm) :
    Rch (cfgL PM1 (ones a (F ::: F ::: F ::: true ::: s)) R)
      (cfgL PM2 (true ::: s) (F ::: F ::: F ::: ones a R)) := by
  sLn a; gL; gL; gL; fin

/-! ## configurations -/

/-- mod walk: about to advance the D hole (at cell `h`); the R hole is at cell `j` -/
def MW (Y : Strm) (d r h j : Nat) : Cfg St :=
  ⟨ma1, ones h (F ::: Y), F ::: ones (d - h) (F ::: F ::: ones j (F ::: ones (r + 1 - j) blank))⟩

/-- the walk is over: back on D's last cell (the home), D hole at cell `h`, R without hole -/
def E3 (Y : Strm) (d r h : Nat) : Cfg St :=
  cfgL e3 (ones (d - h) (F ::: ones h (F ::: Y))) (F ::: F ::: ones (r + 2) blank)

/-- `P = d + 1` is prime: the head on R's erased cell 1, D (`d + 1` cells, no hole) to the left -/
def WP (Y : Strm) (d : Nat) : Cfg St := cfgL w1 (F ::: F ::: F ::: F ::: ones (d + 1) (F ::: Y)) blank

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

theorem ones_cons_blank (s : Nat) : ones s (true ::: blank) = ones (s + 1) blank := (ones_succ' s blank).symm

/-- a right step, also on the blank part of the tape -/
macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))

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

/-- the right parser from the D hole to the R hole at cell `j`, and the left parser back -/
theorem pr_find (L : Strm) (a j m : Nat) :
    Rch ⟨PR1, L, ones a (F ::: F ::: ones j (F ::: ones (m + 1) blank))⟩
      ⟨PR2, F ::: ones j (F ::: F ::: ones a L), ones (m + 1) blank⟩ := by
  rcases j with _ | j
  · exact PPR.find3 a L (ones m blank)
  · exact PPR.find2 a j L (ones m blank)

theorem pm_find (s R : Strm) (a b : Nat) :
    Rch (cfgL PM1 (ones a (F ::: F ::: ones b (F ::: true ::: s))) R)
      (cfgL PM2 (true ::: s) (F ::: ones b (F ::: F ::: ones a R))) := by
  rcases b with _ | b
  · exact PPM.find3 a s R
  · exact PPM.find2 a b s R

/-- one round of the walk, the R hole not at its last cell `r` -/
theorem mw_step (Y : Strm) (d r h j : Nat) (hd : 2 ≤ d) (h1 : 1 ≤ h) (hh : h ≤ d) (hj : j < r) :
    Rch (MW Y d r h j) (MW Y d r (h % d + 1) (j + 1)) := by
  obtain ⟨m, hm⟩ : ∃ m, r + 1 - j = m + 2 := ⟨r - 1 - j, by omega⟩
  have hh' : h % d + 1 ≤ d := Nat.mod_lt h (by omega)
  unfold MW
  rw [hm, show r + 1 - (j + 1) = m + 1 by omega]
  refine Rch.tr (dadv Y _ d h h1 hh) ?_
  refine Rch.tr (pr_find _ _ j (m + 1)) ?_
  gL; gR; gR; gL; gL
  rw [show ones j (F ::: F ::: ones (d - (h % d + 1)) (F ::: ones (h % d + 1) (F ::: Y))) =
    ones j (F ::: F ::: ones (d - (h % d + 1)) (F ::: true ::: ones (h % d) (F ::: Y))) from rfl]
  refine Rch.tr (pm_find _ _ (j + 1) _) ?_
  gR
  fin

/-- the walk after `j` of its `r + 1` rounds, from the D hole home and the R hole at cell 0 -/
theorem mw_upto (Y : Strm) (d r : Nat) (hd : 2 ≤ d) :
    ∀ j, j ≤ r → Rch (MW Y d r d 0) (MW Y d r ((d + j - 1) % d + 1) j)
  | 0, _ => by
    rw [show d + 0 - 1 = d - 1 by omega, Nat.mod_eq_of_lt (by omega), show d - 1 + 1 = d by omega]; fin
  | j + 1, hj => by
    refine Rch.tr (mw_upto Y d r hd j (by omega)) ?_
    have := mw_step Y d r ((d + j - 1) % d + 1) j hd (by omega) (Nat.mod_lt _ (by omega)) (by omega)
    have e : ((d + j - 1) % d + 1) % d = (d + (j + 1) - 1) % d := by
      rw [show d + (j + 1) - 1 = d + j - 1 + 1 by omega, Nat.add_mod (d + j - 1) 1 d,
        Nat.mod_eq_of_lt (show 1 < d by omega)]
    rw [e] at this
    exact this

/-- the last round: the R hole falls off, back to D's last cell -/
theorem mw_last (Y : Strm) (d r h : Nat) (hd : 2 ≤ d) (h1 : 1 ≤ h) (hh : h ≤ d) :
    Rch (MW Y d r h r) (E3 Y d r (h % d + 1)) := by
  have hh' : h % d + 1 ≤ d := Nat.mod_lt h (by omega)
  unfold MW E3
  rw [show r + 1 - r = 0 + 1 by omega]
  refine Rch.tr (dadv Y _ d h h1 hh) ?_
  refine Rch.tr (pr_find _ _ r 0) ?_
  gL; gR; gR; refine blankR ?_; gL
  show Rch (cfgL e1 (ones (r + 2) (F ::: F ::: ones (d - (h % d + 1)) (F ::: ones (h % d + 1) (F ::: Y))))
    (F ::: blank)) _
  sLn (r + 2); gL; gL
  rw [cons_blank]; fin

/-! ## after the walk -/

/-- the D hole is home: `d ∣ P`, composite.  Fill the hole and the separator, back to
D's cell 0, then to cell 1 (`g1`): from there all of D and R are ones -/
theorem comp_start (Y : Strm) (d r : Nat) :
    Rch (E3 Y d r d) ⟨g1, true ::: F ::: Y, ones (d + r + 4) blank⟩ := by
  unfold E3
  rw [Nat.sub_self, ones_zero]
  gR; gR; gL
  show Rch (cfgL x3 (ones (d + 2) (F ::: Y)) (ones (r + 3) blank)) _
  sLn (d + 2); gR; gR
  show Rch ⟨g1, _, ones (d + 1) (ones (r + 3) blank)⟩ _
  rw [ones_add, show d + 1 + (r + 3) = d + r + 4 by omega]
  fin

/-- the D hole is not home: fill it; the first separator cell becomes D's new home, R loses
its cell 0 and gets its hole at its new cell 0; then the walk for `d + 1` -/
theorem shift (Y : Strm) (d r h : Nat) (hh : h < d) :
    Rch (E3 Y d (r + 1) h) (MW Y (d + 1) r (d + 1) 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = h + k + 1 := ⟨d - h - 1, by omega⟩
  unfold E3 MW
  rw [show h + k + 1 - h = k + 1 by omega, Nat.sub_self, show r + 1 - 0 = r + 1 by omega]
  gL
  show Rch (cfgL f1 (ones k (F ::: ones h (F ::: Y))) _) _
  sLn k; gR
  rw [← ones_succ']
  sRn (k + 1); gR; gR; gR; gR; gL
  show Rch (cfgL PM2 (F ::: F ::: F ::: F ::: ones (k + 1) (true ::: ones h (F ::: Y))) _) _
  gL; gL; gL; gL; gR
  show Rch ⟨ma1, true ::: ones k (true ::: ones h (F ::: Y)), F ::: F ::: F ::: F ::: true ::: ones r blank⟩ _
  rw [← ones_succ', ← ones_succ, ones_add, show k + 1 + 1 + h = h + k + 1 + 1 by omega]
  fin

/-- `r = 0` and the D hole not home: `P = d + 1` is prime -/
theorem prime_end (Y : Strm) (d h : Nat) (hh : h < d) :
    Rch (E3 Y d 0 h) (WP Y d) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = h + k + 1 := ⟨d - h - 1, by omega⟩
  unfold E3 WP
  rw [show h + k + 1 - h = k + 1 by omega]
  gL
  show Rch (cfgL f1 (ones k (F ::: ones h (F ::: Y))) _) _
  sLn k; gR
  rw [← ones_succ']
  sRn (k + 1); gR; gR; gR; gR; refine blankR ?_; gL
  show Rch (cfgL w1 (F ::: F ::: F ::: F ::: ones (k + 1) (true ::: ones h (F ::: Y))) (F ::: blank)) _
  rw [cons_blank, ← ones_succ', ones_add, show k + 1 + 1 + h = h + k + 1 + 1 by omega]
  fin

end TM.Riesel
