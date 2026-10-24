import TinyCryptids.Core.Routines
import TinyCryptids.Riesel.Tac
import TinyCryptids.Riesel.Spec

/-!
# Trial division (the mod walk of `legendre/`) and the composite rebuild

Tape (`F` = blank):

    C 00 K 00 D 00 R

* `D` : `d + 2` cells, the trial divisor `d`, with a hole at cell `c + 1`;
* `R` : `r + 2` cells, `r = P - d`, during the mod walk with a hole at cell `j`.

Configurations take the contents left of D's separator as a stream `X`
(nearest cell first): K, its separator and C.
-/

namespace TM.Riesel
open St

local notation "F" => false

/-! ## the copies of the generic routines -/

theorem Dma : Dadv delta ma1 ma2 ma3 ma4 maw1 maw2 maw3 PR1 PR1 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
theorem PPR : ParserR delta PR1 PR2 := by constructor <;> rfl
theorem PPM : ParserL delta PM1 PM2 := by constructor <;> rfl
theorem PPK : ParserL delta PK1 PK2 := by constructor <;> rfl

/-! ## configurations -/

/-- mod walk: about to advance the D hole (residue `c`); the R hole is at `j` -/
def MW (X : Strm) (d r c j : Nat) : Cfg St :=
  ⟨ma1, ones (c + 1) (F ::: F ::: X), F ::: ones (d - c) (F ::: F ::: ones j (F ::: ones (r + 1 - j) blank))⟩

/-- not a divisor: hole at cell 1, head on cell 2, about to shift -/
def SH (X : Strm) (d r : Nat) : Cfg St := ⟨sh1, F ::: ones 1 (F ::: F ::: X), ones d (F ::: F ::: ones (r + 2) blank)⟩

/-- head on cell 0 of R (no hole); D has its hole at cell 1 -/
def SHT (X : Strm) (d r : Nat) : Cfg St :=
  ⟨sh4, F ::: F ::: ones d (F ::: true ::: F ::: F ::: X), ones (r + 2) blank⟩

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

theorem ones_cons_blank (s : Nat) : ones s (true ::: blank) = ones (s + 1) blank := (ones_succ' s blank).symm

/-- a left step from any configuration whose cells compute (e.g. on the blank part) -/
macro "gL0" : tactic => `(tactic| refine Rch.tr (stepL (δ := delta) (by rfl)) ?_)
macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))

/-! ## mod walk -/

/-- advance D, then the R hole (not at its end) -/
theorem mw_step (X : Strm) (d r c j : Nat) (hc : c < d) (hj1 : 1 ≤ j) (hj : j < r) :
    Rch (MW X d r c j) (MW X d r ((c + 1) % d) (j + 1)) := by
  obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, r = b + 1 + m + 1 := ⟨r - b - 2, by omega⟩
  unfold MW
  rw [show b + 1 + m + 1 + 1 - (b + 1) = m + 2 by omega,
      show b + 1 + m + 1 + 1 - (b + 1 + 1) = m + 1 by omega]
  by_cases hw : c + 1 < d
  · obtain ⟨k, rfl⟩ : ∃ k, d = c + k + 2 := ⟨d - c - 2, by omega⟩
    rw [Nat.mod_eq_of_lt hw, show c + k + 2 - c = k + 2 by omega,
        show c + k + 2 - (c + 1) = k + 1 by omega]
    refine Rch.tr (Dma.nowrap c k _ _) ?_
    refine Rch.tr (PPR.find2 (k + 1) b _ (ones (m + 1) blank)) ?_
    gL; gR; gR; gL; gL
    refine Rch.tr (PPM.find2 (b + 2) k _ _) ?_
    gR; fin
  · obtain rfl : d = c + 1 := by omega
    rw [Nat.mod_self, show c + 1 - c = 1 by omega, show c + 1 - 0 = c + 1 by omega]
    refine Rch.tr (Dma.toDW.wrap (c + 1) (F ::: X) _) ?_
    refine Rch.tr (PPR.find2 (c + 1) b _ (ones (m + 1) blank)) ?_
    gL; gR; gR; gL; gL
    refine Rch.tr (PPM.find2 (b + 2) c _ _) ?_
    gR; fin

/-- last step of the mod walk, residue not 0: d does not divide r -/
theorem mw_last_nodiv (X : Strm) (d r c : Nat) (hr : 1 ≤ r) (hw : c + 1 < d) :
    Rch (MW X d r c r) (SH X d r) := by
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, d = c + k + 2 := ⟨d - c - 2, by omega⟩
  unfold MW SH
  rw [show c + k + 2 - c = k + 2 by omega, show b + 1 + 1 - (b + 1) = 1 by omega]
  refine Rch.tr (Dma.nowrap c k _ _) ?_
  refine Rch.tr (PPR.find2 (k + 1) b _ blank) ?_
  gL; gR; gR; refine blankR ?_; gL
  refine Rch.tr (PPK.find2 (b + 3) k _ _) ?_
  gL; gR; gR; gL
  sLn (c + 2); gR; gR; gR
  rw [cons_blank, ← ones_succ, ones_add, show c + (k + 1 + 1) = c + k + 2 by omega]
  fin

/-! ## shift: d += 1, r -= 1 -/

theorem shift (X : Strm) (d r : Nat) (hr : 1 ≤ r) : Rch (SH X d r) (SHT X (d + 1) (r - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  unfold SH SHT
  rw [show m + 1 - 1 = m by omega]
  sRn d; gR; gR; gR; fin

/-- r ≥ 1: make the R hole and start the mod walk with d -/
theorem tail_more (X : Strm) (d r : Nat) (hd : 1 ≤ d) (hr : 1 ≤ r) : Rch (SHT X d r) (MW X d r 0 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  unfold SHT MW
  rw [show m + 1 + 1 - 1 = m + 1 by omega, show e + 1 - 0 = e + 1 by omega]
  gR; gR; gL; gL
  refine Rch.tr (PPM.find2 1 e _ _) ?_
  gR; fin

/-- head two cells past R (r = 0): `d + 0` is prime -/
def P6 (X : Strm) (d : Nat) : Cfg St := ⟨sh6, ones 2 (F ::: F ::: ones d (F ::: true ::: F ::: F ::: X)), blank⟩

theorem tail_zero (X : Strm) (d : Nat) : Rch (SHT X d 0) (P6 X d) := by
  unfold SHT P6; gR; gR; fin

/-- the mod walk after `j` of its `r` steps -/
theorem mw_upto (X : Strm) (d r : Nat) (hd : 1 ≤ d) :
    ∀ j, 1 ≤ j → j ≤ r → Rch (MW X d r 0 1) (MW X d r ((j - 1) % d) j) := by
  intro j hj hjr
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Nat.zero_mod]; fin
    refine Rch.tr (ih hj0 (by omega)) ?_
    have := mw_step X d r ((j - 1) % d) j (Nat.mod_lt _ (by omega)) hj0 (by omega)
    have ms := mod_succ (j - 1) d
    rw [show j - 1 + 1 = j by omega] at ms
    rw [show j + 1 - 1 = j by omega]
    by_cases hw : (j - 1) % d + 1 < d
    · rw [ms.1 hw]; rw [Nat.mod_eq_of_lt hw] at this; exact this
    · have h2 : (j - 1) % d + 1 = d := by have := Nat.mod_lt (j - 1) (show d > 0 by omega); omega
      rw [ms.2 h2]; rw [h2, Nat.mod_self] at this; exact this

end TM.Riesel
