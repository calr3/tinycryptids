import TinyCryptids.Core.Routines
import TinyCryptids.Oppermann.Tac

/-!
# Routines of the design

Tape (`F` = blank):

    [1 0] Q 00 D 00 R

* `Q` : `q + 2` cells (interval `q`), hole at cell `k + 1` (`k = 2i`): the `i`-th number of the
  interval;
* the flag (a prime was seen in this interval): a 1 two cells left of `Q`;
* `D` : `d + 2` cells, the trial divisor `d`, with a hole at cell `c + 1`;
* `R` : `r + 2` cells, `r = m - d`, during the mod walk with a hole at cell `j`.

Configurations take the contents left of D's separator as a stream `X`
(nearest cell first); between candidates `X = QX q k f`.
-/

namespace TM.Oppermann
open St

local notation "F" => false

/-! ## the copies of the generic routines -/

theorem Dma : Dadv delta ma1 ma2 ma3 ma4 maw1 maw2 maw3 PR1 PR1 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
theorem PPR : ParserR delta PR1 PR2 := by constructor <;> rfl
theorem PPF : ParserR delta PF1 PF2 := by constructor <;> rfl
theorem PPN : ParserR delta PN1 PN2 := by constructor <;> rfl
theorem PPM : ParserL delta PM1 PM2 := by constructor <;> rfl
theorem PPK : ParserL delta PK1 PK2 := by constructor <;> rfl
theorem PPQ : ParserL delta PQ1 PQ2 := by constructor <;> rfl
theorem PPC : ParserL delta PC1 PC2 := by constructor <;> rfl
theorem PPP : ParserL delta PP1 PP2 := by constructor <;> rfl

/-! ## configurations -/

/-- left of Q: the flag `1` two cells away, or nothing -/
def FL : Bool → Strm
  | true => F ::: true ::: blank
  | false => blank

/-- Q seen from its right end: hole at cell `k + 1` of `q + 2` cells, then the flag -/
def QX (q k : Nat) (f : Bool) : Strm := ones (q - k) (F ::: ones (k + 1) (FL f))

/-- mod walk: about to advance the D hole (residue `c`); the R hole is at `j` -/
def MW (X : Strm) (d r c j : Nat) : Cfg St :=
  ⟨ma1, ones (c + 1) (F ::: F ::: X), F ::: ones (d - c) (F ::: F ::: ones j (F ::: ones (r + 1 - j) blank))⟩

/-- not a divisor: hole at cell 1, head on cell 2, about to shift -/
def SH (X : Strm) (d r : Nat) : Cfg St := ⟨sh1, F ::: ones 1 (F ::: F ::: X), ones d (F ::: F ::: ones (r + 2) blank)⟩

/-- head on cell 0 of R (no hole); D has its hole at cell 1 -/
def SHT (X : Strm) (d r : Nat) : Cfg St :=
  ⟨sh4, F ::: F ::: ones d (F ::: true ::: F ::: F ::: X), ones (r + 2) blank⟩

/-- on the Q hole, about to advance it -/
def AQ (q k : Nat) (f : Bool) (d r : Nat) : Cfg St :=
  ⟨q1, ones (k + 1) (FL f), F ::: ones (q - k) (F ::: F ::: true ::: F ::: ones d (F ::: F ::: ones (r + 2) blank))⟩

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

theorem ones_cons_blank (s : Nat) : ones s (true ::: blank) = ones (s + 1) blank := (ones_succ' s blank).symm

/-- a left step from any configuration whose cells compute (e.g. on the blank part) -/
macro "gL0" : tactic => `(tactic| refine Rch.tr (stepL (δ := delta) (by rfl)) ?_)

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

/-- last step of the mod walk, residue 0: d divides r, so m is composite -/
theorem mw_last_div (q k : Nat) (f : Bool) (d r : Nat) (hr : 1 ≤ r) (hd : 1 ≤ d) (hk : k < q) :
    Rch (MW (QX q k f) d r (d - 1) r) (AQ q k f d r) := by
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, q - k = e + 1 := ⟨q - k - 1, by omega⟩
  unfold MW AQ
  rw [show c + 1 - 1 = c by omega, show c + 1 - c = 1 by omega, show b + 1 + 1 - (b + 1) = 1 by omega, he]
  refine Rch.tr (Dma.toDW.wrap (c + 1) (F ::: QX q k f) _) ?_
  refine Rch.tr (PPR.find2 (c + 1) b _ blank) ?_
  gL; gR; gR; refine blankR ?_; gL
  refine Rch.tr (PPK.find2 (b + 3) c _ _) ?_
  gL; gL; gL
  unfold QX; rw [he]
  refine Rch.tr (PPQ.find0 (e + 1) _ _) ?_
  gR
  rw [cons_blank]; fin

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

/-- head two cells past R (r = 0) -/
def P6 (X : Strm) (d : Nat) : Cfg St := ⟨sh6, ones 2 (F ::: F ::: ones d (F ::: true ::: F ::: F ::: X)), blank⟩

theorem tail_zero (X : Strm) (d : Nat) : Rch (SHT X d 0) (P6 X d) := by
  unfold SHT P6; gR; gR; fin

/-- r = 0: m is prime; set the flag and go to the Q hole -/
theorem prime_path (q k : Nat) (f : Bool) (d : Nat) (hk : k < q) (hd : 1 ≤ d) :
    Rch (P6 (QX q k f) d) (AQ q k true d 0) := by
  obtain ⟨e, he⟩ : ∃ e, q - k = e + 1 := ⟨q - k - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  unfold P6 AQ QX
  rw [he]
  refine blankR ?_; gL
  refine Rch.tr (PPC.find2 2 c _ _) ?_
  gL
  refine Rch.tr (PPP.find2 0 e _ _) ?_
  gL; sLn k
  cases f
  · simp only [FL]
    gL0; gR; gR
    simp only [tl_cons]; rw [← ones_succ']
    refine Rch.tr (PPF.find0 (k + 1) _ _) ?_
    gL; rw [cons_blank]; fin
  · simp only [FL]
    gL; gR; gR
    rw [← ones_succ']
    refine Rch.tr (PPF.find0 (k + 1) _ _) ?_
    gL; rw [cons_blank]; fin

/-! ## next candidate: advance the Q hole, rebuild D := 2 -/

/-- rebuild from cell 3 of D (d = g + 2, hole at cell 1): D := 2, R := m - 1 -/
theorem rebuild (X : Strm) (g r : Nat) :
    Rch ⟨c1, true ::: F ::: true ::: F ::: F ::: X, ones (g + 1) (F ::: F ::: ones (r + 2) blank)⟩
      (SHT X 2 (g + r + 1)) := by
  unfold SHT
  sRn (g + 1); gR; gR; sRn (r + 2); refine blankR ?_; gL
  show Rch (cfgL c4 (true ::: ones (r + 1) (true ::: true ::: ones (g + 1)
    (true ::: F ::: true ::: F ::: F ::: X))) (true ::: blank)) _
  rw [show true ::: ones (r + 1) (true ::: true ::: ones (g + 1) (true ::: F ::: true ::: F ::: F ::: X)) =
      ones (r + 2) (ones 2 (ones (g + 1) (ones 1 (F ::: true ::: F ::: F ::: X)))) from rfl,
    ones_add, ones_add, ones_add, show r + 2 + 2 + (g + 1) + 1 = g + r + 6 by omega]
  sLn (g + r + 6); gR; gR; gR; gR; gR
  rw [ones_cons_blank, show g + r + 2 + 1 = g + r + 1 + 2 by omega]; fin

theorem qadv_next (q k : Nat) (f : Bool) (d r : Nat) (hk : k + 2 < q) (hd : 2 ≤ d) :
    Rch (AQ q k f d r) (SHT (QX q (k + 2) f) 2 (d + r - 1)) := by
  obtain ⟨e, he⟩ : ∃ e, q - k = e + 3 := ⟨q - k - 3, by omega⟩
  obtain ⟨g, rfl⟩ : ∃ g, d = g + 2 := ⟨d - 2, by omega⟩
  unfold AQ
  rw [he]
  gR; gR; gR; gL; gR
  refine Rch.tr (PPN.find2 (e + 1) 0 _ _) ?_
  gR
  have := rebuild (QX q (k + 2) f) g r
  rw [show g + r + 1 = g + 2 + r - 1 by omega] at this
  unfold QX at this ⊢
  rw [show q - (k + 2) = e + 1 by omega] at this ⊢
  exact this

/-- the hole ran off Q: the head on Q's last cell, Q all ones, going left -/
def IE (q : Nat) (f : Bool) (d r : Nat) : Cfg St :=
  cfgL ie1 (ones (q + 2) (FL f)) (F ::: F ::: true ::: F ::: ones d (F ::: F ::: ones (r + 2) blank))

theorem qadv_end (q k : Nat) (f : Bool) (d r : Nat) (hk : k + 1 = q ∨ k + 2 = q) :
    Rch (AQ q k f d r) (IE q f d r) := by
  unfold AQ IE
  rcases hk with hk | hk
  · rw [show q - k = 1 by omega]
    gR; gR; gL
    subst hk; fin
  · rw [show q - k = 2 by omega]
    gR; gR; gR; gL
    subst hk; fin

theorem ie_halt (q d r : Nat) : HaltAt (IE q false d r) := by
  unfold IE HaltAt; apply Exists.intro; apply Exists.intro
  sLn (q + 2); simp only [FL]; gL0; gR; fin

theorem ie_next (q d r : Nat) (hd : 2 ≤ d) :
    Rch (IE q true d r) (SHT (QX (q + 1) 0 false) 2 (d + r - 1)) := by
  obtain ⟨g, rfl⟩ : ∃ g, d = g + 2 := ⟨d - 2, by omega⟩
  unfold IE
  rw [show ones (q + 2) (FL true) = true ::: ones (q + 1) (FL true) from rfl]
  sLn (q + 2); simp only [FL]; gL; gR; gR; gR
  refine Rch.tr (PPN.find2 (q + 1) 0 _ _) ?_
  gR
  have := rebuild (QX (q + 1) 0 false) g r
  rw [show g + r + 1 = g + 2 + r - 1 by omega] at this
  unfold QX at this ⊢
  rw [show q + 1 - 0 = q + 1 by omega] at this ⊢
  simp only [tl_cons]; rw [cons_blank]
  exact this

/-! ## the seed -/

macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))

theorem seed_reach : Rch start (P6 (QX 3 0 false) 2) := by
  unfold start P6 QX FL
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  fin

end TM.Oppermann
