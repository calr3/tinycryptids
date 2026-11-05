import TinyCryptids.Core.Routines
import TinyCryptids.Defs
import TinyCryptids.Andrica.Tac

/-!
# Trial division on a pair `D 00 R`

`../legendre`'s mod walk and shift, stated for a pair anywhere on the tape:

* `D` : `d + 2` cells (`1`, the hole at cell `c + 1`, `d` more cells), the trial divisor `d`;
* `R` : `r + 2` cells; `m = d + r` is the number tested;
* left of D's cell 0 there is a `0` and then `Lx`; right of R a `0` and then `Ry`.

The test starts with `d = 2` and ends in `y1` (composite: a divisor `d < m` was found) or in
`PC1` (prime: `d = m`, `r = 0`), on the way left to the countdown.
-/

namespace TM.Andrica

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
def MW (Lx Ry : Strm) (d r c j : Nat) : Cfg St :=
  ⟨ma1, ones (c + 1) (F ::: Lx), F ::: ones (d - c) (F ::: F ::: ones j (F ::: ones (r + 1 - j) (F ::: Ry)))⟩

/-- not a divisor: hole at cell 1, head on cell 2, about to shift -/
def SH (Lx Ry : Strm) (d r : Nat) : Cfg St :=
  ⟨sh1, F ::: ones 1 (F ::: Lx), ones d (F ::: F ::: ones (r + 2) (F ::: Ry))⟩

/-- head on cell 0 of R (no hole); D has its hole at cell 1 -/
def SHT (Lx Ry : Strm) (d r : Nat) : Cfg St :=
  ⟨sh4, F ::: F ::: ones d (F ::: true ::: F ::: Lx), ones (r + 2) (F ::: Ry)⟩

/-- composite: the head on the cell left of D's left neighbour -/
def CK (Lx Ry : Strm) (d r : Nat) : Cfg St :=
  cfgL y1 Lx (F ::: true ::: F ::: ones d (F ::: F ::: ones (r + 2) (F ::: Ry)))

/-- prime (`r = 0`): the head on R's last cell -/
def CP (Lx Ry : Strm) (d : Nat) : Cfg St :=
  cfgL PC1 (ones 2 (F ::: F ::: ones d (F ::: true ::: F ::: Lx))) (F ::: Ry)

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

/-! ## mod walk -/

/-- advance D, then the R hole (not at its end) -/
theorem mw_step (Lx Ry : Strm) (d r c j : Nat) (hc : c < d) (hj1 : 1 ≤ j) (hj : j < r) :
    Rch (MW Lx Ry d r c j) (MW Lx Ry d r ((c + 1) % d) (j + 1)) := by
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
    refine Rch.tr (PPR.find2 (k + 1) b _ (ones (m + 1) (F ::: Ry))) ?_
    gL; gR; gR; gL; gL
    refine Rch.tr (PPM.find2 (b + 2) k _ _) ?_
    gR; fin
  · obtain rfl : d = c + 1 := by omega
    rw [Nat.mod_self, show c + 1 - c = 1 by omega, show c + 1 - 0 = c + 1 by omega]
    refine Rch.tr (Dma.toDW.wrap (c + 1) Lx _) ?_
    refine Rch.tr (PPR.find2 (c + 1) b _ (ones (m + 1) (F ::: Ry))) ?_
    gL; gR; gR; gL; gL
    refine Rch.tr (PPM.find2 (b + 2) c _ _) ?_
    gR; fin

/-- last step of the mod walk, residue not 0: d does not divide r -/
theorem mw_last_nodiv (Lx Ry : Strm) (d r c : Nat) (hr : 1 ≤ r) (hw : c + 1 < d) :
    Rch (MW Lx Ry d r c r) (SH Lx Ry d r) := by
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, d = c + k + 2 := ⟨d - c - 2, by omega⟩
  unfold MW SH
  rw [show c + k + 2 - c = k + 2 by omega, show b + 1 + 1 - (b + 1) = 1 by omega]
  refine Rch.tr (Dma.nowrap c k _ _) ?_
  refine Rch.tr (PPR.find2 (k + 1) b _ (F ::: Ry)) ?_
  gL; gR; gR; gL
  refine Rch.tr (PPK.find2 (b + 3) k _ _) ?_
  gL; gR; gR; gL
  sLn (c + 2); gR; gR; gR
  rw [← ones_succ, ones_add, show c + (k + 1 + 1) = c + k + 2 by omega]
  fin

/-- last step of the mod walk, residue 0: d divides r, so m is composite -/
theorem mw_last_div (Lx Ry : Strm) (d r : Nat) (hr : 1 ≤ r) (hd : 1 ≤ d) :
    Rch (MW Lx Ry d r (d - 1) r) (CK Lx Ry d r) := by
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  unfold MW CK
  rw [show c + 1 - 1 = c by omega, show c + 1 - c = 1 by omega, show b + 1 + 1 - (b + 1) = 1 by omega]
  refine Rch.tr (Dma.toDW.wrap (c + 1) Lx _) ?_
  refine Rch.tr (PPR.find2 (c + 1) b _ (F ::: Ry)) ?_
  gL; gR; gR; gL
  refine Rch.tr (PPK.find2 (b + 3) c _ _) ?_
  gL; gL; fin

/-! ## shift: d += 1, r -= 1 -/

theorem shift (Lx Ry : Strm) (d r : Nat) (hr : 1 ≤ r) : Rch (SH Lx Ry d r) (SHT Lx Ry (d + 1) (r - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  unfold SH SHT
  rw [show m + 1 - 1 = m by omega]
  sRn d; gR; gR; gR; fin

/-- r ≥ 1: make the R hole and start the mod walk with d -/
theorem tail_more (Lx Ry : Strm) (d r : Nat) (hd : 1 ≤ d) (hr : 1 ≤ r) : Rch (SHT Lx Ry d r) (MW Lx Ry d r 0 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  unfold SHT MW
  rw [show m + 1 + 1 - 1 = m + 1 by omega, show e + 1 - 0 = e + 1 by omega]
  gR; gR; gL; gL
  refine Rch.tr (PPM.find2 1 e _ _) ?_
  gR; fin

/-- r = 0: m = d is prime -/
theorem tail_zero (Lx Ry : Strm) (d : Nat) : Rch (SHT Lx Ry d 0) (CP Lx Ry d) := by
  unfold SHT CP; gR; gR; gL; fin

/-! ## testing one number -/

/-- `(x + 1) % d` from `x % d` -/
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

theorem add_mod_self_left' (d x : Nat) : (d + x) % d = x % d := by
  rw [Nat.add_comm]; exact Nat.add_mod_right x d

/-- the mod walk after `j` of its `r` steps -/
theorem mw_upto (Lx Ry : Strm) (d r : Nat) (hd : 1 ≤ d) :
    ∀ j, 1 ≤ j → j ≤ r → Rch (MW Lx Ry d r 0 1) (MW Lx Ry d r ((j - 1) % d) j) := by
  intro j hj hjr
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Nat.zero_mod]; fin
    refine Rch.tr (ih hj0 (by omega)) ?_
    have := mw_step Lx Ry d r ((j - 1) % d) j (Nat.mod_lt _ (by omega)) hj0 (by omega)
    have ms := mod_succ (j - 1) d
    rw [show j - 1 + 1 = j by omega] at ms
    rw [show j + 1 - 1 = j by omega]
    by_cases hw : (j - 1) % d + 1 < d
    · rw [ms.1 hw]; rw [Nat.mod_eq_of_lt hw] at this; exact this
    · have h2 : (j - 1) % d + 1 = d := by have := Nat.mod_lt (j - 1) (show d > 0 by omega); omega
      rw [ms.2 h2]; rw [h2, Nat.mod_self] at this; exact this

/-- trial division of `m = d + r` by `d, d+1, …`, no divisor below `d` -/
theorem test (Lx Ry : Strm) : ∀ r d, 2 ≤ d →
    (∀ e, 2 ≤ e → e < d → (d + r) % e ≠ 0) →
    (TinyCryptids.Prime (d + r) → Rch (SHT Lx Ry d r) (CP Lx Ry (d + r))) ∧
    (¬ TinyCryptids.Prime (d + r) → ∃ d' r', d' + r' = d + r ∧ 2 ≤ d' ∧
      Rch (SHT Lx Ry d r) (CK Lx Ry d' r')) := by
  intro r
  induction r with
  | zero =>
    intro d hd hno
    refine ⟨fun _ => tail_zero _ _ d, fun hp => ?_⟩
    exact absurd ⟨hd, fun e h1 h2 => hno e h2 h1⟩ hp
  | succ r ih =>
    intro d hd hno
    have walk := Rch.tr (tail_more Lx Ry d (r + 1) (by omega) (by omega))
      (mw_upto Lx Ry d (r + 1) (by omega) (r + 1) (by omega) (Nat.le_refl _))
    rw [show r + 1 - 1 = r by omega] at walk
    have ms := mod_succ r d
    have hlt := Nat.mod_lt r (show d > 0 by omega)
    by_cases hw : r % d + 1 < d
    · -- d does not divide m: shift and go on with d + 1
      have hnd : (d + (r + 1)) % d ≠ 0 := by rw [add_mod_self_left', ms.1 hw]; omega
      have step := Rch.tr walk (Rch.tr (mw_last_nodiv Lx Ry d (r + 1) _ (by omega) hw)
        (shift Lx Ry d (r + 1) (by omega)))
      rw [show r + 1 - 1 = r by omega] at step
      have := ih (d + 1) (by omega) (fun e h1 h2 => by
        rw [show d + 1 + r = d + (r + 1) by omega]
        rcases Nat.lt_or_ge e d with h | h
        · exact hno e h1 h
        · rw [show e = d by omega]; exact hnd)
      rw [show d + 1 + r = d + (r + 1) by omega] at this
      exact ⟨fun hp => Rch.tr step (this.1 hp), fun hp => by
        obtain ⟨d', r', h1, h2, h3⟩ := this.2 hp
        exact ⟨d', r', h1, h2, Rch.tr step h3⟩⟩
    · -- d divides m: composite
      have h2 : r % d + 1 = d := by omega
      have hdv : (d + (r + 1)) % d = 0 := by rw [add_mod_self_left', ms.2 h2]
      rw [show r % d = d - 1 by omega] at walk
      have st := Rch.tr walk (mw_last_div Lx Ry d (r + 1) (by omega) (by omega))
      refine ⟨fun hp => absurd hdv (hp.2 d (by omega) hd), fun _ => ⟨d, r + 1, rfl, hd, st⟩⟩

end TM.Andrica
