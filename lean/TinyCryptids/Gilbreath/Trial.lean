import TinyCryptids.Core.Routines
import TinyCryptids.Gilbreath.Tac
import TinyCryptids.Gilbreath.Spec

/-!
# Trial division (the routines of `../legendre`)

The right end of the tape is `D 00 R`: `D` (`d + 2` cells, the trial divisor `d`, hole at
cell `c + 1`), `R` (`r + 2` cells, `r = m - d`, during the mod walk with a hole at cell `j`).
Configurations take the contents left of D's separator as a stream `X` (nearest cell first).
The proofs are those of `TM.Legendre` (`../Legendre/Round.lean`, `../Legendre/Main.lean`);
only the exits differ: a composite `m` leaves in `gZ1`, a prime one in `nP`.
-/

namespace TM.Gilbreath
open St TinyCryptids

local notation "F" => false

theorem Dma : Dadv delta ma1 ma2 ma3 ma4 maw1 maw2 maw3 PR1 PR1 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
theorem PPR : ParserR delta PR1 PR2 := by constructor <;> rfl
theorem PPM : ParserL delta PM1 PM2 := by constructor <;> rfl
theorem PPK : ParserL delta PK1 PK2 := by constructor <;> rfl
theorem PPC : ParserL delta PC1 PC2 := by constructor <;> rfl

/-- mod walk: about to advance the D hole (residue `c`); the R hole is at `j` -/
def MW (X : Strm) (d r c j : Nat) : Cfg St :=
  ⟨ma1, ones (c + 1) (F ::: F ::: X), F ::: ones (d - c) (F ::: F ::: ones j (F ::: ones (r + 1 - j) blank))⟩

/-- not a divisor: hole at cell 1, head on cell 2, about to shift -/
def SH (X : Strm) (d r : Nat) : Cfg St := ⟨sh1, F ::: ones 1 (F ::: F ::: X), ones d (F ::: F ::: ones (r + 2) blank)⟩

/-- head on cell 0 of R (no hole); D has its hole at cell 1 -/
def SHT (X : Strm) (d r : Nat) : Cfg St :=
  ⟨sh4, F ::: F ::: ones d (F ::: true ::: F ::: F ::: X), ones (r + 2) blank⟩

/-- composite: the head two cells left of D, entering the finder to G -/
def CP (X : Strm) (d r : Nat) : Cfg St :=
  cfgL gZ1 (F ::: X) (F ::: true ::: F ::: ones d (F ::: F ::: ones (r + 2) blank))

/-- prime (`d = m`, `r = 0`): the head left of D, entering the finder to G -/
def PX (X : Strm) (d : Nat) : Cfg St :=
  cfgL nP (F ::: F ::: X) (true ::: F ::: ones d (F ::: F ::: ones 2 blank))

theorem ones_cons_blank (s : Nat) : ones s (true ::: blank) = ones (s + 1) blank := (ones_succ' s blank).symm

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
theorem mw_last_div (X : Strm) (d r : Nat) (hr : 1 ≤ r) (hd : 1 ≤ d) :
    Rch (MW X d r (d - 1) r) (CP X d r) := by
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  unfold MW CP
  rw [show c + 1 - 1 = c by omega, show c + 1 - c = 1 by omega, show b + 1 + 1 - (b + 1) = 1 by omega]
  refine Rch.tr (Dma.toDW.wrap (c + 1) (F ::: X) _) ?_
  refine Rch.tr (PPR.find2 (c + 1) b _ blank) ?_
  gL; gR; gR; refine blankR ?_; gL
  refine Rch.tr (PPK.find2 (b + 3) c _ _) ?_
  gL; gL
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

/-- r = 0: m is prime; past D's hole -/
theorem prime_exit (X : Strm) (d : Nat) (hd : 1 ≤ d) : Rch (P6 X d) (PX X d) := by
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  unfold P6 PX
  refine blankR ?_; gL
  refine Rch.tr (PPC.find2 2 c _ _) ?_
  gL
  rw [cons_blank]; fin

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

/-- trial division of `m = d + r` by `d, d+1, …`, no divisor below `d` -/
theorem test (X : Strm) : ∀ r d, 2 ≤ d →
    (∀ e, 2 ≤ e → e < d → (d + r) % e ≠ 0) →
    (Prime (d + r) → Rch (SHT X d r) (PX X (d + r))) ∧
    (¬ Prime (d + r) → ∃ d' r', d' + r' = d + r ∧ 2 ≤ d' ∧ Rch (SHT X d r) (CP X d' r')) := by
  intro r
  induction r with
  | zero =>
    intro d hd hno
    refine ⟨fun _ => Rch.tr (tail_zero _ d) (prime_exit X d (by omega)), fun hp => ?_⟩
    exact absurd ⟨hd, fun e h1 h2 => hno e h2 h1⟩ hp
  | succ r ih =>
    intro d hd hno
    have walk := Rch.tr (tail_more X d (r + 1) (by omega) (by omega))
      (mw_upto _ d (r + 1) (by omega) (r + 1) (by omega) (Nat.le_refl _))
    rw [show r + 1 - 1 = r by omega] at walk
    have ms := mod_succ r d
    have hlt := Nat.mod_lt r (show d > 0 by omega)
    by_cases hw : r % d + 1 < d
    · have hnd : (d + (r + 1)) % d ≠ 0 := by rw [add_mod_self_left', ms.1 hw]; omega
      have step := Rch.tr walk (Rch.tr (mw_last_nodiv _ d (r + 1) _ (by omega) hw)
        (shift _ d (r + 1) (by omega)))
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
    · have h2 : r % d + 1 = d := by omega
      have hdv : (d + (r + 1)) % d = 0 := by rw [add_mod_self_left', ms.2 h2]
      rw [show r % d = d - 1 by omega] at walk
      have st := Rch.tr walk (mw_last_div X d (r + 1) (by omega) (by omega))
      refine ⟨fun hp => absurd hdv (hp.2 d (by omega) hd), fun _ => ⟨d, r + 1, rfl, hd, st⟩⟩

/-- the candidate `m ≥ 2`: prime, or composite with some `d + r = m` -/
theorem cand (X : Strm) (m : Nat) (hm : 2 ≤ m) :
    (Prime m → Rch (SHT X 2 (m - 2)) (PX X m)) ∧
    (¬ Prime m → ∃ d r, d + r = m ∧ 2 ≤ d ∧ Rch (SHT X 2 (m - 2)) (CP X d r)) := by
  have t := test X (m - 2) 2 (Nat.le_refl _) (fun e h1 h2 => by omega)
  rw [show 2 + (m - 2) = m by omega] at t
  exact t

end TM.Gilbreath
