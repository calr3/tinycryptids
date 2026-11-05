import TinyCryptids.Core.Routines
import TinyCryptids.HardyLittlewood2.Tac
import TinyCryptids.Defs

/-!
# Trial division (the mod walk of `legendre/`) 

Tape (`F` = blank): the region `D 00 R` at the right end, as in `sierpinski/`.

* `D` : `d + 2` cells, the trial divisor `d`, with a hole at cell `c + 1`;
* `R` : `r + 2` cells, `r = P - d`, during the mod walk with a hole at cell `j`.

Configurations take the contents left of D's separator as a stream `X`
(nearest cell first).
-/

namespace TM.HardyLittlewood2
open St TinyCryptids

local notation "F" => false

theorem add_mod_self_left' (d x : Nat) : (d + x) % d = x % d := by
  rw [Nat.add_comm]; exact Nat.add_mod_right x d

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

/-! ## trial division -/

/-- trial division of `P = d + r + 1` by `d, d+1, …`, from the walk with `r + 1` steps;
no divisor below `d` -/
theorem test (X : Strm) : ∀ r d, 3 ≤ d →
    (∀ e, 2 ≤ e → e < d → (d + r + 1) % e ≠ 0) →
    (Prime (d + r + 1) → Rch (MW X d (r + 1) 0 1) (P6 X (d + r + 1))) ∧
    (¬ Prime (d + r + 1) → ∃ d' r', d' + r' = d + r + 1 ∧ 3 ≤ d' ∧ 1 ≤ r' ∧
      Rch (MW X d (r + 1) 0 1) (MW X d' r' (d' - 1) r')) := by
  intro r
  induction r with
  | zero =>
    intro d hd hno
    have st := Rch.tr (mw_last_nodiv X d 1 0 (Nat.le_refl _) (by omega))
      (Rch.tr (shift X d 1 (Nat.le_refl _)) (tail_zero X (d + 1)))
    have hp : Prime (d + 0 + 1) := ⟨by omega, fun e h1 h2 => by
      rcases Nat.lt_or_ge e d with h | h
      · exact hno e h2 h
      · rw [show e = d by omega, show d + 0 + 1 = d + 1 by omega, add_mod_self_left',
          Nat.mod_eq_of_lt (by omega)]
        omega⟩
    exact ⟨fun _ => st, fun hnp => absurd hp hnp⟩
  | succ r ih =>
    intro d hd hno
    have walk := mw_upto X d (r + 2) (by omega) (r + 2) (by omega) (Nat.le_refl _)
    rw [show r + 2 - 1 = r + 1 by omega] at walk
    have ms := mod_succ (r + 1) d
    have hlt := Nat.mod_lt (r + 1) (show d > 0 by omega)
    by_cases hw : (r + 1) % d + 1 < d
    · have hnd : (d + (r + 1) + 1) % d ≠ 0 := by
        rw [Nat.add_assoc, add_mod_self_left', ms.1 hw]; omega
      have step := Rch.tr walk (Rch.tr (mw_last_nodiv _ d (r + 2) _ (by omega) hw)
        (Rch.tr (shift _ d (r + 2) (by omega)) (tail_more _ (d + 1) (r + 2 - 1) (by omega) (by omega))))
      rw [show r + 2 - 1 = r + 1 by omega] at step
      have := ih (d + 1) (by omega) (fun e h1 h2 => by
        rw [show d + 1 + r + 1 = d + (r + 1) + 1 by omega]
        rcases Nat.lt_or_ge e d with h | h
        · exact hno e h1 h
        · rw [show e = d by omega]; exact hnd)
      rw [show d + 1 + r + 1 = d + (r + 1) + 1 by omega] at this
      exact ⟨fun hp => Rch.tr step (this.1 hp), fun hp => by
        obtain ⟨d', r', h1, h2, h3, h4⟩ := this.2 hp
        exact ⟨d', r', h1, h2, h3, Rch.tr step h4⟩⟩
    · have h2 : (r + 1) % d + 1 = d := by omega
      have hdv : (d + (r + 1) + 1) % d = 0 := by rw [Nat.add_assoc, add_mod_self_left', ms.2 h2]
      rw [show (r + 1) % d = d - 1 by omega] at walk
      refine ⟨fun hp => absurd hdv (hp.2 d (by omega) (by omega)),
        fun _ => ⟨d, r + 2, by omega, hd, by omega, walk⟩⟩

end TM.HardyLittlewood2
