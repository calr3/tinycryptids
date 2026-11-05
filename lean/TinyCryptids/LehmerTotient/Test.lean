import TinyCryptids.Core.Routines
import TinyCryptids.LehmerTotient.Walk

/-!
# Trial division on a pair `D 00 R`

`../legendre`'s mod walk and shift, stated for a pair anywhere on the tape:

* `D` : `d + 2` cells (`1`, the hole at cell `c + 1`, `d` more cells), the trial divisor `d`;
* `R` : `r + 2` cells; `m = d + r` is the number tested;
* left of D's cell 0 there is a `0` and then `Lx`; right of R a `0` and then `Ry`.

Here the pair is `D 00 P` with `d = φ(n)`, `r = n - 1 - φ(n)`, and one mod walk tests `d ∣ r`:
the machine halts if so (`mw_last_div`), else the walk ends at `A` (`ND`, `mw_last_nodiv`).
-/

namespace TM.LehmerTotient

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

/-- head on cell 0 of R (no hole); D has its hole at cell 1 -/
def SHT (Lx Ry : Strm) (d r : Nat) : Cfg St :=
  ⟨sh4, F ::: F ::: ones d (F ::: true ::: F ::: Lx), ones (r + 2) (F ::: Ry)⟩

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

/-- not a divisor: `A` on cell `c + 1`, the D hole on cell `c + 2`, P without a hole -/
def ND (Lx Ry : Strm) (d r c : Nat) : Cfg St :=
  ⟨A, ones (c + 1) (F ::: Lx), true ::: F ::: ones (d - c - 1) (F ::: F ::: ones (r + 2) (F ::: Ry))⟩

/-- last step of the mod walk, residue not 0: d does not divide r -/
theorem mw_last_nodiv (Lx Ry : Strm) (d r c : Nat) (hr : 1 ≤ r) (hw : c + 1 < d) :
    Rch (MW Lx Ry d r c r) (ND Lx Ry d r c) := by
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, d = c + k + 2 := ⟨d - c - 2, by omega⟩
  unfold MW ND
  rw [show c + k + 2 - c = k + 2 by omega, show b + 1 + 1 - (b + 1) = 1 by omega,
    show k + 2 - 1 = k + 1 by omega]
  refine Rch.tr (Dma.nowrap c k _ _) ?_
  refine Rch.tr (PPR.find2 (k + 1) b _ (F ::: Ry)) ?_
  gL; gR; gR; gL
  refine Rch.tr (PPK.find2 (b + 3) k _ _) ?_
  gL; gR; fin

/-- last step of the mod walk, residue 0: d divides r, the machine halts -/
theorem mw_last_div (Lx Ry : Strm) (d r : Nat) (hr : 1 ≤ r) (hd : 1 ≤ d) :
    HaltAt (MW Lx Ry d r (d - 1) r) := by
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  unfold MW HaltAt
  rw [show c + 1 - 1 = c by omega, show c + 1 - c = 1 by omega, show b + 1 + 1 - (b + 1) = 1 by omega]
  apply Exists.intro; apply Exists.intro
  refine Rch.tr (Dma.toDW.wrap (c + 1) Lx _) ?_
  refine Rch.tr (PPR.find2 (c + 1) b _ (F ::: Ry)) ?_
  gL; gR; gR; gL
  refine Rch.tr (PPK.find2 (b + 3) c _ _) ?_
  gL; gL; fin

/-- r ≥ 1: make the R hole and start the mod walk with d -/
theorem tail_more (Lx Ry : Strm) (d r : Nat) (hd : 1 ≤ d) (hr : 1 ≤ r) : Rch (SHT Lx Ry d r) (MW Lx Ry d r 0 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  unfold SHT MW
  rw [show m + 1 + 1 - 1 = m + 1 by omega, show e + 1 - 0 = e + 1 by omega]
  gR; gR; gL; gL
  refine Rch.tr (PPM.find2 1 e _ _) ?_
  gR; fin

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

/-- one mod walk: `d ∣ r` halts, else `ND` -/
theorem one_test (Lx Ry : Strm) (d r : Nat) (hd : 2 ≤ d) (hr : 1 ≤ r) :
    (r % d = 0 → HaltAt (SHT Lx Ry d r)) ∧
    (r % d ≠ 0 → Rch (SHT Lx Ry d r) (ND Lx Ry d r ((r - 1) % d))) := by
  have walk := Rch.tr (tail_more Lx Ry d r (by omega) hr) (mw_upto Lx Ry d r (by omega) r hr (Nat.le_refl _))
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  rw [show b + 1 - 1 = b by omega] at walk ⊢
  have ms := mod_succ b d
  have hlt := Nat.mod_lt b (show d > 0 by omega)
  constructor
  · intro h0
    have h2 : b % d + 1 = d := by
      rcases Nat.lt_or_ge (b % d + 1) d with h | h
      · rw [ms.1 h] at h0; omega
      · omega
    rw [show b % d = d - 1 by omega] at walk
    exact HaltAt.back walk (mw_last_div Lx Ry d (b + 1) hr (by omega))
  · intro h0
    have hw : b % d + 1 < d := by
      rcases Nat.lt_or_ge (b % d + 1) d with h | h
      · exact h
      · exact absurd (ms.2 (by omega)) h0
    exact Rch.tr walk (mw_last_nodiv Lx Ry d (b + 1) _ hr hw)

end TM.LehmerTotient
