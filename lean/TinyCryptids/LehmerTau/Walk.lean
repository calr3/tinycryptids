import TinyCryptids.Core.Routines
import TinyCryptids.LehmerTau.Tac

/-!
# The frame engine: the mod walk of `legendre/` on a frame `X 00 R`

A frame is a block `X` (`x + 2` cells, a hole at cell `c + 1`: the residue `c`) and a block
`R` (`r + 2` cells; during the walk a cursor at cell `j`), with `x + r = s` fixed. The engine
visits the divisors of `s` in increasing order: at each one it stops in `DV` (state `k1` on
X's cell −1, X's hole at cell 1); after the divisor has been used the machine comes back in
`RS` and the engine goes on to the next one; after `x = s` it unshifts the frame to
`X = 1, R = s − 1` (`UN`, `unshift`).

`X` (left of X's separator) and `B` (right of R's separator) are the rest of the tape.
-/

namespace TM.LehmerTau
open St

local notation "F" => false

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

theorem add_mod_self_left' (d x : Nat) : (d + x) % d = x % d := by
  rw [Nat.add_comm]; exact Nat.add_mod_right x d

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

theorem Dwa : Dadv delta wa1 wa2 wa3 wa4 waw1 waw2 waw3 PRw1 PRw1 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
theorem PPRw : ParserR delta PRw1 PRw2 := ⟨rfl, rfl, rfl⟩
theorem PPMw : ParserL delta PMw1 PMw2 := ⟨rfl, rfl, rfl⟩
theorem PPKw : ParserL delta PKw1 PKw2 := ⟨rfl, rfl, rfl⟩
theorem PPDz : ParserL delta PDz1 PDz2 := ⟨rfl, rfl, rfl⟩
theorem PPSx : ParserL delta PSx1 PSx2 := ⟨rfl, rfl, rfl⟩

/-! ## configurations -/

/-- the rest of the tape right of R: its separator, then `B` -/
abbrev RB (r : Nat) (B : Strm) : Strm := ones (r + 2) (F ::: F ::: B)

/-- mod walk: head on X's hole (residue `c`); R's cursor at cell `j` -/
def MW (X B : Strm) (x r c j : Nat) : Cfg St :=
  ⟨wa1, ones (c + 1) (F ::: F ::: X), F ::: ones (x - c) (F ::: F ::: ones j (F ::: ones (r + 1 - j) (F ::: F ::: B)))⟩

/-- not a divisor: X's hole at cell 1, head on cell 2, about to shift -/
def SH (X B : Strm) (x r : Nat) : Cfg St := ⟨sh1, F ::: ones 1 (F ::: F ::: X), ones x (F ::: F ::: RB r B)⟩

/-- after a divisor: the same tape, about to go on -/
def RS (X B : Strm) (x r : Nat) : Cfg St := ⟨rsm, F ::: ones 1 (F ::: F ::: X), ones x (F ::: F ::: RB r B)⟩

/-- `x` divides `x + r`: state `k1` on X's cell −1 -/
def DV (X B : Strm) (x r : Nat) : Cfg St := ⟨k1, F ::: X, F ::: true ::: F ::: ones x (F ::: F ::: RB r B)⟩

/-! ## mod walk -/

theorem mw_step (X B : Strm) (d r c j : Nat) (hc : c < d) (hj1 : 1 ≤ j) (hj : j < r) :
    Rch (MW X B d r c j) (MW X B d r ((c + 1) % d) (j + 1)) := by
  obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, r = b + 1 + m + 1 := ⟨r - b - 2, by omega⟩
  unfold MW
  rw [show b + 1 + m + 1 + 1 - (b + 1) = m + 2 by omega,
      show b + 1 + m + 1 + 1 - (b + 1 + 1) = m + 1 by omega]
  by_cases hw : c + 1 < d
  · obtain ⟨k, rfl⟩ : ∃ k, d = c + k + 2 := ⟨d - c - 2, by omega⟩
    rw [Nat.mod_eq_of_lt hw, show c + k + 2 - c = k + 2 by omega,
        show c + k + 2 - (c + 1) = k + 1 by omega]
    refine Rch.tr (Dwa.nowrap c k _ _) ?_
    refine Rch.tr (PPRw.find2 (k + 1) b _ _) ?_
    gL; gR; gR; gL; gL
    refine Rch.tr (PPMw.find2 (b + 2) k _ _) ?_
    gR; fin
  · obtain rfl : d = c + 1 := by omega
    rw [Nat.mod_self, show c + 1 - c = 1 by omega, show c + 1 - 0 = c + 1 by omega]
    refine Rch.tr (Dwa.toDW.wrap (c + 1) (F ::: X) _) ?_
    refine Rch.tr (PPRw.find2 (c + 1) b _ _) ?_
    gL; gR; gR; gL; gL
    refine Rch.tr (PPMw.find2 (b + 2) c _ _) ?_
    gR; fin

/-- last step, the residue does not become 0 -/
theorem mw_last_nodiv (X B : Strm) (d r c : Nat) (hr : 1 ≤ r) (hw : c + 1 < d) :
    Rch (MW X B d r c r) (SH X B d r) := by
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, d = c + k + 2 := ⟨d - c - 2, by omega⟩
  unfold MW SH
  rw [show c + k + 2 - c = k + 2 by omega, show b + 1 + 1 - (b + 1) = 1 by omega]
  refine Rch.tr (Dwa.nowrap c k _ _) ?_
  refine Rch.tr (PPRw.find2 (k + 1) b _ _) ?_
  gL; gR; gR; gL
  refine Rch.tr (PPKw.find2 (b + 3) k _ _) ?_
  gL; gR; gR; gL
  sLn (c + 2); gR; gR; gR
  rw [← ones_succ, ones_add, show c + (k + 1 + 1) = c + k + 2 by omega]
  fin

/-- last step, the residue becomes 0: a divisor -/
theorem mw_last_div (X B : Strm) (d r : Nat) (hr : 1 ≤ r) (hd : 1 ≤ d) :
    Rch (MW X B d r (d - 1) r) (DV X B d r) := by
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  unfold MW DV
  rw [show c + 1 - 1 = c by omega, show c + 1 - c = 1 by omega, show b + 1 + 1 - (b + 1) = 1 by omega]
  refine Rch.tr (Dwa.toDW.wrap (c + 1) (F ::: X) _) ?_
  refine Rch.tr (PPRw.find2 (c + 1) b _ _) ?_
  gL; gR; gR; gL
  refine Rch.tr (PPKw.find2 (b + 3) c _ _) ?_
  gL; fin

/-- the walk after `j` of its `r` steps -/
theorem mw_upto (X B : Strm) (d r : Nat) (hd : 1 ≤ d) :
    ∀ j, 1 ≤ j → j ≤ r → Rch (MW X B d r 0 1) (MW X B d r ((j - 1) % d) j) := by
  intro j hj hjr
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Nat.zero_mod]; fin
    refine Rch.tr (ih hj0 (by omega)) ?_
    have := mw_step X B d r ((j - 1) % d) j (Nat.mod_lt _ (by omega)) hj0 (by omega)
    have ms := mod_succ (j - 1) d
    rw [show j - 1 + 1 = j by omega] at ms
    rw [show j + 1 - 1 = j by omega]
    by_cases hw : (j - 1) % d + 1 < d
    · rw [ms.1 hw]; rw [Nat.mod_eq_of_lt hw] at this; exact this
    · have h2 : (j - 1) % d + 1 = d := by have := Nat.mod_lt (j - 1) (show d > 0 by omega); omega
      rw [ms.2 h2]; rw [h2, Nat.mod_self] at this; exact this

/-! ## shift and resume -/

/-- shift `x += 1, r -= 1`; if `r` becomes 0 the new `x` divides, else the walk starts -/
theorem shift (X B : Strm) (d r : Nat) (hr : 1 ≤ r) :
    (r = 1 → Rch (SH X B d r) (DV X B (d + 1) 0)) ∧
    (2 ≤ r → Rch (SH X B d r) (MW X B (d + 1) (r - 1) 0 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  unfold SH
  constructor
  · intro h; obtain rfl : m = 0 := by omega
    unfold DV
    sRn d; gR; gR; gR; gR; gR; gL
    refine Rch.tr (PPDz.find2 2 d _ _) ?_
    gL; fin
  · intro h; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    unfold MW
    rw [show k + 1 + 1 - 1 = k + 1 by omega, show d + 1 - 0 = d + 1 by omega,
      show k + 1 + 1 - 1 = k + 1 by omega]
    sRn d; gR; gR; gR; gR; gR; gL; gL
    refine Rch.tr (PPMw.find2 1 d _ _) ?_
    gR; fin

/-- resume: `r = 0` ends the loop (`F2a` on R's cell 1), else shift -/
def F2 (X B : Strm) (x : Nat) : Cfg St :=
  ⟨F2a, true ::: F ::: F ::: ones x (F ::: true ::: F ::: F ::: X), true ::: F ::: F ::: B⟩

theorem resume_zero (X B : Strm) (x : Nat) : Rch (RS X B x 0) (F2 X B x) := by
  unfold RS F2 RB
  sRn x; gR; gR; gR; gR; gL; fin

theorem resume_more (X B : Strm) (x r : Nat) (hx : 1 ≤ x) (hr : 1 ≤ r) : Rch (RS X B x r) (SH X B x r) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  unfold RS SH RB
  sRn (y + 1); gR; gR; gR; gR; gL
  show Rch (cfgL PSx1 (ones 2 (F ::: F ::: ones (y + 1) (F ::: true ::: F ::: F ::: X))) _) _
  refine Rch.tr (PPSx.find2 2 y _ _) ?_
  gR; gR; fin

/-! ## the divisor loop -/

/-- from `SH x r` (x has been used), the next divisor of `x + r` -/
theorem next_div (X B : Strm) : ∀ r x, 1 ≤ x → 1 ≤ r →
    ∃ y, x < y ∧ y ≤ x + r ∧ (x + r) % y = 0 ∧ (∀ z, x < z → z < y → (x + r) % z ≠ 0) ∧
      Rch (SH X B x r) (DV X B y (x + r - y)) := by
  intro r
  induction r with
  | zero => intro x _ hr; omega
  | succ r ih =>
  intro x hx _
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨x + 1, by omega, by omega, Nat.mod_self _, fun z h1 h2 => by omega, ?_⟩
    rw [show x + 1 - (x + 1) = 0 by omega]; exact (shift X B x 1 (Nat.le_refl _)).1 rfl
  · have st := (shift X B x (r + 1) (by omega)).2 (by omega)
    rw [show r + 1 - 1 = r by omega] at st
    have walk := mw_upto X B (x + 1) r (by omega) r hr (Nat.le_refl _)
    have hlt := Nat.mod_lt (r - 1) (show x + 1 > 0 by omega)
    have ms := mod_succ (r - 1) (x + 1)
    rw [show r - 1 + 1 = r by omega] at ms
    have key : (x + (r + 1)) % (x + 1) = r % (x + 1) := by
      rw [show x + (r + 1) = (x + 1) + r by omega, add_mod_self_left']
    by_cases hw : (r - 1) % (x + 1) + 1 < x + 1
    · have hnd : (x + (r + 1)) % (x + 1) ≠ 0 := by rw [key, ms.1 hw]; omega
      have s2 := Rch.tr st (Rch.tr walk (mw_last_nodiv X B (x + 1) r _ hr hw))
      obtain ⟨y, h1, h2, h3, h4, h5⟩ := ih (x + 1) (by omega) hr
      rw [show x + 1 + r = x + (r + 1) by omega] at h2 h3 h4 h5
      refine ⟨y, by omega, h2, h3, fun z hz1 hz2 => ?_, Rch.tr s2 h5⟩
      rcases Nat.eq_or_lt_of_le (show x + 1 ≤ z by omega) with rfl | h
      · exact hnd
      · exact h4 z h hz2
    · have h2' : (r - 1) % (x + 1) + 1 = x + 1 := by omega
      rw [show (r - 1) % (x + 1) = x + 1 - 1 by omega] at walk
      have s2 := Rch.tr st (Rch.tr walk (mw_last_div X B (x + 1) r hr (by omega)))
      refine ⟨x + 1, by omega, by omega, by rw [key, ms.2 h2'], fun z h1 h2 => by omega, ?_⟩
      rw [show x + (r + 1) - (x + 1) = r by omega]; exact s2

/-! ## unshift: X(x) R(r) → X(1) R(x − 1 + r), filling X's hole -/

/-- unshift loop, head on X's last cell (state `U1`); X has its hole at cell 1 -/
def UN (X Rr : Strm) (x : Nat) : Cfg St :=
  ⟨U1, ones (x - 1) (F ::: true ::: F ::: F ::: X), true ::: F ::: F ::: Rr⟩

theorem F2_UN (X B : Strm) (x : Nat) (hx : 1 ≤ x) : Rch (F2 X B x) (UN X (ones 2 (F ::: F ::: B)) x) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  unfold F2 UN
  gL; gL; gL; gL
  rw [show y + 1 - 1 = y by omega]; fin

/-- the loop, ending on `Uv` on the cell two left of X's separator -/
theorem unshift (Y : Strm) : ∀ x Rr, 1 ≤ x →
    Rch (UN (true ::: Y) Rr x) (cfgL Uv Y (true ::: F ::: F ::: ones 3 (F ::: F ::: ones (x - 1) Rr))) := by
  intro x
  induction x with
  | zero => omega
  | succ x ih =>
    intro Rr hx
    rcases Nat.eq_zero_or_pos x with rfl | h
    · unfold UN; simp only [Nat.sub_self, ones_zero]
      gL; gL; gL; gL; gL; gL; fin
    · have := ih (true ::: Rr) h
      rw [← ones_succ', show x - 1 + 1 = x by omega] at this
      rw [show x + 1 - 1 = x by omega]
      refine Rch.tr ?_ this
      obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
      unfold UN
      rw [show y + 1 + 1 - 1 = y + 1 by omega, show y + 1 - 1 = y by omega]
      gL; gR; gR; gR; gL; gL; gL
      fin

end TM.LehmerTau
