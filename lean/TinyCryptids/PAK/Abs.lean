import TinyCryptids.PAK.Nodes
import TinyCryptids.PA.Abs

/-!
# The subroutines on the abstract registers

Between subroutines the scratch registers are zero and `wffstack` is a stack: `TM.PA.A` and
its embedding `A.emb` (`PA/Abs.lean`).  Each subroutine node maps `A.emb a` to `A.emb` of the
operation of `PA/Abs.lean` (`*_emb`), as in the 2-symbol machine: `push`, `par1` … `par3`,
`cons`, `select`, `drop`, the reload, the zeroing and decoding steps, B6a's check (in two
parts: `b6pre`, then `scratch1 → param1`), and the halt test.  `run_ch` steps a run of slots
over a child whose denotation is known.
-/

namespace TMK.PA

open TM.PA (R A enc pair unpair tri nextN nextP)

/-! ## stepping a run of slots -/

theorem run_ch {c : Nat} {g : Den} {l : List SS} {x y : R} (h : g x = (.brk 0, y)) :
    runS (.ch c g :: l) x = runS l y := by
  simp only [runS, h, if_true]

theorem run_incT (l : List SS) (a : A) : runS (.op (.inc 2) :: l) a.emb = runS l (A.incT a).emb := rfl

theorem den_nil (x : R) : den [] x = (.brk 0, x) := rfl

/-- the last slot, a child that halts or is done -/
theorem run_last_h {c : Nat} {g : Den} {x y : R} {b : Prop} [Decidable b]
    (h : g x = (if b then .halt else .brk 0, y)) :
    runS [.ch c g] x = (.exit (if b then .halt else .brk 0), y) := by
  by_cases hb : b <;> simp [runS, h, hb, chOut]

/-! ## the moving loops, closed forms -/

theorem pairF_eq (s : R) : pairF s = { s with top := 0, s1 := s.s1 + tri s.top } := rfl

/-- `pair(scratch1, wffstack, topwff)`: scratch1 += pair(wffstack, topwff) -/
theorem d21_eq (s : R) : d21 s = (.brk 0, { s with ws := 0, top := 0, s1 := s.s1 + pair s.ws s.top }) := by
  simp only [d21, d22, pairF, TM.PA.R.set, TM.PA.R.get, pair]
  congr 2
  rw [Nat.add_comm s.top s.ws]; omega

theorem unp_emb (a : A) :
    unpF33 a.emb = { a.emb with ws := 0, s2 := (unpair (enc a.base a.stk)).1, s1 := (unpair (enc a.base a.stk)).2 } := by
  simp only [unpF33, A.emb, TM.PA.R.get, TM.PA.R.set, TM.PA.nextN_eq]
  simp [TM.PA.pair, TM.PA.tri]

/-! ## push and the parameters -/

theorem push_emb (a : A) : d20 a.emb = (.brk 0, (A.push a).emb) := by
  simp only [d20, den, runS, d21_eq, d25, if_true]
  simp [A.emb, A.push, enc, TM.PA.R.set, TM.PA.R.get]

theorem par1_emb (a : A) : d26 a.emb = (.brk 0, (A.par1 a).emb) := by
  simp only [d26, den, runS, push_emb, d27, d16, if_true]
  simp [A.emb, A.push, A.par1, TM.PA.R.set, TM.PA.R.get]

theorem par2_emb (a : A) : d46 a.emb = (.brk 0, (A.par2 a).emb) := by
  simp only [d46, den, runS, push_emb, d47, d18, if_true]
  simp [A.emb, A.push, A.par2, TM.PA.R.set, TM.PA.R.get]

theorem par3_emb (a : A) : d52 a.emb = (.brk 0, (A.par3 a).emb) := by
  simp only [d52, den, runS, push_emb, d53, d19, if_true]
  simp [A.emb, A.push, A.par3, TM.PA.R.set, TM.PA.R.get]

/-! ## the stack -/

theorem cons_emb (a : A) : d32 a.emb = (.brk 0, (A.cons a).emb) := by
  simp only [d32, d33, den, runS, d25, d21_eq, d36, if_true]
  rw [unp_emb, A.unpair_enc]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := A.pop_fields a
  simp [A.emb, A.cons, TM.PA.R.set, TM.PA.R.get, h1, h2, h3, h4, h5, h6, h7]

/-- pop the stack into `scratch1` (`un(wffstack)`, then `scratch2 → wffstack`) -/
theorem pop_emb (a : A) : d41 a.emb = (.brk 0, { (A.pop a).2.emb with s1 := (A.pop a).1 }) := by
  simp only [d41, d33, den, runS, if_true]
  rw [unp_emb, A.unpair_enc]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := A.pop_fields a
  simp [A.emb, TM.PA.R.set, TM.PA.R.get, h1, h2, h3, h4, h5, h6, h7]

theorem select_emb (a : A) : d40 a.emb = (.brk 0, (A.select a).emb) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := A.pop_fields a
  simp only [d40, den, runS, pop_emb, if_true]
  by_cases h0 : a.ac = 0
  · simp [d42, d43, d44, d45, d36, den, runS, A.emb, A.select, TM.PA.R.set, TM.PA.R.get,
      TM.PA.R.dec, h0, h1, h2, h3, h4, h5, h6, h7]
  · simp [d42, d43, d44, d45, d36, den, runS, chOut, A.emb, A.select, TM.PA.R.set,
      TM.PA.R.get, TM.PA.R.dec, h0, h1, h2, h3, h4, h5, h6, h7]

theorem drop_emb (a : A) : d82 a.emb = (.brk 0, (A.drop a).emb) := by
  simp only [d82, den, runS, pop_emb, if_true]
  simp [d44, A.emb, A.drop, TM.PA.R.set]

/-! ## the reload and the decoding -/

theorem reload_emb (a : A) : d2 a.emb = (.brk 0, (A.reload a).emb) := by
  by_cases h0 : a.pl = 0
  · simp [d2, d3, d4, d6, d7, den, runS, A.emb, A.reload, TM.PA.R.set, TM.PA.R.get, TM.PA.R.inc, h0]
  · simp [d2, d3, den, runS, chOut, A.emb, A.reload, TM.PA.R.set, TM.PA.R.get, TM.PA.R.dec, h0]

theorem zeroAc_emb (a : A) : d8 a.emb = (.brk 0, (A.zeroAc a).emb) := rfl
theorem zeroP1_emb (a : A) : d9 a.emb = (.brk 0, (A.zeroP1 a).emb) := rfl
theorem zeroP3_emb (a : A) : d10 a.emb = (.brk 0, (A.zeroP3 a).emb) := rfl

/-- `prooflist` unpaired: the rest in `prooflist`, the component in `scratch1` -/
def unpl (a : A) : R := { a.emb with pl := (unpair a.pl).1, s1 := (unpair a.pl).2 }

theorem dec_emb (a : A) : d11 a.emb = (.brk 0, unpl a) := by
  simp [d11, d12, d7, unpF12, den, runS, A.emb, unpl, TM.PA.R.set, TM.PA.R.get, TM.PA.nextN_eq,
    TM.PA.pair, TM.PA.tri]

theorem decAc_emb (a : A) : d15 (unpl a) = (.brk 0, (A.decAc a).emb) := by
  simp [d15, unpl, A.emb, A.decAc, TM.PA.R.set, TM.PA.R.get]
theorem decP1_emb (a : A) : d16 (unpl a) = (.brk 0, (A.decP1 a).emb) := by
  simp [d16, unpl, A.emb, A.decP1, TM.PA.R.set, TM.PA.R.get]
theorem decP2_emb (a : A) : d18 (unpl a) = (.brk 0, (A.decP2 a).emb) := by
  simp [d18, unpl, A.emb, A.decP2, TM.PA.R.set, TM.PA.R.get]
theorem decP3_emb (a : A) : d19 (unpl a) = (.brk 0, (A.decP3 a).emb) := by
  simp [d19, unpl, A.emb, A.decP3, TM.PA.R.set, TM.PA.R.get]

/-! ## `if_eq` and B6a's check -/

/-- `if_eq(param2, scratch2, eqbody)`: both zeroed; if they were equal, `topwff := param1` -/
theorem d74_eq (s : R) :
    d74 s = (.brk 0, { s with p2 := 0, s2 := 0, top := if s.p2 = s.s2 then s.p1 else s.top, p1 := if s.p2 = s.s2 then 0 else s.p1 }) := by
  by_cases hle : s.p2 ≤ s.s2
  · by_cases heq : s.p2 = s.s2
    · simp [d74, d75, d78, d79, d45, lsO, lsF, den, runS, hle, heq, TM.PA.R.set, TM.PA.R.get]
    · have : s.s2 - s.p2 ≠ 0 := by omega
      simp [d74, d75, d78, d79, den, runS, chOut, lsO, lsF, hle, heq, this, TM.PA.R.set, TM.PA.R.get,
        TM.PA.R.dec]
  · have heq : s.p2 ≠ s.s2 := by omega
    simp [d74, d75, den, runS, chOut, lsO, lsF, hle, heq]

/-- B6a's check up to its last loop: `scratch1` holds `param1` -/
def b6pre (a : A) : R :=
  { a.emb with p1 := 0, p2 := 0, p3 := 0, top := if a.p2 = a.p3 ∨ a.p3 = a.p1 then 0 else a.top, s1 := a.p1 }

theorem b6pre_run (a : A) (l : List SS) :
    runS (.ch 72 d72 :: .ch 73 d73 :: .ch 74 d74 :: .ch 18 d18 :: .ch 72 d72 :: .ch 74 d74 :: l) a.emb =
      runS l (b6pre a) := by
  simp only [runS, d72, d73, d18, d74_eq, if_true]
  congr 1
  by_cases h1 : a.p2 = a.p3 <;> by_cases h2 : a.p3 = a.p1 <;>
    simp [b6pre, A.emb, TM.PA.R.set, TM.PA.R.get, h1, h2]

theorem b6check_emb (a : A) : d16 (b6pre a) = (.brk 0, (A.b6check a).emb) := by
  simp [d16, b6pre, A.emb, A.b6check, TM.PA.R.set, TM.PA.R.get]

/-- DET's comparison: `topwff → scratch2`, then `if_eq(param2, scratch2, eqbody)` -/
theorem detCmp_run (b : A) (l : List SS) :
    runS (.ch 84 d84 :: .ch 74 d74 :: l) b.emb = runS l (A.detCmp b).emb := by
  simp only [runS, d84, d74_eq, if_true]
  congr 1
  by_cases h : b.p2 = b.top <;> simp [A.emb, A.detCmp, TM.PA.R.set, TM.PA.R.get, h]

/-! ## the halt test -/

theorem halt_run (a : A) :
    runS [.op (.dec 2), .ch 85 d85] a.emb = (.exit (if a.top = 1 then .halt else .brk 0), (A.haltT a).emb) := by
  by_cases h0 : a.top = 0
  · simp [runS, A.emb, A.haltT, h0, TM.PA.R.get]
  · by_cases h1 : a.top = 1
    · simp [runS, d85, d86, den, chOut, A.emb, A.haltT, h1, TM.PA.R.get, TM.PA.R.dec, TM.PA.R.set]
    · have h2 : a.top - 1 ≠ 0 := by omega
      simp [runS, d85, d86, den, chOut, A.emb, A.haltT, h0, h1, h2, TM.PA.R.get, TM.PA.R.dec,
        TM.PA.R.set, TM.PA.R.inc]
      omega

end TMK.PA
