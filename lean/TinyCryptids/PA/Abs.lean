import TinyCryptids.PA.Clean

/-!
# The registers between subroutines

Between the program's subroutines the scratch registers are zero and `wffstack` is a stack:
values pushed during this iteration (`stk`, top first) on a base (the stack the iteration
started with).  `A.emb` is that register file; each subroutine node maps `A.emb a` to
`A.emb` of a simple operation on `a` (`*_emb` lemmas).
-/

namespace TM.PA

/-- registers between subroutines -/
structure A where
  pl : Nat
  np : Nat
  top : Nat
  ac : Nat
  p1 : Nat
  p2 : Nat
  p3 : Nat
  base : Nat
  stk : List Nat

/-- the stack `xs` (top first) pushed on `base` -/
def enc (base : Nat) : List Nat → Nat
  | [] => base
  | x :: xs => pair (enc base xs) x

namespace A

def emb (a : A) : R := ⟨a.pl, a.np, a.top, enc a.base a.stk, a.ac, a.p1, a.p2, a.p3, 0, 0⟩

/-- the top of the stack and the rest (below the base: `unpair`) -/
def pop (a : A) : Nat × A :=
  match a.stk with
  | x :: st => (x, { a with stk := st })
  | [] => ((unpair a.base).snd, { a with base := (unpair a.base).fst })

theorem unpair_enc (a : A) :
    unpair (enc a.base a.stk) = (enc a.pop.snd.base a.pop.snd.stk, a.pop.fst) := by
  obtain ⟨pl, np, top, ac, p1, p2, p3, base, _ | ⟨x, st⟩⟩ := a
  · simp [pop, enc]
  · simp [pop, enc, unpair_pair]

theorem pop_fields (a : A) : a.pop.snd.pl = a.pl ∧ a.pop.snd.np = a.np ∧ a.pop.snd.top = a.top ∧
    a.pop.snd.ac = a.ac ∧ a.pop.snd.p1 = a.p1 ∧ a.pop.snd.p2 = a.p2 ∧ a.pop.snd.p3 = a.p3 := by
  obtain ⟨pl, np, top, ac, p1, p2, p3, base, _ | ⟨x, st⟩⟩ := a <;> simp [pop]

/-! ## the operations -/

def push (a : A) : A := { a with stk := a.top :: a.stk, top := 0 }
def incT (a : A) : A := { a with top := a.top + 1 }
def par1 (a : A) : A := { a with stk := a.top :: a.stk, top := a.p1 }
def par2 (a : A) : A := { a with stk := a.top :: a.stk, top := a.p2 }
def par3 (a : A) : A := { a with stk := a.top :: a.stk, top := a.p3 }
/-- `top := pair(x, top)` with `x` popped -/
def cons (a : A) : A := { a.pop.snd with top := pair a.pop.fst a.top }
/-- keep the candidate (`axiomcode` > 0, then decremented) or the popped selection -/
def select (a : A) : A := { a.pop.snd with ac := a.ac - 1, top := if a.ac = 0 then a.pop.fst else a.top }
def drop (a : A) : A := a.pop.snd
def pop3 (a : A) : A := { a.pop.snd with p3 := a.p3 + a.pop.fst }
def pop2 (a : A) : A := { a.pop.snd with p2 := a.p2 + a.pop.fst }
def reload (a : A) : A :=
  { a with pl := if a.pl = 0 then a.np else a.pl - 1, np := if a.pl = 0 then a.np + 1 else a.np }
def zeroAc (a : A) : A := { a with ac := 0 }
def zeroP1 (a : A) : A := { a with p1 := 0 }
def zeroP3 (a : A) : A := { a with p3 := 0 }
def decAc (a : A) : A := { a with pl := (unpair a.pl).fst, ac := a.ac + (unpair a.pl).snd }
def decP1 (a : A) : A := { a with pl := (unpair a.pl).fst, p1 := a.p1 + (unpair a.pl).snd }
def decP2 (a : A) : A := { a with pl := (unpair a.pl).fst, p2 := a.p2 + (unpair a.pl).snd }
def decP3 (a : A) : A := { a with pl := (unpair a.pl).fst, p3 := a.p3 + (unpair a.pl).snd }
/-- B6a's side condition: the candidate becomes `v0 = v0` (code 0) if `p3` is `p1` or `p2` -/
def b6check (a : A) : A :=
  { a with top := if a.p2 = a.p3 ∨ a.p3 = a.p1 then 0 else a.top, p2 := 0, p3 := 0 }
/-- DET's comparison: keep `p1` if the popped premise `p2` is `top` (= `q -> p1`), else 0 -/
def detCmp (a : A) : A :=
  { a with top := if a.p2 = a.top then a.p1 else 0, p1 := if a.p2 = a.top then 0 else a.p1, p2 := 0 }
def decAc1 (a : A) : A := { a with ac := a.ac - 1 }

end A

open N

/-! ## the register file of each operation -/

theorem emb_s1 (a : A) : a.emb.s1 = 0 := rfl
theorem emb_s2 (a : A) : a.emb.s2 = 0 := rfl

theorem push_emb (a : A) : f49 a.emb = (A.push a).emb := by
  simp [f49, f52_eq, f53_eq, A.emb, A.push, enc]

theorem push_emb' (a : A) : f46 a.emb = (A.push a).emb := push_emb a

theorem incT_emb (a : A) : a.emb.inc 2 = (A.incT a).emb := rfl

theorem par1_emb (a : A) : f138 a.emb = (A.par1 a).emb := by
  simp [f138, f142, f46, f147_eq, f29_eq, f49, f52_eq, f53_eq, A.emb, A.par1, enc]

theorem par2_emb (a : A) : f137 a.emb = (A.par2 a).emb := by
  simp [f137, f141, f46, f146_eq, f36_eq, f49, f52_eq, f53_eq, A.emb, A.par2, enc]

theorem par3_emb (a : A) : f59 a.emb = (A.par3 a).emb := by
  simp [f59, f65, f46, f73_eq, f41_eq, f49, f52_eq, f53_eq, A.emb, A.par3, enc]

theorem cons_emb (a : A) : f66 a.emb = (A.cons a).emb := by
  rw [f66_eq _ rfl rfl]
  have h := A.unpair_enc a
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := A.pop_fields a
  simp only [A.emb, A.cons, h, h1, h2, h3, h4, h5, h6, h7]

theorem select_emb (a : A) : f109 a.emb = (A.select a).emb := by
  rw [f109_eq _ rfl rfl]
  have h := A.unpair_enc a
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := A.pop_fields a
  simp only [A.emb, A.select, h, h1, h2, h3, h4, h5, h6, h7]

theorem drop_emb (a : A) : f220 a.emb = (A.drop a).emb := by
  simp only [f220, f112_eq a.emb rfl rfl, f123]
  have h := A.unpair_enc a
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := A.pop_fields a
  simp only [A.emb, A.drop, h, h1, h2, h3, h4, h5, h6, h7]

theorem pop3_emb (a : A) : f216 a.emb = (A.pop3 a).emb := by
  simp only [f216, f112_eq a.emb rfl rfl, f41_eq]
  have h := A.unpair_enc a
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := A.pop_fields a
  simp only [A.emb, A.pop3, h, h1, h2, h3, h4, h5, h6, h7]

theorem pop2_emb (a : A) : f221 a.emb = (A.pop2 a).emb := by
  simp only [f221, f112_eq a.emb rfl rfl, f36_eq]
  have h := A.unpair_enc a
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := A.pop_fields a
  simp only [A.emb, A.pop2, h, h1, h2, h3, h4, h5, h6, h7]

end TM.PA

namespace TM.PA

open N

/-- `if_eq(param2, scratch2, eqbody)`: both zeroed; if they were equal, `topwff := param1` -/
theorem f193_eq (s : R) :
    f193 s = { s with p2 := 0, s2 := 0, top := if s.p2 = s.s2 then s.p1 else s.top, p1 := if s.p2 = s.s2 then 0 else s.p1 } := by
  by_cases h : s.p2 ≤ s.s2
  · by_cases h' : s.p2 = s.s2
    · simp [f193, p195, f195, f196, p199, f199, f200, f204, f208, f205_eq, f120, h']
    · have : s.s2 - s.p2 ≠ 0 := by omega
      simp [f193, p195, f195, f196, p199, f199, f200, f204, f208, f205_eq, f120, h, h', this]
  · have h' : s.p2 ≠ s.s2 := by omega
    simp [f193, p195, f195, f196, p199, f199, f200, f204, f208, f205_eq, f120, h, h']

theorem reload_emb (a : A) : f1 a.emb = (A.reload a).emb := by
  simp only [f1, p3, f3, f4, f8, f13, f7_eq, f12_eq, f18_eq]
  by_cases h : a.pl = 0 <;> simp [h, A.emb, A.reload]

theorem zeroAc_emb (a : A) : f5 a.emb = (A.zeroAc a).emb := rfl
theorem zeroP1_emb (a : A) : f9 a.emb = (A.zeroP1 a).emb := rfl
theorem zeroP3_emb (a : A) : f14 a.emb = (A.zeroP3 a).emb := rfl

theorem f19_emb (a : A) :
    f19 a.emb = { a.emb with pl := (unpair a.pl).fst, s1 := (unpair a.pl).snd } := by
  simp [f19, f22_eq, f18_eq, A.emb]

theorem decAc_emb (a : A) : f23 (f19 a.emb) = (A.decAc a).emb := by
  rw [f19_emb]; simp [A.emb, A.decAc]
theorem decP1_emb (a : A) : f29 (f19 a.emb) = (A.decP1 a).emb := by
  rw [f19_emb]; simp [A.emb, A.decP1]
theorem decP2_emb (a : A) : f36 (f19 a.emb) = (A.decP2 a).emb := by
  rw [f19_emb]; simp [A.emb, A.decP2]
theorem decP3_emb (a : A) : f41 (f19 a.emb) = (A.decP3 a).emb := by
  rw [f19_emb]; simp [A.emb, A.decP3]

theorem b6check_emb (a : A) :
    f29 (f193 (f189 (f36 (f193 (f191 (f189 a.emb)))))) = (A.b6check a).emb := by
  simp only [f189_eq, f191_eq, f193_eq, f36_eq, f29_eq, A.emb, A.b6check]
  by_cases h1 : a.p2 = a.p3 <;> by_cases h2 : a.p3 = a.p1 <;> simp [h1, h2]

theorem detCmp_emb (a : A) : f224 a.emb = (A.drop (A.detCmp a)).emb := by
  simp only [f224, f227, f226_eq]
  rw [f193_eq]
  have := drop_emb (A.detCmp a)
  rw [← this]
  congr 1
  simp only [A.emb, A.detCmp]
  by_cases h : a.p2 = a.top <;> simp [h]

theorem dec4_emb (a : A) : a.emb.dec 4 = (A.decAc1 a).emb := rfl

theorem ite_emb (c : Prop) [Decidable c] (x y : A) : (if c then x.emb else y.emb) = (if c then x else y).emb := by
  by_cases h : c <;> simp [h]

end TM.PA

namespace TM.PA

open N

namespace A

def v2 (a : A) : A := a.push.incT.incT
def v4 (a : A) : A := a.v2.incT.incT
def wim (a : A) : A := a.cons.v2.cons
def wal (a : A) : A := a.cons.v4.cons

/-- GEN, when kept: the top theorem `q` popped into `p3`, `topwff := A. p1 q` -/
def gen (a : A) : A := if a.ac = 0 then a else a.decAc1.pop3.par1.par3.wal.drop

/-- DET, when kept: the next theorem `M` popped into `p2`; `topwff := p1` if `M = (p3 -> p1)` -/
def det (a : A) : A := if a.ac = 0 then a else a.decAc1.pop2.par3.par1.wim.detCmp.drop

/-- the halt test leaves `topwff` alone unless it is 1 (and then the machine halts) -/
def haltT (a : A) : A := if a.top = 1 then { a with top := 0 } else a

end A

theorem emb_get4 (a : A) : a.emb.get 4 = a.ac := rfl
theorem emb_get2 (a : A) : a.emb.get 2 = a.top := rfl

theorem gen_emb (a : A) : f211 a.emb = (A.gen a).emb := by
  simp only [f211, emb_get4, dec4_emb, f213, f217, f156, f54, f60, f67, f76, f61, f68,
    pop3_emb, par1_emb, par3_emb, cons_emb, push_emb', incT_emb, drop_emb, ite_emb]
  rfl

theorem det_emb (a : A) : f214 a.emb = (A.det a).emb := by
  simp only [f214, emb_get4, dec4_emb, f218, f222, f175, f134, f95, f98, f61, f68,
    pop2_emb, par1_emb, par3_emb, cons_emb, push_emb', incT_emb, detCmp_emb, ite_emb]
  rfl

theorem halt_emb (a : A) : f215 a.emb = (A.haltT a).emb ∧ h215 a.emb = decide (a.top = 1) := by
  constructor
  · simp only [f215, f219, f223, f225, f68, emb_get2]
    by_cases h : a.top = 0
    · simp [h, A.haltT]
    · by_cases h1 : a.top = 1
      · simp [h1, A.haltT, A.emb]
      · have : a.top - 1 ≠ 0 := by omega
        simp [h, h1, this, A.haltT, A.emb]; omega
  · simp only [h215, h219, p223, emb_get2]
    by_cases h : a.top = 0
    · simp [h]
    · by_cases h1 : a.top = 1
      · simp [h1, A.emb]
      · have : a.top - 1 ≠ 0 := by omega
        simp [h, h1, this, A.emb]

end TM.PA

namespace TM.PA

namespace A

/-! ## stack operations on a fixed register file: `ts a t st` is `a` with `topwff := t`
and the stack `st` -/

def ts (a : A) (t : Nat) (st : List Nat) : A := { a with top := t, stk := st }

theorem push_a (a : A) : a.push = a.ts 0 (a.top :: a.stk) := rfl
theorem par1_a (a : A) : a.par1 = a.ts a.p1 (a.top :: a.stk) := rfl
theorem par2_a (a : A) : a.par2 = a.ts a.p2 (a.top :: a.stk) := rfl
theorem par3_a (a : A) : a.par3 = a.ts a.p3 (a.top :: a.stk) := rfl
theorem push_ts (a : A) (t : Nat) (st : List Nat) : (a.ts t st).push = a.ts 0 (t :: st) := rfl
theorem incT_ts (a : A) (t : Nat) (st : List Nat) : (a.ts t st).incT = a.ts (t + 1) st := rfl
theorem par1_ts (a : A) (t : Nat) (st : List Nat) : (a.ts t st).par1 = a.ts a.p1 (t :: st) := rfl
theorem par2_ts (a : A) (t : Nat) (st : List Nat) : (a.ts t st).par2 = a.ts a.p2 (t :: st) := rfl
theorem par3_ts (a : A) (t : Nat) (st : List Nat) : (a.ts t st).par3 = a.ts a.p3 (t :: st) := rfl
theorem cons_ts (a : A) (t x : Nat) (st : List Nat) : (a.ts t (x :: st)).cons = a.ts (pair x t) st := rfl
theorem select_ts (a : A) (t x : Nat) (st : List Nat) :
    (a.ts t (x :: st)).select = { a.ts (if a.ac = 0 then x else t) st with ac := a.ac - 1 } := rfl
theorem b6check_ts (a : A) (t : Nat) (st : List Nat) :
    (a.ts t st).b6check = { a.ts (if a.p2 = a.p3 ∨ a.p3 = a.p1 then 0 else t) st with p2 := 0, p3 := 0 } := rfl

end A

end TM.PA

namespace TM.PA

namespace A

@[simp] theorem ts_ts (a : A) (t t' : Nat) (st st' : List Nat) : (a.ts t st).ts t' st' = a.ts t' st' := rfl
@[simp] theorem ts_top (a : A) (t : Nat) (st : List Nat) : (a.ts t st).top = t := rfl
@[simp] theorem ts_stk (a : A) (t : Nat) (st : List Nat) : (a.ts t st).stk = st := rfl
@[simp] theorem ts_p1 (a : A) (t : Nat) (st : List Nat) : (a.ts t st).p1 = a.p1 := rfl
@[simp] theorem ts_p2 (a : A) (t : Nat) (st : List Nat) : (a.ts t st).p2 = a.p2 := rfl
@[simp] theorem ts_p3 (a : A) (t : Nat) (st : List Nat) : (a.ts t st).p3 = a.p3 := rfl
@[simp] theorem ts_ac (a : A) (t : Nat) (st : List Nat) : (a.ts t st).ac = a.ac := rfl

end A

end TM.PA
