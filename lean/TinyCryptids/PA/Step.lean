import TinyCryptids.PA.Cand

/-!
# One iteration, on the four registers that carry over

`S.step` is `pa/ref.py`'s `iterate_tail` for this machine: decode a step
`(axiomcode, p1, p2, p3)` from the proof code, keep candidate number `axiomcode` (`kept`), and
push the last theorem (or pop the premises of GEN and DET: `nextWs`).  `iter_eq`: the
machine's iteration `A.iter` computes it.
-/

namespace TM.PA

/-- the registers that carry over between iterations -/
structure S where
  pl : Nat
  np : Nat
  top : Nat
  ws : Nat

/-- the twelve axiom candidates (`axiomcode` 1 … 12) for parameters `p1 p2 p3`;
B6a is `v0 = v0` (code 0) when `p3` is `p1` or `p2` -/
def candList (p1 p2 p3 : Nat) : List Nat :=
  [axE p1 p2 p3, axB2 p1 p2 p3, axB8c p1 p2 p3, axB8b p1 p2 p3, axB8a p1 p2 p3, axB3 p1 p2 p3,
   axB7 p1 p2 p3, axB4 p1 p2 p3, axB6b p1 p2 p3, axB1 p1 p2 p3, axB6c p1 p2 p3,
   if p2 = p3 ∨ p3 = p1 then 0 else axB6a p1 p2 p3]

/-- the kept theorem: `v0 = v0` (code 0) for `axiomcode` 0, an axiom for 1 … 12,
generalisation of the last theorem for 13, modus ponens on the last two for 14 and above -/
def kept (ac p1 p2 p3 top ws : Nat) : Nat :=
  if ac = 0 then 0
  else if ac ≤ 12 then (candList p1 p2 p3).getD (ac - 1) 0
  else if ac = 13 then allC p1 top
  else if (unpair ws).snd = impC top p1 then p1 else 0

/-- the stack after the step: the last theorem pushed, or popped by GEN (and DET) -/
def nextWs (ac top ws : Nat) : Nat :=
  if ac ≤ 12 then pair ws top else if ac = 13 then ws else (unpair ws).fst

/-- a step `(axiomcode, p1, p2, p3)` -/
structure Stp where
  ac : Nat
  p1 : Nat
  p2 : Nat
  p3 : Nat

/-- the next proof code (`prooflist` decremented, or reloaded from `nextproof`) -/
def S.code (σ : S) : Nat := if σ.pl = 0 then σ.np else σ.pl - 1

def S.np' (σ : S) : Nat := if σ.pl = 0 then σ.np + 1 else σ.np

/-- a proof code: its first step and the rest -/
def decStep (n : Nat) : Stp × Nat :=
  let a := unpair n
  let b := unpair a.fst
  let c := unpair b.fst
  let d := unpair c.fst
  (⟨a.snd, b.snd, c.snd, d.snd⟩, d.fst)

/-- the effect of a step on `topwff` and `wffstack` -/
def runStp (s : Stp) (top ws : Nat) : Nat × Nat :=
  (kept s.ac s.p1 s.p2 s.p3 top ws, nextWs s.ac top ws)

/-- one iteration -/
def S.step (σ : S) : S :=
  let d := decStep σ.code
  ⟨d.snd, σ.np', (runStp d.fst σ.top σ.ws).fst, (runStp d.fst σ.top σ.ws).snd⟩

/-- `A.iter` from a register file whose stack is empty (on its base) and `param2` zero -/
theorem iter_eq (a : A) (hs : a.stk = []) (hp : a.p2 = 0) :
    let σ : S := ⟨a.pl, a.np, a.top, a.base⟩
    (A.iter a).pl = σ.step.pl ∧ (A.iter a).np = σ.step.np ∧ (A.iter a).top = σ.step.top ∧
      enc (A.iter a).base (A.iter a).stk = σ.step.ws ∧ (A.iter a).p2 = 0 := by
  obtain ⟨pl, np, top, ac, p1, p2, p3, base, stk⟩ := a
  simp only at hs hp
  subst hs hp
  simp only [A.iter, A.decode, A.reload, A.zeroAc, A.zeroP1, A.zeroP3, A.decAc, A.decP1, A.decP2,
    A.decP3, A.push, candE_eq, candB2_eq, candB8c_eq, candB8b_eq, candB8a_eq, candB3_eq, candB7_eq,
    candB4_eq, candB6b_eq, candB1_eq, candB6c_eq, candB6a_eq, S.step, decStep, S.code, S.np',
    runStp, kept, nextWs, candList, Nat.zero_add]
  generalize (unpair (unpair (unpair (unpair (if pl = 0 then np else pl - 1)).fst).fst).fst).snd = P3
  generalize (unpair (unpair (unpair (unpair (if pl = 0 then np else pl - 1)).fst).fst).fst).fst = RST
  generalize (unpair (unpair (unpair (if pl = 0 then np else pl - 1)).fst).fst).snd = P2
  generalize (unpair (unpair (if pl = 0 then np else pl - 1)).fst).snd = P1
  generalize (unpair (if pl = 0 then np else pl - 1)).snd = AC
  rcases AC with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | AC
  all_goals simp [A.gen, A.det, A.decAc1, A.pop3, A.pop2, A.pop, A.par1, A.par3, A.wal, A.wim, A.v2,
    A.v4, A.cons, A.push, A.incT, A.detCmp, A.drop, enc, allC, impC]

end TM.PA
