import TinyCryptids.Core.Multi
import TinyCryptids.PAK.Tree

/-!
# The compiled machine

The machine `pa_nsymbols/kary.py` compiles from the program tree (`Tree.lean`), with 8 digit
values: symbols `0` (blank), `v + 1` for the digit value `v` (`sy v`; `1` is also the gap and a
register's unit) and `9` (`SEP`, the register separator).

```
0 [d_0 d_1 … d_h] 1 1 … 1 [9 1^v0] [9 1^v1] … [9 1^v9] 0 0 …
   program counter   gap        register file
```

* `node i`: a node of the tree; reading `sy v` it runs the slot whose value is `v` (`slotOf`).
* `scan` runs left to the blank before cell 0 and enters main (`node 0`); `adv` advances the
  cell it reads (or erases it and carries left); `ebrk e`, `ecnt e` erase `e` more cells for
  a break or continue.
* `cinc j`, `cdec j` count `j` separators to a register (the last one creates it on a blank);
  `carry1`, `carryS` shift the rest right (inc), `dstart`, `dscan`, `dput`, `dlast` shift it
  left (a successful decnz); `retok`, `retfail` return to the op's node cell.
* `bA`, `bB`, `bC`: the boot, which writes the gap of 12 ones.

`delta` is `kary.py`'s `emit`; `M10.lean` checks that it is the table of
`machines/pa_10sym_470.txt`.
-/

namespace TMK.PA


open TM (Dir)

/-- the digit values -/
def D : Nat := 8
/-- the last digit value: a node's last slot leaves it -/
def T : Nat := 7
/-- the register separator -/
def SEP : Nat := 9
/-- the number of registers -/
def NR : Nat := 10

/-- the symbol of digit value `v` -/
def sy (v : Nat) : Nat := v + 1

inductive St
  | node (i : Nat)
  | scan | adv
  | ebrk (e : Nat) | ecnt (e : Nat)
  | cinc (j : Nat) | cdec (j : Nat)
  | carry1 | carryS | dstart | dscan | dput | dlast
  | retok | retfail
  | bA | bB | bC
  | halt
  deriving DecidableEq

/-- where a break that erases `h` more cells goes (`adv`: the label is done) -/
def E : Nat → St
  | 0 => .adv
  | h + 1 => .ebrk (h + 1)

/-- where a continue that erases `h` more cells goes (`scan`: the label starts again) -/
def C : Nat → St
  | 0 => .scan
  | h + 1 => .ecnt (h + 1)

def findV : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: l, v => if x = v then some 0 else (findV l v).map (· + 1)

/-- the slot node `i` runs when its cell holds `v` (its value, or the skip value of its last) -/
def slotOf (i v : Nat) : Option Nat :=
  match findV (vals i) v with
  | some j => some j
  | none => if skp i = some v then some ((slots i).length - 1) else none

/-- the transition of slot `j` of node `i` -/
def slotTr (i j : Nat) : Sl → Option (Nat × Dir × St)
  | .node c => some (sy ((wrs i).getD j 0), .R, .node c)
  | .inc r => some (sy ((wrs i).getD j 0), .R, .cinc (mpos r + 1))
  | .dec r => some (sy ((wrs i).getD j 0), .R, .cdec (mpos r + 1))
  | .brk h => some (1, .L, E h)
  | .cnt h => some (1, .L, C h)
  | .jmp k => some (sy ((vals i).getD k 0), .L, .scan)
  | .done => some (1, .L, .adv)
  | .halt => some (sy ((wrs i).getD j 0), .R, .halt)

def nodeTr (i : Nat) : Nat → Option (Nat × Dir × St)
  | 0 => none
  | v + 1 => match slotOf i v with
    | none => none
    | some j => match (slots i).get? j with
      | none => none
      | some x => slotTr i j x

/-- a register chain: `j` separators to go; `first` is the operation -/
def chain (j : Nat) (k : Nat → St) (first : St) : Nat → Option (Nat × Dir × St)
  | 1 => if 1 ≤ j ∧ j ≤ NR then some (1, .R, k j) else none
  | 9 => if j = 1 then some (9, .R, first)
         else if 2 ≤ j ∧ j ≤ NR then some (9, .R, k (j - 1)) else none
  | 0 => if j = 1 then some (9, .R, first) else none
  | _ => none

def delta0 : St → Nat → Option (Nat × Dir × St)
  | .node i, a => nodeTr i a
  | .scan, 0 => some (0, .R, .node 0)
  | .scan, a + 1 => if a < D then some (a + 1, .L, .scan) else none
  | .adv, 0 => some (0, .R, .node 0)
  | .adv, a + 1 => if advV.contains a then
      (if a = T then some (1, .L, .adv) else some (a + 2, .L, .scan)) else none
  | .ebrk e, a + 1 => if (ebV e).contains a then some (1, .L, E (e - 1)) else none
  | .ecnt e, a + 1 => if (ecV e).contains a then some (1, .L, C (e - 1)) else none
  | .cinc j, a => chain j .cinc .carry1 a
  | .cdec j, a => chain j .cdec .dstart a
  | .carry1, 1 => some (1, .R, .carry1)
  | .carry1, 9 => some (1, .R, .carryS)
  | .carry1, 0 => some (1, .L, .retok)
  | .carryS, 1 => some (9, .R, .carry1)
  | .carryS, 9 => some (9, .R, .carryS)
  | .carryS, 0 => some (9, .L, .retok)
  | .dstart, 1 => some (1, .R, .dscan)
  | .dstart, 9 => some (9, .L, .retfail)
  | .dstart, 0 => some (0, .L, .retfail)
  | .dscan, 1 => some (1, .R, .dscan)
  | .dscan, 9 => some (1, .L, .dput)
  | .dscan, 0 => some (0, .L, .dlast)
  | .dput, 1 => some (9, .R, .dscan)
  | .dlast, 1 => some (0, .L, .retok)
  | .retok, 1 => some (1, .L, .retok)
  | .retok, 9 => some (9, .L, .retok)
  | .retok, a + 1 => if okV.contains a then
      (if a = T then some (1, .L, .adv) else some (a + 2, .L, .scan)) else none
  | .retfail, 1 => some (1, .L, .retfail)
  | .retfail, 9 => some (9, .L, .retfail)
  | .retfail, a + 1 => if failV.contains a then some (1, .L, .adv) else none
  | .bA, 0 => some (2, .L, .bB)
  | .bB, 0 => some (1, .R, .bC)
  | .bB, 1 => some (2, .R, .bB)
  | .bB, 2 => some (1, .L, .bB)
  | .bC, 0 => some (2, .R, .bA)
  | .bC, 1 => some (1, .L, .scan)
  | .bC, 2 => some (1, .R, .bB)
  | _, _ => none

/-- the compiled machine (symbols `0 … 9`) -/
def delta (q : St) (a : Nat) : Option (Nat × Dir × St) := if a < 10 then delta0 q a else none

def start : Cfg St := ⟨.bA, blank, blank⟩

theorem getD_ge {α : Type} {l : List α} {i : Nat} {d : α} (h : l.length ≤ i) : l.getD i d = d := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x l ih =>
    cases i with
    | zero => simp at h
    | succ i => exact ih (by simp at h; omega)

theorem chain_none (j : Nat) (k : Nat → St) (first : St) (a : Nat) (h : NR < j) :
    chain j k first a = none := by
  have h1 : ¬ (1 ≤ j ∧ j ≤ NR) := by simp only [NR] at h ⊢; omega
  have h2 : ¬ (2 ≤ j ∧ j ≤ NR) := by simp only [NR] at h ⊢; omega
  have h3 : j ≠ 1 := by simp only [NR] at h; omega
  unfold chain; split <;> simp [h1, h2, h3]

theorem ebV_ge (e : Nat) (h : 2 ≤ e) : ebV e = [] := by
  match e, h with
  | e + 2, _ => rfl

theorem ecV_ge (e : Nat) (h : 2 ≤ e) : ecV e = [] := by
  match e, h with
  | e + 2, _ => rfl

theorem delta_cinc_none (j a : Nat) (h : NR < j) : delta (.cinc j) a = none := by
  unfold delta; split
  · exact chain_none j _ _ a h
  · rfl

theorem delta_cdec_none (j a : Nat) (h : NR < j) : delta (.cdec j) a = none := by
  unfold delta; split
  · exact chain_none j _ _ a h
  · rfl

theorem delta_ebrk_none (e a : Nat) (h : 2 ≤ e) : delta (.ebrk e) a = none := by
  unfold delta; split
  · cases a <;> simp [delta0, ebV_ge e h]
  · rfl

theorem delta_ecnt_none (e a : Nat) (h : 2 ≤ e) : delta (.ecnt e) a = none := by
  unfold delta; split
  · cases a <;> simp [delta0, ecV_ge e h]
  · rfl

end TMK.PA
