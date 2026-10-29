import TinyCryptids.Core.Basic

/-!
# The compiled machine

A. J. Wade's TMBuilder (as forked in `pa/tmbuilder.py`) compiles a register program into a
2-symbol Turing machine: a fixed *framework* (boot, register operations, dispatch, program
counter updates) and one state per node of a binary *decision DAG* (`dag`, generated in
`Dag.lean`).  This file defines that machine for any DAG; `M309.lean` checks that the
309-state machine is this machine with two equal states merged.

A DAG node reads one program-counter bit and goes to its `car` (bit 0) or `cdr` (bit 1).
A child is another node or a leaf: a register operation, a `break`/`continue` (a program
counter update), or `halt`.
-/

namespace TM.PA

/-- A child of a DAG node. -/
inductive Ch
  | node (i : Nat)
  | inc (r : Fin 10)
  | dec (r : Fin 10)     -- `decnz`: decrement if nonzero, else fail
  | brk (k : Nat)        -- `_break.k`
  | cnt (k : Nat)        -- `_continue.k`
  | halt
  deriving DecidableEq, Repr

/-- States: the framework (named after TMBuilder's states), one per DAG node, and `halt`. -/
inductive St
  | bA | bB | bC | bD | bE          -- 0a.boot1.A–E
  | b2s0 | b2s1 | b2s2              -- 0b.boot2.0–2
  | prep1 | prep2                   -- 1b.reg.prep_1, prep_2
  | chI (k : Fin 12)                -- 2b.reg.(k-2).inc
  | chD (k : Fin 12)                -- 2b.reg.(k-2).dec
  | dcheck | dscan1 | dscan2 | dshift1 | dshift2   -- 2b.reg.dec.*
  | ishift1 | ishift2                              -- 2b.reg.inc.shift_1, shift_2
  | r0a | r0b | r1a | r1b           -- 2c.reg.return_0_1, return_0_2, return_1_1, return_1_2
  | cl1 | cl2                       -- 2e.reg.cleanup_1, cleanup_2
  | incL (r : Fin 10)               -- 3.R.inc
  | decL (r : Fin 10)               -- 3.R.decnz
  | disp (i : Fin 7)                -- 4.dispatch.i
  | scan                            -- 4.dispatch.scan
  | root1 | root2                   -- 5.root.1, 5.root.2
  | brk0 | brk1 | cnt0 | cnt1       -- 6.break.0, 6.break.1, 6.continue.0, 6.continue.1
  | node (i : Nat)
  | halt
  deriving DecidableEq, Repr

open Dir

/-- The state reached through a child that is a node, a register operation or `halt`. -/
def Ch.st : Ch → Option St
  | .node i => some (.node i)
  | .inc r => some (.incL r)
  | .dec r => some (.decL r)
  | .halt => some .halt
  | _ => none

/-- The `break` state `k` (only levels 0 and 1 exist). -/
def brkSt : Nat → Option St
  | 0 => some .brk0
  | 1 => some .brk1
  | _ => none

def cntSt : Nat → Option St
  | 0 => some .cnt0
  | 1 => some .cnt1
  | _ => none

/-- A node state reading `0`: its car. -/
def carTr : Ch → Option (Bool × Dir × St)
  | .brk 0 => some (true, L, .cnt0)
  | .brk (k + 1) => (brkSt k).map fun q => (false, L, q)
  | .cnt k => (cntSt k).map fun q => (false, L, q)
  | c => c.st.map fun q => (false, R, q)

/-- A node state reading `1`: its cdr. -/
def cdrTr : Ch → Option (Bool × Dir × St)
  | .brk k => (brkSt k).map fun q => (false, L, q)
  | .cnt (k + 1) => (cntSt k).map fun q => (false, L, q)
  | .cnt 0 => none
  | c => c.st.map fun q => (true, R, q)

/-- Chain index of register `r` (`2b.reg.r.*` is `chI (r + 2)`). -/
def chOf (r : Fin 10) : Fin 12 := ⟨r.val + 2, by omega⟩

variable (dag : Nat → Option (Ch × Ch)) (main : Nat)

/-- The machine compiled from `dag` (with root node `main`). -/
def delta : St → Bool → Option (Bool × Dir × St)
  | .bA, false => some (true, R, .bB)
  | .bA, true => some (true, L, .bC)
  | .bB, false => some (false, L, .bA)
  | .bB, true => some (false, L, .bD)
  | .bC, false => some (true, L, .bA)
  | .bC, true => some (true, R, .incL 0)
  | .bD, false => some (true, L, .bB)
  | .bD, true => some (true, R, .bE)
  | .bE, false => some (false, R, .bD)
  | .bE, true => some (false, R, .bB)
  | .b2s0, false => some (true, L, .cnt0)
  | .b2s0, true => some (true, R, .b2s1)
  | .b2s1, false => some (false, R, .b2s0)
  | .b2s1, true => some (true, R, .b2s2)
  | .b2s2, false => some (false, R, .incL 0)
  | .b2s2, true => some (true, R, .decL 0)
  | .prep1, false => some (false, R, .prep2)
  | .prep1, true => none
  | .prep2, false => some (true, R, .prep2)
  | .prep2, true => some (true, L, .cnt0)
  | .chI ⟨0, _⟩, false => some (true, R, .ishift1)
  | .chI ⟨k + 1, h⟩, false => some (false, R, .chI ⟨k, by omega⟩)
  | .chI k, true => some (true, R, .chI k)
  | .chD ⟨0, _⟩, false => some (true, L, .r1a)
  | .chD ⟨0, _⟩, true => some (false, R, .dcheck)
  | .chD ⟨k + 1, h⟩, false => some (false, R, .chD ⟨k, by omega⟩)
  | .chD ⟨k + 1, h⟩, true => some (true, R, .chD ⟨k + 1, h⟩)
  | .dcheck, false => some (false, L, .chD 0)
  | .dcheck, true => some (true, R, .dscan1)
  | .dscan1, false => some (false, R, .dscan2)
  | .dscan1, true => some (true, R, .dscan1)
  | .dscan2, false => some (false, L, .dshift1)
  | .dscan2, true => some (true, R, .dscan1)
  | .dshift1, false => some (true, L, .dshift2)
  | .dshift1, true => some (true, L, .dshift1)
  | .dshift2, false => some (false, L, .r0a)
  | .dshift2, true => some (false, L, .dshift1)
  | .ishift1, false => some (false, L, .r0a)
  | .ishift1, true => some (false, R, .ishift2)
  | .ishift2, false => some (true, R, .ishift1)
  | .ishift2, true => some (true, R, .ishift2)
  | .r0a, false => some (false, L, .r0b)
  | .r0a, true => some (true, L, .r0a)
  | .r0b, false => some (false, L, .brk0)
  | .r0b, true => some (true, L, .r0a)
  | .r1a, false => some (false, L, .r1b)
  | .r1a, true => some (true, L, .r1a)
  | .r1b, false => some (false, L, .brk1)
  | .r1b, true => some (true, L, .r1a)
  | .cl1, false => some (false, R, .cl1)
  | .cl1, true => some (false, R, .cl2)
  | .cl2, false => some (false, L, .b2s0)
  | .cl2, true => some (false, R, .cl2)
  | .incL _, false => some (true, R, .prep1)
  | .incL r, true => some (false, R, .chI (chOf r))
  | .decL _, false => some (true, R, .prep1)
  | .decL r, true => some (false, R, .chD (chOf r))
  | .disp ⟨0, _⟩, false => some (false, L, .scan)
  | .disp ⟨i + 1, h⟩, false => some (false, L, .disp ⟨i, by omega⟩)
  | .disp _, true => some (true, L, .disp 6)
  | .scan, false => some (false, R, .scan)
  | .scan, true => some (true, R, .root1)
  | .root1, false => some (false, R, .b2s0)
  | .root1, true => some (true, R, .root2)
  | .root2, _ => some (false, R, .node main)
  | .brk0, false => some (true, R, .cl1)
  | .brk0, true => some (false, L, .brk0)
  | .brk1, false => some (false, L, .brk0)
  | .brk1, true => some (false, L, .brk1)
  | .cnt0, false => some (false, L, .cnt0)
  | .cnt0, true => some (true, L, .disp 6)
  | .cnt1, false => some (false, L, .cnt1)
  | .cnt1, true => some (false, L, .cnt0)
  | .node i, b => (dag i).bind fun cd => if b then cdrTr cd.2 else carTr cd.1
  | .halt, _ => none

def start : Cfg St := ⟨.bA, blank, blank⟩

end TM.PA
