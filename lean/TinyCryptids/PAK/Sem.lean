import TinyCryptids.PAK.Machine
import TinyCryptids.PA.Prog

/-!
# Big-step semantics of the program tree

`Run i j s o t`: node `i`, run from its slot `j` on registers `s` (`TM.PA.R`), ends with
outcome `o` and registers `t`.  The outcome is what the node's parent sees (`Res`):

* `brk 0` — the node is done (its cell is erased and its parent's advanced);
* `brk (k + 1)` — a break that erases `k + 1` more cells: the parent's outcome is `brk k`;
* `cnt (k + 1)` — a continue that erases `k + 1` more cells: the parent's outcome is `cnt k`,
  and a parent whose outcome would be `cnt 0` runs again from its first slot;
* `halt`.

A slot runs a child (`node c`), a register operation (a failed `decnz` ends the node), a break
or continue (`brk h`, `cnt h`: `h` more cells; `cnt 0` restarts the node), a jump to another
slot of the node (`jmp k`), the end of the node (`done`), or halts.  A child's break or
continue past its parent needs the erase state to read the parent's cell (`ebV`, `ecV`).
-/

namespace TMK.PA

open TM.PA (R)

/-- The outcome of running a node, as its parent sees it. -/
inductive Res
  | brk (k : Nat)
  | cnt (k : Nat)
  | halt
  deriving DecidableEq, Repr

/-- slot `j` of node `i` -/
def slot (i j : Nat) : Option Sl := (slots i).get? j

/-- the value slot `j`'s transition writes on node `i`'s cell -/
def wr (i j : Nat) : Nat := (wrs i).getD j 0

inductive Run : Nat → Nat → R → Res → R → Prop
  /-- past the last slot: the node is done -/
  | fin {i j : Nat} {s : R} : slot i j = none → Run i j s (.brk 0) s
  | inc {i j : Nat} {r : Fin 10} {s t : R} {o : Res} : slot i j = some (.inc r) →
      Run i (j + 1) (s.inc r) o t → Run i j s o t
  | decp {i j : Nat} {r : Fin 10} {s t : R} {o : Res} : slot i j = some (.dec r) → 0 < s.get r →
      Run i (j + 1) (s.dec r) o t → Run i j s o t
  /-- a failed `decnz` ends the node -/
  | decz {i j : Nat} {r : Fin 10} {s : R} : slot i j = some (.dec r) → s.get r = 0 →
      Run i j s (.brk 0) s
  | child {i j c : Nat} {s u t : R} {o : Res} : slot i j = some (.node c) → Run c 0 s (.brk 0) u →
      Run i (j + 1) u o t → Run i j s o t
  | childB {i j c k : Nat} {s u : R} : slot i j = some (.node c) → Run c 0 s (.brk (k + 1)) u →
      wr i j ∈ ebV (k + 1) → Run i j s (.brk k) u
  | childC {i j c k : Nat} {s u : R} : slot i j = some (.node c) → Run c 0 s (.cnt (k + 2)) u →
      wr i j ∈ ecV (k + 2) → Run i j s (.cnt (k + 1)) u
  /-- the child continues this node: it runs again -/
  | childR {i j c : Nat} {s u t : R} {o : Res} : slot i j = some (.node c) → Run c 0 s (.cnt 1) u →
      wr i j ∈ ecV 1 → Run i 0 u o t → Run i j s o t
  | childH {i j c : Nat} {s u : R} : slot i j = some (.node c) → Run c 0 s .halt u →
      Run i j s .halt u
  | brk {i j h : Nat} {s : R} : slot i j = some (.brk h) → Run i j s (.brk h) s
  | cnt0 {i j : Nat} {s t : R} {o : Res} : slot i j = some (.cnt 0) → Run i 0 s o t → Run i j s o t
  | cnt {i j h : Nat} {s : R} : slot i j = some (.cnt (h + 1)) → Run i j s (.cnt (h + 1)) s
  | jmp {i j k : Nat} {s t : R} {o : Res} : slot i j = some (.jmp k) → Run i k s o t → Run i j s o t
  | done {i j : Nat} {s : R} : slot i j = some .done → Run i j s (.brk 0) s
  | halt {i j : Nat} {s : R} : slot i j = some .halt → Run i j s .halt s

/-- running a node from its first slot -/
abbrev Ex (i : Nat) (s : R) (o : Res) (t : R) : Prop := Run i 0 s o t

end TMK.PA
