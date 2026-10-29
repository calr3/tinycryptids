import TinyCryptids.PA.Machine

/-!
# Big-step semantics of a decision DAG

The registers (`R`) and what running a node does to them (`Ex`).  A node reads its program
counter bit: `0` runs its car, `1` its cdr.  Running a child ends with an *outcome* at the
bit that led into it (`Res`):

* `brk 0` — the child is done: the bit is incremented (a car is followed by its cdr; a cdr
  makes its parent done);
* `brk (k + 1)` — leave `k + 1` levels: a car makes its parent `brk k`, a cdr `brk (k + 1)`;
* `cnt k` — erase `k` one-bits and re-dispatch: a car makes its parent `cnt k`, a cdr
  `cnt (k - 1)`; a parent whose outcome would be `cnt 0` is run again from the start;
* `halt`.

A register leaf is done after `inc` or a successful `decnz`, and a failed `decnz` is `brk 1`.
-/

namespace TM.PA

/-- The ten registers, in TMBuilder's order. -/
structure R where
  pl : Nat    -- 0 prooflist
  np : Nat    -- 1 nextproof
  top : Nat   -- 2 topwff
  ws : Nat    -- 3 wffstack
  ac : Nat    -- 4 axiomcode
  p1 : Nat    -- 5 param1
  p2 : Nat    -- 6 param2
  p3 : Nat    -- 7 param3
  s1 : Nat    -- 8 scratch1
  s2 : Nat    -- 9 scratch2
  deriving DecidableEq, Repr

namespace R

def get (s : R) : Fin 10 → Nat
  | ⟨0, _⟩ => s.pl | ⟨1, _⟩ => s.np | ⟨2, _⟩ => s.top | ⟨3, _⟩ => s.ws | ⟨4, _⟩ => s.ac
  | ⟨5, _⟩ => s.p1 | ⟨6, _⟩ => s.p2 | ⟨7, _⟩ => s.p3 | ⟨8, _⟩ => s.s1 | ⟨9, _⟩ => s.s2

def set (s : R) : Fin 10 → Nat → R
  | ⟨0, _⟩, v => { s with pl := v } | ⟨1, _⟩, v => { s with np := v }
  | ⟨2, _⟩, v => { s with top := v } | ⟨3, _⟩, v => { s with ws := v }
  | ⟨4, _⟩, v => { s with ac := v } | ⟨5, _⟩, v => { s with p1 := v }
  | ⟨6, _⟩, v => { s with p2 := v } | ⟨7, _⟩, v => { s with p3 := v }
  | ⟨8, _⟩, v => { s with s1 := v } | ⟨9, _⟩, v => { s with s2 := v }

def inc (s : R) (r : Fin 10) : R := s.set r (s.get r + 1)
def dec (s : R) (r : Fin 10) : R := s.set r (s.get r - 1)

def toList (s : R) : List Nat := [s.pl, s.np, s.top, s.ws, s.ac, s.p1, s.p2, s.p3, s.s1, s.s2]

/-- `toList` with register `r` changed by `f`: the first `r` values, `f` of register `r`,
the rest. -/
theorem toList_set (s : R) (r : Fin 10) (v : Nat) :
    (s.set r v).toList = s.toList.take r.val ++ v :: s.toList.drop (r.val + 1) := by
  match r with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩
  | ⟨9, _⟩ => rfl

theorem get_eq (s : R) (r : Fin 10) : s.toList.drop r.val = s.get r :: s.toList.drop (r.val + 1) := by
  match r with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩
  | ⟨9, _⟩ => rfl

theorem length_take (s : R) (r : Fin 10) : (s.toList.take r.val).length = r.val := by
  match r with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩
  | ⟨9, _⟩ => rfl

end R

/-- The outcome of running a child, at the bit that led into it. -/
inductive Res
  | brk (k : Nat)
  | cnt (k : Nat)
  | halt
  deriving DecidableEq, Repr

/-- A car's outcome as its parent's (when it is not `brk 0`). -/
def adj0 : Res → Res
  | .brk (k + 1) => .brk k
  | o => o

/-- A cdr's outcome as its parent's. -/
def adj1 : Res → Res
  | .cnt (k + 1) => .cnt k
  | o => o

variable (dag : Nat → Option (Ch × Ch))

/-- `Ex c s o t`: running child `c` from registers `s` ends with outcome `o` and registers `t`
(a node whose outcome would be `cnt 0` runs again). -/
inductive Ex : Ch → R → Res → R → Prop
  | inc (r : Fin 10) (s : R) : Ex (.inc r) s (.brk 0) (s.inc r)
  | decp (r : Fin 10) (s : R) : 0 < s.get r → Ex (.dec r) s (.brk 0) (s.dec r)
  | decz (r : Fin 10) (s : R) : s.get r = 0 → Ex (.dec r) s (.brk 1) s
  | brk (k : Nat) (s : R) : Ex (.brk k) s (.brk k) s
  | cnt (k : Nat) (s : R) : Ex (.cnt k) s (.cnt k) s
  | halt (s : R) : Ex .halt s .halt s
  /-- the car ends the node -/
  | car {i : Nat} {c d : Ch} {s t : R} {o : Res} : dag i = some (c, d) → Ex c s o t →
      o ≠ .brk 0 → adj0 o ≠ .cnt 0 → Ex (.node i) s (adj0 o) t
  /-- the car is done, the cdr ends the node -/
  | cdr {i : Nat} {c d : Ch} {s t u : R} {o : Res} : dag i = some (c, d) → Ex c s (.brk 0) t →
      Ex d t o u → adj1 o ≠ .cnt 0 → Ex (.node i) s (adj1 o) u
  /-- the cdr restarts the node -/
  | restart {i : Nat} {c d : Ch} {s t u v : R} {o : Res} : dag i = some (c, d) →
      Ex c s (.brk 0) t → Ex d t (.cnt 1) u → Ex (.node i) u o v → Ex (.node i) s o v

end TM.PA
