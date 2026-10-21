import TinyCryptids.Core.Sys

/-!
# Turing machines with three symbols

The semantics of `Basic.lean` with the symbols `0, 1, 2` (`Sym`) in place of `Bool`; `0` is
the blank. A tape side is a stream `Nat → Sym`; a configuration stores the state, the left side
(nearest cell first) and the right side, whose first cell is the cell under the head. Runs,
reachability and halting are those of the step system `step δ` (`TinyCryptids.Core.Sys`).
-/

namespace TM3

/-- the tape symbols; `s0` is the blank -/
inductive Sym | s0 | s1 | s2
deriving DecidableEq, Repr

abbrev Strm := Nat → Sym

def blank : Strm := fun _ => Sym.s0

def cons (b : Sym) (s : Strm) : Strm := fun n => match n with
  | 0 => b
  | n + 1 => s n

infixr:67 " ::: " => cons

def tl (s : Strm) : Strm := fun n => s (n + 1)

/-- `ones n s` : n cells containing 1, then `s`. -/
def ones : Nat → Strm → Strm
  | 0, s => s
  | n + 1, s => Sym.s1 ::: ones n s

@[simp] theorem cons_zero (b : Sym) (s : Strm) : (b ::: s) 0 = b := rfl
@[simp] theorem tl_cons (b : Sym) (s : Strm) : tl (b ::: s) = s := rfl
@[simp] theorem ones_zero (s : Strm) : ones 0 s = s := rfl
theorem ones_succ (n : Nat) (s : Strm) : ones (n + 1) s = Sym.s1 ::: ones n s := rfl

@[simp] theorem tl_blank : tl blank = blank := rfl

theorem cons_blank : Sym.s0 ::: blank = blank := by
  funext n; cases n <;> rfl

theorem ones_add (a b : Nat) (s : Strm) : ones a (ones b s) = ones (a + b) s := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.add_right_comm, ones_succ, ones_succ, ih]

theorem ones_succ' (n : Nat) (s : Strm) : ones (n + 1) s = ones n (Sym.s1 ::: s) :=
  (ones_add n 1 s).symm

inductive Dir | L | R
deriving DecidableEq

structure Cfg (Q : Type) where
  q : Q
  L : Strm
  R : Strm

variable {Q : Type} (δ : Q → Sym → Option (Sym × Dir × Q))

def step (c : Cfg Q) : Option (Cfg Q) :=
  match δ c.q (c.R 0) with
  | none => none
  | some (w, Dir.R, q') => some ⟨q', w ::: c.L, tl c.R⟩
  | some (w, Dir.L, q') => some ⟨q', tl c.L, c.L 0 ::: w ::: tl c.R⟩

abbrev run : Nat → Cfg Q → Option (Cfg Q) := Sys.run (step δ)
abbrev Reach (c c' : Cfg Q) : Prop := Sys.Reach (step δ) c c'
/-- Strict reachability (at least one step), used for non-termination. -/
abbrev Reach1 (c c' : Cfg Q) : Prop := Sys.Reach1 (step δ) c c'
abbrev Halts (c : Cfg Q) : Prop := Sys.Halts (step δ) c

theorem Reach.refl (c : Cfg Q) : Reach δ c c := Sys.Reach.refl c

theorem Reach.trans {a b c : Cfg Q} : Reach δ a b → Reach δ b c → Reach δ a c := Sys.Reach.trans

theorem Reach.halts {a b : Cfg Q} : Reach δ a b → Halts δ b → Halts δ a := Sys.Reach.halts

theorem halts_of_step {c : Cfg Q} (h : step δ c = none) : Halts δ c := Sys.Halts.of_step h

theorem reach_step {c c' : Cfg Q} (h : step δ c = some c') : Reach δ c c' := Sys.Reach.single h

theorem Reach1.reach {c c' : Cfg Q} : Reach1 δ c c' → Reach δ c c' := Sys.Reach1.reach

theorem Reach1.trans_reach {a b c : Cfg Q} : Reach1 δ a b → Reach δ b c → Reach1 δ a c :=
  Sys.Reach1.trans_reach

theorem not_halts_of_progress (P : Cfg Q → Prop)
    (hP : ∀ c, P c → ∃ c', P c' ∧ Reach1 δ c c') :
    ∀ c, P c → ¬ Halts δ c := Sys.not_halts_of_progress P hP

variable {δ}

/-! ## single steps and runs over ones -/

theorem stepR {q q' : Q} {L R : Strm} {w : Sym} (h : δ q (R 0) = some (w, Dir.R, q')) :
    Reach δ ⟨q, L, R⟩ ⟨q', w ::: L, tl R⟩ :=
  reach_step δ (by simp [step, h])

theorem stepR1 {q q' : Q} {L R : Strm} {w : Sym} (h : δ q (R 0) = some (w, Dir.R, q')) :
    Reach1 δ ⟨q, L, R⟩ ⟨q', w ::: L, tl R⟩ :=
  ⟨0, by simp [run, Sys.run, step, h]⟩

theorem halt_none {q : Q} {L R : Strm} (h : δ q (R 0) = none) : Halts δ ⟨q, L, R⟩ :=
  halts_of_step δ (by simp [step, h])

/-- Configuration whose head reads `s 0` with `tl s` to its left: the natural
shape for leftward motion (the mirror image of `⟨q, L, s⟩`). -/
def cfgL (q : Q) (s R : Strm) : Cfg Q := ⟨q, tl s, s 0 ::: R⟩

theorem stepL' {q q' : Q} {s R : Strm} {w : Sym} (h : δ q (s 0) = some (w, Dir.L, q')) :
    Reach δ (cfgL q s R) (cfgL q' (tl s) (w ::: R)) :=
  reach_step δ (by simp [step, cfgL, h])

theorem stepL1 {q q' : Q} {s R : Strm} {w : Sym} (h : δ q (s 0) = some (w, Dir.L, q')) :
    Reach1 δ (cfgL q s R) (cfgL q' (tl s) (w ::: R)) :=
  ⟨0, by simp [run, Sys.run, step, cfgL, h]⟩

theorem scanR {q : Q} (h : δ q Sym.s1 = some (Sym.s1, Dir.R, q)) (n : Nat) (L R : Strm) :
    Reach δ ⟨q, L, ones n R⟩ ⟨q, ones n L, R⟩ := by
  induction n generalizing L with
  | zero => exact Reach.refl δ _
  | succ n ih =>
    refine Reach.trans δ (stepR (δ := δ) (R := ones (n+1) R) h) ?_
    have := ih (Sym.s1 ::: L); rw [← ones_succ'] at this; exact this

theorem scanL {q : Q} (h : δ q Sym.s1 = some (Sym.s1, Dir.L, q)) (n : Nat) (s R : Strm) :
    Reach δ (cfgL q (ones n s) R) (cfgL q s (ones n R)) := by
  induction n generalizing R with
  | zero => exact Reach.refl δ _
  | succ n ih =>
    refine Reach.trans δ (stepL' (δ := δ) (s := ones (n+1) s) h) ?_
    have := ih (Sym.s1 ::: R); rw [← ones_succ'] at this; exact this

end TM3
