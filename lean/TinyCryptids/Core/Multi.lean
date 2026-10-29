import TinyCryptids.Core.Basic

/-!
# Turing machines with more than two symbols

As `Basic.lean`, with symbols `Nat` (0 is the blank) instead of `Bool`: a tape side is a stream
`Nat → Nat`, a configuration the state, the left side (nearest cell first) and the right side,
whose first cell is under the head.  The run, reachability and halting are those of the step
system `step δ` (`Sys`).
-/

namespace TMK

open TM (Dir)

abbrev Strm := Nat → Nat

def blank : Strm := fun _ => 0

def cons (a : Nat) (s : Strm) : Strm := fun n => match n with
  | 0 => a
  | n + 1 => s n

infixr:67 " ∷ " => cons

def tl (s : Strm) : Strm := fun n => s (n + 1)

/-- the cells of a list, then `s` -/
def lst : List Nat → Strm → Strm
  | [], s => s
  | a :: l, s => a ∷ lst l s

@[simp] theorem cons_zero (a : Nat) (s : Strm) : (a ∷ s) 0 = a := rfl
@[simp] theorem cons_succ (a : Nat) (s : Strm) (n : Nat) : (a ∷ s) (n + 1) = s n := rfl
@[simp] theorem tl_cons (a : Nat) (s : Strm) : tl (a ∷ s) = s := rfl
@[simp] theorem tl_blank : tl blank = blank := rfl
@[simp] theorem blank_apply (n : Nat) : blank n = 0 := rfl
@[simp] theorem lst_nil (s : Strm) : lst [] s = s := rfl
@[simp] theorem lst_cons (a : Nat) (l : List Nat) (s : Strm) : lst (a :: l) s = a ∷ lst l s := rfl

theorem cons_blank : 0 ∷ blank = blank := by
  funext n; cases n <;> rfl

theorem cons_head_tl (s : Strm) : s 0 ∷ tl s = s := by
  funext n; cases n <;> rfl

theorem lst_append (l m : List Nat) (s : Strm) : lst (l ++ m) s = lst l (lst m s) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

structure Cfg (Q : Type) where
  q : Q
  L : Strm
  R : Strm

variable {Q : Type} (δ : Q → Nat → Option (Nat × Dir × Q))

def step (c : Cfg Q) : Option (Cfg Q) :=
  match δ c.q (c.R 0) with
  | none => none
  | some (w, Dir.R, q') => some ⟨q', w ∷ c.L, tl c.R⟩
  | some (w, Dir.L, q') => some ⟨q', tl c.L, c.L 0 ∷ w ∷ tl c.R⟩

abbrev run : Nat → Cfg Q → Option (Cfg Q) := Sys.run (step δ)
abbrev Reach (c c' : Cfg Q) : Prop := Sys.Reach (step δ) c c'
abbrev Reach1 (c c' : Cfg Q) : Prop := Sys.Reach1 (step δ) c c'
abbrev Halts (c : Cfg Q) : Prop := Sys.Halts (step δ) c

theorem Reach.refl (c : Cfg Q) : Reach δ c c := Sys.Reach.refl c

theorem Reach.trans {a b c : Cfg Q} : Reach δ a b → Reach δ b c → Reach δ a c := Sys.Reach.trans

theorem reach_step {c c' : Cfg Q} (h : step δ c = some c') : Reach δ c c' := Sys.Reach.single h

theorem halts_of_step {c : Cfg Q} (h : step δ c = none) : Halts δ c := Sys.Halts.of_step h

variable {δ}

theorem stepR {q q' : Q} {L R : Strm} {w : Nat} (h : δ q (R 0) = some (w, Dir.R, q')) :
    Reach δ ⟨q, L, R⟩ ⟨q', w ∷ L, tl R⟩ :=
  reach_step δ (by simp [step, h])

theorem stepL {q q' : Q} {L R : Strm} {w : Nat} (h : δ q (R 0) = some (w, Dir.L, q')) :
    Reach δ ⟨q, L, R⟩ ⟨q', tl L, L 0 ∷ w ∷ tl R⟩ :=
  reach_step δ (by simp [step, h])

theorem stepR1 {q q' : Q} {L R : Strm} {w : Nat} (h : δ q (R 0) = some (w, Dir.R, q')) :
    Reach1 δ ⟨q, L, R⟩ ⟨q', w ∷ L, tl R⟩ :=
  ⟨0, by simp [run, Sys.run, step, h]⟩

theorem halt_none {q : Q} {L R : Strm} (h : δ q (R 0) = none) : Halts δ ⟨q, L, R⟩ :=
  halts_of_step δ (by simp [step, h])

/-! ## Simulation: a machine that agrees on all used transitions -/

def Compat {Q Q' : Type} (φ : Q → Q') : Option (Nat × Dir × Q) → Option (Nat × Dir × Q') → Prop
  | none, _ => True
  | some (w, d, q), x => x = some (w, d, φ q)

def Cfg.map {Q Q' : Type} (φ : Q → Q') (c : Cfg Q) : Cfg Q' := ⟨φ c.q, c.L, c.R⟩

theorem sim_run {Q Q' : Type} (δ : Q → Nat → Option (Nat × Dir × Q))
    (δ' : Q' → Nat → Option (Nat × Dir × Q')) (φ : Q → Q')
    (h : ∀ q a, Compat φ (δ q a) (δ' (φ q) a)) :
    ∀ n (c c' : Cfg Q), run δ n c = some c' → run δ' n (c.map φ) = some (c'.map φ) := by
  intro n
  induction n with
  | zero => intro c c' hc; simp [run, Sys.run] at hc ⊢; rw [hc]
  | succ n ih =>
    intro c c' hc
    simp only [run, Sys.run] at hc ⊢
    have hq := h c.q (c.R 0)
    unfold step at hc ⊢
    simp only [Cfg.map]
    revert hc hq
    cases δ c.q (c.R 0) with
    | none => intro hc; exact absurd hc (by simp)
    | some t =>
      obtain ⟨w, d, q⟩ := t
      intro hc hq
      simp only [Compat] at hq
      rw [hq]
      cases d with
      | R => exact ih _ _ hc
      | L => exact ih _ _ hc

/-- Transfer of a halting theorem to a machine that simulates the original: it halts iff the
original does, provided the original only halts by reaching a configuration where the
simulator halts. -/
theorem halts_iff_of_sim {Q Q' : Type} (δ : Q → Nat → Option (Nat × Dir × Q))
    (δ' : Q' → Nat → Option (Nat × Dir × Q')) (φ : Q → Q')
    (h : ∀ q a, Compat φ (δ q a) (δ' (φ q) a)) (s : Cfg Q) {P : Prop}
    (hiff : Halts δ s ↔ P) (hhalt : P → ∃ c, Reach δ s c ∧ δ' (φ c.q) (c.R 0) = none) :
    Halts δ' (s.map φ) ↔ P := by
  constructor
  · intro ⟨N, hN⟩
    apply Classical.byContradiction; intro hno
    cases hr : run δ N s with
    | none => exact hno (hiff.1 ⟨N, hr⟩)
    | some c =>
      have := sim_run δ δ' φ h N s c hr
      exact Option.noConfusion (this.symm.trans hN)
  · intro hp
    obtain ⟨c, ⟨n, hn⟩, hq⟩ := hhalt hp
    have hs := sim_run δ δ' φ h n s c hn
    refine Sys.Reach.halts ⟨n, hs⟩ (halts_of_step δ' ?_)
    simp [step, Cfg.map, hq]

end TMK
