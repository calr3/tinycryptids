import TinyCryptids.PA.Pair
import TinyCryptids.Defs

/-!
# Formula codes

A formula is coded by Cantor pairing (as in `pa/ref.py`): `x = y` is `pair(pair(x, y), 0)`,
`x e. y` is `pair(pair(x, y), 1)`, `φ -> ψ` is `pair(pair(φ, ψ), 2)`, `-. φ` is `pair(φ, 3)`,
`A. x φ` is `pair(pair(x, φ), 4)`; variables are numbers.
-/

namespace TM.PA

def eqC (x y : Nat) : Nat := pair (pair x y) 0
def elC (x y : Nat) : Nat := pair (pair x y) 1
def impC (a b : Nat) : Nat := pair (pair a b) 2
def negC (a : Nat) : Nat := pair a 3
def allC (x a : Nat) : Nat := pair (pair x a) 4
def exC (x a : Nat) : Nat := negC (allC x (negC a))
def andC (a b : Nat) : Nat := negC (impC a (negC b))

end TM.PA

namespace TM.PA

open TinyCryptids

theorem unpair_fst_le (n : Nat) : (unpair n).fst ≤ n := by
  have := pair_le_left (unpair n).fst (unpair n).snd; rw [pair_unpair] at this; exact this

theorem unpair_snd_le (n : Nat) : (unpair n).snd ≤ n := by
  have := pair_le_right (unpair n).fst (unpair n).snd; rw [pair_unpair] at this; exact this

theorem unpair_fst_lt {n : Nat} (h : 0 < (unpair n).snd) : (unpair n).fst < n := by
  have := pair_fst_lt (a := (unpair n).fst) (b := (unpair n).snd) (by omega)
  rw [pair_unpair] at this; exact this

/-- the code of a formula -/
def code : Wff → Nat
  | .eq x y => eqC x y
  | .el x y => elC x y
  | .imp φ ψ => impC (code φ) (code ψ)
  | .neg φ => negC (code φ)
  | .all x φ => allC x (code φ)

/-- the formula of a code; a code whose tag is above 4 reads as `v0 = v0` -/
def decode (n : Nat) : Wff :=
  match _h : (unpair n).snd with
  | 0 => .eq (unpair (unpair n).fst).fst (unpair (unpair n).fst).snd
  | 1 => .el (unpair (unpair n).fst).fst (unpair (unpair n).fst).snd
  | 2 => .imp (decode (unpair (unpair n).fst).fst) (decode (unpair (unpair n).fst).snd)
  | 3 => .neg (decode (unpair n).fst)
  | 4 => .all (unpair (unpair n).fst).fst (decode (unpair (unpair n).fst).snd)
  | _ + 5 => .eq 0 0
termination_by n
decreasing_by
  all_goals
    have h1 := unpair_fst_lt (n := n) (by omega)
    first
    | exact Nat.lt_of_le_of_lt (unpair_fst_le _) h1
    | exact Nat.lt_of_le_of_lt (unpair_snd_le _) h1
    | exact h1

theorem decode_eqC (x y : Nat) : decode (eqC x y) = .eq x y := by
  rw [decode]; split <;> simp_all [eqC, unpair_pair]
theorem decode_elC (x y : Nat) : decode (elC x y) = .el x y := by
  rw [decode]; split <;> simp_all [elC, unpair_pair]
theorem decode_impC (a b : Nat) : decode (impC a b) = .imp (decode a) (decode b) := by
  rw [decode]; split <;> simp_all [impC, unpair_pair]
theorem decode_negC (a : Nat) : decode (negC a) = .neg (decode a) := by
  rw [decode]; split <;> simp_all [negC, unpair_pair]
theorem decode_allC (x a : Nat) : decode (allC x a) = .all x (decode a) := by
  rw [decode]; split <;> simp_all [allC, unpair_pair]
theorem decode_exC (x a : Nat) : decode (exC x a) = Wff.ex x (decode a) := by
  simp [exC, decode_negC, decode_allC, Wff.ex]
theorem decode_andC (a b : Nat) : decode (andC a b) = Wff.and (decode a) (decode b) := by
  simp [andC, decode_negC, decode_impC, Wff.and]

theorem decode_code (φ : Wff) : decode (code φ) = φ := by
  induction φ with
  | eq x y => exact decode_eqC x y
  | el x y => exact decode_elC x y
  | imp φ ψ ih1 ih2 => simp [code, decode_impC, ih1, ih2]
  | neg φ ih => simp [code, decode_negC, ih]
  | all x φ ih => simp [code, decode_allC, ih]

theorem code_ex (x : Nat) (φ : Wff) : code (Wff.ex x φ) = exC x (code φ) := rfl
theorem code_and (φ ψ : Wff) : code (Wff.and φ ψ) = andC (code φ) (code ψ) := rfl

theorem decode_zero : decode 0 = .eq 0 0 := decode_eqC 0 0
theorem decode_one : decode 1 = .el 0 0 := decode_elC 0 0

end TM.PA
