import TinyCryptids.PA.Frame
import TinyCryptids.PA.Dag

/-!
# The DAG meets the compiler's conditions

Checked node by node with the certificate tables of `Dag.lean`: the leaves are of the kinds the
framework has states for, every program counter has at most 6 zeros in a row (7 dispatch
states), and the program counter never reaches the -1 register at cell `G = 3824`.
-/

namespace TM.PA

/-- the cell of the -1 register after the boot -/
def G : Nat := 3824

def zr (i : Nat) : Nat := zrT.getD i 0
def dep (i : Nat) : Nat := depT.getD i 0

def carOK (i : Nat) : Ch → Bool
  | .node j => zr i + 1 ≤ zr j && zr j ≤ 6 && dep i + 1 ≤ dep j
  | .inc _ => zr i ≤ 5
  | .dec _ => zr i ≤ 5
  | .brk 0 => true
  | _ => false

def cdrOK (i : Nat) : Ch → Bool
  | .node j => dep i + 1 ≤ dep j
  | .inc _ => true
  | .dec _ => true
  | .brk 1 => true
  | .cnt 1 => true
  | .cnt 2 => true
  | .halt => true
  | _ => false

def nodeOK (i : Nat) : Bool :=
  match dag i with
  | some (c, d) => carOK i c && cdrOK i d && zr i ≤ 6 && dep i + 5 ≤ G
  | none => true

def allOK : Nat → Bool
  | 0 => true
  | n + 1 => allOK n && nodeOK n

set_option maxRecDepth 100000 in
theorem allOK_nodes : allOK nNodes = true := by decide

theorem nodeOK_all (i : Nat) : nodeOK i = true := by
  by_cases h : i < nNodes
  · have : ∀ n, allOK n = true → ∀ i < n, nodeOK i = true := by
      intro n; induction n with
      | zero => intro _ i h; omega
      | succ n ih =>
        intro hn i hi
        simp only [allOK, Bool.and_eq_true] at hn
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact ih hn.1 i hi
        · exact hn.2
    exact this _ allOK_nodes i h
  · have : dag i = none := List.get?_eq_none (by rw [table_length]; exact Nat.le_of_not_lt h)
    simp [nodeOK, this]

theorem dagOK : DagOK dag zr dep G where
  root := by decide
  car := by
    intro i c d hi
    have := nodeOK_all i
    simp only [nodeOK, hi, Bool.and_eq_true, decide_eq_true_eq] at this
    have hc := this.1.1.1
    cases c with
    | node j => simp only [carOK, Bool.and_eq_true, decide_eq_true_eq] at hc; exact Or.inl ⟨j, rfl, hc.1.1, hc.1.2, hc.2⟩
    | inc r => simp only [carOK, decide_eq_true_eq] at hc; exact Or.inr (Or.inl ⟨r, Or.inl rfl, hc⟩)
    | dec r => simp only [carOK, decide_eq_true_eq] at hc; exact Or.inr (Or.inl ⟨r, Or.inr rfl, hc⟩)
    | brk k => cases k with
      | zero => exact Or.inr (Or.inr rfl)
      | succ k => simp [carOK] at hc
    | cnt k => simp [carOK] at hc
    | halt => simp [carOK] at hc
  cdr := by
    intro i c d hi
    have := nodeOK_all i
    simp only [nodeOK, hi, Bool.and_eq_true, decide_eq_true_eq] at this
    have hd := this.1.1.2
    cases d with
    | node j => simp only [cdrOK, decide_eq_true_eq] at hd; exact Or.inl ⟨j, rfl, hd⟩
    | inc r => exact Or.inr (Or.inl ⟨r, Or.inl rfl⟩)
    | dec r => exact Or.inr (Or.inl ⟨r, Or.inr rfl⟩)
    | brk k =>
      rcases k with _ | _ | k
      · simp [cdrOK] at hd
      · exact Or.inr (Or.inr (Or.inl rfl))
      · simp [cdrOK] at hd
    | cnt k =>
      rcases k with _ | _ | _ | k
      · simp [cdrOK] at hd
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · simp [cdrOK] at hd
    | halt => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  zr6 := by
    intro i c d hi
    have := nodeOK_all i
    simp only [nodeOK, hi, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.2
  depG := by
    intro i c d hi
    have := nodeOK_all i
    simp only [nodeOK, hi, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2

end TM.PA
