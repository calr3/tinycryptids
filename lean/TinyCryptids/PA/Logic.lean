import TinyCryptids.PA.Luk

/-!
# Hilbert-style derivations

`Prov Ax` is the closure of an axiom set under modus ponens and generalisation.  With
Łukasiewicz's propositional axioms (B1–B3, `Prop3`), `Luk.lean` derives permutation,
contraposition, contraction and `φ ∧ ψ → φ`; with B4 (`all_congr`) implications pass under
quantifiers.  This gives the two rewrites the machine uses (antecedents swapped in B4 and
inside E) and `⊢ v0 = v0`.
-/

namespace TM.PA

open TinyCryptids Wff

variable {Ax : Wff → Prop}

theorem Prov.mono {Ax Ax' : Wff → Prop} (h : ∀ φ, Ax φ → Prov Ax' φ) {φ : Wff} (hφ : Prov Ax φ) :
    Prov Ax' φ := by
  induction hφ with
  | ax h' => exact h _ h'
  | mp _ _ ih1 ih2 => exact Prov.mp ih1 ih2
  | gen x _ ih => exact Prov.gen x ih

theorem provable_iff (φ : Wff) : Provable φ ↔ Prov Axiom φ := by
  constructor
  · intro h
    induction h with
    | ax h => exact Prov.ax h
    | mp _ _ ih1 ih2 => exact Prov.mp ih1 ih2
    | gen x _ ih => exact Prov.gen x ih
  · intro h
    induction h with
    | ax h => exact Provable.ax h
    | mp _ _ ih1 ih2 => exact Provable.mp ih1 ih2
    | gen x _ ih => exact Provable.gen x ih

section
variable (hP : Prop3 Ax)
include hP

theorem syl {p q r : Wff} (h1 : Prov Ax (imp p q)) (h2 : Prov Ax (imp q r)) : Prov Ax (imp p r) :=
  Prov.mp (Prov.mp (hP.b1 p q r) h1) h2

theorem perm_r {p q r : Wff} (h : Prov Ax (imp p (imp q r))) : Prov Ax (imp q (imp p r)) :=
  Prov.mp (perm hP p q r) h

theorem contra_r {p q : Wff} (h : Prov Ax (imp p q)) : Prov Ax (imp (neg q) (neg p)) :=
  Prov.mp (contra hP p q) h

theorem imp_left {p q : Wff} (r : Wff) (h : Prov Ax (imp p q)) : Prov Ax (imp (imp q r) (imp p r)) :=
  Prov.mp (hP.b1 p q r) h

/-- `a → a'` gives `a ∧ b → a' ∧ b` -/
theorem and_congr_left {a a' : Wff} (b : Wff) (h : Prov Ax (imp a a')) :
    Prov Ax (imp (Wff.and a b) (Wff.and a' b)) :=
  contra_r hP (imp_left hP (neg b) h)

end

/-- B4 in its standard form is derivable -/
def QAx (Ax : Wff → Prop) : Prop :=
  ∀ x φ ψ, Prov Ax (imp (all x (imp φ ψ)) (imp (all x φ) (all x ψ)))

section
variable (hP : Prop3 Ax) (hQ : QAx Ax)
include hP hQ

omit hP in
theorem all_congr {p q : Wff} (x : Nat) (h : Prov Ax (imp p q)) : Prov Ax (imp (all x p) (all x q)) :=
  Prov.mp (hQ x p q) (Prov.gen x h)

theorem ex_congr {p q : Wff} (x : Nat) (h : Prov Ax (imp p q)) : Prov Ax (imp (ex x p) (ex x q)) :=
  contra_r hP (all_congr hQ x (contra_r hP h))

end

/-! ## the matrix of E with its first antecedents swapped -/

/-- E's matrix (form 0) -/
def eMat (φ : Wff) : Wff :=
  Wff.and (imp (imp (neg (el 0 2)) (eq 0 3)) (imp (all 1 φ) (el 0 1))) (imp (el 0 1) (all 1 φ))

/-- E's matrix with the first two antecedents swapped (the machine's form 1) -/
def eMat1 (φ : Wff) : Wff :=
  Wff.and (imp (all 1 φ) (imp (imp (neg (el 0 2)) (eq 0 3)) (el 0 1))) (imp (el 0 1) (all 1 φ))

theorem e_swap (hP : Prop3 Ax) (hQ : QAx Ax) (φ : Wff) :
    Prov Ax (imp (ex 1 (all 0 (eMat φ))) (ex 1 (all 0 (eMat1 φ)))) ∧
    Prov Ax (imp (ex 1 (all 0 (eMat1 φ))) (ex 1 (all 0 (eMat φ)))) :=
  ⟨ex_congr hP hQ 1 (all_congr hQ 0 (and_congr_left hP _ (perm hP _ _ _))),
   ex_congr hP hQ 1 (all_congr hQ 0 (and_congr_left hP _ (perm hP _ _ _)))⟩

end TM.PA
