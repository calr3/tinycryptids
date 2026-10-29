import TinyCryptids.Core.Lemmas
import TinyCryptids.PA.Sem

/-!
# The register file on the tape

Right of the program counter the tape holds zeros, the *-1 register* (a run of ones ending at
a fixed cell `G`), and the registers as unary blocks: register value `v` is `1^(v+1)`, each
block preceded by a single `0` (`blist`).  The blocks end the written tape.

This file proves the register operations of phase 2: the chain of states `2b.reg.k` walks to
register `r`, `inc` lengthens it and shifts the blocks to its right one cell right, a
successful `decnz` shortens it and shifts the blocks to its right one cell left (leaving a new
block `1` = value 0 at the end), and the return walks left to the `00` that marks the end of
the program counter.
-/

namespace TM.PA

open TM

/-- Cells of register blocks, each preceded by a `0`. -/
def blist : List Nat → List Bool
  | [] => []
  | v :: vs => false :: (List.replicate (v + 1) true ++ blist vs)

/-- Cells from the -1 register (`a` ones) to the end of the register file. -/
def rcells (a : Nat) (rs : List Nat) : List Bool := List.replicate a true ++ blist rs

@[simp] theorem blist_nil : blist [] = [] := rfl
theorem blist_cons (v : Nat) (vs : List Nat) :
    blist (v :: vs) = false :: (List.replicate (v + 1) true ++ blist vs) := rfl

theorem blist_append (us vs : List Nat) : blist (us ++ vs) = blist us ++ blist vs := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [blist_cons, ih]

theorem app_ones (n : Nat) (s : Strm) : app (List.replicate n true) s = ones n s := app_replicate n s

/-! ## single steps, as in the other machines' `Tac.lean` -/

section
variable {dag : Nat → Option (Ch × Ch)}

abbrev Rch (dag : Nat → Option (Ch × Ch)) := Reach (delta dag 0)

theorem sR {q q' : St} {L R : Strm} {b w : Bool} (h : delta dag 0 q b = some (w, Dir.R, q')) :
    Rch dag ⟨q, L, b ::: R⟩ ⟨q', w ::: L, R⟩ := stepR (δ := delta dag 0) (R := b ::: R) h

theorem sL {q q' : St} {s R : Strm} {b w : Bool} (h : delta dag 0 q b = some (w, Dir.L, q')) :
    Rch dag (cfgL q (b ::: s) R) (cfgL q' s (w ::: R)) := stepL' (δ := delta dag 0) (s := b ::: s) h

/-- a left move from an ordinary configuration -/
theorem sLc {q q' : St} {s R : Strm} {b c w : Bool} (h : delta dag 0 q c = some (w, Dir.L, q')) :
    Rch dag ⟨q, b ::: s, c ::: R⟩ ⟨q', s, b ::: w ::: R⟩ :=
  stepL (δ := delta dag 0) (L := b ::: s) (R := c ::: R) h

theorem Rch.tr {a b c : Cfg St} (h1 : Rch dag a b) (h2 : Rch dag b c) : Rch dag a c :=
  Reach.trans (delta dag 0) h1 h2

theorem Rch.of_eq {a b : Cfg St} (h : a = b) : Rch dag a b := h ▸ Reach.refl _ _

/-- a `cfgL` configuration is an ordinary one -/
theorem cfgL_cons (q : St) (b : Bool) (s R : Strm) : cfgL q (b ::: s) R = ⟨q, s, b ::: R⟩ := rfl

end

macro "gR" : tactic => `(tactic| refine Rch.tr (sR (by rfl)) ?_)
macro "gL" : tactic => `(tactic| refine Rch.tr (sL (by rfl)) ?_)
macro "gLc" : tactic => `(tactic| refine Rch.tr (sLc (by rfl)) ?_)
macro "fin" : tactic => `(tactic| exact Reach.refl _ _)

section
variable {dag : Nat → Option (Ch × Ch)}

theorem scanRq {q : St} (h : delta dag 0 q true = some (true, Dir.R, q)) (n : Nat) (L R : Strm) :
    Rch dag ⟨q, L, ones n R⟩ ⟨q, ones n L, R⟩ := scanR h n L R

theorem scanLq {q : St} (h : delta dag 0 q true = some (true, Dir.L, q)) (n : Nat) (s R : Strm) :
    Rch dag (cfgL q (ones n s) R) (cfgL q s (ones n R)) := scanL h n s R

theorem zerosRq {q : St} (h : delta dag 0 q false = some (false, Dir.R, q)) (n : Nat) (L R : Strm) :
    Rch dag ⟨q, L, zeros n R⟩ ⟨q, zeros n L, R⟩ := scanR0 h n L R

theorem zerosLq {q : St} (h : delta dag 0 q false = some (false, Dir.L, q)) (n : Nat) (s R : Strm) :
    Rch dag (cfgL q (zeros n s) R) (cfgL q s (zeros n R)) := scanL0 h n s R

/-! ## the chain to register `r` -/

theorem chI_true (k : Fin 12) : delta dag 0 (.chI k) true = some (true, Dir.R, .chI k) := by
  obtain ⟨n, h⟩ := k; cases n <;> rfl

theorem chD_true (k : Nat) (h : k + 1 < 12) :
    delta dag 0 (.chD ⟨k + 1, h⟩) true = some (true, Dir.R, .chD ⟨k + 1, h⟩) := rfl

theorem chainI (vs : List Nat) (k : Nat) (hk : k + vs.length < 12) (L X : Strm) :
    Rch dag ⟨.chI ⟨k + vs.length, hk⟩, L, app (blist vs) X⟩
      ⟨.chI ⟨k, by omega⟩, app (blist vs).reverse L, X⟩ := by
  induction vs generalizing k L with
  | nil => exact Reach.refl _ _
  | cons v vs ih =>
    have hk' : k + vs.length + 1 < 12 := by simp at hk; omega
    show Rch dag ⟨.chI ⟨(k + vs.length) + 1, hk'⟩, L, false ::: app (List.replicate (v+1) true ++ blist vs) X⟩ _
    gR
    rw [app_append, app_ones]
    refine Rch.tr (scanRq (chI_true _) _ _ _) ?_
    have := ih k (by omega) (ones (v + 1) (false ::: L))
    simp only [blist_cons, List.reverse_cons, List.reverse_append, List.append_assoc,
      List.reverse_replicate, app_append, app_ones] at this ⊢
    exact this

theorem chainD (vs : List Nat) (k : Nat) (hk : k + 1 + vs.length < 12) (L X : Strm) :
    Rch dag ⟨.chD ⟨k + 1 + vs.length, hk⟩, L, app (blist vs) X⟩
      ⟨.chD ⟨k + 1, by omega⟩, app (blist vs).reverse L, X⟩ := by
  induction vs generalizing k L with
  | nil => exact Reach.refl _ _
  | cons v vs ih =>
    have hk' : k + vs.length + 1 + 1 < 12 := by simp at hk; omega
    have e : (⟨k + 1 + (v :: vs).length, hk⟩ : Fin 12) = ⟨(k + vs.length + 1) + 1, hk'⟩ :=
      Fin.ext (by simp; omega)
    rw [e]
    show Rch dag ⟨.chD ⟨(k + vs.length + 1) + 1, hk'⟩, L, false ::: app (List.replicate (v+1) true ++ blist vs) X⟩ _
    gR
    rw [app_append, app_ones]
    refine Rch.tr (scanRq (chD_true (k + vs.length) (by omega)) _ _ _) ?_
    have := ih k (by omega) (ones (v + 1) (false ::: L))
    simp only [blist_cons, List.reverse_cons, List.reverse_append, List.append_assoc,
      List.reverse_replicate, app_append, app_ones, Nat.add_right_comm k 1] at this ⊢
    exact this

/-! ## `inc`: lengthen the block and shift the blocks right of it one cell right -/

/-- cells under `ishift1` once the separator right of the grown block is overwritten -/
def shiftIn : List Nat → List Bool
  | [] => []
  | u :: rest => List.replicate (u + 1) true ++ blist rest

theorem app_blist_blank (rest : List Nat) :
    app (blist rest) blank = false ::: app (shiftIn rest) blank := by
  cases rest with
  | nil => exact cons_blank.symm
  | cons u rest => rfl

theorem ishift (rest : List Nat) (L : Strm) :
    Rch dag ⟨.ishift1, L, app (shiftIn rest) blank⟩ ⟨.ishift1, app (blist rest).reverse L, blank⟩ := by
  induction rest generalizing L with
  | nil => exact Reach.refl _ _
  | cons u rest ih =>
    show Rch dag ⟨.ishift1, L, app (true :: (List.replicate u true ++ blist rest)) blank⟩ _
    rw [app_cons]
    gR
    rw [app_append, app_ones]
    refine Rch.tr (scanRq (by rfl) _ _ _) ?_
    rw [app_blist_blank]
    gR
    refine Rch.tr (ih _) ?_
    have e : app (blist (u :: rest)).reverse L =
        app (blist rest).reverse (true ::: ones u (false ::: L)) := by
      simp only [blist_cons, List.reverse_cons, List.reverse_append, List.reverse_replicate,
        List.append_assoc, app_append, app_ones, List.singleton_append, app_cons, app_nil]
      rw [← ones_succ, ones_succ']
    rw [e]
    exact Reach.refl _ _

/-- `inc` on a block `1^(v+1)` (state `2b.reg.-2.inc` on its first cell): it becomes
`1^(v+2)`, the blocks after it move one cell right, and `return_0_1` starts on the last cell. -/
theorem incOp (v : Nat) (rest : List Nat) (L : Strm) :
    Rch dag ⟨.chI 0, L, app (List.replicate (v + 1) true ++ blist rest) blank⟩
      (cfgL .r0a (app (List.replicate (v + 2) true ++ blist rest).reverse L) blank) := by
  rw [app_append, app_ones]
  refine Rch.tr (scanRq (chI_true _) _ _ _) ?_
  rw [app_blist_blank]
  gR
  refine Rch.tr (ishift rest _) ?_
  rw [← cons_blank]
  refine Rch.tr (stepL (δ := delta dag 0) (L := app (blist rest).reverse (true ::: ones (v + 1) L))
    (R := false ::: blank) (by rfl)) ?_
  have e : app (List.replicate (v + 2) true ++ blist rest).reverse L =
      app (blist rest).reverse (true ::: ones (v + 1) L) := by
    simp only [List.reverse_append, List.reverse_replicate, app_append, app_ones]; rfl
  rw [e]
  exact Reach.refl _ _

/-! ## `decnz` -/

/-- cells right of a block after `dec`'s left shift, up to the new block at the end -/
def shiftOut : List Nat → List Bool
  | [] => []
  | u :: us => List.replicate u true ++ false :: true :: shiftOut us

theorem shiftOut_eq (rest : List Nat) :
    false :: true :: shiftOut rest = blist rest ++ [false, true] := by
  induction rest with
  | nil => rfl
  | cons u us ih =>
    simp only [shiftOut, blist_cons, List.cons_append, List.append_assoc, ← ih]
    simp [List.replicate_succ]

theorem dscan (rest : List Nat) (L : Strm) :
    Rch dag ⟨.dscan1, L, app (blist rest) blank⟩
      (cfgL .dshift1 (false ::: app (blist rest).reverse L) blank) := by
  induction rest generalizing L with
  | nil =>
    have h1 : app (blist []) blank = false ::: false ::: blank := by
      rw [blist_nil, app_nil, cons_blank, cons_blank]
    rw [h1]
    gR; gLc
    exact Rch.of_eq (by simp [cfgL, cons_blank])
  | cons u rest ih =>
    show Rch dag ⟨.dscan1, L, false ::: app (true :: (List.replicate u true ++ blist rest)) blank⟩ _
    gR
    rw [app_cons]
    gR
    rw [app_append, app_ones]
    refine Rch.tr (scanRq (by rfl) _ _ _) ?_
    refine Rch.tr (ih _) ?_
    have e : app (blist (u :: rest)).reverse L =
        app (blist rest).reverse (ones u (true ::: false ::: L)) := by
      simp only [blist_cons, List.reverse_cons, List.reverse_append, List.reverse_replicate,
        List.append_assoc, app_append, app_ones, List.singleton_append, app_cons, app_nil]
      rw [ones_succ']
    rw [e]
    exact Reach.refl _ _

theorem dshift_block (u : Nat) (Lx R : Strm) :
    Rch dag (cfgL .dshift1 (false ::: ones (u + 1) (false ::: Lx)) R)
      (cfgL .dshift1 (false ::: Lx) (ones u (false ::: true ::: R))) := by
  gL
  rw [ones_succ]
  gL
  exact scanLq (by rfl) _ _ _

theorem dshift (rest : List Nat) (L1 R : Strm) :
    Rch dag (cfgL .dshift1 (false ::: app (blist rest).reverse L1) R)
      (cfgL .dshift1 (false ::: L1) (app (shiftOut rest) R)) := by
  induction rest generalizing L1 R with
  | nil => exact Reach.refl _ _
  | cons u rest ih =>
    have e : app (blist (u :: rest)).reverse L1 =
        app (blist rest).reverse (ones (u + 1) (false ::: L1)) := by
      simp [blist_cons, List.reverse_append, app_append, app_ones]
    rw [e]
    refine Rch.tr (ih _ _) ?_
    have := dshift_block (dag := dag) u L1 (app (shiftOut rest) R)
    simpa [shiftOut, app_append, app_ones] using this

/-- a successful `decnz` on a block `1^(w+2)` (state `2b.reg.-2.dec` on its first cell,
separator on its left): the block becomes `1^(w+1)`, the blocks after it move one cell left,
a new block `1` ends the file, and `return_0_1` starts left of the separator. -/
theorem decOpPos (w : Nat) (rest : List Nat) (L : Strm) :
    Rch dag ⟨.chD 0, false ::: L, app (List.replicate (w + 2) true ++ blist rest) blank⟩
      (cfgL .r0a L (app (blist (w :: (rest ++ [0]))) blank)) := by
  show Rch dag ⟨.chD 0, false ::: L, app (true :: true :: (List.replicate w true ++ blist rest)) blank⟩ _
  rw [app_cons, app_cons]
  gR; gR
  rw [app_append, app_ones]
  refine Rch.tr (scanRq (by rfl) _ _ _) ?_
  refine Rch.tr (dscan rest _) ?_
  refine Rch.tr (dshift rest _ _) ?_
  -- the block itself: shift it and stop left of its separator
  show Rch dag (cfgL .dshift1 (false ::: ones w (true ::: false ::: false ::: L)) _) _
  rw [ones_cons_true, ← ones_succ]
  gL
  rw [ones_succ]
  gL
  refine Rch.tr (scanLq (by rfl) _ _ _) ?_
  gL; gL
  have e : app (blist (w :: (rest ++ [0]))) blank =
      false ::: true ::: ones w (false ::: true ::: app (shiftOut rest) blank) := by
    have h2 := shiftOut_eq rest
    have h3 : blist [0] = [false, true] := rfl
    rw [blist_cons, blist_append, h3, ← h2]
    simp only [app_cons, app_append, app_ones, List.replicate_succ, cons_blank]
  rw [e]
  exact Reach.refl _ _

/-- a failed `decnz` (block `1`): the block is restored and `return_1_1` starts on its
separator. -/
theorem decOpZero (rest : List Nat) (L : Strm) :
    Rch dag ⟨.chD 0, false ::: L, app (true :: blist rest) blank⟩
      (cfgL .r1a (false ::: L) (app (true :: blist rest) blank)) := by
  rw [app_cons, app_blist_blank]
  gR
  gL; gL
  rw [← app_blist_blank]
  exact Reach.refl _ _

/-! ## the return to the `00` left of the -1 register -/

/-- cell lists (nearest first) where every `0` is followed by a `1` -/
inductive Sep1 : List Bool → Prop
  | nil : Sep1 []
  | one {l} : Sep1 l → Sep1 (true :: l)
  | zero {l} : Sep1 l → Sep1 (false :: true :: l)

theorem ret0 {w : List Bool} (hw : Sep1 w) (s R : Strm) :
    Rch dag (cfgL .r0a (app w (false ::: false ::: s)) R)
      (cfgL .brk0 s (false ::: false ::: app w.reverse R)) := by
  induction hw generalizing R with
  | nil => gL; gL; exact Reach.refl _ _
  | @one l _ ih =>
    rw [app_cons]; gL
    simpa [app_append] using ih (true ::: R)
  | @zero l _ ih =>
    rw [app_cons, app_cons]; gL; gL
    simpa [app_append] using ih (true ::: false ::: R)

theorem ret1 {w : List Bool} (hw : Sep1 w) (s R : Strm) :
    Rch dag (cfgL .r1a (app w (false ::: false ::: s)) R)
      (cfgL .brk1 s (false ::: false ::: app w.reverse R)) := by
  induction hw generalizing R with
  | nil => gL; gL; exact Reach.refl _ _
  | @one l _ ih =>
    rw [app_cons]; gL
    simpa [app_append] using ih (true ::: R)
  | @zero l _ ih =>
    rw [app_cons, app_cons]; gL; gL
    simpa [app_append] using ih (true ::: false ::: R)

theorem rep_cons {α : Type} (v : Nat) (a : α) (l : List α) :
    List.replicate v a ++ a :: l = a :: (List.replicate v a ++ l) := by
  induction v with
  | zero => rfl
  | succ v ih => simp [List.replicate_succ, ih]

theorem Sep1.tail_one {l : List Bool} (h : Sep1 (true :: l)) : Sep1 l := by
  cases h; assumption

theorem Sep1.replicate (n : Nat) {l : List Bool} (h : Sep1 l) : Sep1 (List.replicate n true ++ l) := by
  induction n with
  | zero => exact h
  | succ n ih => exact Sep1.one ih

/-- blocks (reversed) followed by a cell `1` -/
theorem Sep1.blocks (vs : List Nat) {l : List Bool} (h : Sep1 (true :: l)) :
    Sep1 ((TM.PA.blist vs).reverse ++ true :: l) := by
  induction vs generalizing l with
  | nil => exact h
  | cons v vs ih =>
    have e : (TM.PA.blist (v :: vs)).reverse ++ true :: l =
        (TM.PA.blist vs).reverse ++ true :: (List.replicate v true ++ false :: true :: l) := by
      simp [blist_cons, List.reverse_append, List.append_assoc, List.replicate_succ, rep_cons]
    rw [e]
    exact ih (Sep1.one (Sep1.replicate v (Sep1.zero h.tail_one)))

theorem Sep1.blocks_false (vs : List Nat) {l : List Bool} (h : Sep1 (true :: l)) :
    Sep1 (false :: ((TM.PA.blist vs).reverse ++ true :: l)) := by
  induction vs generalizing l with
  | nil => exact Sep1.zero h.tail_one
  | cons v vs ih =>
    have e : (TM.PA.blist (v :: vs)).reverse ++ true :: l =
        (TM.PA.blist vs).reverse ++ true :: (List.replicate v true ++ false :: true :: l) := by
      simp [blist_cons, List.reverse_append, List.append_assoc, List.replicate_succ, rep_cons]
    rw [e]
    exact ih (Sep1.one (Sep1.replicate v (Sep1.zero h.tail_one)))

theorem Sep1.rcells_rev {a : Nat} (ha : 1 ≤ a) (vs : List Nat) : Sep1 (rcells a vs).reverse := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have e : (rcells (a' + 1) vs).reverse = (TM.PA.blist vs).reverse ++ true :: List.replicate a' true := by
    simp [rcells, List.reverse_append, List.replicate_succ, rep_cons]
  rw [e]
  exact Sep1.blocks vs (Sep1.one (by simpa using Sep1.replicate a' Sep1.nil))

theorem Sep1.rcells_rev_false {a : Nat} (ha : 1 ≤ a) (vs : List Nat) :
    Sep1 (false :: (rcells a vs).reverse) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have e : (rcells (a' + 1) vs).reverse = (TM.PA.blist vs).reverse ++ true :: List.replicate a' true := by
    simp [rcells, List.reverse_append, List.replicate_succ, rep_cons]
  rw [e]
  exact Sep1.blocks_false vs (Sep1.one (by simpa using Sep1.replicate a' Sep1.nil))

/-! ## phase 2: from the marker to `6.break` -/

theorem rcells_app (a : Nat) (pre rest : List Nat) (v : Nat) :
    app (rcells a (pre ++ v :: rest)) blank =
      ones a (app (blist pre) (false ::: app (List.replicate (v + 1) true ++ blist rest) blank)) := by
  simp [rcells, blist_append, blist_cons, app_append, app_ones]

/-- `inc` on register `pre.length`: from the chain state on the cell right of the (erased)
marker to `6.break.0` on the cell left of it. -/
theorem phase2Inc (pre rest : List Nat) (v : Nat) (hr : pre.length < 10) (a : Nat) (ha : 1 ≤ a)
    (L : Strm) :
    Rch dag ⟨.chI ⟨pre.length + 2, by omega⟩, false ::: L, false ::: app (rcells a (pre ++ v :: rest)) blank⟩
      (cfgL .brk0 L (false ::: false ::: app (rcells a (pre ++ (v + 1) :: rest)) blank)) := by
  gR
  rw [rcells_app]
  refine Rch.tr (scanRq (chI_true _) _ _ _) ?_
  have e : (⟨pre.length + 1, by omega⟩ : Fin 12) = ⟨1 + pre.length, by omega⟩ := Fin.ext (by simp; omega)
  rw [e]
  refine Rch.tr (chainI pre 1 (by omega) _ _) ?_
  gR
  refine Rch.tr (incOp v rest _) ?_
  have hw : Sep1 (rcells a (pre ++ (v + 1) :: rest)).reverse := Sep1.rcells_rev ha _
  have e1 : app (rcells a (pre ++ (v + 1) :: rest)).reverse (false ::: false ::: L) =
      app (List.replicate (v + 2) true ++ blist rest).reverse
        (false ::: app (blist pre).reverse (ones a (false ::: false ::: L))) := by
    simp [rcells, blist_append, blist_cons, List.reverse_append, app_append, app_ones]
  rw [← e1]
  refine Rch.tr (ret0 hw L blank) (Rch.of_eq ?_)
  simp [List.reverse_reverse]

/-- the chain of `decnz` on register `pre.length`, up to the operation state on its block -/
theorem chainDec (pre : List Nat) (hr : pre.length < 10) (a : Nat) (L X : Strm) :
    Rch dag ⟨.chD ⟨pre.length + 2, by omega⟩, false ::: L, false ::: ones a (app (blist pre) (false ::: X))⟩
      ⟨.chD 0, false ::: app (rcells a pre).reverse (false ::: false ::: L), X⟩ := by
  gR
  refine Rch.tr (scanRq (chD_true _ (by omega)) _ _ _) ?_
  have e : (⟨pre.length + 1, by omega⟩ : Fin 12) = ⟨0 + 1 + pre.length, by omega⟩ :=
    Fin.ext (by simp; omega)
  rw [e]
  refine Rch.tr (chainD pre 0 (by omega) _ _) ?_
  gR
  exact Rch.of_eq (by simp [rcells, List.reverse_append, app_append, app_ones])

/-- a successful `decnz` on register `pre.length` (value `w + 1`): a new register ends the file -/
theorem phase2DecPos (pre rest : List Nat) (w : Nat) (hr : pre.length < 10) (a : Nat) (ha : 1 ≤ a)
    (L : Strm) :
    Rch dag ⟨.chD ⟨pre.length + 2, by omega⟩, false ::: L, false ::: app (rcells a (pre ++ (w + 1) :: rest)) blank⟩
      (cfgL .brk0 L (false ::: false ::: app (rcells a (pre ++ w :: (rest ++ [0]))) blank)) := by
  rw [rcells_app]
  refine Rch.tr (chainDec pre hr a L _) ?_
  refine Rch.tr (decOpPos w rest _) ?_
  refine Rch.tr (ret0 (Sep1.rcells_rev ha pre) L _) (Rch.of_eq ?_)
  simp [rcells, blist_append, List.reverse_reverse, app_append]

/-- a failed `decnz` on register `pre.length` (value 0) -/
theorem phase2DecZero (pre rest : List Nat) (hr : pre.length < 10) (a : Nat) (ha : 1 ≤ a)
    (L : Strm) :
    Rch dag ⟨.chD ⟨pre.length + 2, by omega⟩, false ::: L, false ::: app (rcells a (pre ++ 0 :: rest)) blank⟩
      (cfgL .brk1 L (false ::: false ::: app (rcells a (pre ++ 0 :: rest)) blank)) := by
  rw [rcells_app]
  refine Rch.tr (chainDec pre hr a L _) ?_
  refine Rch.tr (decOpZero rest _) ?_
  refine Rch.tr (ret1 (Sep1.rcells_rev_false ha pre) L _) (Rch.of_eq ?_)
  simp [rcells, blist_append, blist_cons, List.reverse_reverse, app_append, app_ones]

end

end TM.PA
