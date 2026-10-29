import TinyCryptids.PAK.Sem

/-!
# The register file and the register operations

The register file is a list of blocks `9 1^v` (`regs`), in the order of first use (`mpos`);
`rfile s n` holds the first `n` registers of `s`.  After the first iteration's first few
operations nine registers exist, and `param2` (the last) may still be missing: `LV s n`.

A register operation starts on the cell right of its node's cell, in a chain state (the node's
cell holds `sy w`, `1 ≤ w ≤ T`).  The chain crosses the gap and the registers before it
(`chain_gap`, `chain_regs`), creating the register on the blank after the file if it is new
(`chain_new`).  An inc shifts the rest of the file right (`shift_ret`), a successful decnz
shifts it left (`dscan_ret`), and the return runs left over `1`s and `9`s to the node's cell
(`ret_back`).
-/

namespace TMK.PA

open TM (Dir)
open TM.PA (R)

/-- the cells of the program counter and the gap -/
def G : Nat := 12

/-- the register file of the present registers `l` -/
def regs : List Nat → List Nat
  | [] => []
  | v :: l => 9 :: List.replicate v 1 ++ regs l

theorem regs_append (a b : List Nat) : regs (a ++ b) = regs a ++ regs b := by
  induction a with
  | nil => rfl
  | cons v a ih => simp [regs, ih]

/-- `l` with position `p` set to `x` -/
def upd (l : List Nat) (p x : Nat) : List Nat := l.take p ++ x :: l.drop (p + 1)

theorem regs_upd (l : List Nat) (p x : Nat) :
    regs (upd l p x) = regs (l.take p) ++ 9 :: List.replicate x 1 ++ regs (l.drop (p + 1)) := by
  simp [upd, regs_append, regs]

theorem regs_split (l : List Nat) (p : Nat) (hp : p < l.length) :
    regs l = regs (l.take p) ++ 9 :: List.replicate (l.getD p 0) 1 ++ regs (l.drop (p + 1)) := by
  have h1 : l.getD p 0 = l[p] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
  rw [h1, ← regs_upd]
  congr 1
  simp only [upd, List.getElem_cons_drop, List.take_append_drop]

/-- the cells the chains, shifts and returns pass: `1` and `9` -/
def U (x : Nat) : Prop := x = 1 ∨ x = 9

theorem U_regs : ∀ (l : List Nat), ∀ x ∈ regs l, U x := by
  intro l
  induction l with
  | nil => intro x hx; simp [regs] at hx
  | cons v l ih =>
    intro x hx
    simp only [regs, List.cons_append, List.mem_cons, List.mem_append, List.mem_replicate] at hx
    rcases hx with h | ⟨_, h⟩ | h
    · right; exact h
    · left; exact h
    · exact ih x h

theorem U_rep (g : Nat) : ∀ x ∈ List.replicate g 1, U x := by
  intro x hx; simp only [List.mem_replicate] at hx; left; exact hx.2

/-! ## moving over runs of cells -/

theorem moveR {q : St} (P : Nat → Prop) (hq : ∀ x, P x → delta q x = some (x, .R, q)) :
    ∀ (xs : List Nat), (∀ x ∈ xs, P x) → ∀ (L R : Strm),
      Reach delta ⟨q, L, lst xs R⟩ ⟨q, lst xs.reverse L, R⟩ := by
  intro xs
  induction xs with
  | nil => intro _ L R; exact Reach.refl _ _
  | cons x xs ih =>
    intro hx L R
    have h1 : Reach delta ⟨q, L, lst (x :: xs) R⟩ ⟨q, x ∷ L, lst xs R⟩ :=
      stepR (hq x (hx x (List.mem_cons_self _ _)))
    refine Reach.trans _ h1 ?_
    have := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) (x ∷ L) R
    simpa [lst_append] using this

theorem moveL {q : St} (P : Nat → Prop) (hq : ∀ x, P x → delta q x = some (x, .L, q)) :
    ∀ (xs : List Nat), (∀ x ∈ xs, P x) → ∀ (L R : Strm), P (R 0) →
      Reach delta ⟨q, lst xs L, R⟩ ⟨q, tl L, L 0 ∷ lst xs.reverse R⟩ := by
  intro xs
  induction xs with
  | nil =>
    intro _ L R hR
    have := stepL (L := L) (R := R) (hq _ hR)
    rwa [cons_head_tl] at this
  | cons y ys ih =>
    intro hy L R hR
    have h1 := stepL (L := lst (y :: ys) L) (R := R) (hq _ hR)
    rw [cons_head_tl] at h1
    refine Reach.trans _ h1 ?_
    have := ih (fun x hx => hy x (List.mem_cons_of_mem _ hx)) L (y ∷ R) (hy y (List.mem_cons_self _ _))
    simpa [lst_append] using this

/-! ## the transitions of the register framework -/

/-- the shift state carrying symbol `c` -/
def cst : Nat → St
  | 9 => .carryS
  | _ => .carry1

theorem cst_tr (c x : Nat) (hc : U c) (hx : U x) : delta (cst c) x = some (c, .R, cst x) := by
  rcases hc with rfl | rfl <;> rcases hx with rfl | rfl <;> rfl

theorem cst_end (c : Nat) (hc : U c) : delta (cst c) 0 = some (c, .L, .retok) := by
  rcases hc with rfl | rfl <;> rfl

theorem ret_tr (x : Nat) (hx : U x) : delta .retok x = some (x, .L, .retok) := by
  rcases hx with rfl | rfl <;> rfl

theorem retf_tr (x : Nat) (hx : U x) : delta .retfail x = some (x, .L, .retfail) := by
  rcases hx with rfl | rfl <;> rfl

/-- a chain state: `cinc j` or `cdec j` -/
def ch (k : Bool) (j : Nat) : St := if k then .cinc j else .cdec j

/-- the operation a chain leads to -/
def first (k : Bool) : St := if k then .carry1 else .dstart

theorem ch_one (k : Bool) (j : Nat) (h1 : 1 ≤ j) (h2 : j ≤ NR) :
    delta (ch k j) 1 = some (1, .R, ch k j) := by
  cases k <;> simp [ch, delta, delta0, chain, h1, h2]

theorem ch_sep (k : Bool) (j : Nat) (h1 : 1 ≤ j) (h2 : j + 1 ≤ NR) :
    delta (ch k (j + 1)) 9 = some (9, .R, ch k j) := by
  have : j + 1 ≠ 1 := by omega
  cases k <;> simp [ch, delta, delta0, chain, this, h2] <;> omega

theorem ch_last (k : Bool) : delta (ch k 1) 9 = some (9, .R, first k) := by
  cases k <;> rfl

theorem ch_new (k : Bool) : delta (ch k 1) 0 = some (9, .R, first k) := by
  cases k <;> rfl

/-! ## the chain -/

theorem chain_gap (k : Bool) (j : Nat) (h1 : 1 ≤ j) (h2 : j ≤ NR) (g : Nat) (L R : Strm) :
    Reach delta ⟨ch k j, L, lst (List.replicate g 1) R⟩ ⟨ch k j, lst (List.replicate g 1) L, R⟩ := by
  have := moveR (q := ch k j) (fun x => x = 1) (fun x hx => by subst hx; exact ch_one k j h1 h2)
    (List.replicate g 1) (fun x hx => (List.mem_replicate.mp hx).2) L R
  rwa [List.reverse_replicate] at this

/-- the chain to register `p` (present): on its unary block, in the operation's state -/
theorem chain_regs (k : Bool) : ∀ (l : List Nat) (p : Nat), p < l.length → p + 1 ≤ NR → ∀ (L : Strm),
    Reach delta ⟨ch k (p + 1), L, lst (regs l) blank⟩
      ⟨first k, lst (regs (l.take p) ++ [9]).reverse L,
        lst (List.replicate (l.getD p 0) 1 ++ regs (l.drop (p + 1))) blank⟩ := by
  intro l
  induction l with
  | nil => intro p hp; simp at hp
  | cons v l ih =>
    intro p hp hN L
    cases p with
    | zero =>
      have := stepR (L := L) (R := lst (regs (v :: l)) blank) (ch_last k)
      simpa [regs, lst_append] using this
    | succ p =>
      have h1 : Reach delta ⟨ch k (p + 1 + 1), L, lst (regs (v :: l)) blank⟩
          ⟨ch k (p + 1), 9 ∷ L, lst (List.replicate v 1) (lst (regs l) blank)⟩ := by
        have := stepR (L := L) (R := lst (regs (v :: l)) blank) (ch_sep k (p + 1) (by omega) hN)
        simpa [regs, lst_append] using this
      refine Reach.trans _ h1 ?_
      refine Reach.trans _ (chain_gap k (p + 1) (by omega) (by omega) v _ _) ?_
      have := ih p (by simp at hp; omega) (by omega) (lst (List.replicate v 1) (9 ∷ L))
      simpa [regs, lst_append, List.reverse_replicate] using this

/-- the chain to the register after the last: it is created -/
theorem chain_new (k : Bool) : ∀ (l : List Nat), l.length + 1 ≤ NR → ∀ (L : Strm),
    Reach delta ⟨ch k (l.length + 1), L, lst (regs l) blank⟩ ⟨first k, lst (regs l ++ [9]).reverse L, blank⟩ := by
  intro l
  induction l with
  | nil =>
    intro _ L
    have := stepR (L := L) (R := blank) (ch_new k)
    simpa [regs] using this
  | cons v l ih =>
    intro hN L
    have h1 : Reach delta ⟨ch k ((v :: l).length + 1), L, lst (regs (v :: l)) blank⟩
        ⟨ch k (l.length + 1), 9 ∷ L, lst (List.replicate v 1) (lst (regs l) blank)⟩ := by
      have := stepR (L := L) (R := lst (regs (v :: l)) blank)
        (ch_sep k (l.length + 1) (by omega) (by simp at hN; omega))
      simpa [regs, lst_append] using this
    refine Reach.trans _ h1 ?_
    refine Reach.trans _ (chain_gap k (l.length + 1) (by omega) (by simp at hN; omega) v _ _) ?_
    have := ih (by simp at hN; omega) (lst (List.replicate v 1) (9 ∷ L))
    simpa [regs, lst_append, List.reverse_replicate] using this

/-! ## the return and the shifts -/

theorem ret_back {q : St} (hq : q = .retok ∨ q = .retfail) (a : Nat) (Lc : Strm) :
    ∀ (ys : List Nat), (∀ y ∈ ys, U y) → ∀ (R : Strm), U (R 0) →
      Reach delta ⟨q, lst ys (a ∷ Lc), R⟩ ⟨q, Lc, a ∷ lst ys.reverse R⟩ := by
  intro ys hy R hR
  have := moveL (q := q) U (fun x hx => by rcases hq with rfl | rfl; exact ret_tr x hx; exact retf_tr x hx)
    ys hy (a ∷ Lc) R hR
  simpa using this

/-- an inc's shift: the carried symbol `c` is written and the rest moves one cell right; then
the return to the node's cell -/
theorem shift_ret (a : Nat) (Lc : Strm) : ∀ (rest ys : List Nat) (c : Nat), U c → (∀ x ∈ rest, U x) →
    (∀ y ∈ ys, U y) →
    Reach delta ⟨cst c, lst ys (a ∷ Lc), lst rest blank⟩ ⟨.retok, Lc, a ∷ lst (ys.reverse ++ c :: rest) blank⟩ := by
  intro rest
  induction rest with
  | nil =>
    intro ys c hc _ hy
    have h1 := stepL (L := lst ys (a ∷ Lc)) (R := blank) (cst_end c hc)
    refine Reach.trans _ h1 ?_
    cases ys with
    | nil => simpa using Reach.refl delta _
    | cons y ys =>
      have := ret_back (Or.inl rfl) a Lc ys (fun x hx => hy x (List.mem_cons_of_mem _ hx))
        (y ∷ c ∷ blank) (hy y (List.mem_cons_self _ _))
      simpa [lst_append] using this
  | cons x rest ih =>
    intro ys c hc hr hy
    have hx : U x := hr x (List.mem_cons_self _ _)
    have h1 := stepR (L := lst ys (a ∷ Lc)) (R := lst (x :: rest) blank) (cst_tr c x hc hx)
    simp only [lst_cons, cons_zero, tl_cons] at h1
    refine Reach.trans _ h1 ?_
    have := ih (c :: ys) x hx (fun y hy' => hr y (List.mem_cons_of_mem _ hy'))
      (fun y hy' => by
        rcases List.mem_cons.mp hy' with rfl | h
        · exact hc
        · exact hy y h)
    simpa [lst_append] using this

/-- a decnz's shift: the `1` left of the head is removed and the rest moves one cell left; then
the return to the node's cell -/
theorem dscan_ret (a : Nat) (Lc : Strm) : ∀ (rest ys : List Nat), (∀ x ∈ rest, U x) → (∀ y ∈ ys, U y) →
    Reach delta ⟨.dscan, 1 ∷ lst ys (a ∷ Lc), lst rest blank⟩ ⟨.retok, Lc, a ∷ lst (ys.reverse ++ rest) blank⟩ := by
  intro rest
  induction rest with
  | nil =>
    intro ys _ hy
    have h1 := stepL (δ := delta) (q := St.dscan) (L := 1 ∷ lst ys (a ∷ Lc)) (R := blank) (w := 0) (q' := .dlast) rfl
    refine Reach.trans _ h1 ?_
    have h2 := stepL (δ := delta) (q := St.dlast) (L := lst ys (a ∷ Lc)) (R := 1 ∷ 0 ∷ blank) (w := 0) (q' := .retok) rfl
    simp only [tl_cons, cons_zero, tl_blank] at h1 h2 ⊢
    refine Reach.trans _ h2 ?_
    rw [cons_blank, cons_blank]
    cases ys with
    | nil => simpa using Reach.refl delta _
    | cons y ys =>
      have := ret_back (Or.inl rfl) a Lc ys (fun x hx => hy x (List.mem_cons_of_mem _ hx))
        (y ∷ blank) (hy y (List.mem_cons_self _ _))
      simpa [lst_append] using this
  | cons x rest ih =>
    intro ys hr hy
    have hx : U x := hr x (List.mem_cons_self _ _)
    have hr' : ∀ y ∈ rest, U y := fun y h => hr y (List.mem_cons_of_mem _ h)
    rcases hx with rfl | rfl
    · have h1 := stepR (δ := delta) (q := St.dscan) (L := 1 ∷ lst ys (a ∷ Lc)) (R := lst (1 :: rest) blank)
        (w := 1) (q' := .dscan) rfl
      simp only [lst_cons, cons_zero, tl_cons] at h1
      refine Reach.trans _ h1 ?_
      have := ih (1 :: ys) hr' (fun y h => by
        rcases List.mem_cons.mp h with rfl | h
        · left; rfl
        · exact hy y h)
      simpa [lst_append] using this
    · have h1 := stepL (δ := delta) (q := St.dscan) (L := 1 ∷ lst ys (a ∷ Lc)) (R := lst (9 :: rest) blank)
        (w := 1) (q' := .dput) rfl
      simp only [lst_cons, cons_zero, tl_cons] at h1
      refine Reach.trans _ h1 ?_
      have h2 := stepR (δ := delta) (q := St.dput) (L := lst ys (a ∷ Lc)) (R := 1 ∷ 1 ∷ lst rest blank)
        (w := 9) (q' := .dscan) rfl
      simp only [cons_zero, tl_cons] at h2
      refine Reach.trans _ h2 ?_
      have h3 := stepR (δ := delta) (q := St.dscan) (L := 9 ∷ lst ys (a ∷ Lc)) (R := 1 ∷ lst rest blank)
        (w := 1) (q' := .dscan) rfl
      simp only [cons_zero, tl_cons] at h3
      refine Reach.trans _ h3 ?_
      have := ih (9 :: ys) hr' (fun y h => by
        rcases List.mem_cons.mp h with rfl | h
        · right; rfl
        · exact hy y h)
      simpa [lst_append] using this

end TMK.PA
