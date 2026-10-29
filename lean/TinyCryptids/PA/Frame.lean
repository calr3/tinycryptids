import TinyCryptids.PA.Tape

/-!
# Dispatch, the walk down the DAG, phase 1 and the program counter updates

The program counter starts at cell 0: the root bits `1 1`, main's entry bit, then the bits
read by the nodes.  *Dispatch* scans left from a `1` counting zeros (a `1` resets the count);
seven zeros in a row mean it is left of the program counter, and it scans right to its first
cell.  `DOK k v` says this works on the cells `v` left of the head (nearest first) when `k`
more zeros may be passed.
-/

namespace TM.PA

open TM

/-- the program counter cells of the path `q` from main -/
def pc (q : List Bool) : List Bool := true :: true :: false :: q

/-- dispatch from `4.dispatch.k` over the cells `v` (nearest first) reaches the first cell -/
def DOK : Nat → List Bool → Prop
  | _, [] => False
  | _, true :: l => l = [] ∨ DOK 6 l
  | 0, false :: _ => False
  | k + 1, false :: l => DOK k l

/-- leading zeros (trailing zeros of the program counter) -/
def lz : List Bool → Nat
  | false :: l => lz l + 1
  | _ => 0

theorem DOK.ne_nil {k : Nat} {v : List Bool} (h : DOK k v) : v ≠ [] := by
  rintro rfl; simp [DOK] at h

theorem tail_app_ne {l : List Bool} (h : l ≠ []) (m : List Bool) : (l ++ m).tail = l.tail ++ m := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => rfl

theorem rev_tail_cons {l : List Bool} (h : l ≠ []) (b : Bool) (R : Strm) :
    app (b :: l).reverse.tail R = app l.reverse.tail (b ::: R) := by
  rw [List.reverse_cons, tail_app_ne (by simpa using h), app_append]; rfl

theorem DOK.of_lz : ∀ (v : List Bool) (k k' : Nat), DOK k v → lz v ≤ k' → DOK k' v
  | [], _, _, h, _ => by simp [DOK] at h
  | true :: _, _, _, h, _ => by simpa [DOK] using h
  | false :: l, 0, _, h, _ => by simp [DOK] at h
  | false :: l, k + 1, 0, _, hl => by simp [lz] at hl
  | false :: l, k + 1, k' + 1, h, hl => by
    simp only [DOK, lz] at h hl ⊢
    exact DOK.of_lz l k k' h (by omega)

section
variable {dag : Nat → Option (Ch × Ch)}

theorem fillR {q : St} (h : delta dag 0 q false = some (true, Dir.R, q)) (n : Nat) (L R : Strm) :
    Rch dag ⟨q, L, zeros n R⟩ ⟨q, ones n L, R⟩ := by
  induction n generalizing L with
  | zero => exact Reach.refl _ _
  | succ n ih =>
    refine Rch.tr (sR (R := zeros n R) h) ?_
    have := ih (true ::: L); rw [← ones_succ'] at this; exact this

/-! ## dispatch -/

theorem disp_true (k : Fin 7) : delta dag 0 (.disp k) true = some (true, Dir.L, .disp 6) := by
  obtain ⟨n, h⟩ := k; cases n <;> rfl

theorem disp_left (R : Strm) :
    Rch dag (cfgL (.disp 6) blank (true ::: R)) ⟨.root1, true ::: blank, R⟩ := by
  have h : (blank : Strm) = zeros 8 blank := (zeros_blank 8).symm
  rw [h]
  gL; gL; gL; gL; gL; gL; gL
  show Rch dag ⟨.scan, blank, zeros 8 (true ::: R)⟩ _
  refine Rch.tr (zerosRq (by rfl) 8 _ _) ?_
  gR
  rw [zeros_blank]
  exact Reach.refl _ _

theorem disp_run : ∀ (v : List Bool) (k : Nat) (hk : k < 7), DOK k v → ∀ R : Strm,
    Rch dag (cfgL (.disp ⟨k, hk⟩) (app v blank) R) ⟨.root1, true ::: blank, app v.reverse.tail R⟩
  | [], _, _, h, _ => absurd h (by simp [DOK])
  | true :: l, k, hk, h, R => by
    rw [app_cons]
    refine Rch.tr (sL (disp_true _)) ?_
    have h : l = [] ∨ DOK 6 l := by simpa only [DOK] using h
    rcases h with rfl | h
    · exact disp_left R
    · refine Rch.tr (disp_run l 6 (by omega) h _) (Rch.of_eq ?_)
      rw [rev_tail_cons h.ne_nil]
  | false :: l, 0, _, h, _ => absurd h (by simp [DOK])
  | false :: l, k + 1, hk, h, R => by
    rw [app_cons]
    refine Rch.tr (sL (by rfl)) ?_
    have h : DOK k l := h
    refine Rch.tr (disp_run l k (by omega) h _) (Rch.of_eq ?_)
    rw [rev_tail_cons h.ne_nil]

/-! ## the walk from the root -/

variable (dag) in
/-- the node reached from node `i` by the bits `q` (all children on the way are nodes) -/
def walkFrom : Nat → List Bool → Option Nat
  | i, [] => some i
  | i, b :: q => match dag i with
    | some (c, d) => match (if b then d else c) with
      | .node j => walkFrom j q
      | _ => none
    | none => none

theorem node_step {i j : Nat} {c d : Ch} (h : dag i = some (c, d)) (b : Bool)
    (hb : (if b then d else c) = .node j) :
    delta dag 0 (.node i) b = some (b, Dir.R, .node j) := by
  cases b <;> simp at hb <;> simp [delta, h, hb, carTr, cdrTr, Ch.st]

theorem walk_run : ∀ (q : List Bool) (i j : Nat), walkFrom dag i q = some j → ∀ L X : Strm,
    Rch dag ⟨.node i, L, app q X⟩ ⟨.node j, app q.reverse L, X⟩
  | [], i, j, h, L, X => by
    simp [walkFrom] at h; subst h; exact Reach.refl _ _
  | b :: q, i, j, h, L, X => by
    simp only [walkFrom] at h
    split at h
    · rename_i c d hcd
      split at h
      · rename_i k hk
        rw [app_cons]
        refine Rch.tr (sR (node_step hcd b hk)) ?_
        refine Rch.tr (walk_run q k j h _ _) (Rch.of_eq ?_)
        simp [app_append]
      · simp at h
    · simp at h

/-- from `5.root.1` (on cell 1) the walk reaches the node of the path `q` (main's entry bit,
cell 2, is cleared on the way) -/
theorem root_run (b : Bool) (q : List Bool) (j : Nat) (h : walkFrom dag 0 q = some j) (X : Strm) :
    Rch dag ⟨.root1, true ::: blank, app (true :: b :: q) X⟩ ⟨.node j, app (pc q).reverse blank, X⟩ := by
  rw [app_cons, app_cons]
  gR
  refine Rch.tr (sR (b := b) (by cases b <;> rfl)) ?_
  refine Rch.tr (walk_run q 0 j h _ _) (Rch.of_eq ?_)
  simp [pc, app_append]

/-! ## `6.continue.0` and dispatch: from a program counter `u` back to `5.root.1` -/

theorem DOK.split : ∀ (v : List Bool) (k : Nat), DOK k v →
    ∃ rest, v = List.replicate (lz v) false ++ true :: rest ∧ (rest = [] ∨ DOK 6 rest)
  | [], _, h => by simp [DOK] at h
  | true :: l, _, h => ⟨l, by simp [lz], by simpa only [DOK] using h⟩
  | false :: l, 0, h => by simp [DOK] at h
  | false :: l, k + 1, h => by
    obtain ⟨rest, h1, h2⟩ := DOK.split l k h
    exact ⟨rest, by simp [lz, List.replicate_succ]; exact h1, h2⟩

theorem app_zeros (n : Nat) (X : Strm) : app (List.replicate n false) X = zeros n X := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, app_cons, ih]; rfl

/-- `6.continue.0` passes any number of zeros left to a `1` and dispatches from there -/
theorem cnt0_run' (k : Nat) (rest : List Bool) (h : rest = [] ∨ DOK 6 rest) (R : Strm) :
    Rch dag (cfgL .cnt0 (zeros k (true ::: app rest blank)) R)
      ⟨.root1, true ::: blank, app (rest.reverse ++ true :: List.replicate k false).tail R⟩ := by
  refine Rch.tr (zerosLq (by rfl) _ _ _) ?_
  refine Rch.tr (sL (by rfl)) ?_
  rcases h with rfl | h2
  · refine Rch.tr (disp_left _) (Rch.of_eq ?_)
    simp [app_append, app_zeros]
  · refine Rch.tr (disp_run rest 6 (by omega) h2 _) (Rch.of_eq ?_)
    rw [tail_app_ne (by simpa using h2.ne_nil), app_append]
    simp [app_zeros]

/-- `6.continue.0` on the last cell of `u` moves left to its last `1` and dispatches -/
theorem cnt0_run (u : List Bool) (hu : DOK 6 u.reverse) (R : Strm) :
    Rch dag (cfgL .cnt0 (app u.reverse blank) R) ⟨.root1, true ::: blank, app u.tail R⟩ := by
  obtain ⟨rest, h1, h2⟩ := DOK.split _ _ hu
  generalize lz u.reverse = n at h1
  have hu' : u = rest.reverse ++ true :: List.replicate n false := by
    have := congrArg List.reverse h1; simpa using this
  subst hu'
  have e : (rest.reverse ++ true :: List.replicate n false).reverse =
      List.replicate n false ++ true :: rest := by simp
  rw [e, app_append, app_zeros, app_cons]
  exact cnt0_run' n rest h2 R

/-! ## the tape right of the program counter -/

/-- the tape from cell `x`: zeros, the -1 register (`a` ones ending at cell `G`), the registers -/
def RT (G x a : Nat) (rs : List Nat) : Strm := zeros (G + 1 - a - x) (app (rcells a rs) blank)

theorem RT_succ {G x a : Nat} (rs : List Nat) (h : a + x ≤ G) :
    RT G x a rs = false ::: RT G (x + 1) a rs := by
  have : G + 1 - a - x = (G + 1 - a - (x + 1)) + 1 := by omega
  rw [RT, this]; rfl

theorem DOK_ones (k : Nat) {l : List Bool} (h : DOK 6 l) : DOK 6 (List.replicate k true ++ l) := by
  induction k with
  | zero => exact h
  | succ k ih => simp only [List.replicate_succ, List.cons_append, DOK]; exact Or.inr ih

/-- phase 1: the leaf state on the marker cell (right of the cells `u`, `u` ending with the
node's bit) marks it, extends the -1 register and dispatches -/
theorem phase1 {G : Nat} (u : List Bool) (hu : DOK 6 u.reverse) (q : St)
    (hq0 : delta dag 0 q false = some (true, Dir.R, .prep1)) (rs : List Nat)
    (hG : u.length + 3 ≤ G) :
    Rch dag ⟨q, app u.reverse blank, RT G u.length 1 rs⟩
      ⟨.root1, true ::: blank, app (u.tail ++ [true, false]) (app (rcells (G - u.length - 1) rs) blank)⟩ := by
  obtain ⟨m, hm⟩ : ∃ m, G - u.length - 3 = m := ⟨_, rfl⟩
  have e1 : RT G u.length 1 rs = false ::: false ::: zeros (m + 1) (app (rcells 1 rs) blank) := by
    have : G + 1 - 1 - u.length = m + 1 + 1 + 1 := by omega
    rw [RT, this]; rfl
  rw [e1]
  refine Rch.tr (sR hq0) ?_
  gR
  refine Rch.tr (fillR (by rfl) _ _ _) ?_
  show Rch dag ⟨.prep2, _, true ::: app (blist rs) blank⟩ _
  refine Rch.tr (stepL (δ := delta dag 0) (L := ones (m + 1) (false ::: true ::: app u.reverse blank))
    (R := true ::: app (blist rs) blank) (by rfl)) ?_
  show Rch dag (cfgL .cnt0 (true ::: ones m (false ::: true ::: app u.reverse blank)) (true ::: app (blist rs) blank)) _
  refine Rch.tr (sL (by rfl)) ?_
  have hv : DOK 6 (List.replicate m true ++ false :: true :: u.reverse) := by
    apply DOK_ones
    show DOK 5 (true :: u.reverse)
    simp only [DOK]; exact Or.inr hu
  have := disp_run (dag := dag) _ 6 (by omega) hv (true ::: true ::: app (blist rs) blank)
  rw [app_append, app_ones] at this
  refine Rch.tr this (Rch.of_eq ?_)
  have hne : u ≠ [] := by have := hu.ne_nil; simpa using this
  have e2 : G - u.length - 1 = m + 2 := by omega
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_reverse,
    List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
  rw [tail_app_ne hne, e2]
  simp [rcells, app_append, app_ones, ones_succ']

/-- `6.break.0` on a `0` right of the cells `u`: the bit becomes `1`, the -1 register is
cleaned up, and dispatch runs -/
theorem cleanup {G : Nat} (u : List Bool) (hu : DOK 6 u.reverse) (a : Nat) (ha : 1 ≤ a)
    (hx : a + u.length + 1 ≤ G + 1) (hG : u.length + 2 ≤ G) (rs : List Nat) :
    Rch dag (cfgL .brk0 (app (false :: u.reverse) blank) (RT G (u.length + 1) a rs))
      ⟨.root1, true ::: blank, app (u.tail ++ [true]) (RT G (u.length + 1) 1 rs)⟩ := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z, G + 1 - (a' + 1) - (u.length + 1) = z := ⟨_, rfl⟩
  have hk : a' + z = G - u.length - 1 := by omega
  rw [app_cons, RT, hz]
  show Rch dag ⟨.brk0, app u.reverse blank, false ::: zeros z (app (rcells (a' + 1) rs) blank)⟩ _
  gR
  refine Rch.tr (zerosRq (by rfl) z _ _) ?_
  show Rch dag ⟨.cl1, _, true ::: app (List.replicate a' true ++ blist rs) blank⟩ _
  gR
  rw [app_append, app_ones]
  refine Rch.tr (eraseR (δ := delta dag 0) (by rfl) a' _ _) ?_
  rw [app_blist_blank, zeros_cons_false, zeros_add]
  show Rch dag ⟨.cl2, false ::: zeros (a' + z) (true ::: app u.reverse blank), false ::: app (shiftIn rs) blank⟩ _
  gLc
  obtain ⟨k, hk'⟩ : ∃ k, a' + z = k + 1 := ⟨a' + z - 1, by omega⟩
  rw [hk']
  show Rch dag ⟨.b2s0, false ::: zeros k (true ::: app u.reverse blank), false ::: false ::: app (shiftIn rs) blank⟩ _
  gLc
  show Rch dag (cfgL .cnt0 (zeros (k + 1) (true ::: app u.reverse blank)) (true ::: false ::: app (shiftIn rs) blank)) _
  refine Rch.tr (cnt0_run' (k + 1) u.reverse (Or.inr hu) _) (Rch.of_eq ?_)
  have e : G + 1 - 1 - (u.length + 1) = k + 1 := by omega
  simp only [List.reverse_reverse, RT, e]
  rw [tail_app_ne (by simpa using hu.ne_nil), app_append, ← app_blist_blank]
  simp [app_zeros, rcells, app_append]


/-! ## configurations of a node and outcomes -/

/-- register values on the tape: the ten registers, then `e` registers that are zero -/
def rsOf (s : R) (e : Nat) : List Nat := s.toList ++ List.replicate e 0

/-- node `i`, reached by the path `q`, reads its bit `b` (the cells right of it are clear) -/
def atNode (G i : Nat) (q : List Bool) (b : Bool) (rs : List Nat) : Cfg St :=
  ⟨.node i, app (pc q).reverse blank, b ::: RT G ((pc q).length + 1) 1 rs⟩

/-- state `X` on the last cell of the path `q` (the bit that led into its node); the -1
register has `a` ones -/
def outc (G : Nat) (X : St) (q : List Bool) (a : Nat) (rs : List Nat) : Cfg St :=
  cfgL X (app (pc q).reverse blank) (RT G (pc q).length a rs)

theorem pc_snoc (q : List Bool) (b : Bool) : pc (q ++ [b]) = pc q ++ [b] := by simp [pc]

theorem pc_len (q : List Bool) : (pc q).length = q.length + 3 := by simp [pc]

/-- a register leaf: phase 1, the walk back, the operation `h4` (phase 2) -/
theorem leafRun {G i : Nat} {q : List Bool} {b : Bool} (hw : walkFrom dag 0 q = some i) {X X' B : St}
    (h1 : delta dag 0 (.node i) b = some (b, Dir.R, X))
    (h2 : delta dag 0 X false = some (true, Dir.R, .prep1))
    (h3 : delta dag 0 X true = some (false, Dir.R, X'))
    (hu : DOK 6 (b :: (pc q).reverse)) (hG : (pc q).length + 5 ≤ G) (rs rs' : List Nat)
    (h4 : ∀ L, Rch dag ⟨X', false ::: L, false ::: app (rcells (G - (pc q).length - 2) rs) blank⟩
            (cfgL B L (false ::: false ::: app (rcells (G - (pc q).length - 2) rs') blank))) :
    Rch dag (atNode G i q b rs) (outc G B (q ++ [b]) (G - (pc q).length - 2) rs') := by
  unfold atNode outc
  refine Rch.tr (sR h1) ?_
  have hu' : DOK 6 (pc q ++ [b]).reverse := by simpa using hu
  have := phase1 (dag := dag) (G := G) (pc q ++ [b]) hu' X h2 rs (by simp; omega)
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.length_append, List.length_singleton] at this
  refine Rch.tr this ?_
  have e1 : (pc q ++ [b]).tail ++ [true, false] = (true :: false :: q) ++ [b, true, false] := by
    simp [pc]
  rw [e1, show G - ((pc q).length + 1) - 1 = G - (pc q).length - 2 by omega, app_append]
  refine Rch.tr (root_run false q i hw _) ?_
  rw [app_cons]
  refine Rch.tr (sR h1) ?_
  rw [app_cons]
  refine Rch.tr (sR h3) ?_
  rw [app_cons]
  refine Rch.tr (h4 _) (Rch.of_eq ?_)
  have e2 : G + 1 - (G - (pc q).length - 2) - (pc q ++ [b]).length = 2 := by simp; omega
  simp only [RT, e2, pc_snoc, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, app_cons]
  rfl

theorem node_leaf {i : Nat} {c d l : Ch} (hi : dag i = some (c, d)) (b : Bool)
    (hl : (if b then d else c) = l) (X : St) (hX : l.st = some X) (hl2 : ∀ k, l ≠ .brk k) (hl3 : ∀ k, l ≠ .cnt k) :
    delta dag 0 (.node i) b = some (b, Dir.R, X) := by
  cases b <;> simp at hl <;> subst hl
  · cases c <;> simp_all [delta, carTr, Ch.st]
  · cases d <;> simp_all [delta, cdrTr, Ch.st]

/-! ## the conditions on the DAG and the paths -/

variable (dag) in
/-- What the compiled machine needs of the DAG, with certificate tables: `zr i` bounds the
trailing zeros of a program counter reaching node `i`, `dep i` the cell of its bit. -/
structure DagOK (zr dep : Nat → Nat) (G : Nat) : Prop where
  root : 1 ≤ zr 0 ∧ 3 ≤ dep 0
  car : ∀ i c d, dag i = some (c, d) →
    (∃ j, c = .node j ∧ zr i + 1 ≤ zr j ∧ zr j ≤ 6 ∧ dep i + 1 ≤ dep j) ∨
    (∃ r, (c = .inc r ∨ c = .dec r) ∧ zr i ≤ 5) ∨ c = .brk 0
  cdr : ∀ i c d, dag i = some (c, d) →
    (∃ j, d = .node j ∧ dep i + 1 ≤ dep j) ∨ (∃ r, d = .inc r ∨ d = .dec r) ∨
    d = .brk 1 ∨ d = .cnt 1 ∨ d = .cnt 2 ∨ d = .halt
  zr6 : ∀ i c d, dag i = some (c, d) → zr i ≤ 6
  depG : ∀ i c d, dag i = some (c, d) → dep i + 5 ≤ G

variable (dag) in
/-- node `i` is reached by the path `q`, and the certificates bound its program counter -/
structure Inv (zr dep : Nat → Nat) (q : List Bool) (i : Nat) : Prop where
  walk : walkFrom dag 0 q = some i
  dok : DOK 6 (pc q).reverse
  zr : lz (pc q).reverse ≤ zr i
  dep : (pc q).length ≤ dep i

theorem walkFrom_snoc : ∀ (q : List Bool) (i j k : Nat) (c d : Ch) (b : Bool),
    walkFrom dag i q = some j → dag j = some (c, d) → (if b then d else c) = .node k →
    walkFrom dag i (q ++ [b]) = some k
  | [], i, j, k, c, d, b, h1, h2, h3 => by
    have : i = j := by simpa [walkFrom] using h1
    subst this; simp [walkFrom, h2, h3]
  | b' :: q, i, j, k, c, d, b, h1, h2, h3 => by
    simp only [walkFrom, List.cons_append] at h1 ⊢
    split at h1
    · rename_i c' d' h'
      split at h1
      · rename_i m hm
        exact walkFrom_snoc q m j k c d b h1 h2 h3
      · simp at h1
    · simp at h1

theorem Inv.car {zr dep : Nat → Nat} {G : Nat} (hd : DagOK dag zr dep G) {q : List Bool} {i j : Nat}
    {d : Ch} (h : Inv dag zr dep q i) (hi : dag i = some (.node j, d)) : Inv dag zr dep (q ++ [false]) j := by
  rcases hd.car i _ _ hi with ⟨j', hj, h1, h6, h2⟩ | ⟨r, hr, _⟩ | h
  · cases hj
    refine ⟨walkFrom_snoc q 0 i j _ _ false h.walk hi rfl, ?_, ?_, ?_⟩
    · rw [pc_snoc, List.reverse_append]
      show DOK 5 (pc q).reverse
      exact DOK.of_lz _ 6 5 h.dok (by have := h.zr; omega)
    · rw [pc_snoc, List.reverse_append]; show lz (pc q).reverse + 1 ≤ zr j; have := h.zr; omega
    · rw [pc_snoc, List.length_append]; have := h.dep; simp; omega
  · rcases hr with hr | hr <;> cases hr
  · cases h

theorem Inv.cdr {zr dep : Nat → Nat} {G : Nat} (hd : DagOK dag zr dep G) {q : List Bool} {i j : Nat}
    {c : Ch} (h : Inv dag zr dep q i) (hi : dag i = some (c, .node j)) : Inv dag zr dep (q ++ [true]) j := by
  rcases hd.cdr i _ _ hi with ⟨j', hj, h2⟩ | ⟨r, hr⟩ | h | h | h | h
  · cases hj
    refine ⟨walkFrom_snoc q 0 i j _ _ true h.walk hi rfl, ?_, ?_, ?_⟩
    · rw [pc_snoc, List.reverse_append]
      show (pc q).reverse = [] ∨ DOK 6 (pc q).reverse
      exact Or.inr h.dok
    · rw [pc_snoc, List.reverse_append]; show 0 ≤ zr j; omega
    · rw [pc_snoc, List.length_append]; have := h.dep; simp; omega
  · rcases hr with hr | hr <;> cases hr
  all_goals cases h

/-! ## moving between a node and its children -/

theorem atNode_child {G i j : Nat} {q : List Bool} {b : Bool} {c d : Ch} (hi : dag i = some (c, d))
    (hb : (if b then d else c) = .node j) (hG : (pc q).length + 3 ≤ G) (rs : List Nat) :
    Rch dag (atNode G i q b rs) (atNode G j (q ++ [b]) false rs) := by
  unfold atNode
  refine Rch.tr (sR (node_step hi b hb)) (Rch.of_eq ?_)
  rw [pc_snoc, List.reverse_append, List.length_append, RT_succ rs (by omega)]
  rfl

theorem out_car_brk1 {G a : Nat} {q : List Bool} (h : a + (pc q).length ≤ G) (rs : List Nat) :
    Rch dag (outc G .brk1 (q ++ [false]) a rs) (outc G .brk0 q a rs) := by
  unfold outc
  rw [pc_snoc, List.reverse_append, List.length_append]
  refine Rch.tr (sL (by rfl)) (Rch.of_eq ?_)
  rw [RT_succ rs h]; rfl

theorem out_car_cnt1 {G : Nat} {q : List Bool} (h : 1 + (pc q).length ≤ G) (rs : List Nat) :
    Rch dag (outc G .cnt1 (q ++ [false]) 1 rs) (outc G .cnt1 q 1 rs) := by
  unfold outc
  rw [pc_snoc, List.reverse_append, List.length_append]
  refine Rch.tr (sL (by rfl)) (Rch.of_eq ?_)
  rw [RT_succ rs h]; rfl

/-- `brk0` / `brk1` -/
def brkS : Nat → St
  | 0 => .brk0
  | _ => .brk1

theorem out_cdr_brk {G a k : Nat} {q : List Bool} (hk : k ≤ 1) (h : a + (pc q).length ≤ G) (rs : List Nat) :
    Rch dag (outc G (brkS k) (q ++ [true]) a rs) (outc G (brkS k) q a rs) := by
  unfold outc
  rw [pc_snoc, List.reverse_append, List.length_append]
  have e : RT G (pc q).length a rs = false ::: RT G ((pc q).length + 1) a rs := RT_succ rs h
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · refine Rch.tr (sL (by rfl)) (Rch.of_eq ?_); rw [e]; rfl
  · refine Rch.tr (sL (by rfl)) (Rch.of_eq ?_); rw [e]; rfl

theorem out_cdr_cnt1 {G : Nat} {q : List Bool} (h : 1 + (pc q).length ≤ G) (rs : List Nat) :
    Rch dag (outc G .cnt1 (q ++ [true]) 1 rs) (cfgL .cnt0 (app (pc q).reverse blank) (RT G (pc q).length 1 rs)) := by
  unfold outc
  rw [pc_snoc, List.reverse_append, List.length_append]
  refine Rch.tr (sL (by rfl)) (Rch.of_eq ?_)
  rw [RT_succ rs h]; rfl

/-- `6.continue.0` on the last cell of a path: the node is entered again -/
theorem restart_run {zr dep : Nat → Nat} {G i : Nat} {q : List Bool} (h : Inv dag zr dep q i)
    (hG : (pc q).length + 3 ≤ G) (rs : List Nat) :
    Rch dag (cfgL .cnt0 (app (pc q).reverse blank) (RT G (pc q).length 1 rs)) (atNode G i q false rs) := by
  refine Rch.tr (cnt0_run (pc q) h.dok _) ?_
  show Rch dag ⟨.root1, true ::: blank, app (true :: false :: q) _⟩ _
  refine Rch.tr (root_run false q i h.walk _) (Rch.of_eq ?_)
  unfold atNode; rw [RT_succ rs (by omega)]

/-- a car that is done: the node's bit becomes `1` and the node is entered again -/
theorem done_run {zr dep : Nat → Nat} {G i a : Nat} {q : List Bool} (h : Inv dag zr dep q i)
    (ha : 1 ≤ a) (hx : a + (pc q).length + 1 ≤ G + 1) (hG : (pc q).length + 3 ≤ G) (rs : List Nat) :
    Rch dag (outc G .brk0 (q ++ [false]) a rs) (atNode G i q true rs) := by
  unfold outc
  rw [pc_snoc, List.reverse_append, List.length_append]
  refine Rch.tr (cleanup (pc q) h.dok a ha hx (by omega) rs) ?_
  show Rch dag ⟨.root1, true ::: blank, app ((true :: false :: q) ++ [true]) _⟩ _
  rw [app_append]
  exact root_run false q i h.walk _

/-! ## register leaves -/

theorem rsOf_split (s : R) (r : Fin 10) (e : Nat) :
    rsOf s e = s.toList.take r.val ++ s.get r :: (s.toList.drop (r.val + 1) ++ List.replicate e 0) := by
  unfold rsOf
  conv => lhs; rw [← List.take_append_drop r.val s.toList, R.get_eq s r]
  simp

theorem rsOf_inc (s : R) (r : Fin 10) (e : Nat) :
    rsOf (s.inc r) e = s.toList.take r.val ++ (s.get r + 1) :: (s.toList.drop (r.val + 1) ++ List.replicate e 0) := by
  unfold rsOf R.inc; rw [R.toList_set]; simp

theorem rsOf_dec (s : R) (r : Fin 10) (e w : Nat) (hw : s.get r = w + 1) :
    rsOf (s.dec r) (e + 1) =
      s.toList.take r.val ++ w :: ((s.toList.drop (r.val + 1) ++ List.replicate e 0) ++ [0]) := by
  have e1 : List.replicate (e + 1) (0 : Nat) = List.replicate e 0 ++ [0] := by
    simpa [List.replicate_succ] using (rep_cons e (0 : Nat) []).symm
  unfold rsOf R.dec; rw [R.toList_set, hw, e1]; simp

theorem chOf_eq (s : R) (r : Fin 10) :
    chOf r = ⟨(s.toList.take r.val).length + 2, by rw [R.length_take]; omega⟩ :=
  Fin.ext (by simp only [chOf]; rw [R.length_take])

theorem leafInc {zr dep : Nat → Nat} {G i : Nat} {q : List Bool} {b : Bool} {c d : Ch}
    (h : Inv dag zr dep q i) (hi : dag i = some (c, d)) (r : Fin 10) (hl : (if b then d else c) = .inc r)
    (hu : DOK 6 (b :: (pc q).reverse)) (hG : (pc q).length + 5 ≤ G) (s : R) (e : Nat) :
    Rch dag (atNode G i q b (rsOf s e))
      (outc G .brk0 (q ++ [b]) (G - (pc q).length - 2) (rsOf (s.inc r) e)) := by
  refine leafRun h.walk (node_leaf hi b hl (.incL r) rfl (by simp) (by simp)) rfl rfl hu hG _ _ ?_
  intro L
  rw [rsOf_split s r, rsOf_inc s r, chOf_eq s r]
  exact phase2Inc _ _ _ (by rw [R.length_take]; omega) _ (by omega) L

theorem leafDecPos {zr dep : Nat → Nat} {G i : Nat} {q : List Bool} {b : Bool} {c d : Ch}
    (h : Inv dag zr dep q i) (hi : dag i = some (c, d)) (r : Fin 10) (hl : (if b then d else c) = .dec r)
    (hu : DOK 6 (b :: (pc q).reverse)) (hG : (pc q).length + 5 ≤ G) (s : R) (hs : 0 < s.get r) (e : Nat) :
    Rch dag (atNode G i q b (rsOf s e))
      (outc G .brk0 (q ++ [b]) (G - (pc q).length - 2) (rsOf (s.dec r) (e + 1))) := by
  refine leafRun h.walk (node_leaf hi b hl (.decL r) rfl (by simp) (by simp)) rfl rfl hu hG _ _ ?_
  intro L
  obtain ⟨w, hw⟩ : ∃ w, s.get r = w + 1 := ⟨s.get r - 1, by omega⟩
  rw [rsOf_split s r, rsOf_dec s r e w hw, hw, chOf_eq s r]
  exact phase2DecPos _ _ _ (by rw [R.length_take]; omega) _ (by omega) L

theorem leafDecZero {zr dep : Nat → Nat} {G i : Nat} {q : List Bool} {b : Bool} {c d : Ch}
    (h : Inv dag zr dep q i) (hi : dag i = some (c, d)) (r : Fin 10) (hl : (if b then d else c) = .dec r)
    (hu : DOK 6 (b :: (pc q).reverse)) (hG : (pc q).length + 5 ≤ G) (s : R) (hs : s.get r = 0) (e : Nat) :
    Rch dag (atNode G i q b (rsOf s e))
      (outc G .brk1 (q ++ [b]) (G - (pc q).length - 2) (rsOf s e)) := by
  refine leafRun h.walk (node_leaf hi b hl (.decL r) rfl (by simp) (by simp)) rfl rfl hu hG _ _ ?_
  intro L
  rw [rsOf_split s r, hs, chOf_eq s r]
  exact phase2DecZero _ _ (by rw [R.length_take]; omega) _ (by omega) L

/-! ## the simulation -/

variable (dag) in
/-- what the machine does from `X` for an outcome `o` of the node of path `q`: a break or
continue ends on the last cell of the path, `halt` halts -/
def SimFrom (G : Nat) (X : Cfg St) (q : List Bool) (o : Res) (t : R) : Prop :=
  match o with
  | .brk k => k ≤ 1 ∧ ∃ a e', 1 ≤ a ∧ a + (pc q).length ≤ G + 1 ∧
      Rch dag X (outc G (brkS k) q a (rsOf t e'))
  | .cnt k => k = 1 ∧ ∃ e', Rch dag X (outc G .cnt1 q 1 (rsOf t e'))
  | .halt => ∃ L R, Rch dag X ⟨.halt, L, R⟩

theorem SimFrom.pre {G : Nat} {X Y : Cfg St} {q : List Bool} {o : Res} {t : R} (h : Rch dag X Y)
    (hs : SimFrom dag G Y q o t) : SimFrom dag G X q o t := by
  match o, hs with
  | .brk k, ⟨hk, a, e', ha, hx, hr⟩ => exact ⟨hk, a, e', ha, hx, Rch.tr h hr⟩
  | .cnt k, ⟨hk, e', hr⟩ => exact ⟨hk, e', Rch.tr h hr⟩
  | .halt, ⟨L, R, hr⟩ => exact ⟨L, R, Rch.tr h hr⟩

theorem dok_car {zr dep : Nat → Nat} {q : List Bool} {i : Nat} (h : Inv dag zr dep q i) (hz : zr i ≤ 5) :
    DOK 6 (false :: (pc q).reverse) := by
  show DOK 5 (pc q).reverse
  exact DOK.of_lz _ 6 5 h.dok (by have := h.zr; omega)

theorem dok_cdr {zr dep : Nat → Nat} {q : List Bool} {i : Nat} (h : Inv dag zr dep q i) :
    DOK 6 (true :: (pc q).reverse) := Or.inr h.dok

/-- the car is done: the machine goes on to the node's cdr -/
theorem carDone {zr dep : Nat → Nat} {G i : Nat} {q : List Bool} {c d : Ch} {s t : R}
    (hd : DagOK dag zr dep G) (hinv : Inv dag zr dep q i) (hi : dag i = some (c, d))
    (hc : Ex dag c s (.brk 0) t)
    (ihc : ∀ j q', c = .node j → Inv dag zr dep q' j → ∀ e,
      SimFrom dag G (atNode G j q' false (rsOf s e)) q' (.brk 0) t) (e : Nat) :
    ∃ e1, Rch dag (atNode G i q false (rsOf s e)) (atNode G i q true (rsOf t e1)) := by
  have hG := hd.depG i c d hi
  have hdep := hinv.dep
  rcases hd.car i c d hi with ⟨j, rfl, h1, h6, h2⟩ | ⟨r, hr, hz⟩ | rfl
  · obtain ⟨_, a, e', ha, hx, hr⟩ := ihc j (q ++ [false]) rfl (Inv.car hd hinv hi) e
    simp only [pc_snoc, List.length_append, List.length_singleton] at hx
    exact ⟨e', Rch.tr (atNode_child hi (b := false) rfl (by omega) _)
      (Rch.tr hr (done_run hinv ha (by omega) (by omega) _))⟩
  · rcases hr with rfl | rfl
    · cases hc
      exact ⟨e, Rch.tr (leafInc hinv hi r rfl (dok_car hinv hz) (by omega) s e)
        (done_run hinv (by omega) (by omega) (by omega) _)⟩
    · cases hc with
      | decp _ _ hs =>
        exact ⟨e + 1, Rch.tr (leafDecPos hinv hi r rfl (dok_car hinv hz) (by omega) s hs e)
          (done_run hinv (by omega) (by omega) (by omega) _)⟩
  · cases hc
    refine ⟨e, ?_⟩
    unfold atNode
    refine Rch.tr (stepL (δ := delta dag 0) (q' := .cnt0) (w := true) (L := app (pc q).reverse blank)
      (R := false ::: RT G ((pc q).length + 1) 1 (rsOf s e)) (by simp [delta, hi, carTr])) ?_
    show Rch dag (cfgL .cnt0 (app (pc q).reverse blank) (true ::: RT G ((pc q).length + 1) 1 (rsOf s e))) _
    refine Rch.tr (cnt0_run (pc q) hinv.dok _) ?_
    exact root_run false q i hinv.walk _

/-- the cdr ends the node -/
theorem cdrRun {zr dep : Nat → Nat} {G i : Nat} {q : List Bool} {c d : Ch} {t u : R} {o : Res}
    (hd : DagOK dag zr dep G) (hinv : Inv dag zr dep q i) (hi : dag i = some (c, d))
    (hdd : Ex dag d t o u) (ho : adj1 o ≠ .cnt 0)
    (ihd : ∀ j q', d = .node j → Inv dag zr dep q' j → ∀ e,
      SimFrom dag G (atNode G j q' false (rsOf t e)) q' o u) (e : Nat) :
    SimFrom dag G (atNode G i q true (rsOf t e)) q (adj1 o) u := by
  have hG := hd.depG i c d hi
  have hdep := hinv.dep
  rcases hd.cdr i c d hi with ⟨j, rfl, h2⟩ | ⟨r, hr⟩ | rfl | rfl | rfl | rfl
  · have := ihd j (q ++ [true]) rfl (Inv.cdr hd hinv hi) e
    refine SimFrom.pre (atNode_child hi (b := true) rfl (by omega) _) ?_
    match o, this with
    | .brk k, ⟨hk, a, e', ha, hx, hr⟩ =>
      simp only [pc_snoc, List.length_append, List.length_singleton] at hx
      exact ⟨hk, a, e', ha, by omega, Rch.tr hr (out_cdr_brk hk (by omega) _)⟩
    | .cnt k, ⟨hk, e', hr⟩ => subst hk; exact absurd rfl ho
    | .halt, hh => exact hh
  · rcases hr with rfl | rfl
    · cases hdd
      exact ⟨by omega, G - (pc q).length - 2, e, by omega, by omega,
        Rch.tr (leafInc hinv hi r rfl (dok_cdr hinv) (by omega) t e) (out_cdr_brk (k := 0) (by omega) (by omega) _)⟩
    · cases hdd with
      | decp _ _ hs =>
        exact ⟨by omega, G - (pc q).length - 2, e + 1, by omega, by omega,
          Rch.tr (leafDecPos hinv hi r rfl (dok_cdr hinv) (by omega) t hs e)
            (out_cdr_brk (k := 0) (by omega) (by omega) _)⟩
      | decz _ _ hs =>
        exact ⟨by omega, G - (pc q).length - 2, e, by omega, by omega,
          Rch.tr (leafDecZero hinv hi r rfl (dok_cdr hinv) (by omega) t hs e)
            (out_cdr_brk (k := 1) (by omega) (by omega) _)⟩
  · cases hdd
    refine ⟨by decide, 1, e, by omega, by omega, ?_⟩
    unfold atNode outc
    refine Rch.tr (stepL (δ := delta dag 0) (q' := .brk1) (w := false) (L := app (pc q).reverse blank)
      (R := true ::: RT G ((pc q).length + 1) 1 (rsOf t e)) (by simp [delta, hi, cdrTr, brkSt])) (Rch.of_eq ?_)
    rw [RT_succ _ (by omega : 1 + (pc q).length ≤ G)]; rfl
  · cases hdd; exact absurd rfl ho
  · cases hdd
    refine ⟨rfl, e, ?_⟩
    unfold atNode outc
    refine Rch.tr (stepL (δ := delta dag 0) (q' := .cnt1) (w := false) (L := app (pc q).reverse blank)
      (R := true ::: RT G ((pc q).length + 1) 1 (rsOf t e)) (by simp [delta, hi, cdrTr, cntSt])) (Rch.of_eq ?_)
    rw [RT_succ _ (by omega : 1 + (pc q).length ≤ G)]; rfl
  · cases hdd
    unfold atNode
    exact ⟨_, _, stepR (δ := delta dag 0) (q' := .halt) (w := true) (L := app (pc q).reverse blank)
      (R := true ::: RT G ((pc q).length + 1) 1 (rsOf t e)) (by simp [delta, hi, cdrTr, Ch.st])⟩

/-- the cdr restarts the node -/
theorem restartRun {zr dep : Nat → Nat} {G i : Nat} {q : List Bool} {c d : Ch} {t u : R}
    (hd : DagOK dag zr dep G) (hinv : Inv dag zr dep q i) (hi : dag i = some (c, d))
    (hdd : Ex dag d t (.cnt 1) u)
    (ihd : ∀ j q', d = .node j → Inv dag zr dep q' j → ∀ e,
      SimFrom dag G (atNode G j q' false (rsOf t e)) q' (.cnt 1) u) (e : Nat) :
    ∃ e2, Rch dag (atNode G i q true (rsOf t e)) (atNode G i q false (rsOf u e2)) := by
  have hG := hd.depG i c d hi
  have hdep := hinv.dep
  rcases hd.cdr i c d hi with ⟨j, rfl, h2⟩ | ⟨r, hr⟩ | rfl | rfl | rfl | rfl
  · obtain ⟨_, e', hr⟩ := ihd j (q ++ [true]) rfl (Inv.cdr hd hinv hi) e
    exact ⟨e', Rch.tr (atNode_child hi (b := true) rfl (by omega) _)
      (Rch.tr hr (Rch.tr (out_cdr_cnt1 (by omega) _) (restart_run hinv (by omega) _)))⟩
  · rcases hr with rfl | rfl <;> cases hdd
  · cases hdd
  · cases hdd
    refine ⟨e, ?_⟩
    show Rch dag ⟨.node i, app (pc q).reverse blank, true ::: RT G ((pc q).length + 1) 1 (rsOf t e)⟩ _
    refine Rch.tr (stepL (δ := delta dag 0) (q' := .cnt0) (w := false) (L := app (pc q).reverse blank)
      (R := true ::: RT G ((pc q).length + 1) 1 (rsOf t e)) (by simp [delta, hi, cdrTr, cntSt])) ?_
    show Rch dag (cfgL .cnt0 (app (pc q).reverse blank) (false ::: RT G ((pc q).length + 1) 1 (rsOf t e))) _
    rw [← RT_succ _ (by omega : 1 + (pc q).length ≤ G)]
    exact restart_run hinv (by omega) _
  · cases hdd
  · cases hdd

theorem sim {zr dep : Nat → Nat} {G : Nat} (hd : DagOK dag zr dep G) {c : Ch} {s : R} {o : Res} {t : R}
    (h : Ex dag c s o t) :
    ∀ i q, c = .node i → Inv dag zr dep q i → ∀ e, SimFrom dag G (atNode G i q false (rsOf s e)) q o t := by
  induction h with
  | inc => intro i q h; cases h
  | decp => intro i q h; cases h
  | decz => intro i q h; cases h
  | brk => intro i q h; cases h
  | cnt => intro i q h; cases h
  | halt => intro i q h; cases h
  | @car i c d s t o hi hc ho ho' ih =>
    intro i' q heq hinv e
    cases heq
    have hG := hd.depG i c d hi
    have hdep := hinv.dep
    rcases hd.car i c d hi with ⟨j, rfl, h1, h6, h2⟩ | ⟨r, hr, hz⟩ | rfl
    · have := ih j (q ++ [false]) rfl (Inv.car hd hinv hi) e
      refine SimFrom.pre (atNode_child hi (b := false) rfl (by omega) _) ?_
      match o, this with
      | .brk 0, _ => exact absurd rfl ho
      | .brk 1, ⟨_, a, e', ha, hx, hr⟩ =>
        simp only [pc_snoc, List.length_append, List.length_singleton] at hx
        exact ⟨by decide, a, e', ha, by omega, Rch.tr hr (out_car_brk1 (by omega) _)⟩
      | .brk (k + 2), ⟨hk, _⟩ => omega
      | .cnt k, ⟨hk, e', hr⟩ =>
        subst hk
        exact ⟨rfl, e', Rch.tr hr (out_car_cnt1 (by omega) _)⟩
      | .halt, hh => exact hh
    · rcases hr with rfl | rfl
      · cases hc; exact absurd rfl ho
      · cases hc with
        | decp => exact absurd rfl ho
        | decz _ _ hs =>
          exact ⟨by decide, G - (pc q).length - 2, e, by omega, by omega,
            Rch.tr (leafDecZero hinv hi r rfl (dok_car hinv hz) (by omega) s hs e)
              (out_car_brk1 (by omega) _)⟩
    · cases hc; exact absurd rfl ho
  | @cdr i c d s t u o hi hc hdd ho ihc ihd =>
    intro i' q heq hinv e
    cases heq
    obtain ⟨e1, h1⟩ := carDone hd hinv hi hc ihc e
    exact SimFrom.pre h1 (cdrRun hd hinv hi hdd ho ihd e1)
  | @restart i c d s t u v o hi hc hdd hn ihc ihd ihn =>
    intro i' q heq hinv e
    cases heq
    obtain ⟨e1, h1⟩ := carDone hd hinv hi hc ihc e
    obtain ⟨e2, h2⟩ := restartRun hd hinv hi hdd ihd e1
    exact SimFrom.pre (Rch.tr h1 h2) (ihn i q rfl hinv e2)

/-! ## the main loop -/

theorem inv_main {zr dep : Nat → Nat} {G : Nat} (hd : DagOK dag zr dep G) : Inv dag zr dep [] 0 :=
  ⟨rfl, by simp [pc, DOK], by simp [pc, lz]; exact hd.root.1, by simp [pc]; exact hd.root.2⟩

/-- main is done: the root bits make it start again -/
theorem main_again {G a : Nat} (ha : 1 ≤ a) (hx : a + 3 ≤ G + 1) (hG : 5 ≤ G) (rs : List Nat) :
    Rch dag (outc G .brk0 [] a rs) (atNode G 0 [] false rs) := by
  have := cleanup (dag := dag) (G := G) [true, true] (by simp [DOK]) a ha (by simpa using hx) (by simp; omega) rs
  unfold outc
  refine Rch.tr this ?_
  show Rch dag ⟨.root1, true ::: blank, true ::: true ::: RT G 3 1 rs⟩ _
  gR; gR
  unfold atNode
  exact Rch.of_eq (by rw [RT_succ rs (by simp [pc]; omega)]; rfl)

/-- one iteration of main on the tape -/
theorem main_step {zr dep : Nat → Nat} {G : Nat} (hd : DagOK dag zr dep G) (hG : 5 ≤ G) {s t : R}
    (h : Ex dag (.node 0) s (.brk 0) t) (e : Nat) :
    ∃ e', Rch dag (atNode G 0 [] false (rsOf s e)) (atNode G 0 [] false (rsOf t e')) := by
  obtain ⟨_, a, e', ha, hx, hr⟩ := sim hd h 0 [] rfl (inv_main hd) e
  exact ⟨e', Rch.tr hr (main_again ha (by simpa [pc] using hx) hG _)⟩

theorem main_halt {zr dep : Nat → Nat} {G : Nat} (hd : DagOK dag zr dep G) {s t : R}
    (h : Ex dag (.node 0) s .halt t) (e : Nat) :
    ∃ L R, Rch dag (atNode G 0 [] false (rsOf s e)) ⟨.halt, L, R⟩ :=
  sim hd h 0 [] rfl (inv_main hd) e

theorem reach1_of_ne {X Y : Cfg St} (h : Rch dag X Y) (hne : X.q ≠ Y.q) : Reach1 (delta dag 0) X Y := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; subst hn; exact absurd rfl hne
  | succ n => exact ⟨n, hn⟩

/-- one iteration of main on the tape takes at least one step -/
theorem main_step1 {zr dep : Nat → Nat} {G : Nat} (hd : DagOK dag zr dep G) (hG : 5 ≤ G) {s t : R}
    (h : Ex dag (.node 0) s (.brk 0) t) (e : Nat) :
    ∃ e', Reach1 (delta dag 0) (atNode G 0 [] false (rsOf s e)) (atNode G 0 [] false (rsOf t e')) := by
  obtain ⟨_, a, e', ha, hx, hr⟩ := sim hd h 0 [] rfl (inv_main hd) e
  exact ⟨e', Reach.trans_reach1 _ hr (reach1_of_ne (main_again ha (by simpa [pc] using hx) hG _)
    (by simp [outc, cfgL, atNode, brkS]))⟩

end

end TM.PA
