import TinyCryptids.PAK.Ops

/-!
# The program counter and the simulation of the program tree

A node `i` at depth `d` runs with its ancestors' values on cells `0 … d - 1` (`pcL`, nearest
first, then the blank before cell 0 and anything `z` left of it), its own value `v` on cell `d`,
then the gap (`G - 1 - d` ones) and the register file (`atNode`).  When it ends, its cell is
erased and the head is on its parent's cell (`endCfg`).

* `dispatch`: `scan` runs left to the blank, enters main and walks down the path (`WalkOK`).
* `nodeOK` (checked by `decide` for every node, `allOK`) lists what the simulation needs of
  each slot: the values that follow one another, the transitions the advance, the returns and
  the erase states take, and the depth of the subtree (`ht`).
* `sim`: by induction on `Run`, every outcome is reached on the tape (`Ends`).
-/

namespace TMK.PA

open TM (Dir)
open TM.PA (R)

/-! ## configurations -/

/-- the cells left of a node's cell: its ancestors' values (nearest first), the blank left of
cell 0, then `z` -/
def pcL (P : List (Nat × Nat)) (z : Strm) : Strm := lst (P.map fun p => sy p.2) (0 ∷ z)

/-- the cells right of the cell at depth `d`: the gap, the register file -/
def rgt (d : Nat) (s : R) (n : Nat) : Strm := lst (List.replicate (G - 1 - d) 1 ++ rfile s n) blank

/-- node `i` with value `v`, below the path `P` -/
def atNode (z : Strm) (P : List (Nat × Nat)) (i v : Nat) (s : R) (n : Nat) : Cfg St :=
  ⟨.node i, pcL P z, sy v ∷ rgt P.length s n⟩

/-- the head on the parent's cell (or the blank left of cell 0), `Y` from the node's cell on -/
def upCfg (q : St) (z : Strm) (P : List (Nat × Nat)) (Y : Strm) : Cfg St :=
  ⟨q, tl (pcL P z), pcL P z 0 ∷ Y⟩

/-- a node below `P` has ended: its cell erased, in state `q` -/
def endCfg (q : St) (z : Strm) (P : List (Nat × Nat)) (t : R) (n : Nat) : Cfg St :=
  upCfg q z P (1 ∷ rgt P.length t n)

theorem rgt_succ (d : Nat) (s : R) (n : Nat) (h : d + 2 ≤ G) : rgt d s n = 1 ∷ rgt (d + 1) s n := by
  unfold rgt
  rw [show G - 1 - d = (G - 1 - (d + 1)) + 1 by omega, List.replicate_succ]
  rfl

theorem stepUp {q q' : St} {z : Strm} {P : List (Nat × Nat)} {a b : Nat} {Y : Strm}
    (h : delta q a = some (b, .L, q')) : Reach delta ⟨q, pcL P z, a ∷ Y⟩ (upCfg q' z P (b ∷ Y)) :=
  stepL (δ := delta) (L := pcL P z) (R := a ∷ Y) h

/-! ## transitions -/

theorem sy_lt {v : Nat} (h : v < D) : sy v < 10 := by simp only [sy, D] at h ⊢; omega

theorem scan_tr (u : Nat) (h : u < D) : delta .scan (sy u) = some (sy u, .L, .scan) := by
  simp only [D] at h; revert u; decide

theorem adv_tr (w : Nat) (h : w < D) (hw : w ∈ advV) :
    delta .adv (sy w) = if w = T then some (1, .L, .adv) else some (sy (w + 1), .L, .scan) := by
  simp only [D] at h; revert w; decide

theorem retok_tr (w : Nat) (h1 : 1 ≤ w) (h : w ≤ T) (hw : w ∈ okV) :
    delta .retok (sy w) = if w = T then some (1, .L, .adv) else some (sy (w + 1), .L, .scan) := by
  have h' : w < 8 := by simp only [T] at h; omega
  have key : ∀ w : Nat, w < 8 → (1 ≤ w ∧ w ∈ okV) →
      delta .retok (sy w) = if w = T then some (1, .L, .adv) else some (sy (w + 1), .L, .scan) := by
    decide
  exact key w h' ⟨h1, hw⟩

theorem retfail_tr (w : Nat) (h1 : 1 ≤ w) (h : w ≤ T) (hw : w ∈ failV) :
    delta .retfail (sy w) = some (1, .L, .adv) := by
  have h' : w < 8 := by simp only [T] at h; omega
  have key : ∀ w : Nat, w < 8 → (1 ≤ w ∧ w ∈ failV) → delta .retfail (sy w) = some (1, .L, .adv) := by
    decide
  exact key w h' ⟨h1, hw⟩

theorem ebrk_tr (e w : Nat) (h : w < D) (hw : w ∈ ebV e) :
    delta (.ebrk e) (sy w) = some (1, .L, E (e - 1)) := by
  have : w + 1 < 10 := by simp only [D] at h; omega
  simp only [delta, this, if_true, sy, delta0, List.contains_iff_mem.mpr hw, if_true]

theorem ecnt_tr (e w : Nat) (h : w < D) (hw : w ∈ ecV e) :
    delta (.ecnt e) (sy w) = some (1, .L, C (e - 1)) := by
  have : w + 1 < 10 := by simp only [D] at h; omega
  simp only [delta, this, if_true, sy, delta0, List.contains_iff_mem.mpr hw, if_true]

theorem node_tr {i v j : Nat} {x : Sl} (hv : slotOf i v = some j) (hx : slot i j = some x)
    (hD : v < D) : delta (.node i) (sy v) = slotTr i j x := by
  have : v + 1 < 10 := by simp only [D] at hD; omega
  simp only [slot] at hx
  simp only [delta, this, if_true, sy, delta0, nodeTr, hv, hx]

/-! ## dispatch -/

/-- the path from main: each ancestor's value leads to the next node -/
def WalkOK : List (Nat × Nat) → Nat → Prop
  | [], i => i = 0
  | (a, u) :: P, i => u < D ∧ delta (.node a) (sy u) = some (sy u, .R, .node i) ∧ WalkOK P a

theorem scan_up (z : Strm) : ∀ (P : List (Nat × Nat)) (Y : Strm), (∀ p ∈ P, p.2 < D) →
    Reach delta (upCfg .scan z P Y) ⟨.node 0, 0 ∷ z, lst (P.reverse.map fun p => sy p.2) Y⟩ := by
  intro P
  induction P with
  | nil =>
    intro Y _
    have := stepR (δ := delta) (q := .scan) (L := z) (R := 0 ∷ Y) (w := 0) (q' := .node 0) rfl
    simpa [upCfg, pcL] using this
  | cons p P ih =>
    intro Y hP
    obtain ⟨a, u⟩ := p
    have hu : u < D := hP (a, u) (List.mem_cons_self _ _)
    have h1 : Reach delta (upCfg .scan z ((a, u) :: P) Y) (upCfg .scan z P (sy u ∷ Y)) :=
      stepUp (P := P) (scan_tr u hu)
    refine Reach.trans _ h1 ?_
    have := ih (sy u ∷ Y) (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    simpa [lst_append] using this

theorem walk (z : Strm) : ∀ (P : List (Nat × Nat)) (i : Nat), WalkOK P i → ∀ (Y : Strm),
    Reach delta ⟨.node 0, 0 ∷ z, lst (P.reverse.map fun p => sy p.2) Y⟩ ⟨.node i, pcL P z, Y⟩ := by
  intro P
  induction P with
  | nil => intro i hi Y; simp only [WalkOK] at hi; subst hi; exact Reach.refl _ _
  | cons p P ih =>
    intro i hi Y
    obtain ⟨a, u⟩ := p
    obtain ⟨_, htr, hP⟩ := hi
    have h1 := ih a hP (sy u ∷ Y)
    have h2 := stepR (δ := delta) (L := pcL P z) (R := sy u ∷ Y) htr
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, lst_append, lst_cons,
      lst_nil] at h1 ⊢
    exact Reach.trans _ h1 h2

theorem walk_lt : ∀ (P : List (Nat × Nat)) (i : Nat), WalkOK P i → ∀ p ∈ P, p.2 < D := by
  intro P
  induction P with
  | nil => intro _ _ p hp; simp at hp
  | cons q P ih =>
    intro i hi p hp
    obtain ⟨a, u⟩ := q
    obtain ⟨hu, _, hP⟩ := hi
    rcases List.mem_cons.mp hp with rfl | h
    · exact hu
    · exact ih a hP p h

theorem dispatch {z : Strm} {P : List (Nat × Nat)} {i : Nat} (hw : WalkOK P i) (Y : Strm) :
    Reach delta (upCfg .scan z P Y) ⟨.node i, pcL P z, Y⟩ :=
  Reach.trans _ (scan_up z P Y (walk_lt P i hw)) (walk z P i hw Y)

/-! ## what the simulation needs of each node -/

def nextOK (i j w : Nat) : Bool :=
  match slot i (j + 1) with
  | none => w == T
  | some _ => decide (w < T) && slotOf i (w + 1) == some (j + 1)

def slotOK (i j : Nat) : Bool :=
  match slot i j with
  | none => true
  | some (.node c) => decide (c < NN) && decide (wr i j < D) && advV.contains (wr i j) &&
      nodeTr i (sy (wr i j)) == some (sy (wr i j), .R, .node c) && decide (ht c + 1 ≤ ht i) &&
      nextOK i j (wr i j)
  | some (.inc _) => decide (1 ≤ wr i j) && decide (wr i j ≤ T) && okV.contains (wr i j) &&
      nextOK i j (wr i j)
  | some (.dec _) => decide (1 ≤ wr i j) && decide (wr i j ≤ T) && okV.contains (wr i j) &&
      failV.contains (wr i j) && nextOK i j (wr i j)
  | some (.jmp k) => slotOf i ((vals i).getD k 0) == some k && decide ((vals i).getD k 0 < D)
  | some _ => true

def nodeOK (i : Nat) : Bool :=
  (List.range (slots i).length).all (slotOK i) && slotOf i 0 == some 0 &&
    (vals i).all (· < D) && (match skp i with | some v => decide (v < D) | none => true) &&
    (vals i).length == (slots i).length && decide (1 ≤ (slots i).length) && decide (1 ≤ ht i)

set_option maxRecDepth 10000 in
theorem allOK : (List.range NN).all nodeOK = true := by decide

theorem nodeOK_of {i : Nat} (h : i < NN) : nodeOK i = true :=
  List.all_eq_true.mp allOK i (List.mem_range.mpr h)

theorem slot_lt {i j : Nat} {x : Sl} (h : slot i j = some x) : j < (slots i).length := by
  simp only [slot] at h
  exact (List.get?_eq_some_iff.mp h).1

theorem slotOK_of {i j : Nat} {x : Sl} (hi : i < NN) (h : slot i j = some x) : slotOK i j = true := by
  have hN := nodeOK_of hi
  simp only [nodeOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hN
  exact hN.1.1.1.1.1.1 j (slot_lt h)

theorem nodeOK_entry {i : Nat} (hi : i < NN) : slotOf i 0 = some 0 := by
  have hN := nodeOK_of hi
  simp only [nodeOK, Bool.and_eq_true, beq_iff_eq] at hN
  exact hN.1.1.1.1.1.2

theorem nodeOK_ht {i : Nat} (hi : i < NN) : 1 ≤ ht i := by
  have hN := nodeOK_of hi
  simp only [nodeOK, Bool.and_eq_true, decide_eq_true_eq] at hN
  exact hN.2

theorem findV_mem : ∀ (l : List Nat) (v j : Nat), findV l v = some j → v ∈ l ∧ j < l.length := by
  intro l
  induction l with
  | nil => intro v j h; simp [findV] at h
  | cons x l ih =>
    intro v j h
    simp only [findV] at h
    split at h
    · cases h; subst x; simp
    · cases hj : findV l v with
      | none => rw [hj] at h; simp at h
      | some k =>
        rw [hj] at h; simp at h
        obtain ⟨h1, h2⟩ := ih v k hj
        subst h; exact ⟨List.mem_cons_of_mem _ h1, by simp; omega⟩

theorem slotOf_spec {i v j : Nat} (hi : i < NN) (h : slotOf i v = some j) :
    v < D ∧ j < (slots i).length := by
  have hN := nodeOK_of hi
  simp only [nodeOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hN
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hv⟩, hs⟩, hl⟩, h1⟩, _⟩ := hN
  simp only [slotOf] at h
  split at h
  · rename_i k hk
    cases h
    obtain ⟨h1', h2'⟩ := findV_mem _ _ _ hk
    exact ⟨hv v h1', by omega⟩
  · split at h
    · rename_i hsk
      cases h
      rw [hsk] at hs
      simp only [decide_eq_true_eq] at hs
      exact ⟨hs, by omega⟩
    · cases h

/-- the next slot: its value follows `w`, or the node ends (`w = T`) -/
def NextP (i j w : Nat) : Prop :=
  (slot i (j + 1) = none → w = T) ∧ (∀ x, slot i (j + 1) = some x → w < T ∧ slotOf i (w + 1) = some (j + 1))

theorem nextP_of {i j w : Nat} (h : nextOK i j w = true) : NextP i j w := by
  unfold nextOK at h
  constructor
  · intro hn; rw [hn] at h; simpa using h
  · intro x hx; rw [hx] at h; simpa using h

theorem facts_node {i j c : Nat} (hi : i < NN) (hx : slot i j = some (.node c)) :
    c < NN ∧ wr i j < D ∧ wr i j ∈ advV ∧
      nodeTr i (sy (wr i j)) = some (sy (wr i j), .R, .node c) ∧ ht c + 1 ≤ ht i ∧ NextP i j (wr i j) := by
  have h := slotOK_of hi hx
  simp only [slotOK, hx, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, nextP_of h6⟩

theorem facts_inc {i j : Nat} {r : Fin 10} (hi : i < NN) (hx : slot i j = some (.inc r)) :
    1 ≤ wr i j ∧ wr i j ≤ T ∧ wr i j ∈ okV ∧ NextP i j (wr i j) := by
  have h := slotOK_of hi hx
  simp only [slotOK, hx, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, nextP_of h4⟩

theorem facts_dec {i j : Nat} {r : Fin 10} (hi : i < NN) (hx : slot i j = some (.dec r)) :
    1 ≤ wr i j ∧ wr i j ≤ T ∧ wr i j ∈ okV ∧ wr i j ∈ failV ∧ NextP i j (wr i j) := by
  have h := slotOK_of hi hx
  simp only [slotOK, hx, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, nextP_of h5⟩

theorem facts_jmp {i j k : Nat} (hi : i < NN) (hx : slot i j = some (.jmp k)) :
    slotOf i ((vals i).getD k 0) = some k ∧ (vals i).getD k 0 < D := by
  have h := slotOK_of hi hx
  simp only [slotOK, hx, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h

/-! ## the simulation -/

/-- a run that ends with outcome `o` and registers `t` reaches its end on the tape -/
def Ends (z : Strm) (P : List (Nat × Nat)) (c0 : Cfg St) : Res → R → Prop
  | .brk k, t => ∃ n', LV t n' ∧ Reach delta c0 (endCfg (E k) z P t n')
  | .cnt k, t => ∃ n', LV t n' ∧ Reach delta c0 (endCfg (C k) z P t n')
  | .halt, _ => ∃ c : Cfg St, Reach delta c0 c ∧ c.q = .halt

theorem Ends.pre {z : Strm} {P : List (Nat × Nat)} {c0 c1 : Cfg St} {o : Res} {t : R}
    (h : Reach delta c0 c1) (h' : Ends z P c1 o t) : Ends z P c0 o t := by
  cases o with
  | brk k => obtain ⟨n', hn, hr⟩ := h'; exact ⟨n', hn, Reach.trans _ h hr⟩
  | cnt k => obtain ⟨n', hn, hr⟩ := h'; exact ⟨n', hn, Reach.trans _ h hr⟩
  | halt => obtain ⟨c, hr, hq⟩ := h'; exact ⟨c, Reach.trans _ h hr, hq⟩

theorem run_none {i j : Nat} {s t : R} {o : Res} (h : Run i j s o t) (hn : slot i j = none) :
    o = .brk 0 ∧ t = s := by
  cases h <;> simp_all

theorem sim {i j : Nat} {s : R} {o : Res} {t : R} (h : Run i j s o t) :
    ∀ (z : Strm) (P : List (Nat × Nat)) (v n : Nat), i < NN → WalkOK P i → P.length + ht i ≤ G →
      slotOf i v = some j → LV s n → Ends z P (atNode z P i v s n) o t := by
  induction h with
  | @fin i j s hn =>
    intro z P v n hi _ _ hv _
    have := (slotOf_spec hi hv).2
    simp only [slot] at hn
    have := List.get?_eq_none_iff.mp hn; omega
  | @inc i j r s t o hx hrun ih =>
    intro z P v n hi hw hd hv hn
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    obtain ⟨w1, wT, wok, hnext⟩ := facts_inc hi hx
    have h1 : Reach delta (atNode z P i v s n) ⟨.cinc (mpos r + 1), sy (wr i j) ∷ pcL P z, rgt P.length s n⟩ :=
      stepR (node_tr hv hx hD)
    obtain ⟨n', hn', h2⟩ := op_inc r s n hn (sy (wr i j)) (pcL P z) (G - 1 - P.length)
    refine Ends.pre (Reach.trans _ h1 h2) ?_
    have hret := retok_tr _ w1 wT wok
    cases hs : slot i (j + 1) with
    | none =>
      have hwT := hnext.1 hs
      obtain ⟨rfl, rfl⟩ := run_none hrun hs
      rw [if_pos hwT] at hret
      exact ⟨n', hn', stepUp hret⟩
    | some x =>
      obtain ⟨hlt, hv'⟩ := hnext.2 x hs
      rw [if_neg (by omega)] at hret
      refine Ends.pre (Reach.trans _ (stepUp hret) (dispatch hw _)) ?_
      exact ih z P (wr i j + 1) n' hi hw hd hv' hn'
  | @decp i j r s t o hx hpos hrun ih =>
    intro z P v n hi hw hd hv hn
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    obtain ⟨w1, wT, wok, _, hnext⟩ := facts_dec hi hx
    have h1 : Reach delta (atNode z P i v s n) ⟨.cdec (mpos r + 1), sy (wr i j) ∷ pcL P z, rgt P.length s n⟩ :=
      stepR (node_tr hv hx hD)
    obtain ⟨n', hn', h2⟩ := (op_dec r s n hn (sy (wr i j)) (pcL P z) (G - 1 - P.length)).1 hpos
    refine Ends.pre (Reach.trans _ h1 h2) ?_
    have hret := retok_tr _ w1 wT wok
    cases hs : slot i (j + 1) with
    | none =>
      have hwT := hnext.1 hs
      obtain ⟨rfl, rfl⟩ := run_none hrun hs
      rw [if_pos hwT] at hret
      exact ⟨n', hn', stepUp hret⟩
    | some x =>
      obtain ⟨hlt, hv'⟩ := hnext.2 x hs
      rw [if_neg (by omega)] at hret
      refine Ends.pre (Reach.trans _ (stepUp hret) (dispatch hw _)) ?_
      exact ih z P (wr i j + 1) n' hi hw hd hv' hn'
  | @decz i j r s hx hz =>
    intro z P v n hi _ _ hv hn
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    obtain ⟨w1, wT, _, wf, _⟩ := facts_dec hi hx
    have h1 : Reach delta (atNode z P i v s n) ⟨.cdec (mpos r + 1), sy (wr i j) ∷ pcL P z, rgt P.length s n⟩ :=
      stepR (node_tr hv hx hD)
    obtain ⟨n', hn', h2⟩ := (op_dec r s n hn (sy (wr i j)) (pcL P z) (G - 1 - P.length)).2 hz
    exact ⟨n', hn', Reach.trans _ h1 (Reach.trans _ h2 (stepUp (retfail_tr _ w1 wT wf)))⟩
  | @child i j c s u t o hx hc hrun ihc ih =>
    intro z P v n hi hw hd hv hn
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    obtain ⟨hcN, wD, wadv, wtr, hht, hnext⟩ := facts_node hi hx
    have hc1 := nodeOK_ht hcN
    have h1 : Reach delta (atNode z P i v s n) (atNode z ((i, wr i j) :: P) c 0 s n) := by
      have e : atNode z ((i, wr i j) :: P) c 0 s n = ⟨.node c, sy (wr i j) ∷ pcL P z, rgt P.length s n⟩ := by
        simp only [atNode, pcL, List.map_cons, lst_cons, List.length_cons]
        rw [rgt_succ P.length s n (by omega)]; rfl
      rw [e]; exact stepR (node_tr hv hx hD)
    have hwc : WalkOK ((i, wr i j) :: P) c :=
      ⟨wD, by rw [← wtr]; simp only [delta, sy_lt wD, if_true]; rfl, hw⟩
    obtain ⟨n1, hn1, h2⟩ := ihc z ((i, wr i j) :: P) 0 n hcN hwc (by simp only [List.length_cons]; omega) (nodeOK_entry hcN) hn
    refine Ends.pre (Reach.trans _ h1 h2) ?_
    have e : endCfg (E 0) z ((i, wr i j) :: P) u n1 = ⟨.adv, pcL P z, sy (wr i j) ∷ rgt P.length u n1⟩ := by
      simp only [endCfg, upCfg, E, pcL, List.map_cons, lst_cons, tl_cons, cons_zero, List.length_cons]
      rw [rgt_succ P.length u n1 (by omega)]
    rw [e]
    have hadv := adv_tr _ wD wadv
    cases hs : slot i (j + 1) with
    | none =>
      have hwT := hnext.1 hs
      obtain ⟨rfl, rfl⟩ := run_none hrun hs
      rw [if_pos hwT] at hadv
      exact ⟨n1, hn1, stepUp hadv⟩
    | some x =>
      obtain ⟨hlt, hv'⟩ := hnext.2 x hs
      rw [if_neg (by omega)] at hadv
      refine Ends.pre (Reach.trans _ (stepUp hadv) (dispatch hw _)) ?_
      exact ih z P (wr i j + 1) n1 hi hw hd hv' hn1
  | @childB i j c k s u hx hc heb ihc =>
    intro z P v n hi hw hd hv hn
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    obtain ⟨hcN, wD, _, wtr, hht, _⟩ := facts_node hi hx
    have hc1 := nodeOK_ht hcN
    have h1 : Reach delta (atNode z P i v s n) (atNode z ((i, wr i j) :: P) c 0 s n) := by
      have e : atNode z ((i, wr i j) :: P) c 0 s n = ⟨.node c, sy (wr i j) ∷ pcL P z, rgt P.length s n⟩ := by
        simp only [atNode, pcL, List.map_cons, lst_cons, List.length_cons]
        rw [rgt_succ P.length s n (by omega)]; rfl
      rw [e]; exact stepR (node_tr hv hx hD)
    have hwc : WalkOK ((i, wr i j) :: P) c :=
      ⟨wD, by rw [← wtr]; simp only [delta, sy_lt wD, if_true]; rfl, hw⟩
    obtain ⟨n1, hn1, h2⟩ := ihc z ((i, wr i j) :: P) 0 n hcN hwc (by simp only [List.length_cons]; omega) (nodeOK_entry hcN) hn
    have e : endCfg (E (k + 1)) z ((i, wr i j) :: P) u n1 =
        ⟨.ebrk (k + 1), pcL P z, sy (wr i j) ∷ rgt P.length u n1⟩ := by
      simp only [endCfg, upCfg, E, pcL, List.map_cons, lst_cons, tl_cons, cons_zero, List.length_cons]
      rw [rgt_succ P.length u n1 (by omega)]
    rw [e] at h2
    have h3 := stepUp (z := z) (P := P) (Y := rgt P.length u n1) (ebrk_tr (k + 1) _ wD heb)
    exact ⟨n1, hn1, Reach.trans _ h1 (Reach.trans _ h2 h3)⟩
  | @childC i j c k s u hx hc hec ihc =>
    intro z P v n hi hw hd hv hn
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    obtain ⟨hcN, wD, _, wtr, hht, _⟩ := facts_node hi hx
    have hc1 := nodeOK_ht hcN
    have h1 : Reach delta (atNode z P i v s n) (atNode z ((i, wr i j) :: P) c 0 s n) := by
      have e : atNode z ((i, wr i j) :: P) c 0 s n = ⟨.node c, sy (wr i j) ∷ pcL P z, rgt P.length s n⟩ := by
        simp only [atNode, pcL, List.map_cons, lst_cons, List.length_cons]
        rw [rgt_succ P.length s n (by omega)]; rfl
      rw [e]; exact stepR (node_tr hv hx hD)
    have hwc : WalkOK ((i, wr i j) :: P) c :=
      ⟨wD, by rw [← wtr]; simp only [delta, sy_lt wD, if_true]; rfl, hw⟩
    obtain ⟨n1, hn1, h2⟩ := ihc z ((i, wr i j) :: P) 0 n hcN hwc (by simp only [List.length_cons]; omega) (nodeOK_entry hcN) hn
    have e : endCfg (C (k + 2)) z ((i, wr i j) :: P) u n1 =
        ⟨.ecnt (k + 2), pcL P z, sy (wr i j) ∷ rgt P.length u n1⟩ := by
      simp only [endCfg, upCfg, C, pcL, List.map_cons, lst_cons, tl_cons, cons_zero, List.length_cons]
      rw [rgt_succ P.length u n1 (by omega)]
    rw [e] at h2
    have h3 := stepUp (z := z) (P := P) (Y := rgt P.length u n1) (ecnt_tr (k + 2) _ wD hec)
    exact ⟨n1, hn1, Reach.trans _ h1 (Reach.trans _ h2 h3)⟩
  | @childR i j c s u t o hx hc hec hrun ihc ih =>
    intro z P v n hi hw hd hv hn
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    obtain ⟨hcN, wD, _, wtr, hht, _⟩ := facts_node hi hx
    have hc1 := nodeOK_ht hcN
    have h1 : Reach delta (atNode z P i v s n) (atNode z ((i, wr i j) :: P) c 0 s n) := by
      have e : atNode z ((i, wr i j) :: P) c 0 s n = ⟨.node c, sy (wr i j) ∷ pcL P z, rgt P.length s n⟩ := by
        simp only [atNode, pcL, List.map_cons, lst_cons, List.length_cons]
        rw [rgt_succ P.length s n (by omega)]; rfl
      rw [e]; exact stepR (node_tr hv hx hD)
    have hwc : WalkOK ((i, wr i j) :: P) c :=
      ⟨wD, by rw [← wtr]; simp only [delta, sy_lt wD, if_true]; rfl, hw⟩
    obtain ⟨n1, hn1, h2⟩ := ihc z ((i, wr i j) :: P) 0 n hcN hwc (by simp only [List.length_cons]; omega) (nodeOK_entry hcN) hn
    have e : endCfg (C 1) z ((i, wr i j) :: P) u n1 =
        ⟨.ecnt 1, pcL P z, sy (wr i j) ∷ rgt P.length u n1⟩ := by
      simp only [endCfg, upCfg, C, pcL, List.map_cons, lst_cons, tl_cons, cons_zero, List.length_cons]
      rw [rgt_succ P.length u n1 (by omega)]
    rw [e] at h2
    have h3 := stepUp (z := z) (P := P) (Y := rgt P.length u n1) (ecnt_tr 1 _ wD hec)
    refine Ends.pre (Reach.trans _ h1 (Reach.trans _ h2 (Reach.trans _ h3 (dispatch hw _)))) ?_
    exact ih z P 0 n1 hi hw hd (nodeOK_entry hi) hn1
  | @childH i j c s u hx hc ihc =>
    intro z P v n hi hw hd hv hn
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    obtain ⟨hcN, wD, _, wtr, hht, _⟩ := facts_node hi hx
    have hc1 := nodeOK_ht hcN
    have h1 : Reach delta (atNode z P i v s n) (atNode z ((i, wr i j) :: P) c 0 s n) := by
      have e : atNode z ((i, wr i j) :: P) c 0 s n = ⟨.node c, sy (wr i j) ∷ pcL P z, rgt P.length s n⟩ := by
        simp only [atNode, pcL, List.map_cons, lst_cons, List.length_cons]
        rw [rgt_succ P.length s n (by omega)]; rfl
      rw [e]; exact stepR (node_tr hv hx hD)
    have hwc : WalkOK ((i, wr i j) :: P) c :=
      ⟨wD, by rw [← wtr]; simp only [delta, sy_lt wD, if_true]; rfl, hw⟩
    exact Ends.pre h1 (ihc z ((i, wr i j) :: P) 0 n hcN hwc (by simp only [List.length_cons]; omega) (nodeOK_entry hcN) hn)
  | @brk i j hh s hx =>
    intro z P v n hi _ _ hv hn
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    exact ⟨n, hn, stepUp (node_tr hv hx hD)⟩
  | @cnt0 i j s t o hx hrun ih =>
    intro z P v n hi hw hd hv hn
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    have h1 := stepUp (z := z) (P := P) (Y := rgt P.length s n) (node_tr hv hx hD)
    refine Ends.pre (Reach.trans _ h1 (dispatch hw _)) ?_
    exact ih z P 0 n hi hw hd (nodeOK_entry hi) hn
  | @cnt i j hh s hx =>
    intro z P v n hi _ _ hv hn
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    exact ⟨n, hn, stepUp (node_tr hv hx hD)⟩
  | @jmp i j k s t o hx hrun ih =>
    intro z P v n hi hw hd hv hn
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    obtain ⟨hk, hkD⟩ := facts_jmp hi hx
    have h1 := stepUp (z := z) (P := P) (Y := rgt P.length s n) (node_tr hv hx hD)
    refine Ends.pre (Reach.trans _ h1 (dispatch hw _)) ?_
    exact ih z P _ n hi hw hd hk hn
  | @done i j s hx =>
    intro z P v n hi _ _ hv hn
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    exact ⟨n, hn, stepUp (node_tr hv hx hD)⟩
  | @halt i j s hx =>
    intro z P v n hi _ _ hv _
    obtain ⟨hD, _⟩ := slotOf_spec hi hv
    exact ⟨_, stepR (node_tr hv hx hD), rfl⟩

end TMK.PA
