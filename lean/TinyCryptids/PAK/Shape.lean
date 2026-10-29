import TinyCryptids.PAK.Sem

/-!
# Running a node's slots on registers

`runS l s` runs a list of slots on registers `s`: operations (`op`), children with a known
denotation (`ch c g`: outcome and registers, `Den`), and a tail run proven separately
(`tail F`).  It ends with an outcome (`exit`) or at a jump back to a slot of the same node
(`back k`: a `jmp k`, a `cnt 0`, or a child's `cnt 1`).  `runS_sound`: when the list is the
node's slots from `j` (`SMatch`), the node does that (`RunOut`).

* `outcomes`: a node's run ends only with the break and continue levels of `brkLv`, `cntLv`;
  with `ctlOK` (checked for every node by `decide`) this gives the erase states' premises.
* `straight_sound`: a node without jumps back runs as `den`.
* `loop_sound`: a loop with a measure; `while_sound`: `decnz r`, a body that keeps `r`, back;
  `zero_sound`, `xfer_sound`, `xfer2_sound`: zeroing and moving loops in closed form.
-/

namespace TMK.PA

open TM.PA (R loopN)

/-! ## static facts: the outcomes of a node -/

def ctlOK (i : Nat) : Bool :=
  (List.range (slots i).length).all fun j =>
    match slot i j with
    | some (.node c) => decide (c < NN) &&
        (brkLv c).all (fun k => (ebV k).contains (wr i j) && (k < 2 || (brkLv i).contains (k - 1))) &&
        (cntLv c).all (fun k => (ecV k).contains (wr i j) && (k < 2 || (cntLv i).contains (k - 1)))
    | some (.brk h) => h == 0 || (brkLv i).contains h
    | some (.cnt (h + 1)) => (cntLv i).contains (h + 1)
    | _ => true

set_option maxRecDepth 10000 in
theorem allCtl : (List.range NN).all ctlOK = true := by decide

theorem slot_lt' {i j : Nat} {x : Sl} (h : slot i j = some x) : j < (slots i).length := by
  simp only [slot] at h
  exact (List.get?_eq_some_iff.mp h).1

def ctlSlot (i j : Nat) : Bool :=
  match slot i j with
  | some (.node c) => decide (c < NN) &&
      (brkLv c).all (fun k => (ebV k).contains (wr i j) && (k < 2 || (brkLv i).contains (k - 1))) &&
      (cntLv c).all (fun k => (ecV k).contains (wr i j) && (k < 2 || (cntLv i).contains (k - 1)))
  | some (.brk h) => h == 0 || (brkLv i).contains h
  | some (.cnt (h + 1)) => (cntLv i).contains (h + 1)
  | _ => true

theorem ctlOK_eq (i : Nat) : ctlOK i = (List.range (slots i).length).all (ctlSlot i) := rfl

theorem ctl_slot {i j : Nat} {x : Sl} (hi : i < NN) (h : slot i j = some x) : ctlSlot i j = true := by
  have hc := List.all_eq_true.mp allCtl i (List.mem_range.mpr hi)
  rw [ctlOK_eq] at hc
  exact List.all_eq_true.mp hc j (List.mem_range.mpr (slot_lt' h))

theorem ctl_node {i j c : Nat} (hi : i < NN) (h : slot i j = some (.node c)) :
    c < NN ∧ (∀ k ∈ brkLv c, wr i j ∈ ebV k ∧ (2 ≤ k → k - 1 ∈ brkLv i)) ∧
      (∀ k ∈ cntLv c, wr i j ∈ ecV k ∧ (2 ≤ k → k - 1 ∈ cntLv i)) := by
  have := ctl_slot hi h
  simp only [ctlSlot, h, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    List.contains_iff_mem] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  refine ⟨h1, fun k hk => ⟨(h2 k hk).1, fun h2k => ?_⟩, fun k hk => ⟨(h3 k hk).1, fun h2k => ?_⟩⟩
  · rcases (h2 k hk).2 with h | h
    · omega
    · exact h
  · rcases (h3 k hk).2 with h | h
    · omega
    · exact h

theorem ctl_brk {i j h : Nat} (hi : i < NN) (hx : slot i j = some (.brk h)) : h = 0 ∨ h ∈ brkLv i := by
  have := ctl_slot hi hx
  simp only [ctlSlot, hx, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at this
  exact this

theorem ctl_cnt {i j h : Nat} (hi : i < NN) (hx : slot i j = some (.cnt (h + 1))) : h + 1 ∈ cntLv i := by
  have := ctl_slot hi hx
  simp only [ctlSlot, hx, List.contains_iff_mem] at this
  exact this

theorem brk0_ne (k : Nat) : Res.brk 0 ≠ Res.brk (k + 1) := by intro h; cases h

/-- the outcomes of a run: break and continue levels from the tables, never `cnt 0` -/
theorem outcomes {i j : Nat} {s t : R} {o : Res} (h : Run i j s o t) : i < NN →
    (∀ k, o = .brk (k + 1) → k + 1 ∈ brkLv i) ∧ (∀ k, o = .cnt k → k ∈ cntLv i ∧ 0 < k) := by
  induction h with
  | fin => intro _; exact ⟨fun k h => absurd h (brk0_ne k), fun _ h => Res.noConfusion h⟩
  | inc _ _ ih => exact ih
  | decp _ _ _ ih => exact ih
  | decz => intro _; exact ⟨fun k h => absurd h (brk0_ne k), fun _ h => Res.noConfusion h⟩
  | child _ _ _ _ ih => exact ih
  | @childB i j c k s u hx hc _ ihc =>
    intro hi
    obtain ⟨hcN, hb, _⟩ := ctl_node hi hx
    have hk := (ihc hcN).1 k rfl
    refine ⟨fun k' hk' => ?_, fun _ h => Res.noConfusion h⟩
    cases hk'
    exact (hb (k' + 1 + 1) hk).2 (by omega)
  | @childC i j c k s u hx hc _ ihc =>
    intro hi
    obtain ⟨hcN, _, hcn⟩ := ctl_node hi hx
    have hk := ((ihc hcN).2 (k + 2) rfl).1
    refine ⟨fun _ h => Res.noConfusion h, fun k' hk' => ?_⟩
    cases hk'
    exact ⟨(hcn (k + 2) hk).2 (by omega), by omega⟩
  | childR _ _ _ _ _ ih => exact ih
  | childH => intro _; exact ⟨fun _ h => Res.noConfusion h, fun _ h => Res.noConfusion h⟩
  | @brk i j h s hx =>
    intro hi
    have := ctl_brk hi hx
    refine ⟨fun k hk => ?_, fun _ h => Res.noConfusion h⟩
    cases hk
    rcases this with h | h
    · omega
    · exact h
  | cnt0 _ _ ih => exact ih
  | @cnt i j h s hx =>
    intro hi
    have := ctl_cnt hi hx
    exact ⟨fun _ h => Res.noConfusion h, fun k hk => by cases hk; exact ⟨this, by omega⟩⟩
  | jmp _ _ ih => exact ih
  | done => intro _; exact ⟨fun k h => absurd h (brk0_ne k), fun _ h => Res.noConfusion h⟩
  | halt => intro _; exact ⟨fun _ h => Res.noConfusion h, fun _ h => Res.noConfusion h⟩

/-! ## running slots -/

/-- how a run of slots ends: with an outcome, or back at slot `k` of the same node -/
inductive Out
  | exit (o : Res)
  | back (k : Nat)

/-- the denotation of a node: its outcome and registers -/
abbrev Den := R → Res × R

/-- a slot with what is known of it -/
inductive SS
  | op (x : Sl)
  | ch (c : Nat) (g : Den)
  | tail (F : Den)

/-- a child that does not finish normally -/
def chOut : Res → R → Out × R
  | .brk 0, u => (.exit (.brk 0), u)
  | .brk (k + 1), u => (.exit (.brk k), u)
  | .cnt 0, u => (.exit (.cnt 0), u)
  | .cnt 1, u => (.back 0, u)
  | .cnt (k + 2), u => (.exit (.cnt (k + 1)), u)
  | .halt, u => (.exit .halt, u)

def runS : List SS → R → Out × R
  | [], s => (.exit (.brk 0), s)
  | .op (.inc r) :: l, s => runS l (s.inc r)
  | .op (.dec r) :: l, s => if s.get r = 0 then (.exit (.brk 0), s) else runS l (s.dec r)
  | .op (.node _) :: _, s => (.exit (.brk 0), s)
  | .op (.brk h) :: _, s => (.exit (.brk h), s)
  | .op (.cnt 0) :: _, s => (.back 0, s)
  | .op (.cnt (h + 1)) :: _, s => (.exit (.cnt (h + 1)), s)
  | .op (.jmp k) :: _, s => (.back k, s)
  | .op .done :: _, s => (.exit (.brk 0), s)
  | .op .halt :: _, s => (.exit .halt, s)
  | .ch _ g :: l, s => if (g s).1 = .brk 0 then runS l (g s).2 else chOut (g s).1 (g s).2
  | .tail F :: _, s => (.exit (F s).1, (F s).2)

/-- the outcome and registers of a run of slots without jumps back -/
def den (l : List SS) (s : R) : Res × R :=
  match runS l s with
  | (.exit o, t) => (o, t)
  | (.back _, t) => (.brk 0, t)

def Sl.isNode : Sl → Bool
  | .node _ => true
  | _ => false

/-- `l` is node `i`'s slots from `j` on -/
def SMatch (i : Nat) : Nat → List SS → Prop
  | j, [] => slot i j = none
  | j, .op x :: l => slot i j = some x ∧ x.isNode = false ∧ SMatch i (j + 1) l
  | j, .ch c g :: l => slot i j = some (.node c) ∧ (∀ s, Ex c s (g s).1 (g s).2) ∧ SMatch i (j + 1) l
  | j, .tail F :: _ => ∀ s, Run i j s (F s).1 (F s).2

/-- what a run of slots from `j` gives: the node's run, or its run from slot `k` -/
def RunOut (i j : Nat) (s : R) : Out × R → Prop
  | (.exit o, t) => Run i j s o t
  | (.back k, t) => ∀ o u, Run i k t o u → Run i j s o u

theorem runS_sound {i : Nat} (hi : i < NN) :
    ∀ (l : List SS) (j : Nat), SMatch i j l → ∀ s, RunOut i j s (runS l s) := by
  intro l
  induction l with
  | nil => intro j hm s; exact Run.fin hm
  | cons x l ih =>
    intro j hm s
    cases x with
    | op x =>
      obtain ⟨hx, hn, hm'⟩ := hm
      have ih' := ih (j + 1) hm'
      cases x with
      | inc r =>
        show RunOut i j s (runS l (s.inc r))
        have := ih' (s.inc r)
        revert this
        cases runS l (s.inc r) with
        | mk out t =>
          cases out with
          | exit o => exact fun h => Run.inc hx h
          | back k => exact fun h o u hr => Run.inc hx (h o u hr)
      | dec r =>
        show RunOut i j s (if s.get r = 0 then (.exit (.brk 0), s) else runS l (s.dec r))
        by_cases h0 : s.get r = 0
        · rw [if_pos h0]; exact Run.decz hx h0
        · rw [if_neg h0]
          have := ih' (s.dec r)
          revert this
          cases runS l (s.dec r) with
          | mk out t =>
            cases out with
            | exit o => exact fun h => Run.decp hx (by omega) h
            | back k => exact fun h o u hr => Run.decp hx (by omega) (h o u hr)
      | node c => simp [Sl.isNode] at hn
      | brk h => exact Run.brk hx
      | cnt h =>
        cases h with
        | zero => exact fun o u hr => Run.cnt0 hx hr
        | succ h => exact Run.cnt hx
      | jmp k => exact fun o u hr => Run.jmp hx hr
      | done => exact Run.done hx
      | halt => exact Run.halt hx
    | ch c g =>
      obtain ⟨hx, hg, hm'⟩ := hm
      obtain ⟨hcN, hb, hcn⟩ := ctl_node hi hx
      have hgs := hg s
      have houts := outcomes hgs hcN
      show RunOut i j s (if (g s).1 = .brk 0 then runS l (g s).2 else chOut (g s).1 (g s).2)
      by_cases h0 : (g s).1 = .brk 0
      · rw [if_pos h0]
        rw [h0] at hgs
        have := ih (j + 1) hm' (g s).2
        revert this
        cases runS l (g s).2 with
        | mk out t =>
          cases out with
          | exit o => exact fun h => Run.child hx hgs h
          | back k => exact fun h o u hr => Run.child hx hgs (h o u hr)
      · rw [if_neg h0]
        revert hgs houts h0
        cases (g s).1 with
        | brk k =>
          intro hgs houts h0
          cases k with
          | zero => exact absurd rfl h0
          | succ k =>
            have hk := houts.1 k rfl
            exact Run.childB hx hgs (hb (k + 1) hk).1
        | cnt k =>
          intro hgs houts h0
          have hk := houts.2 k rfl
          cases k with
          | zero => omega
          | succ k =>
            cases k with
            | zero => exact fun o u hr => Run.childR hx hgs (hcn 1 hk.1).1 hr
            | succ k => exact Run.childC hx hgs (hcn (k + 2) hk.1).1
        | halt => intro hgs _ _; exact Run.childH hx hgs
    | tail F => exact hm s

/-- no jump back: no `cnt 0`, no `jmp`, no child that can continue its parent (`cnt 1`) -/
def noBack : List SS → Bool
  | [] => true
  | .op (.cnt 0) :: _ => false
  | .op (.jmp _) :: _ => false
  | .op _ :: l => noBack l
  | .ch c _ :: l => !(cntLv c).contains 1 && noBack l
  | .tail _ :: _ => true

theorem noBack_sound {i : Nat} (hi : i < NN) : ∀ (l : List SS) (j : Nat), SMatch i j l → noBack l = true →
    ∀ s, ∃ o t, runS l s = (.exit o, t) := by
  intro l
  induction l with
  | nil => intro _ _ _ s; exact ⟨_, _, rfl⟩
  | cons x l ih =>
    intro j hm hn s
    cases x with
    | op x =>
      obtain ⟨_, _, hm'⟩ := hm
      cases x with
      | inc r => exact ih (j + 1) hm' hn (s.inc r)
      | dec r =>
        show ∃ o t, (if s.get r = 0 then (.exit (.brk 0), s) else runS l (s.dec r)) = (.exit o, t)
        split
        · exact ⟨_, _, rfl⟩
        · exact ih (j + 1) hm' hn (s.dec r)
      | node c => exact ⟨_, _, rfl⟩
      | brk h => exact ⟨_, _, rfl⟩
      | cnt h => cases h with
        | zero => simp [noBack] at hn
        | succ h => exact ⟨_, _, rfl⟩
      | jmp k => simp [noBack] at hn
      | done => exact ⟨_, _, rfl⟩
      | halt => exact ⟨_, _, rfl⟩
    | ch c g =>
      obtain ⟨hx, hg, hm'⟩ := hm
      simp only [noBack, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hn
      have hcN := (ctl_node hi hx).1
      have houts := outcomes (hg s) hcN
      show ∃ o t, (if (g s).1 = .brk 0 then runS l (g s).2 else chOut (g s).1 (g s).2) = (.exit o, t)
      split
      · exact ih (j + 1) hm' hn.2 (g s).2
      · revert houts
        cases (g s).1 with
        | brk k => intro _; cases k <;> exact ⟨_, _, rfl⟩
        | cnt k =>
          intro houts
          rcases k with _ | _ | k
          · exact absurd (houts.2 0 rfl).2 (by omega)
          · exact absurd (houts.2 1 rfl).1 (by simpa using hn.1)
          · exact ⟨_, _, rfl⟩
        | halt => intro _; exact ⟨_, _, rfl⟩
    | tail F => exact ⟨_, _, rfl⟩

/-- a node whose run never jumps back -/
theorem straight_sound {i : Nat} (hi : i < NN) {l : List SS} (hm : SMatch i 0 l) (hn : noBack l = true) :
    ∀ s, Ex i s (den l s).1 (den l s).2 := by
  intro s
  have h := runS_sound hi l 0 hm s
  obtain ⟨o, t, he⟩ := noBack_sound hi l 0 hm hn s
  rw [he] at h
  simp only [den, he]
  exact h

/-! ## loops -/

theorem loop_sound {i k : Nat} (hi : i < NN) {l : List SS} (hm : SMatch i k l) (O : R → Res) (F : R → R)
    (μ : R → Nat) (P : R → Prop)
    (hstep : ∀ s, P s → runS l s = (.exit (O s), F s) ∨
      ∃ t, runS l s = (.back k, t) ∧ P t ∧ μ t < μ s ∧ O t = O s ∧ F t = F s) :
    ∀ s, P s → Run i k s (O s) (F s) := by
  intro s hs
  generalize hn : μ s = n
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
    have h := runS_sound hi l k hm s
    rcases hstep s hs with he | ⟨t, he, hP, hμ, hO, hF⟩
    · rw [he] at h; exact h
    · rw [he] at h
      have := ih (μ t) (by omega) t hP rfl
      rw [hO, hF] at this
      exact h _ _ this

theorem runS_dec (r : Fin 10) (l : List SS) (s : R) :
    runS (.op (.dec r) :: l) s = if s.get r = 0 then (.exit (.brk 0), s) else runS l (s.dec r) := rfl

/-- `decnz r`, a body that finishes and keeps `r`, then back to the `decnz` -/
theorem while_sound {i k : Nat} (hi : i < NN) {r : Fin 10} {body : List SS} {b : Sl}
    (hm : SMatch i k (.op (.dec r) :: (body ++ [.op b]))) (hb : ∀ s, runS [.op b] s = (.back k, s))
    (g : R → R) (hbody : ∀ s, ∀ tl, runS (body ++ tl) s = runS tl (g s)) (hkeep : ∀ s, (g s).get r = s.get r) :
    ∀ s, Run i k s (.brk 0) (loopN r g (s.get r) s) := by
  intro s
  have := loop_sound hi hm (fun _ => .brk 0) (fun s => loopN r g (s.get r) s) (fun s => s.get r) (fun _ => True)
    (fun s _ => by
      by_cases h0 : s.get r = 0
      · left
        rw [runS_dec, if_pos h0]
        show (Out.exit (Res.brk 0), s) = (Out.exit (Res.brk 0), loopN r g (s.get r) s)
        rw [h0]; rfl
      · right
        refine ⟨g (s.dec r), ?_, trivial, ?_, rfl, ?_⟩
        · rw [runS_dec, if_neg h0, hbody, hb]
        · show (g (s.dec r)).get r < s.get r
          rw [hkeep]; simp [TM.PA.R.dec, TM.PA.R.get_set]; omega
        · obtain ⟨n, hn⟩ : ∃ n, s.get r = n + 1 := ⟨s.get r - 1, by omega⟩
          show loopN r g ((g (s.dec r)).get r) (g (s.dec r)) = loopN r g (s.get r) s
          rw [hn, loopN, hkeep]
          simp [TM.PA.R.dec, TM.PA.R.get_set, hn]) s trivial
  exact this

theorem runS_inc (r : Fin 10) (s : R) (tl : List SS) : runS ([.op (.inc r)] ++ tl) s = runS tl (s.inc r) := rfl

theorem zero_sound {i k : Nat} (hi : i < NN) {r : Fin 10} {b : Sl}
    (hm : SMatch i k [.op (.dec r), .op b]) (hb : ∀ s, runS [.op b] s = (.back k, s)) :
    ∀ s, Run i k s (.brk 0) (s.set r 0) := by
  intro s
  have := while_sound hi (body := []) hm hb id (fun _ _ => rfl) (fun _ => rfl) s
  suffices e : ∀ n s, n = s.get r → loopN r id n s = s.set r 0 by rw [← e _ s rfl]; exact this
  intro n
  induction n with
  | zero => intro s h; simp [loopN, TM.PA.R.set_eq_of_get h.symm]
  | succ n ih =>
    intro s h
    rw [loopN, ih _ (by simp [TM.PA.R.dec, TM.PA.R.get_set]; omega)]
    simp [TM.PA.R.dec, TM.PA.R.set_set]

theorem xfer_sound {i k : Nat} (hi : i < NN) {r x : Fin 10} (hrx : r ≠ x) {b : Sl}
    (hm : SMatch i k [.op (.dec r), .op (.inc x), .op b]) (hb : ∀ s, runS [.op b] s = (.back k, s)) :
    ∀ s, Run i k s (.brk 0) ((s.set r 0).set x (s.get x + s.get r)) := by
  intro s
  have := while_sound hi (body := [.op (.inc x)]) hm hb (fun s => s.inc x) (fun _ _ => rfl)
    (fun s => by simp [TM.PA.R.inc, TM.PA.R.get_set_ne _ (Ne.symm hrx)]) s
  rw [TM.PA.loopN_inc r x hrx _ s (Nat.le_refl _), Nat.sub_self] at this
  exact this

theorem xfer2_sound {i k c : Nat} (hi : i < NN) {r x y : Fin 10} (h1 : r ≠ x) (h2 : r ≠ y) (h3 : x ≠ y)
    {g : Den} (hg : ∀ s, g s = (.brk 0, (s.inc x).inc y)) {b : Sl}
    (hm : SMatch i k [.op (.dec r), .ch c g, .op b]) (hb : ∀ s, runS [.op b] s = (.back k, s)) :
    ∀ s, Run i k s (.brk 0) (((s.set r 0).set x (s.get x + s.get r)).set y (s.get y + s.get r)) := by
  intro s
  have := while_sound hi (body := [.ch c g]) hm hb (fun s => (s.inc x).inc y)
    (fun s tl => by simp [runS, hg])
    (fun s => by simp [TM.PA.R.inc, TM.PA.R.get_set_ne _ (Ne.symm h1), TM.PA.R.get_set_ne _ (Ne.symm h2)]) s
  rw [TM.PA.loopN_inc2 r x y h1 h2 h3 _ s (Nat.le_refl _), Nat.sub_self] at this
  exact this

end TMK.PA
