import TinyCryptids.Beal.Pow
namespace TM.Beal
open St

/-! Pushing R, the next base, and the compare (as in `TinyCryptids/Fermat/`). -/

/-- `t1`/`t3` scanning a block list to its end, then writing the new R block's
first cell (state `p1` afterwards). -/
theorem tscan {W : List Bool} (hW : Blk W) : ∀ L : Strm,
    Rch ⟨t1, L, app W blank⟩ ⟨p1, true ::: false ::: false ::: app W.reverse L, blank⟩ ∧
    Rch ⟨t3, L, app W blank⟩ ⟨p1, true ::: false ::: false ::: app W.reverse L, blank⟩ := by
  induction hW with
  | one n =>
    intro L
    have key : Rch ⟨t1, true ::: L, app (List.replicate n true) blank⟩
        ⟨p1, true ::: false ::: false ::: app (List.replicate (n+1) true).reverse L, blank⟩ := by
      rw [app_replicate]; sRn n
      refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR
      simp [List.reverse_replicate, app_replicate, ones_succ']; fin
    exact ⟨Rch.tr (sR rfl) key, Rch.tr (sR rfl) key⟩
  | @cons n l hl ih =>
    intro L
    have key : Rch ⟨t1, true ::: L, app (List.replicate n true ++ false :: false :: l) blank⟩
        ⟨p1, true ::: false ::: false :::
          app (List.replicate (n+1) true ++ false :: false :: l).reverse L, blank⟩ := by
      rw [app_append, app_replicate]; sRn n; gR; gR
      refine Rch.tr (ih _).2 ?_
      simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, ones_succ']; fin
    exact ⟨Rch.tr (sR rfl) key, Rch.tr (sR rfl) key⟩

/-- after `tscan`: write the new R block `1 0 1` and walk left to its cell 0 -/
theorem push3 (L : Strm) :
    Rch ⟨p1, L, blank⟩ (cfgL NB1 L (false ::: true ::: blank)) := by
  refine blankR ?_; gR; refine blankR ?_; gL; gL; fin

/-- zig-zag: A (α cells), a gap of `g + r` blanks with the head on the
`g`-th from the left... precisely: head on the first of `zeros g` (read leftwards),
`r` blanks to the right, then Z (ζ cells). Left of A: `00 M Lt`. -/
def zz (g r α ζ : Nat) (Lt : Strm) : Cfg St :=
  cfgL zH1 (zeros g (ones α (F ::: F ::: true ::: Lt))) (zeros r (ones ζ blank))

theorem zz_step (g r a z : Nat) (Lt : Strm) :
    Rch (zz g r (a+2) (z+2) Lt) (zz (g + r + 1) 1 (a+1) (z+1) Lt) := by
  unfold zz
  zLn g; gL; gR; gR; zRn g; zRn r; gR; gL; gL
  rw [zeros_add, ← zeros_succ', show r + g + 1 = g + r + 1 by omega]; fin

theorem halt_cfg (L R : Strm) : Halts delta (⟨halt, L, R⟩ : Cfg St) := halt_none rfl

theorem halt_of_rch {c : Cfg St} {L R : Strm} (h : Rch c ⟨halt, L, R⟩) : Halts delta c :=
  Reach.halts delta h (halt_cfg L R)

/-- reaches the explicit halting state -/
def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; halt_of_rch h

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem zz_halt (g r : Nat) (Lt : Strm) : HaltAt (zz g r 1 1 Lt) := by
  unfold zz
  apply Exists.intro; apply Exists.intro
  zLn g; gL; gR; gR; zRn g; zRn r; gR
  refine blankR ?_; gR; fin

/-- the common clearing point: head on M in state `cr3`, all blank to the right -/
def crC (Lt : Strm) : Cfg St := cfgL cr3 (true ::: Lt) blank

theorem zz_clearA (g r z : Nat) (Lt : Strm) : Rch (zz g r 1 (z+2) Lt) (crC Lt) := by
  unfold zz crC
  zLn g; gL; gR; gR; zRn g; zRn r; gR; gR; eRn z
  refine blankR ?_; gL
  zLn z; gL; gL; zLn r; zLn g; gL; gL; gL
  simp only [zeros_cons_false, zeros_blank, cons_blank]; fin

theorem zz_clearZ (g r a : Nat) (Lt : Strm) : Rch (zz g r (a+2) 1 Lt) (crC Lt) := by
  unfold zz crC
  zLn g; gL; gR; gR; zRn g; zRn r; gR
  refine blankR ?_; gL; gL
  zLn r; zLn g; gL; gL
  eLn a; gL; gL
  simp only [zeros_cons_false, zeros_blank, cons_blank]; fin

theorem zz_result (Lt : Strm) : ∀ α ζ g r, 1 ≤ α → 1 ≤ ζ →
    (α = ζ → HaltAt (zz g r α ζ Lt)) ∧ (α ≠ ζ → Rch (zz g r α ζ Lt) (crC Lt)) := by
  intro α
  induction α with
  | zero => intro _ _ _ _ h; omega
  | succ a ih =>
    intro ζ g r _ hz
    obtain ⟨z, rfl⟩ : ∃ z, ζ = z + 1 := ⟨ζ - 1, by omega⟩
    cases a with
    | zero =>
      cases z with
      | zero => exact ⟨fun _ => zz_halt g r Lt, fun h => absurd rfl h⟩
      | succ z => exact ⟨fun h => by omega, fun _ => zz_clearA g r z Lt⟩
    | succ a =>
      cases z with
      | zero => exact ⟨fun h => by omega, fun _ => zz_clearZ g r a Lt⟩
      | succ z =>
        have := ih (z+1) (g + r + 1) 1 (by omega) (by omega)
        exact ⟨fun h => HaltAt.back (zz_step g r a z Lt) (this.1 (by omega)),
               fun h => Rch.tr (zz_step g r a z Lt) (this.2 (by omega))⟩


theorem PMQ : ParserR delta MQ1 MQ2 := ⟨rfl, rfl, rfl⟩

/-- move the base cursor to the next block, add R into A, push a new R and find the base
cursor: the next pair starts. Its exponent block is the old next one (`n + 2` cells), the
blocks in between are the old one next to the base (`m` cells) and the old base block. -/
theorem next_base {Y : List Bool} (hY : Blk Y) (n m E β β' α r : Nat) (Lx : Strm)
    (hm : 2 ≤ m) (hb' : 1 ≤ β') (ha : 1 ≤ α) (hr : 1 ≤ r) :
    Rch (nbC n m E β (rep (β' + 3) ++ F :: F :: (Y ++ F :: F :: rep α)) r Lx)
      (bAtC (true ::: leftOf (m - 2) (β + 3) (n + 1) 1 (F ::: F ::: ones (E + 1) Lx)) β' 1
        (Y ++ F :: F :: rep (α + r)) 1 0) := by
  obtain ⟨b, rfl⟩ : ∃ b, β' = b + 1 := ⟨β' - 1, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, α = a + 1 := ⟨α - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  unfold nbC
  gR; sRn β
  unfold rgt
  simp only [sep, app_append, app_cons, app_replicate]
  gR; gR; gR; gR; gR
  have hw : Clean (rep (b + 1) ++ F :: F :: (Y ++ F :: F :: (rep (a + 1) ++ [F, F, true]))) :=
    Clean.rep_append _ (hY.clean_sep_append (Clean.sep (Clean.rep_append a (Clean.sep Clean.nil))))
  have e1 : ones (b + 1) (F ::: F ::: app Y (F ::: F ::: ones (a + 1)
      (false ::: false ::: true ::: false ::: ones (s + 1) (false ::: false ::: ones 0 blank)))) =
      app (rep (b + 1) ++ F :: F :: (Y ++ F :: F :: (rep (a + 1) ++ [F, F, true])))
        (false ::: true ::: ones s blank) := by
    simp [app_append, app_replicate, ones_succ, cons_blank]
  rw [e1]
  refine Rch.tr (PMQ.find hw _ _) ?_
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.reverse_replicate, List.cons_append, List.singleton_append, List.append_assoc,
    app_append, app_cons, app_nil, app_replicate]
  gL; gL; gL; gL; gR
  gR; gR; gR; sRn (s + 1)
  rw [show ∀ Z : Strm, true ::: true ::: true ::: true ::: tl (F ::: ones (a + 1) Z) = ones (a + 5) Z
    from fun Z => rfl, ones_add, show s + 1 + (a + 5) = (a + s + 2) + 4 by omega]
  first | gL | (refine blankR ?_; gL)
  gL; gL; gL; gL
  simp only [cons_blank]
  refine Rch.tr (tscan (Blk.one 0) _).1 ?_
  refine Rch.tr (push3 _) ?_
  have hw2 : Clean (true :: F :: F :: (rep (a + s + 2) ++ F :: F :: (Y.reverse ++ F :: F :: rep (b + 1)))) :=
    Clean.one (Clean.sep (Clean.rep_append (a + s + 1)
      (hY.reverse.clean_sep_append (Clean.sep (Clean.replicate b)))))
  have e2 : ∀ S : Strm, true ::: false ::: false ::: app (List.replicate (0 + 1) true).reverse
      (tl (ones (a + s + 2) (F ::: F ::: app Y.reverse (F ::: F ::: ones (b + 1) (false ::: true ::: S))))) =
      app (true :: F :: F :: (rep (a + s + 2) ++ F :: F :: (Y.reverse ++ F :: F :: rep (b + 1))))
        (false ::: true ::: S) := by
    intro S; simp [app_append, app_replicate, ones_succ]
  rw [e2]
  refine Rch.tr (PNB.find hw2 _ _) ?_
  gR
  unfold bAtC rgt leftOf preL
  simp only [Nat.add_sub_cancel, sep, List.reverse_append, List.reverse_replicate, app_append, app_replicate,
    cons_blank, app_cons, app_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.singleton_append, List.append_assoc, ones_cons_true]
  rw [show a + 1 + (s + 1) = a + s + 2 by omega]
  simp only [List.reverse_reverse, ones_zero, cons_blank, tl_cons]
  rw [show ∀ X : Strm, true ::: ones β (ones 2 X) = ones (β + 3) X from fun X => by rw [← ones_succ, ones_add]]
  fin

theorem PCP : ParserR delta CP1 CP2 := ⟨rfl, rfl, rfl⟩

/-- after the last power: the base cursor meets the marker; the compare starts -/
theorem compare_entry (n m E β α r : Nat) (Lx : Strm) (ha : 1 ≤ α) (hr : 1 ≤ r) :
    Rch (nbC n m E β (true :: F :: F :: rep α) r Lx)
      (zz 2 0 α (r + 2) (F ::: F ::: ones (β + 3) (F ::: F ::: ones m (F ::: F ::: ones n
        (F ::: true ::: F ::: F ::: ones (E + 1) Lx))))) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  unfold nbC rgt
  gR; sRn β
  simp only [sep, app_cons, app_nil]
  gR; gR; gR; gR; gR
  have e : app (rep α) (false ::: false ::: true ::: false ::: ones (s + 1) (false ::: false ::: ones 0 blank)) =
      app (rep α ++ [F, F, true]) (false ::: true ::: ones s blank) := by
    simp [app_append, app_replicate, cons_blank, ones_succ]
  rw [e]
  refine Rch.tr (PCP.find ((Clean.replicate α).append (Clean.sep Clean.nil)) _ _) ?_
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.reverse_replicate, List.cons_append, List.singleton_append, app_append, app_cons, app_nil, app_replicate]
  gL; gL; gL
  unfold zz
  simp only [zeros, ones_cons_true, ones_succ, cons_blank, ones_zero]
  fin

end TM.Beal
