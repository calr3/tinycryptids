import TinyCryptids.LehmerTau.NStep

/-!
# The seed

The seed writes the right part of the tape (X, Z, D with its hole, Rd, E, Re, S0) and the
constants as binary counters; each counter, last first, is drained into a new block at the far
left (one cell per decrement), then erased. Then P is created, K252 and K691 are switched on,
and the head finds D's hole: the start of `n = 2`.

A counter is a list of bits, least significant first; on the tape (left to right) the bits
come most significant first, each after a marker 1, and a final 1.
-/

namespace TM.LehmerTau
open St

local notation "F" => false

/-- the counter read leftward from the cell left of its final 1 -/
def cr : List Bool → List Bool
  | [] => []
  | b :: r => b :: true :: cr r

def vL : List Bool → Nat
  | [] => 0
  | b :: r => (if b then 1 else 0) + 2 * vL r

def decL : List Bool → Option (List Bool)
  | [] => none
  | true :: r => some (false :: r)
  | false :: r => (decL r).map (true :: ·)

theorem decL_some : ∀ r r', decL r = some r' → vL r' + 1 = vL r
  | [], _, h => by simp [decL] at h
  | true :: r, r', h => by simp [decL] at h; subst h; simp [vL]; omega
  | false :: r, r', h => by
    simp only [decL, Option.map_eq_some'] at h
    obtain ⟨r'', h1, rfl⟩ := h
    have := decL_some r r'' h1
    simp [vL]; omega

theorem decL_none : ∀ r, decL r = none → vL r = 0
  | [], _ => rfl
  | true :: r, h => by simp [decL] at h
  | false :: r, h => by
    simp only [decL, Option.map_eq_none'] at h
    simp [vL, decL_none r h]

theorem c12_cr : ∀ (r : List Bool) {W : List Bool}, Clean12 W → Clean12 (cr r ++ W)
  | [], _, h => h
  | true :: r, _, h => Clean12.one (Clean12.one (c12_cr r h))
  | false :: r, _, h => Clean12.z1 (c12_cr r h)

theorem c12_crr : ∀ r : List Bool, Clean12 ((cr r).reverse ++ [true])
  | [] => Clean12.one Clean12.nil
  | b :: r => by
    have := c12_crr r
    simp only [cr, List.reverse_cons, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
    rw [show (cr r).reverse ++ [true, b, true] = ((cr r).reverse ++ [true]) ++ [b, true] by simp]
    refine Clean12.append this ?_
    cases b
    · exact Clean12.z1 Clean12.nil
    · exact Clean12.one (Clean12.one Clean12.nil)

theorem FDA : FarL delta DA1 DA2 DA3 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- the borrow, from `DC3` on a bit; `t` ones (the lower bits and markers, now 1) right of it -/
theorem dc3 : ∀ (r r' : List Bool) (W : List Bool) (t : Nat), Clean12 W → decL r = some r' →
    Rch (cfgL DC3 (app (cr r ++ W) blank) (ones t blank))
      (cfgL DA3 blank (F ::: F ::: app ((cr r' ++ W).reverse ++ rep t) blank))
  | [], _, _, _, _, h => by simp [decL] at h
  | true :: r, r', W, t, hW, h => by
    simp [decL] at h; subst h
    simp only [cr, List.cons_append, app_cons]
    gL
    refine Rch.tr (FDA.go (w := true :: (cr r ++ W)) (Clean12.one (c12_cr r hW)) _) ?_
    simp [cr, List.reverse_append, app_append, app_rep]; fin
  | false :: r, r', W, t, hW, h => by
    simp only [decL, Option.map_eq_some'] at h
    obtain ⟨r'', h1, rfl⟩ := h
    simp only [cr, List.cons_append, app_cons]
    gL; gR; gL; gL
    have := dc3 r r'' W (t + 2) hW h1
    refine Rch.tr this ?_
    simp [cr, List.reverse_append, app_append, app_rep, rep_add]
    rw [ones_add]; fin

/-- a decrement, from `DC1` on bit 0 -/
theorem dc1 (b : Bool) (r r' W : List Bool) (hW : Clean12 W) (h : decL (b :: r) = some r') :
    Rch (cfgL DC1 (app (cr (b :: r) ++ W) blank) (ones 1 blank))
      (cfgL DA3 blank (F ::: F ::: app ((cr r' ++ W).reverse ++ rep 1) blank)) := by
  cases b
  · simp only [decL, Option.map_eq_some'] at h
    obtain ⟨r'', h1, rfl⟩ := h
    simp only [cr, List.cons_append, app_cons]
    gL; gL
    refine Rch.tr (dc3 r r'' W 3 hW h1) ?_
    simp [cr, List.reverse_append, app_append, app_rep, rep_add]
    fin
  · simp [decL] at h; subst h
    simp only [cr, List.cons_append, app_cons]
    gL
    refine Rch.tr (FDA.go (w := true :: (cr r ++ W)) (Clean12.one (c12_cr r hW)) _) ?_
    simp [cr, List.reverse_append, app_append, app_rep]; fin

/-- the counter is 0: the borrow runs out (`DU0` on the separator's first cell) -/
theorem dc3_none : ∀ (r : List Bool) (W : List Bool) (t : Nat), decL r = none →
    Rch (cfgL DC3 (app (cr r ++ F :: F :: W) blank) (ones t blank))
      ⟨DU0, F ::: app W blank, F ::: ones (t + 2 * r.length) blank⟩
  | [], W, t, _ => by
    simp only [cr, List.nil_append, app_cons]
    gL; gR; fin
  | true :: r, _, _, h => by simp [decL] at h
  | false :: r, W, t, h => by
    simp only [decL, Option.map_eq_none'] at h
    simp only [cr, List.cons_append, app_cons]
    gL; gR; gL; gL
    refine Rch.tr (dc3_none r W (t + 2) h) ?_
    simp only [List.length_cons]
    rw [show t + 2 + 2 * r.length = t + 2 * (r.length + 1) by omega]; fin

theorem dc1_none (r W : List Bool) (h : decL (false :: r) = none) :
    Rch (cfgL DC1 (app (cr (false :: r) ++ F :: F :: W) blank) (ones 1 blank))
      ⟨DU0, F ::: app W blank, F ::: ones (3 + 2 * r.length) blank⟩ := by
  simp only [decL, Option.map_eq_none'] at h
  simp only [cr, List.cons_append, app_cons]
  gL; gL
  exact dc3_none r W 3 h

/-- draining a counter `r` into the block A (`a + 2` cells, at the far left; `DB1` on its cell 1);
`Wm` between A and the counter -/
def DBc (a : Nat) (Wm r : List Bool) : Cfg St :=
  ⟨DB1, true ::: blank, app (rep (a + 1) ++ F :: F :: Wm ++ F :: F :: (cr r).reverse ++ [true]) blank⟩

theorem FDB : FarR delta DB1 DB2 DB3 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `Wm` is a word of blocks: clean both ways, a 1 at both ends -/
structure WmOk (Wm : List Bool) : Prop where
  c : Clean12 Wm
  cr : Clean12 Wm.reverse
  hd : ∃ w, Wm = true :: w
  tl : ∃ w, Wm.reverse = true :: w

theorem c12_sepW {W : List Bool} (hW : Clean12 W) (h : ∃ w, W = true :: w) : Clean12 (F :: F :: W) := by
  obtain ⟨w, rfl⟩ := h; cases hW with | one h => exact Clean12.z2 h

theorem crr_head : ∀ r : List Bool, ∃ w, (cr r).reverse ++ [true] = true :: w
  | [] => ⟨[], rfl⟩
  | b :: r => by
    obtain ⟨w, hw⟩ := crr_head r
    refine ⟨w ++ [b, true], ?_⟩
    simp only [cr, List.reverse_cons]
    rw [show (cr r).reverse ++ [true] ++ [b] ++ [true] = ((cr r).reverse ++ [true]) ++ [b, true] by simp, hw]; rfl

theorem drain_word (a : Nat) (Wm r : List Bool) (hW : WmOk Wm) :
    Clean12 (rep (a + 1) ++ F :: F :: Wm ++ F :: F :: (cr r).reverse ++ [true]) := by
  have h1 : Clean12 (F :: F :: ((cr r).reverse ++ [true])) := by
    refine c12_sepW (c12_crr r) ?_
    exact crr_head r
  have h2 := Clean12.append (c12_sepW hW.c hW.hd) h1
  have := c12_rep (a + 1) h2
  simpa [List.append_assoc] using this

theorem drain_left (a : Nat) (Wm : List Bool) (hW : WmOk Wm) :
    Clean12 (F :: F :: (Wm.reverse ++ F :: F :: rep (a + 2))) := by
  refine c12_sepW ?_ ?_
  · exact Clean12.append hW.cr (Clean12.z2 (by simpa [rep] using c12_rep (a + 1) Clean12.nil))
  · obtain ⟨w, hw⟩ := hW.tl; exact ⟨w ++ F :: F :: rep (a + 2), by rw [hw]; rfl⟩

/-- one decrement: A gains a cell -/
theorem drain_step (a : Nat) (Wm r r' : List Bool) (hW : WmOk Wm) (h : decL r = some r') :
    Rch (DBc a Wm r) (DBc (a + 1) Wm r') := by
  unfold DBc
  refine Rch.tr (FDB.go (drain_word a Wm r hW) _) ?_
  have e : (rep (a + 1) ++ F :: F :: Wm ++ F :: F :: (cr r).reverse ++ [true]).reverse =
      true :: (cr r ++ F :: F :: (Wm.reverse ++ F :: F :: rep (a + 1))) := by
    simp [List.reverse_append, rep_rev]
  rw [e]
  gL0; gL; gL; gL
  obtain ⟨b, rs, rfl⟩ : ∃ b rs, r = b :: rs := by
    cases r with
    | nil => simp [decL] at h
    | cons b rs => exact ⟨b, rs, rfl⟩
  have := dc1 b rs r' _ (drain_left a Wm hW) h
  refine Rch.tr (?_ : Rch _ (cfgL DC1 (app (cr (b :: rs) ++ F :: F :: (Wm.reverse ++ F :: F :: rep (a + 2))) blank)
    (ones 1 blank))) (Rch.tr this ?_)
  · simp only [app_cons, app_append, app_rep]
    rw [← ones_succ' (a + 1)]
    show Rch (cfgL DC1 _ (true ::: F ::: F ::: F ::: blank)) _
    simp only [cons_blank]; fin
  · have e2 : (cr r' ++ F :: F :: (Wm.reverse ++ F :: F :: rep (a + 2))).reverse ++ rep 1 =
        rep (a + 1 + 1) ++ F :: F :: Wm ++ F :: F :: (cr r').reverse ++ [true] := by
      simp [List.reverse_append, rep_rev, rep]
    rw [e2]
    gR0; gR; gR
    show Rch ⟨DB1, true ::: F ::: F ::: blank, _⟩ _
    simp only [cons_blank]; fin

/-- the counter is 0: it is erased; `DU2` on the last cell of `Wm` -/
theorem drain_end (a : Nat) (Wm rs : List Bool) (hW : WmOk Wm) (h : decL (false :: rs) = none) :
    Rch (DBc a Wm (false :: rs)) (cfgL DU2 (app (Wm.reverse ++ F :: F :: rep (a + 2)) blank) blank) := by
  unfold DBc
  refine Rch.tr (FDB.go (drain_word a Wm _ hW) _) ?_
  have e : (rep (a + 1) ++ F :: F :: Wm ++ F :: F :: (cr (false :: rs)).reverse ++ [true]).reverse =
      true :: (cr (false :: rs) ++ F :: F :: (Wm.reverse ++ F :: F :: rep (a + 1))) := by
    simp [List.reverse_append, rep_rev]
  rw [e]
  gL0; gL; gL; gL
  have := dc1_none rs (Wm.reverse ++ F :: F :: rep (a + 2)) h
  refine Rch.tr (?_ : Rch _ (cfgL DC1 (app (cr (false :: rs) ++ F :: F :: (Wm.reverse ++ F :: F :: rep (a + 2))) blank)
    (ones 1 blank))) (Rch.tr this ?_)
  · simp only [app_cons, app_append, app_rep]
    rw [← ones_succ' (a + 1)]
    show Rch (cfgL DC1 _ (true ::: F ::: F ::: F ::: blank)) _
    simp only [cons_blank]; fin
  · gR; eRn (3 + 2 * rs.length); gL0; zLn (3 + 2 * rs.length); gL; gL
    simp only [tl_blank, zeros_blank, cons_blank]; fin

theorem decL_len : ∀ r r', decL r = some r' → r'.length = r.length
  | [], _, h => by simp [decL] at h
  | true :: r, r', h => by simp [decL] at h; subst h; rfl
  | false :: r, r', h => by
    simp only [decL, Option.map_eq_some'] at h
    obtain ⟨r'', h1, rfl⟩ := h
    simp [decL_len r r'' h1]

/-- **A counter drained**: A gains `vL r` cells, the counter is erased -/
theorem drain_all (Wm : List Bool) (hW : WmOk Wm) : ∀ v a r, vL r = v → r ≠ [] →
    Rch (DBc a Wm r) (cfgL DU2 (app (Wm.reverse ++ F :: F :: rep (a + v + 2)) blank) blank) := by
  intro v
  induction v with
  | zero =>
    intro a r hv hne
    obtain ⟨b, rs, rfl⟩ : ∃ b rs, r = b :: rs := by
      cases r with
      | nil => exact absurd rfl hne
      | cons b rs => exact ⟨b, rs, rfl⟩
    cases h : decL (b :: rs) with
    | none =>
      cases b
      · exact drain_end a Wm rs hW h
      · simp [decL] at h
    | some r' => have := decL_some _ _ h; omega
  | succ v ih =>
    intro a r hv hne
    cases h : decL r with
    | none => have := decL_none r h; omega
    | some r' =>
      have h1 := decL_some _ _ h
      have h2 := decL_len _ _ h
      refine Rch.tr (drain_step a Wm r r' hW h) ?_
      have := ih (a + 1) r' (by omega) (by intro e; rw [e] at h2; cases r <;> simp_all)
      rw [show a + 1 + v + 2 = a + (v + 1) + 2 by omega] at this; exact this

/-- a word as it is written (left to right) -/
def cw (r : List Bool) : List Bool := (cr r).reverse ++ [true]

theorem FDN : FarL delta DN1 DN2 DN3 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- the next counter (the last block of `Wm' 00 cw r`): a new block A at the far left -/
theorem next_counter (Wm' : List Bool) (hW : WmOk Wm') (b : Bool) (rs : List Bool) (A : Nat) :
    Rch (cfgL DU2 (app ((Wm' ++ F :: F :: cw (b :: rs)).reverse ++ F :: F :: rep (A + 1)) blank) blank)
      (DBc 0 (rep (A + 1) ++ F :: F :: Wm') (b :: rs)) := by
  have e : (Wm' ++ F :: F :: cw (b :: rs)).reverse ++ F :: F :: rep (A + 1) =
      true :: b :: true :: (cr rs ++ F :: F :: (Wm'.reverse ++ F :: F :: rep (A + 1))) := by
    simp [cw, cr, List.reverse_append, rep_rev]
  have hc : Clean12 (cr rs ++ F :: F :: (Wm'.reverse ++ F :: F :: rep (A + 1))) := by
    refine c12_cr rs (c12_sepW (Clean12.append hW.cr (Clean12.z2 ?_)) ?_)
    · simpa [rep] using c12_rep A Clean12.nil
    · obtain ⟨w, hw⟩ := hW.tl; exact ⟨w ++ F :: F :: rep (A + 1), by rw [hw]; rfl⟩
  rw [e]
  simp only [app_cons]
  have rest : Rch (cfgL DN1 (app (cr rs ++ F :: F :: (Wm'.reverse ++ F :: F :: rep (A + 1))) blank)
      (true ::: b ::: true ::: blank)) (DBc 0 (rep (A + 1) ++ F :: F :: Wm') (b :: rs)) := by
    refine Rch.tr (FDN.go hc _) ?_
    gL0; gR0
    show Rch ⟨DB1, true ::: blank, true ::: F ::: F ::: app (cr rs ++ F :: F :: (Wm'.reverse ++ F :: F ::
      rep (A + 1))).reverse (true ::: b ::: true ::: blank)⟩ _
    unfold DBc
    have e2 : rep (0 + 1) ++ F :: F :: (rep (A + 1) ++ F :: F :: Wm') ++ F :: F :: (cr (b :: rs)).reverse ++ [true] =
        true :: F :: F :: ((cr rs ++ F :: F :: (Wm'.reverse ++ F :: F :: rep (A + 1))).reverse ++ [true, b, true]) := by
      simp [cr, List.reverse_append, rep_rev, rep]
    rw [e2]; simp [app_append]; fin
  cases b <;> (gL; gL; gL; exact rest)

/-- the right part of the tape: X, Z, D (hole), Rd = 0, E = 1, Re = 0, S0 -/
def rightW : List Bool :=
  rep 13 ++ [F, F, true, F, F, true, F, true, F, F, true, true, F, F, true, true, true, F, F, true, true, F, F, true, true]

theorem FDP : FarL delta DP1 DP2 DP3 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- all counters drained: P created, K252 and K691 on, the start of `n = 2` -/
theorem seed_end (kA kB kC : Nat) (hC : 1 ≤ kC) :
    Rch (cfgL DU2 (app ((rep (kB + 2) ++ F :: F :: rep (kC + 2) ++ F :: F :: rightW).reverse ++ F :: F :: rep (kA + 2))
      blank) blank) (Sn kA kB kC 2) := by
  obtain ⟨c, rfl⟩ : ∃ c, kC = c + 1 := ⟨kC - 1, by omega⟩
  have e : (rep (kB + 2) ++ F :: F :: rep (c + 1 + 2) ++ F :: F :: rightW).reverse ++ F :: F :: rep (kA + 2) =
      [true, true, F] ++ (F :: ([true, true, F, F, true, true, true, F, F, true, true, F, F, true, F, true, F, F, true,
        F, F] ++ rep 13 ++ F :: F :: rep (c + 3) ++ F :: F :: rep (kB + 2) ++ F :: F :: rep (kA + 2))) := by
    simp [rightW, List.reverse_append, rep_rev]
  rw [e]
  simp only [List.cons_append, List.nil_append, app_cons]
  gL; gL; gL
  have hc : Clean12 (F :: ([true, true, F, F, true, true, true, F, F, true, true, F, F, true, F, true, F, F, true,
        F, F] ++ rep 13 ++ F :: F :: rep (c + 3) ++ F :: F :: rep (kB + 2) ++ F :: F :: rep (kA + 2))) := by
    refine Clean12.z1 ?_
    have t1 : Clean12 (F :: F :: rep (kA + 2)) := Clean12.z2 (by simpa [rep] using c12_rep (kA + 1) Clean12.nil)
    have t2 : Clean12 (F :: F :: (rep (kB + 2) ++ F :: F :: rep (kA + 2))) :=
      Clean12.z2 (by simpa [rep] using c12_rep (kB + 1) t1)
    have t3 : Clean12 (F :: F :: (rep (c + 3) ++ F :: F :: rep (kB + 2) ++ F :: F :: rep (kA + 2))) :=
      Clean12.z2 (by simpa [rep, List.append_assoc] using c12_rep (c + 2) t2)
    have t4 : Clean12 (F :: F :: (rep 13 ++ F :: F :: rep (c + 3) ++ F :: F :: rep (kB + 2) ++ F :: F :: rep (kA + 2))) :=
      Clean12.z2 (by simpa [rep, List.append_assoc] using c12_rep 12 t3)
    have t5 := Clean12.append (l := [true, F, F, true, true, true, F, F, true, true, F, F, true, F, true, F, F, true])
      (by repeat (first | exact Clean12.nil | apply Clean12.one | apply Clean12.z1 | apply Clean12.z2)) t4
    simpa [List.append_assoc] using t5
  refine Rch.tr (FDP.go hc _) ?_
  simp only [List.reverse_cons, List.reverse_append, rep_rev, List.append_assoc, List.cons_append, List.nil_append,
    List.singleton_append, app_append, app_cons, app_rep, app_nil]
  gR0; gR; gR; sRn (kA + 2); gR; gR; gR; gR; sRn kB; gR; gR; gR; gR
  sRn (c + 1)
  gR; gR; sRn 13; gR; gR; gR; gR; gR; gR; gR; gL; gL; gL
  unfold Sn DV BD RB KR
  simp only [LS_pl, LS_dg1, LS, lpR, KB.w, List.nil_append, app_append, app_rep, rep, app_replicate,
    List.reverse_replicate, List.reverse_cons, List.reverse_nil, List.singleton_append, List.cons_append, app_cons,
    app_nil, List.reverse_append, ones_cons_true, Nat.add_sub_cancel, cons_blank]
  fin

/-! ## concrete words -/

/-- a checker for `Clean12` -/
def c12b : List Bool → Bool
  | [] => true
  | true :: l => c12b l
  | false :: true :: l => c12b l
  | false :: false :: true :: l => c12b l
  | _ => false

theorem c12b_ok : ∀ l, c12b l = true → Clean12 l
  | [], _ => Clean12.nil
  | true :: l, h => Clean12.one (c12b_ok l h)
  | false :: true :: l, h => Clean12.z1 (c12b_ok l h)
  | false :: false :: true :: l, h => Clean12.z2 (c12b_ok l h)
  | [false], h => by simp [c12b] at h
  | [false, false], h => by simp [c12b] at h
  | false :: false :: false :: _, h => by simp [c12b] at h

def c65 : List Bool := [true, F, F, F, F, F, true]
def c252 : List Bool := [F, F, true, true, true, true, true, true]
def c691 : List Bool := [true, true, F, F, true, true, F, true, F, true]

theorem vals : vL c65 = 65 ∧ vL c252 = 252 ∧ vL c691 = 691 := by decide

/-- the word the seed writes -/
def Pat : List Bool := rightW ++ F :: F :: cw c65 ++ F :: F :: cw c252 ++ F :: F :: cw c691

theorem Pat_eq : Pat = [
  true, true, true, true, true, true, true, true, true, true, true, true, true, F, F, true, F, F, 
  true, F, true, F, F, true, true, F, F, true, true, true, F, F, true, true, F, F, true, true, F, F, 
  true, true, true, F, true, F, true, F, true, F, true, F, true, true, true, F, F, true, true, true, 
  true, true, true, true, true, true, true, true, true, true, F, true, F, true, F, F, true, true, 
  true, F, true, true, true, F, true, true, true, true, true, F, true, F, true, true, true, true, 
  true] := by decide

def Wm1 : List Bool := rightW ++ F :: F :: cw c65 ++ F :: F :: cw c252

/-- the seed writes its word; the first counter (K691) is drained -/
theorem seed_start : Rch start (DBc 0 Wm1 c691) := by
  unfold start
  iterate 97 gR0
  simp only [tl_blank]
  apply blankR
  show Rch (cfgL DN1 (app (F :: Pat.reverse) blank) blank) _
  have hc : Clean12 (F :: Pat.reverse) := c12b_ok _ (by rw [Pat_eq]; decide)
  refine Rch.tr (FDN.go hc _) ?_
  gL0; gR0
  unfold DBc
  have e : rep (0 + 1) ++ F :: F :: Wm1 ++ F :: F :: (cr c691).reverse ++ [true] = true :: F :: F :: Pat := by
    rw [Pat_eq]; decide
  rw [e, List.reverse_cons, List.reverse_reverse, app_append]
  show Rch ⟨DB1, true ::: blank, true ::: F ::: F ::: app Pat (F ::: blank)⟩ _
  rw [cons_blank]; fin

theorem wmok_of (l : List Bool) (h1 : c12b l = true) (h2 : c12b l.reverse = true) (h3 : l.head? = some true)
    (h4 : l.reverse.head? = some true) : WmOk l := by
  refine ⟨c12b_ok _ h1, c12b_ok _ h2, ?_, ?_⟩
  · cases l with
    | nil => simp at h3
    | cons x w => simp at h3; exact ⟨w, by rw [h3]⟩
  · cases h : l.reverse with
    | nil => rw [h] at h4; simp at h4
    | cons x w => rw [h] at h4; simp at h4; exact ⟨w, by rw [h4]⟩

theorem wmok_rep (n : Nat) (W : List Bool) (hW : WmOk W) : WmOk (rep (n + 1) ++ F :: F :: W) := by
  refine ⟨c12_rep (n + 1) (c12_sepW hW.c hW.hd), ?_, ⟨rep n ++ F :: F :: W, rfl⟩, ?_⟩
  · simp only [List.reverse_append, List.reverse_cons, rep_rev, List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append]
    exact Clean12.append hW.cr (Clean12.z2 (by simpa [rep] using c12_rep n Clean12.nil))
  · obtain ⟨w, hw⟩ := hW.tl
    exact ⟨w ++ F :: F :: rep (n + 1), by simp [List.reverse_append, hw, rep_rev]⟩

def Wm1' : List Bool := rightW ++ F :: F :: cw c65

/-- **The seed**: the start of `n = 2` -/
theorem seed : Rch start (Sn 65 252 691 2) := by
  have w1 : WmOk Wm1 := wmok_of _ (by decide) (by decide) (by decide) (by decide)
  have w1' : WmOk Wm1' := wmok_of _ (by decide) (by decide) (by decide) (by decide)
  have w0 : WmOk rightW := wmok_of _ (by decide) (by decide) (by decide) (by decide)
  have w2 : WmOk (rep 693 ++ F :: F :: rightW) := wmok_rep 692 _ w0
  have w2' : WmOk (rep 693 ++ F :: F :: Wm1') := wmok_rep 692 _ w1'
  have w3 : WmOk (rep 254 ++ F :: F :: (rep 693 ++ F :: F :: rightW)) := wmok_rep 253 _ w2
  refine Rch.tr seed_start ?_
  refine Rch.tr (drain_all Wm1 w1 691 0 c691 (by decide) (by decide)) ?_
  refine Rch.tr (next_counter Wm1' w1' false [F, true, true, true, true, true, true] 692) ?_
  refine Rch.tr (drain_all _ w2' 252 0 c252 (by decide) (by decide)) ?_
  rw [show rep 693 ++ F :: F :: Wm1' = (rep 693 ++ F :: F :: rightW) ++ F :: F :: cw c65 by
    simp [Wm1', List.append_assoc]]
  refine Rch.tr (next_counter _ w2 true [F, F, F, F, F, true] 253) ?_
  refine Rch.tr (drain_all _ w3 65 0 c65 (by decide) (by decide)) ?_
  have := seed_end 65 252 691 (by omega)
  simpa [List.append_assoc] using this

end TM.LehmerTau
