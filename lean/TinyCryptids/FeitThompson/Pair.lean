import TinyCryptids.FeitThompson.Trial
import TinyCryptids.Core.Routines

/-!
# The pair step

From `PC m pre p post` (the marker on block `p`): H1 pushes `A = rep p m` right of `M`, H2 pushes
`B = rep m p` right of `A`, then `CYC(B, A)`: `B ∣ A` halts, else `A`, `B` are erased and the
marker moves one block left.  For `P0` (`p = 1`), H1 makes a copy of `m`: the next candidate.
-/

namespace TM.FeitThompson
open St TinyCryptids

local notation "F" => false
local notation "T" => true

/-- a walk to the first run of three blanks -/
structure Walk (w1 w2 w3 : St) : Prop where
  a1 : delta w1 true = some (true, Dir.R, w1)
  a0 : delta w1 false = some (false, Dir.R, w2)
  b1 : delta w2 true = some (true, Dir.R, w1)
  b0 : delta w2 false = some (false, Dir.R, w3)
  c1 : delta w3 true = some (true, Dir.R, w1)

theorem Walk.cross {w1 w2 w3 : St} (W : Walk w1 w2 w3) {u : List Bool} (hu : Clean12 u) (L X : Strm) :
    Rch ⟨w1, L, app u X⟩ ⟨w1, app u.reverse L, X⟩ := by
  induction hu generalizing L with
  | nil => fin
  | @one l _ ih =>
    refine Rch.tr (sR W.a1) ?_
    simpa [app_append] using ih (T ::: L)
  | @z1 l _ ih =>
    refine Rch.tr (sR W.a0) ?_
    refine Rch.tr (sR W.b1) ?_
    simpa [app_append] using ih (T ::: F ::: L)
  | @z2 l _ ih =>
    refine Rch.tr (sR W.a0) ?_
    refine Rch.tr (sR W.b0) ?_
    refine Rch.tr (sR W.c1) ?_
    simpa [app_append] using ih (T ::: F ::: F ::: L)

theorem Walk.go {w1 w2 w3 : St} (W : Walk w1 w2 w3) {u : List Bool} (hu : Clean12 u) (L X : Strm) :
    Rch ⟨w1, L, app u (F ::: F ::: F ::: X)⟩ ⟨w3, F ::: F ::: app u.reverse L, F ::: X⟩ := by
  refine Rch.tr (W.cross hu L _) ?_
  refine Rch.tr (sR W.a0) ?_
  exact sR W.b0

theorem WPW : Walk pw1 pw2 pw3 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem WTW : Walk tw1 tw2 tw3 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem clean_seps : ∀ qs, Clean (seps qs)
  | [] => Clean.nil
  | q :: qs => by
    show Clean (F :: F :: (List.replicate (q + 1 + 1) T ++ seps qs))
    rw [List.replicate_succ]
    exact Clean.sep (Clean.rep_append _ (clean_seps qs))

theorem clean12_skp (m : Nat) (hm : 1 ≤ m) : Clean12 (skp m) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact Clean12.one (by rw [List.replicate_succ]; exact Clean12.z1 (Clean12.of_clean (Clean.replicate m')))

theorem clean12_tail (p : Nat) (post : List Nat) (m : Nat) (hm : 1 ≤ m) :
    Clean12 (List.replicate p T ++ seps post ++ [F, F] ++ skp m) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [List.append_assoc]
  refine Clean12.append (Clean12.of_clean (Clean.rep_append p (clean_seps post))) ?_
  show Clean12 (F :: F :: T :: F :: (T :: List.replicate m' T))
  exact Clean12.z2 (Clean12.z1 (Clean12.of_clean (Clean.replicate m')))

/-- push `R = 101` on the third blank -/
theorem push (L : Strm) : Rch ⟨pw3, L, F ::: blank⟩ (cfgL HE1 (F ::: T ::: L) (T ::: blank)) := by
  gR
  refine blankR ?_
  gR
  refine blankR ?_
  gL0; fin

theorem lft_eq (m : Nat) (pre : List Nat) :
    app (skp m ++ seps pre ++ [F, F]).reverse blank = lft (F ::: blank) m 1 (seps pre ++ [F, F]) :=
  tc_left m pre

/-- H1 after the walk to the right end: push `R`, `A = rep p m` -/
theorem pair_h1' (m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    Rch ⟨pw3, F ::: F ::: app (List.replicate p T ++ seps post ++ [F, F] ++ skp m).reverse
        (F ::: T ::: app (skp m ++ seps pre ++ [F, F]).reverse blank), F ::: blank⟩
      ⟨hd1, F ::: T ::: F ::: blank, ones m (app (seps pre ++ [F, F])
        (app (bH1 p) (rgt (seps post ++ [F, F]) m (rep p m) 0)))⟩ := by
  refine Rch.tr (push _) ?_
  have key : F ::: T ::: F ::: F ::: app (List.replicate p T ++ seps post ++ [F, F] ++ skp m).reverse
      (F ::: T ::: app (skp m ++ seps pre ++ [F, F]).reverse blank) =
      ones 0 (F ::: T ::: F ::: F ::: app (skp m).reverse (app (seps post ++ [F, F]).reverse
        (ones p (F ::: T ::: lft (F ::: blank) m 1 (seps pre ++ [F, F]))))) := by
    rw [← lft_eq]
    simp only [List.reverse_append, List.reverse_replicate, app_append, app_replicate, ones_zero]
  rw [key]
  refine Rch.tr (he_chain (gap_seps post) (gap_seps pre) (F ::: blank) (T ::: blank) m 1 p m 0
    (Nat.le_refl _) hm hp hm) ?_
  have h := horner (gap_seps post) (gap_seps pre) blank m p m hm hp hm
  refine Rch.tr ?_ h
  unfold eAtC rgt
  simp only [sep_blank, sep, ones_zero, ones_succ, cons_blank]
  fin

/-- H1: `A = rep p m` pushed right of `M` -/
theorem pair_h1 (m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    Rch (PC m pre p post) ⟨hd1, F ::: T ::: F ::: blank, ones m (app (seps pre ++ [F, F])
      (app (bH1 p) (rgt (seps post ++ [F, F]) m (rep p m) 0)))⟩ := by
  unfold PC
  rw [show app (List.replicate p T ++ seps post ++ [F, F] ++ skp m) blank =
    app (List.replicate p T ++ seps post ++ [F, F] ++ skp m) (F ::: F ::: F ::: blank) by
    simp only [cons_blank]]
  refine Rch.tr (WPW.go (clean12_tail p post m hm) _ _) ?_
  exact pair_h1' m pre p post hm hp

theorem c12_skp (y : Nat) (hy : 1 ≤ y) {l : List Bool} (hl : Clean12 l) :
    Clean12 ([F, F] ++ skp y ++ l) := by
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  show Clean12 (F :: F :: T :: F :: T :: (List.replicate y' T ++ l))
  exact Clean12.z2 (Clean12.z1 ((Clean12.of_clean (Clean.replicate y')).append hl))

theorem walk2 {l : List Bool} (hl : Clean12 (F :: F :: l)) (L X : Strm) :
    Rch ⟨pw2, L, app (F :: l) (F ::: F ::: F ::: X)⟩ ⟨pw3, F ::: F ::: app (F :: l).reverse L, F ::: X⟩ := by
  cases hl with
  | z2 h =>
    rename_i l'
    gR; gR
    refine Rch.tr (WPW.go h _ _) ?_
    simp only [List.reverse_cons, app_append, app_cons, app_nil]
    fin

/-- the tail of the tape after `P0`'s first separator cell, after H1 -/
def tl1 (pre' : List Nat) (p : Nat) (post : List Nat) (m a : Nat) : List Bool :=
  seps pre' ++ [F, F] ++ skp p ++ seps post ++ [F, F] ++ skp m ++ [F, F] ++ skp a

theorem clean_tl1 (pre' : List Nat) (p : Nat) (post : List Nat) (m a : Nat) (hp : 1 ≤ p)
    (hm : 1 ≤ m) (ha : 1 ≤ a) : Clean12 (tl1 pre' p post m a) := by
  have h1 : Clean12 ([F, F] ++ skp a) := by simpa using c12_skp a ha Clean12.nil
  have h2 := c12_skp m hm h1
  have h3 := (Clean12.of_clean (clean_seps post)).append h2
  have h4 := c12_skp p hp h3
  have h5 := (Clean12.of_clean (clean_seps pre')).append h4
  unfold tl1
  simpa only [List.append_assoc] using h5

theorem gap_ff {g : List Bool} (h : Gap g) : ∃ w, g = F :: F :: w := by
  rcases h with rfl | ⟨P, _, rfl⟩
  · exact ⟨[], rfl⟩
  · exact ⟨_, rfl⟩

/-- after H1 (not for `P0`): past `P0`, to the right end, push `R`, H2: `B = rep m p` -/
theorem pair_h2 (m : Nat) (pre' : List Nat) (p : Nat) (post : List Nat) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    Rch ⟨hd1, F ::: T ::: F ::: blank, ones m (app (seps (1 :: pre') ++ [F, F])
      (app (bH1 p) (rgt (seps post ++ [F, F]) m (rep p m) 0)))⟩
      ⟨hd1, F ::: T ::: app (skp m ++ seps (1 :: pre') ++ [F, F]).reverse blank,
        ones p (app (seps post ++ [F, F]) (app (bH1 m) (rgt [F, F] (rep p m) (rep m p) 0)))⟩ := by
  have ha := rep_pos p m hm
  obtain ⟨w, hw⟩ := gap_ff (gap_seps pre')
  have ht : tl1 pre' p post m (rep p m) = F :: F :: (w ++ skp p ++ seps post ++ [F, F] ++ skp m ++
      [F, F] ++ skp (rep p m)) := by
    unfold tl1; rw [hw]; simp
  have hc := clean_tl1 pre' p post m (rep p m) hp hm ha
  rw [ht] at hc
  have hws : ∀ X, app (seps pre') (F ::: F ::: X) = F ::: F ::: app w X := by
    intro X; have := congrArg (fun l => app l X) hw; simpa [app_append] using this
  have eR : app (seps (1 :: pre') ++ [F, F]) (app (bH1 p) (rgt (seps post ++ [F, F]) m (rep p m) 0)) =
      F ::: F ::: T ::: T ::: T ::: F ::: app (F :: (w ++ skp p ++ seps post ++ [F, F] ++ skp m ++
        [F, F] ++ skp (rep p m))) (F ::: F ::: F ::: blank) := by
    simp only [seps, rgt, bH1, sep, List.cons_append, List.append_assoc, app_cons, app_append,
      app_replicate, ones_zero, cons_blank, List.replicate, hws]
    simp only [skp, app_cons, app_nil, app_replicate, List.append_assoc, app_append, cons_blank]
  rw [eR]
  sRn m
  gR; gR; gR; gR; gR; gR
  refine Rch.tr (walk2 hc _ _) ?_
  refine Rch.tr (push _) ?_
  have hwr : ∀ X, F ::: F ::: app (seps pre').reverse X = app w.reverse (F ::: F ::: X) := by
    intro X
    have := congrArg (fun l => app l.reverse X) hw
    simpa [List.reverse_append, app_append] using this
  have eLe : app (skp m ++ seps (1 :: pre') ++ [F, F]).reverse blank =
      F ::: app (F :: (seps (1 :: pre')).reverse ++ (skp m).reverse) blank := by
    simp [List.reverse_append, app_append]
  rw [eLe]
  have key : F ::: T ::: F ::: F ::: app (F :: (w ++ skp p ++ seps post ++ [F, F] ++ skp m ++ [F, F] ++
      skp (rep p m))).reverse (F ::: T ::: T ::: T ::: F ::: F ::: ones m (F ::: T ::: F ::: blank)) =
      ones 0 (F ::: T ::: F ::: F ::: app (skp (rep p m)).reverse (app [F, F].reverse (ones m (F ::: T :::
        lft (F ::: app (F :: (seps (1 :: pre')).reverse ++ (skp m).reverse) blank) p 1 (seps post ++ [F, F])))))
      := by
    simp only [lft, skp, seps, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
      app_append, app_cons, app_nil, app_replicate, ones_zero, Nat.add_sub_cancel, ones_succ]
    rw [← hwr]
    simp only [cons_blank]
  rw [key]
  refine Rch.tr (he_chain Gap.sep (gap_seps post) _ (T ::: blank) p 1 m (rep p m) 0
    (Nat.le_refl _) hp hm ha) ?_
  have h := horner Gap.sep (gap_seps post) (app (F :: (seps (1 :: pre')).reverse ++ (skp m).reverse) blank)
    p m (rep p m) hp hm ha
  have hb : rep m p = rep m p := rfl
  refine Rch.tr ?_ h
  unfold eAtC rgt
  simp only [sep_blank, sep, ones_zero, ones_succ, cons_blank]
  fin

/-- to the right end and back to `B`'s hole; the test cycle -/
theorem test_run {u : List Bool} (b a : Nat) (hu : Clean12 (u ++ [F, F] ++ skp a ++ [F, F] ++ skp b))
    (hb : 1 ≤ b) (ha : 1 ≤ a) (L : Strm) :
    Rch ⟨tw1, L, app (u ++ [F, F] ++ skp a ++ [F, F] ++ skp b) blank⟩
      ⟨if b ∣ a then kd3 else kn3, ones (b + 2) (cyL (F ::: F ::: app u.reverse L) a 1 [F, F]), blank⟩ := by
  rw [show app (u ++ [F, F] ++ skp a ++ [F, F] ++ skp b) blank =
    app (u ++ [F, F] ++ skp a ++ [F, F] ++ skp b) (F ::: F ::: F ::: blank) by simp only [cons_blank]]
  refine Rch.tr (WTW.go hu _ _) ?_
  gL; gL; gL
  simp only [skp, List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, app_append,
    app_cons, app_nil, app_replicate]
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [ones_succ]; gL; sLn b'; gR
  have h := cyc_run Gap.sep (F ::: app u.reverse L) blank a (b' + 1) ha hb
  simp only [cons_blank] at h
  refine Rch.tr ?_ h
  unfold cyc2 cyL
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, app_cons,
    app_nil, Nat.add_sub_cancel, ones_succ, ones_zero, cons_blank, tl_cons, ones_cons_true]
  fin

/-- the test failed: erase `B` and `A`, stop on `M`'s last cell -/
theorem cleanup (a b : Nat) (Y : Strm) (ha : 1 ≤ a) :
    Rch ⟨kn3, ones (b + 2) (cyL (F ::: F ::: T ::: Y) a 1 [F, F]), blank⟩ (cfgL RA1 Y (T ::: blank)) := by
  unfold cyL
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, app_cons,
    app_nil, Nat.add_sub_cancel]
  refine blankR ?_; gR
  refine blankR ?_; gR
  refine blankR ?_; gL0
  gL; gL
  rw [show b + 2 = b + 1 + 1 from rfl, ones_succ]
  gL
  eLn (b + 1)
  gL; gL
  eLn a
  gL
  rw [ones_succ, ones_zero]
  gL; gL; gL; gL
  simp only [tl_blank, zeros_blank, cons_blank]
  fin

theorem PRA : ParserL delta RA1 RA2 := ⟨rfl, rfl, rfl⟩
theorem PRB : ParserL delta RB1 RB2 := ⟨rfl, rfl, rfl⟩

/-- after the cleanup: past `M`'s hole to the marker; fill it; RETREAT to the previous block -/
theorem back (m p q : Nat) (pre0 post : List Nat) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    Rch (cfgL RA1 (ones (m - 1) (F ::: T ::: app ([F, F] ++ (seps post).reverse)
        (ones p (F ::: T ::: app (skp m ++ seps (pre0 ++ [q]) ++ [F, F]).reverse blank)))) (T ::: blank))
      (PC m pre0 q (p :: post)) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  refine Rch.tr (PRA.find0 m' _ _) ?_
  gL
  cases p with
  | zero => exact absurd hp (by omega)
  | succ p' =>
  have hw : Clean ([F, F] ++ (seps post).reverse ++ List.replicate (p' + 1) T) := by
    have := ((gap_seps post).reverse).clean (Clean.replicate p')
    simpa [List.reverse_append, List.replicate_succ] using this
  have e1 : app ([F, F] ++ (seps post).reverse) (ones (p' + 1)
      (F ::: T ::: app (skp (m' + 1) ++ seps (pre0 ++ [q]) ++ [F, F]).reverse blank)) =
      app ([F, F] ++ (seps post).reverse ++ List.replicate (p' + 1) T)
        (F ::: T ::: F ::: F ::: ones (q + 2) (F ::: F ::: app ((seps pre0).reverse ++ (skp (m' + 1)).reverse) blank)) := by
    simp only [seps_append, seps, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
      app_append, app_cons, app_nil, app_replicate]
  rw [e1]
  refine Rch.tr (PRB.find hw _ _) ?_
  gR; gL
  refine Rch.tr (retreat 1 q _ _) ?_
  unfold PC
  simp only [seps, skp, List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
    app_append, app_cons, app_nil, app_replicate, ones_succ, ones_zero]
  simp only [List.reverse_reverse]; rw [ones_cons_true]; fin

theorem probe_cons (m p q : Nat) (post : List Nat) (Le2 : Strm) (a b : Nat) (hq : 2 ≤ q) :
    Rch ⟨hd1, F ::: T ::: Le2, ones p (app (seps (q :: post) ++ [F, F]) (app (bH1 m) (rgt [F, F] a b 0)))⟩
      ⟨tw1, T ::: T ::: T ::: T ::: F ::: F ::: ones p (F ::: T ::: Le2),
        app (List.replicate (q - 2) T ++ seps post ++ [F, F] ++ skp m ++ [F, F] ++ skp a ++ [F, F] ++ skp b) blank⟩ := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  sRn p
  simp only [seps, bH1, rgt, sep, skp, List.cons_append, List.append_assoc, app_cons, app_append,
    app_replicate, ones_succ, ones_zero, cons_blank, Nat.add_sub_cancel, app_nil, List.replicate]
  gR; gR; gR; gR; gR; gR
  fin

theorem probe_nil (m p : Nat) (Le2 : Strm) (a b : Nat) (hm : 2 ≤ m) :
    Rch ⟨hd1, F ::: T ::: Le2, ones p (app (seps [] ++ [F, F]) (app (bH1 m) (rgt [F, F] a b 0)))⟩
      ⟨tw1, T ::: T ::: F ::: T ::: F ::: F ::: ones p (F ::: T ::: Le2),
        app (List.replicate (m - 2) T ++ [F, F] ++ skp a ++ [F, F] ++ skp b) blank⟩ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  sRn p
  simp only [seps, bH1, rgt, sep, skp, List.cons_append, List.nil_append, List.append_assoc, app_cons,
    app_append, app_replicate, ones_succ, ones_zero, cons_blank, Nat.add_sub_cancel, app_nil, List.replicate]
  gR; gR; gR; gR; gR; gR
  fin

theorem halt_kd3 (X : Strm) : HaltAt ⟨kd3, X, blank⟩ := by
  refine ⟨F ::: F ::: F ::: X, blank, ?_⟩
  refine blankR ?_; gR
  refine blankR ?_; gR
  refine blankR ?_; gR
  fin

theorem c12_ab (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : Clean12 ([F, F] ++ skp a ++ [F, F] ++ skp b) := by
  have := c12_skp a ha (by simpa using c12_skp b hb Clean12.nil)
  simpa only [List.append_assoc] using this

/-- **The pair step** for the block `p` (not `P0`) -/
theorem pair_step (m q p : Nat) (pre0 pre' post : List Nat) (hpre : pre0 ++ [q] = 1 :: pre')
    (hm : 3 ≤ m) (hp : 2 ≤ p) (hpost : ∀ x ∈ post, 2 ≤ x) :
    (rep m p ∣ rep p m → HaltAt (PC m (pre0 ++ [q]) p post)) ∧
    (¬ rep m p ∣ rep p m → Rch1 (PC m (pre0 ++ [q]) p post) (PC m pre0 q (p :: post))) := by
  have ha := rep_pos p m (by omega)
  have hb := rep_pos m p (by omega)
  have h1 := pair_h1 m (pre0 ++ [q]) p post (by omega) (by omega)
  have h2 := pair_h2 m pre' p post (by omega) (by omega)
  rw [← hpre] at h2
  -- to the test
  obtain ⟨u, L0, hu, hL0, hrun⟩ : ∃ u L0, Clean12 (u ++ [F, F] ++ skp (rep p m) ++ [F, F] ++ skp (rep m p)) ∧
      app u.reverse L0 = T ::: ones (m - 1) (F ::: T ::: app ([F, F] ++ (seps post).reverse)
        (ones p (F ::: T ::: app (skp m ++ seps (pre0 ++ [q]) ++ [F, F]).reverse blank))) ∧
      Rch ⟨hd1, F ::: T ::: F ::: blank, ones m (app (seps (pre0 ++ [q]) ++ [F, F])
          (app (bH1 p) (rgt (seps post ++ [F, F]) m (rep p m) 0)))⟩
        ⟨tw1, L0, app (u ++ [F, F] ++ skp (rep p m) ++ [F, F] ++ skp (rep m p)) blank⟩ := by
    cases post with
    | nil =>
      refine ⟨List.replicate (m - 2) T, _, ?_, ?_, Rch.tr h2 (probe_nil m p _ _ _ (by omega))⟩
      · have := (Clean12.of_clean (Clean.replicate (m - 2))).append (c12_ab _ _ ha hb)
        simpa only [List.append_assoc] using this
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
        simp only [List.reverse_replicate, app_replicate, seps, List.reverse_nil, List.append_nil,
          app_cons, app_nil, show m' + 3 - 2 = m' + 1 by omega, show m' + 3 - 1 = m' + 2 by omega,
          ones_succ]
        rw [ones_cons_true, ones_cons_true]
    | cons x post' =>
      have hx := hpost x (by simp)
      refine ⟨List.replicate (x - 2) T ++ seps post' ++ [F, F] ++ skp m, _, ?_, ?_,
        Rch.tr h2 (probe_cons m p x post' _ _ _ hx)⟩
      · have h3 := c12_skp m (by omega) (c12_ab _ _ ha hb)
        have := (Clean12.of_clean (Clean.rep_append (x - 2) (clean_seps post'))).append h3
        simpa only [List.append_assoc] using this
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
        obtain ⟨x', rfl⟩ : ∃ x', x = x' + 2 := ⟨x - 2, by omega⟩
        simp only [skp, seps, List.reverse_append, List.reverse_cons, List.reverse_replicate,
          List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
          app_append, app_cons, app_nil, app_replicate, Nat.add_sub_cancel,
          show m' + 3 - 1 = m' + 2 by omega, ones_succ]
        simp only [ones_cons_true]
  have ht := Rch.tr hrun (test_run (rep m p) (rep p m) hu hb ha L0)
  rw [hL0] at ht
  constructor
  · intro hd
    rw [if_pos hd] at ht
    exact HaltAt.back (Rch.tr h1 ht) (halt_kd3 _)
  · intro hd
    rw [if_neg hd] at ht
    obtain ⟨n, hn⟩ := h1
    cases n with
    | zero => simp [Sys.run, PC] at hn
    | succ n =>
      exact Reach1.trans_reach delta ⟨n, hn⟩
        (Rch.tr ht (Rch.tr (cleanup _ _ _ ha) (back m p q pre0 post (by omega) (by omega))))

theorem rep_one : ∀ m, rep 1 m = m
  | 0 => rfl
  | m + 1 => by rw [rep_succ, rep_one m, Nat.one_pow]

theorem PPO : ParserR delta PO1 PO2 := ⟨rfl, rfl, rfl⟩

/-- `P0`: H1 copies `m` right of `M`; `M` joins the list, the copy is the next `M`, then as for
a composite: the next candidate -/
theorem per_prime_tail (m p1 : Nat) (ps rest : List Nat) (hm : 2 ≤ m) (hps : ps ++ [m] = p1 :: rest) :
    Rch ⟨hd1, F ::: T ::: F ::: blank, ones m (app (seps [] ++ [F, F])
      (app (bH1 1) (rgt (seps ps ++ [F, F]) m m 0)))⟩ (TC (m + 1) [1] p1 rest) := by
  have hn := next_cand m p1 rest hm
  rw [← hps] at hn
  refine Rch.tr ?_ hn
  obtain ⟨w, hw⟩ := gap_ff (gap_seps ps)
  have hws : ∀ X, app (seps ps) (F ::: F ::: X) = F ::: F ::: app w X := by
    intro X; have := congrArg (fun l => app l X) hw; simpa [app_append] using this
  have hwr : ∀ X, F ::: F ::: app (seps ps).reverse X = app w.reverse (F ::: F ::: X) := by
    intro X
    have := congrArg (fun l => app l.reverse X) hw
    simpa [List.reverse_append, app_append] using this
  sRn m
  simp only [seps, bH1, rgt, sep, skp, List.nil_append, List.cons_append, List.append_assoc, app_cons,
    app_append, app_replicate, ones_succ, ones_zero, cons_blank, app_nil, List.replicate, hws]
  gR; gR; gR; gR; gR; gL; gL; gR
  have hc : Clean ([T, F, F] ++ w ++ [T]) := by
    have := (gap_seps ps).clean Clean.nil
    rw [hw] at this
    exact Clean.one (by simpa using this)
  have e1 : T ::: F ::: F ::: app w (T ::: F ::: ones m (F ::: F ::: T ::: F ::: ones m blank)) =
      app ([T, F, F] ++ w ++ [T]) (F ::: T ::: ones (m - 1) (F ::: F ::: T ::: F ::: ones m blank)) := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [app_append, app_cons, app_nil, Nat.add_sub_cancel, ones_succ]
  rw [e1]
  refine Rch.tr (PPO.find hc _ _) ?_
  gL; gR
  have e2 : T ::: ones (m - 1) (F ::: F ::: T ::: F ::: ones m blank) =
      app (List.replicate m T ++ [F, F, T]) (F ::: T ::: ones (m - 1) blank) := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [app_append, app_cons, app_nil, app_replicate, Nat.add_sub_cancel, ones_succ]
  rw [e2]
  refine Rch.tr (PPM.find (Clean.rep_append _ (Clean.sep Clean.nil)) _ _) ?_
  gR
  simp only [seps_append, seps, List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
    app_append, app_cons, app_nil, app_replicate]
  show Rch ⟨ms, T ::: F ::: T ::: F ::: F ::: ones m (T ::: T ::: app w.reverse (F ::: F ::: T ::: T ::: T :::
    F ::: F ::: ones m (F ::: T ::: blank))), ones (m - 1) blank⟩ _
  rw [← hwr, ones_cons_true, ones_cons_true]; fin

theorem per_prime (m p1 : Nat) (ps rest : List Nat) (hm : 2 ≤ m) (hps : ps ++ [m] = p1 :: rest) :
    Rch (PC m [] 1 ps) (TC (m + 1) [1] p1 rest) := by
  have h1 := pair_h1 m [] 1 ps (by omega) (Nat.le_refl _)
  rw [rep_one] at h1
  exact Rch.tr h1 (per_prime_tail m p1 ps rest hm hps)

end TM.FeitThompson
