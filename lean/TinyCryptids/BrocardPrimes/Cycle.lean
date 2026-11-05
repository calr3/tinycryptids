import TinyCryptids.BrocardPrimes.Left
namespace TM.BrocardPrimes
open St

/-! # One increment `m → m+1` -/

/-- The invariant at checkpoint `m`: `n = isqrt m`, the counter `1^(c+1)` with
`c` the number of primes in `(base n, m]`. -/
def Inv (m n c : Nat) : Prop :=
  2 ≤ m ∧ 1 ≤ n ∧ n*n ≤ m ∧ m < (n+1)*(n+1) ∧ c = pc m - pc (base n)

theorem ones_T_blank (k : Nat) : ones k (true ::: blank) = ones (k+1) blank := (ones_succ' k blank).symm

/-- the left part of the tape after the sweep, as a list (M's first cell excluded) -/
noncomputable def zoneW (m n : Nat) : List Bool :=
  pzRList ((loB m n).map stp) ++ F :: F :: true ::
    (pzRList ((upB m n).map stp) ++ F :: F :: List.replicate (m+2) true)

theorem app_zoneW (m n : Nat) : app (zoneW m n) (true ::: blank) = leftS m n := by
  simp [zoneW, leftS, app_append, app_pzRList, app_replicate, ones_T_blank]

theorem zoneW_clean (m n : Nat) : Clean3 (zoneW m n) ∧ Clean3 (F :: zoneW m n) := by
  have h1 := (Clean3.pzR ((upB m n).map stp) (List.replicate (m+1) true) (Clean3.rep _)).1
  have := Clean3.pzR ((loB m n).map stp) _ h1
  simp only [zoneW, rep_succ_T]; exact this

theorem zoneW_rev (m n : Nat) :
    (zoneW m n).reverse = List.replicate (m+2) true ++ F :: F :: (pzList ((upB m n).map stp) ++
      true :: F :: F :: pzList ((loB m n).map stp)) := by
  simp [zoneW, List.reverse_append, pzRList_reverse, List.reverse_replicate]

theorem from_step {m n c : Nat} {X : Cfg St}
    (h : Rch ⟨hg6, F ::: blank, F ::: F ::: app (CW m n c) blank⟩ X) : Rch1 (chk m n c) X :=
  Reach1.of_step_reach delta (chk_step m n c) h

theorem upB_prime (m n : Nat) (hm : sv n < m + 1) (h : PrimeDvd (m+1)) :
    upB (m+1) n = (m, 0) :: (upB m n).map stp := by
  rw [upB, upB, up_prime m n hm h, up, map_stp']
  simp [pb]

theorem loB_prime (m n : Nat) (hm : sv n < m + 1) (h : PrimeDvd (m+1)) :
    loB (m+1) n = (loB m n).map stp := by
  rw [loB, loB, lo_prime m n hm h, lo, map_stp']

theorem upB_comp (m n : Nat) (h : ¬ PrimeDvd (m+1)) : upB (m+1) n = (upB m n).map stp := by
  rw [upB, upB, up_comp m n h, up, map_stp']

theorem loB_comp (m n : Nat) (h : ¬ PrimeDvd (m+1)) : loB (m+1) n = (loB m n).map stp := by
  rw [loB, loB, lo_comp m n h, lo, map_stp']

theorem wraps_ul (m n : Nat) (hm : 1 ≤ m) :
    (wraps (upB m n) || wraps (loB m n)) = true ↔ ¬ PrimeDvd (m+1) := wraps_blocks m n hm

/-- `m+1` prime: S's hole moves, K grows, M is copied. -/
theorem cyc_prime (m n c : Nat) (hI : Inv m n c) (hp : PrimeDvd (m+1)) :
    Rch1 (chk m n c) (chk (m+1) n (c+1)) ∧ Inv (m+1) n (c+1) := by
  obtain ⟨hm2, hn, h1, h2, hc⟩ := hI
  have hsq := sq_succ n
  have hw : (wraps (upB m n) || wraps (loB m n)) = false := by
    cases h : (wraps (upB m n) || wraps (loB m n))
    · rfl
    · exact absurd hp ((wraps_ul m n (by omega)).1 h)
  have hns : m + 1 ≠ (n+1)*(n+1) := fun e => sq_not_prime n hn (e ▸ hp)
  have hsv : sv n < m + 1 := by
    unfold sv; have : 1 * n ≤ n * n := Nat.mul_le_mul_right n hn; omega
  obtain ⟨x, hX⟩ : ∃ x, sx m n = x + 1 := ⟨sx m n - 1, by unfold sx; omega⟩
  have hX' : sx (m+1) n = x := by unfold sx at hX ⊢; omega
  have hY' : sy (m+1) n = sy m n + 1 := by unfold sy; omega
  refine ⟨from_step (Rch.tr (sweep_all m n c) ?_), ⟨by omega, hn, by omega, by omega, ?_⟩⟩
  · rw [hw, hX]
    let y := sy m n
    refine Rch.tr (s_prime x y c _) ?_
    let w := List.replicate (c+1) true ++ F :: ((blkList x (y+1)).reverse ++ F :: zoneW m n)
    have hwc : Clean3 w := by
      refine Clean3.rep_app _ ?_
      have hb := Clean3.revblk x (y+1) (zoneW_clean m n).2
      rw [blkList_reverse] at hb ⊢; exact Clean3.z1' hb
    have ew : ones (c+1) (F ::: blkR x (y+1) (F ::: leftS m n)) = app w (true ::: blank) := by
      simp only [w, app_cons, app_append, app_replicate, app_blkList_rev, app_zoneW]
    let Z' := F ::: pz ((upB m n).map stp) (true ::: F ::: F ::: pz ((loB m n).map stp)
      (F ::: blk x (y+1) (F ::: ones (c+2) blank)))
    have hR : app w.reverse (true ::: blank) = true ::: ones m (true ::: (F ::: Z')) := by
      simp only [w, Z', List.reverse_cons, List.reverse_append, zoneW_rev, List.reverse_reverse,
        app_append, app_cons, app_nil, app_replicate, app_pzList, app_blkList, List.append_assoc,
        List.cons_append, List.singleton_append, List.nil_append, List.reverse_replicate]
      rw [show m + 2 = (m + 1) + 1 from rfl, ones_succ, ones_succ']
      simp only [ones_succ, ones_cons_true]
    rw [ew]
    refine Rch.tr (home_copy hwc _ m _ hR) ?_
    refine Rch.tr (cpy_all Z' m 1 0 2) ?_
    let w2 := true :: F :: (List.replicate (m+1) true ++ F :: F :: List.replicate (m+2) true)
    have hw2 : Clean3 w2 := by
      refine Clean3.one (Clean3.z1' ?_)
      rw [rep_succ_T]
      exact Clean3.one (Clean3.rep_app m (Clean3.z2 (by rw [rep_succ_T]; exact Clean3.one (Clean3.rep _))))
    let R2 := F :: F :: (pzList ((upB m n).map stp) ++ true :: F :: F ::
      (pzList ((loB m n).map stp) ++ tailW (c+1) x (y+1)))
    have e1 : (true ::: F ::: ones (1 + 0 + m) (F ::: F ::: ones (2 + m + 1) blank) : Strm) =
        app w2 (true ::: blank) := by
      simp only [w2, app_cons, app_append, app_replicate, ones_T_blank]
      rw [show 1 + 0 + m = m + 1 by omega, show 2 + m + 1 = m + 2 + 1 by omega]
    have e2 : (F ::: Z' : Strm) = app R2 blank := by
      simp only [Z', R2, app_cons, app_append, app_pzList, app_tailW, tailS]
    rw [e1, e2]
    refine Rch.tr (home_chk hw2 R2) ?_
    have eW : true :: w2.reverse ++ R2 = CW (m+1) n (c+1) := by
      rw [CW, upB_prime m n hsv hp, loB_prime m n hsv hp, hX', hY']
      simp [w2, R2, pzList, blkList, List.reverse_append, List.reverse_replicate, List.replicate_succ,
        List.append_assoc, rep_cons]
    rw [eW]; exact Reach.refl delta _
  · have hb := base_le n hn
    have := pc_succ m; rw [if_pos hp] at this
    have := pc_le (show base n ≤ m by omega)
    omega

theorem pzRList_snoc (u : List (Nat × Nat)) (a b : Nat) :
    pzRList (u ++ [(a, b)]) = F :: F :: ((blkList a b).reverse ++ pzRList u) := by
  induction u with
  | nil => simp [pzRList]
  | cons x u ih => obtain ⟨c, d⟩ := x; simp [pzRList, ih]

theorem pzList_snoc (u : List (Nat × Nat)) (a b : Nat) :
    pzList (u ++ [(a, b)]) = pzList u ++ blkList a b ++ [F, F] := by
  rw [pzList_append]; simp [pzList]

/-- not at a prime square: the scan, having found the marker, goes home -/
theorem lf_home (m : Nat) (up' : List (Nat × Nat)) (hcase : up' = [] ∨ ∃ u x y, up' = u ++ [(x, y+1)])
    (Z : Strm) (hZ : pzR up' (F ::: F ::: ones (m+3) blank) = F ::: F ::: Z) (Rl : List Bool) :
    Rch (cfgL lf Z (app (F :: F :: Rl) blank))
      (chkW (List.replicate (m+3) true ++ F :: F :: (pzList up' ++ Rl))) := by
  rcases hcase with rfl | ⟨u, x, y, rfl⟩
  · simp only [pzR] at hZ
    obtain rfl : Z = ones (m+3) blank := by
      have := congrArg (fun s : Strm => tl (tl s)) hZ; exact this.symm
    rw [show m + 3 = (m + 1) + 1 + 1 from rfl, ones_succ, ones_succ]
    gL; gL
    have hw : Clean3 (List.replicate m true) := Clean3.rep m
    rw [show ones (m+1) blank = app (List.replicate m true) (true ::: blank) by
      rw [app_replicate, ones_T_blank]]
    refine Rch.tr (home_chk hw (true :: true :: F :: F :: Rl)) ?_
    simp [pzList, List.reverse_replicate, List.replicate_succ, rep_cons]; fin
  · rw [pzR_snoc] at hZ
    obtain rfl : Z = blkR x (y+1) (pzR u (F ::: F ::: ones (m+3) blank)) := by
      have := congrArg (fun s : Strm => tl (tl s)) hZ; exact this.symm
    unfold blkR; rw [ones_succ]
    gL; gL
    let W := List.replicate y true ++ F :: (List.replicate x true ++ true ::
      (pzRList u ++ F :: F :: List.replicate (m+2) true))
    have hw : Clean3 W := by
      refine Clean3.rep_app y ?_
      rw [rep_cons]
      refine Clean3.z1 (Clean3.rep_app x ?_)
      rw [rep_succ_T]
      exact (Clean3.pzR u _ (Clean3.rep _)).1
    have e : ones y (F ::: ones x (true ::: pzR u (F ::: F ::: ones (m+3) blank))) =
        app W (true ::: blank) := by
      simp only [W, app_append, app_cons, app_replicate, app_pzRList, ones_T_blank]
    rw [e]
    refine Rch.tr (home_chk hw (true :: true :: F :: F :: Rl)) ?_
    simp [W, pzList_snoc, blkList, List.reverse_append, pzRList_reverse, List.reverse_replicate,
      List.replicate_succ, rep_cons, List.append_assoc]
    fin

/-- `m+1` composite and not a square: S's hole moves. -/
theorem cyc_comp (m n c : Nat) (hI : Inv m n c) (hnp : ¬ PrimeDvd (m+1))
    (hns : m + 1 ≠ (n+1)*(n+1)) :
    Rch1 (chk m n c) (chk (m+1) n c) ∧ Inv (m+1) n c := by
  obtain ⟨hm2, hn, h1, h2, hc⟩ := hI
  have hsq := sq_succ n
  have hw : (wraps (upB m n) || wraps (loB m n)) = true := (wraps_ul m n (by omega)).2 hnp
  obtain ⟨x, hX⟩ : ∃ x, sx m n = x + 1 := ⟨sx m n - 1, by unfold sx; omega⟩
  have hX' : sx (m+1) n = x := by unfold sx at hX ⊢; omega
  have hY' : sy (m+1) n = sy m n + 1 := by unfold sy; omega
  refine ⟨from_step (Rch.tr (sweep_all m n c) ?_), ⟨by omega, hn, by omega, by omega, ?_⟩⟩
  · rw [hw, hX]
    let y := sy m n
    refine Rch.tr (s_comp x y _ _) ?_
    let w := List.replicate x true ++ true :: F :: zoneW m n
    have hwc : Clean3 w := Clean3.rep_app _ (Clean3.one (zoneW_clean m n).2)
    let R := F :: (List.replicate (y+1) true ++ true :: F :: List.replicate (c+1) true)
    have e1 : ones x (true ::: F ::: leftS m n) = app w (true ::: blank) := by
      simp only [w, app_append, app_cons, app_replicate, app_zoneW]
    have e2 : (F ::: ones (y+1) (true ::: F ::: ones (c+1) blank) : Strm) = app R blank := by
      simp only [R, app_cons, app_append, app_replicate]
    rw [e1, e2]
    refine Rch.tr (home_chk hwc R) ?_
    have eW : true :: w.reverse ++ R = CW (m+1) n c := by
      rw [CW, upB_comp m n hnp, loB_comp m n hnp, hX', hY']
      simp [w, R, zoneW_rev, tailW, blkList, List.reverse_append, List.reverse_replicate,
        List.replicate_succ, List.append_assoc, rep_cons]
    rw [eW]; exact Reach.refl delta _
  · have := pc_succ m; rw [if_neg hnp] at this; omega

theorem pzR_FF (l : List (Nat × Nat)) : ∀ L : Strm, ∃ Z, pzR l (F ::: F ::: L) = F ::: F ::: Z := by
  induction l with
  | nil => intro L; exact ⟨L, rfl⟩
  | cons x l ih => intro L; obtain ⟨a, b⟩ := x; exact ih _

theorem base_sq (n : Nat) (hn : 1 ≤ n) (h : ¬ (PrimeDvd (n+1) ∧ 2 ≤ n)) : base (n+1) = base n := by
  by_cases hp : PrimeDvd (n+1)
  · obtain rfl : n = 1 := by
      apply Classical.byContradiction; intro h1; exact h ⟨hp, by omega⟩
    unfold base; rw [lp_succ, if_pos hp, lp_one]; simp
  · unfold base; rw [lp_succ, if_neg hp]

/-- the blocks above the marker after the sweep, at a square that is not a prime square -/
theorem up_case (m n : Nat) (hn : 1 ≤ n) (hsq : m + 1 = (n+1)*(n+1))
    (h : ¬ (PrimeDvd (n+1) ∧ 2 ≤ n)) :
    (upB m n).map stp = [] ∨ ∃ u x y, (upB m n).map stp = u ++ [(x, y+1)] := by
  have hd := up_not_dvd m n hn hsq h
  rw [upB, up, map_stp']
  rcases List.eq_nil_or_concat ((primesDesc m).filter (fun p => decide (sv n < p))) with e | ⟨L, q, e⟩
  · left; rw [e]; rfl
  · right
    have hq := hd q (by rw [up, e]; simp)
    refine ⟨L.map (pb (m+1)), q - 1 - (m+1) % q, (m+1) % q - 1, ?_⟩
    rw [e, List.concat_eq_append, List.map_append]; simp [pb]; omega

theorem sq_arith (n : Nat) : 2*(n+1) = 2*n + 2 := by omega

/-- `m+1 = (n+1)^2` with `n+1` not a prime `≥ 3`: S grows, the marker stays. -/
theorem cyc_sq (m n c : Nat) (hI : Inv m n c) (hsq' : m + 1 = (n+1)*(n+1))
    (h : ¬ (PrimeDvd (n+1) ∧ 2 ≤ n)) :
    Rch1 (chk m n c) (chk (m+1) (n+1) c) ∧ Inv (m+1) (n+1) c := by
  obtain ⟨hm2, hn, h1, h2, hc⟩ := hI
  have hsq := sq_succ n
  have hsq2 := sq_succ (n+1)
  have hnp := sq_not_prime n hn
  rw [← hsq'] at hnp
  have hw : (wraps (upB m n) || wraps (loB m n)) = true := (wraps_ul m n (by omega)).2 hnp
  have hX : sx m n = 0 := by unfold sx; omega
  have hX' : sx (m+1) (n+1) = sy m n + 2 := by unfold sx sy; omega
  have hY' : sy (m+1) (n+1) = 0 := by unfold sy; omega
  refine ⟨from_step (Rch.tr (sweep_all m n c) ?_), ⟨by omega, by omega, by omega, by omega, ?_⟩⟩
  · rw [hw, hX]
    let y := sy m n
    refine Rch.tr (s_square y c _) ?_
    obtain ⟨Z, hZ⟩ := pzR_FF ((upB m n).map stp) (ones (m+3) blank)
    refine Rch.tr (scan_all c y _ _ _ Z hZ) ?_
    let Rl := true :: F :: F :: (pzList ((loB m n).map stp) ++ tailW c (y+2) 0)
    have e : (F ::: F ::: true ::: F ::: F ::: pz ((loB m n).map stp) (tailS c (y+2) 0) : Strm) =
        app (F :: F :: Rl) blank := by
      simp only [Rl, app_cons, app_append, app_pzList, app_tailW]
    rw [e]
    refine Rch.tr (lf_home m _ (up_case m n hn hsq' h) Z hZ Rl) ?_
    have eW : List.replicate (m+3) true ++ F :: F :: (pzList ((upB m n).map stp) ++ Rl) =
        CW (m+1) (n+1) c := by
      have hu : (upB m n).map stp = upB (m+1) (n+1) := by
        rw [upB, upB, up_comp m (n+1) hnp, up_sq m n h, up, map_stp']
      have hl : (loB m n).map stp = loB (m+1) (n+1) := by
        rw [loB, loB, lo_comp m (n+1) hnp, lo_sq m n h, lo, map_stp']
      rw [CW, hX', hY', ← hu, ← hl]
    rw [eW]; exact Reach.refl delta _
  · rw [base_sq n hn h]
    have := pc_succ m; rw [if_neg hnp] at this; omega

theorem rep_add (a b : Nat) : List.replicate (a+b) true = List.replicate a true ++ List.replicate b true := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 by omega, List.replicate_succ, List.replicate_succ, ih]; rfl

/-- the left part after the scan, below the moved block -/
noncomputable def fullW (m : Nat) (u : List (Nat × Nat)) : List Bool :=
  pzRList u ++ F :: F :: List.replicate (m+2) true

theorem app_fullW (m : Nat) (u : List (Nat × Nat)) :
    app (fullW m u) (true ::: blank) = pzR u (F ::: F ::: ones (m+3) blank) := by
  simp [fullW, app_append, app_pzRList, app_replicate, ones_T_blank]

theorem fullW_clean (m : Nat) (u : List (Nat × Nat)) : Clean3 (fullW m u) := by
  have := (Clean3.pzR u (List.replicate (m+1) true) (Clean3.rep _)).1
  simp only [fullW, rep_succ_T]; exact this

/-- at a prime square `(n+1)^2 = m+1`: the blocks above the marker after the sweep end with
the block of `n+1`, hole at its last index -/
theorem up_bd_map (m n : Nat) (hp : PrimeDvd (n+1)) (h2 : 2 ≤ n) (hm : n + 1 ≤ m)
    (hsq : m + 1 = (n+1)*(n+1)) :
    (upB m n).map stp = upB (m+1) (n+1) ++ [(n, 0)] := by
  have hnp : ¬ PrimeDvd (m+1) := by rw [hsq]; exact sq_not_prime n (by omega)
  rw [upB, upB, up_comp m (n+1) hnp, up_bd m n hp h2 hm, map_stp, List.map_append]
  · simp only [List.map_cons, List.map_nil, pb]
    have : (m + 1) % (n + 1) = 0 := by rw [hsq]; exact Nat.mul_mod_right _ _
    rw [this]; simp
  · intro p hp'
    rw [List.mem_append] at hp'
    rcases hp' with hp' | hp'
    · exact two_le_of_mem hp'
    · simp at hp'; omega

theorem loB_bd (m n : Nat) (hp : PrimeDvd (n+1)) (h2 : 2 ≤ n) (hm : n + 1 ≤ m)
    (hsq : m + 1 = (n+1)*(n+1)) :
    loB (m+1) (n+1) = (n, 0) :: (loB m n).map stp := by
  have hnp : ¬ PrimeDvd (m+1) := by rw [hsq]; exact sq_not_prime n (by omega)
  rw [loB, loB, lo_comp m (n+1) hnp, lo_bd m n hp h2 hm, List.map_cons, lo, map_stp']
  simp only [pb]
  have : (m + 1) % (n + 1) = 0 := by rw [hsq]; exact Nat.mul_mod_right _ _
  rw [this]; simp

theorem pzList_reverse (l : List (Nat × Nat)) : (pzList l).reverse = pzRList l := by
  rw [← pzRList_reverse, List.reverse_reverse]

theorem Clean3.pz3 (l : List (Nat × Nat)) : ∀ r : List Bool, Clean3 (true :: r) →
    Clean3 (F :: F :: (pzList l ++ F :: true :: r)) := by
  induction l with
  | nil => intro r h; exact Clean3.z3' h
  | cons x l ih =>
    intro r h
    obtain ⟨a, b⟩ := x
    simp only [pzList, List.append_assoc, List.cons_append]
    have := Clean3.blk a b (ih r h)
    simp only [blkList, List.cons_append] at this ⊢
    exact Clean3.z2' this

/-- the right part crossed on the way to the counter -/
noncomputable def rW (n c : Nat) (lo' : List (Nat × Nat)) : List Bool :=
  List.replicate (n+1) true ++ F :: true :: F :: F :: (pzList lo' ++ tailW c (2*n+2) 0)

theorem rW_clean (n c : Nat) (lo' : List (Nat × Nat)) : Clean3 (rW n c lo') := by
  refine Clean3.rep_app _ (Clean3.z1 ?_)
  have := Clean3.pz3 lo' (List.replicate (2*n+2) true ++ F :: true :: F :: List.replicate (c+1) true) ?_
  · simpa [rW, tailW, blkList, List.append_assoc] using this
  · exact Clean3.one (Clean3.rep_app _ (Clean3.z1 (Clean3.z1 (Clean3.rep _))))

/-- a prime square: up to the right end, with the marker already moved -/
theorem reach_k (m n c : Nat) (hI : Inv m n c) (hsq' : m + 1 = (n+1)*(n+1))
    (hp : PrimeDvd (n+1)) (h2 : 2 ≤ n) :
    Rch ⟨hg6, F ::: blank, F ::: F ::: app (CW m n c) blank⟩
      ⟨r1, app (rW n c ((loB m n).map stp)).reverse (F ::: F ::: true ::: pzR (upB (m+1) (n+1))
        (F ::: F ::: ones (m+3) blank)), blank⟩ := by
  obtain ⟨hm2, hn, h1, h2', hc⟩ := hI
  have hsq := sq_succ n
  have hnp := sq_not_prime n hn
  rw [← hsq'] at hnp
  have hw : (wraps (upB m n) || wraps (loB m n)) = true := (wraps_ul m n (by omega)).2 hnp
  have hX : sx m n = 0 := by unfold sx; omega
  have hY : sy m n + 2 = 2*n + 2 := by unfold sy; omega
  have hnm : n + 1 ≤ m := by have := Nat.mul_le_mul_left (n+1) (show 2 ≤ n + 1 by omega); omega
  refine Rch.tr (sweep_all m n c) ?_
  rw [hw, hX]
  refine Rch.tr (s_square (sy m n) c _) ?_
  obtain ⟨Lu, hLu⟩ := pzR_FF (upB (m+1) (n+1)) (ones (m+3) blank)
  have hZ : pzR ((upB m n).map stp) (F ::: F ::: ones (m+3) blank) =
      F ::: F ::: blkR n 0 (F ::: F ::: Lu) := by
    rw [up_bd_map m n hp h2 hnm hsq', pzR_snoc, hLu]
  refine Rch.tr (scan_all c _ _ _ _ _ hZ) ?_
  obtain ⟨x, rfl⟩ : ∃ x, n = x + 2 := ⟨n - 2, by omega⟩
  unfold blkR; simp only [ones_zero]
  gL
  refine Rch.tr (bd_shift x Lu _) ?_
  rw [hY]
  have := rcross (rW_clean (x+2) c ((loB m (x+2)).map stp)) (F ::: F ::: true ::: F ::: F ::: Lu) blank
  rw [hLu]
  simpa [rW, app_append, app_pzList, app_tailW, app_replicate] using this


/-- `m+1 = (n+1)^2` with `n+1 ≥ 3` prime and at least 4 primes counted: the marker moves
past the block of `n+1`, the counter restarts. -/
theorem cyc_bd (m n c : Nat) (hI : Inv m n c) (hsq' : m + 1 = (n+1)*(n+1))
    (hp : PrimeDvd (n+1)) (h2 : 2 ≤ n) (hc4 : 4 ≤ c) :
    Rch1 (chk m n c) (chk (m+1) (n+1) 0) ∧ Inv (m+1) (n+1) 0 := by
  have hr := reach_k m n c hI hsq' hp h2
  obtain ⟨hm2, hn, h1, h2', hc⟩ := hI
  have hsq := sq_succ n
  have hsq2 := sq_succ (n+1)
  have hnm : n + 1 ≤ m := by have := Nat.mul_le_mul_left (n+1) (show 2 ≤ n + 1 by omega); omega
  refine ⟨from_step (Rch.tr hr ?_), ⟨by omega, by omega, by omega, by omega, ?_⟩⟩
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 4 := ⟨c - 4, by omega⟩
    let lo' := (loB m n).map stp
    let u := upB (m+1) (n+1)
    let Y := blkR (2*n+2) 0 (F ::: pzR lo' (F ::: F ::: true ::: F ::: ones (n+1)
      (F ::: F ::: true ::: pzR u (F ::: F ::: ones (m+3) blank))))
    have eY : app (rW n (c'+4) lo').reverse (F ::: F ::: true ::: pzR u (F ::: F ::: ones (m+3) blank)) =
        ones (c'+5) (F ::: Y) := by
      simp only [Y, rW, tailW, List.reverse_append, List.reverse_cons, List.reverse_replicate,
        pzList_reverse, app_pzRList, app_append, app_cons, app_nil, app_replicate, app_blkList_rev,
        List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
    rw [eY]
    refine Rch.tr (e_reset c' Y) ?_
    let w := F :: ((blkList (2*n+2) 0).reverse ++ F :: (pzRList lo' ++ F :: F :: true :: F ::
      (List.replicate (n+1) true ++ [F, F, true] ++ fullW m u)))
    have hwc : Clean3 w := by
      have hr : Clean3 (F :: (List.replicate (n+1) true ++ [F, F, true] ++ fullW m u)) := by
        have h3 := Clean3.rep_app n (Clean3.z2 (fullW_clean m u))
        rw [rep_succ_T]
        exact Clean3.z1 (by simpa [List.append_assoc] using h3)
      have hb := Clean3.revblk (2*n+2) 0 (Clean3.pzR lo' _ hr).2
      rw [blkList_reverse] at hb; simp only [w, blkList_reverse]; exact Clean3.z1' hb
    have e1 : (F ::: Y : Strm) = app w (true ::: blank) := by
      simp only [Y, w, app_append, app_cons, app_nil, app_replicate, app_blkList_rev, app_pzRList,
        app_fullW]
    have e2 : (true ::: blank : Strm) = app [true] blank := rfl
    rw [e1, e2]
    refine Rch.tr (home_chk hwc [true]) ?_
    have hX' : sx (m+1) (n+1) = 2*n+2 := by unfold sx; omega
    have hY' : sy (m+1) (n+1) = 0 := by unfold sy; omega
    have eW : true :: w.reverse ++ [true] = CW (m+1) (n+1) 0 := by
      rw [CW, loB_bd m n hp h2 hnm hsq', hX', hY', tailW]
      simp [w, u, fullW, pzList, blkList, List.reverse_append, pzRList_reverse,
        List.reverse_replicate, List.replicate_succ, List.append_assoc, rep_cons]
    rw [eW]; exact Reach.refl delta _
  · have hb : base (n+1) = (n+1)*(n+1) := by
      unfold base; rw [lp_succ, if_pos hp, if_pos (by omega)]
    rw [hb, ← hsq']; omega

/-- `m+1 = (n+1)^2` with `n+1 ≥ 3` prime and fewer than 4 primes counted: HALT. -/
theorem cyc_halt (m n c : Nat) (hI : Inv m n c) (hsq' : m + 1 = (n+1)*(n+1))
    (hp : PrimeDvd (n+1)) (h2 : 2 ≤ n) (hc4 : c < 4) : HaltAt (chk m n c) := by
  refine HaltAt.back (from_step (reach_k m n c hI hsq' hp h2)).reach ?_
  let Y := blkR (2*n+2) 0 (F ::: pzR ((loB m n).map stp) (F ::: F ::: true ::: F ::: ones (n+1)
    (F ::: F ::: true ::: pzR (upB (m+1) (n+1)) (F ::: F ::: ones (m+3) blank))))
  have eY : app (rW n c ((loB m n).map stp)).reverse
      (F ::: F ::: true ::: pzR (upB (m+1) (n+1)) (F ::: F ::: ones (m+3) blank)) = ones (c+1) (F ::: Y) := by
    simp only [Y, rW, tailW, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      pzList_reverse, app_pzRList, app_append, app_cons, app_nil, app_replicate, app_blkList_rev,
      List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
  rw [eY]; exact e_halt c hc4 Y

end TM.BrocardPrimes
