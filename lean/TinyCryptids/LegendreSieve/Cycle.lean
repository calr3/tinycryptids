import TinyCryptids.LegendreSieve.Tape
namespace TM.LegendreSieve
open St

/-! ## One increment `m → m+1` -/

/-- The invariant at checkpoint `m`: `n = isqrt m` (with `n ≥ 1`) and `f` says
whether a prime lies in `(n², m]`. -/
def Inv (m n : Nat) (f : Bool) : Prop :=
  1 ≤ n ∧ n*n ≤ m ∧ m < (n+1)*(n+1) ∧ (f = true ↔ ∃ p, PrimeDvd p ∧ n*n < p ∧ p ≤ m)

theorem ones_T_blank (k : Nat) : ones k (true ::: blank) = ones (k+1) blank := (ones_succ' k blank).symm

theorem Clean3.z1' {l : List Bool} (h : Clean3 (true :: l)) : Clean3 (F :: true :: l) := by
  cases h with | one h => exact Clean3.z1 h

theorem rep_succ_T (k : Nat) : List.replicate (k+1) true = true :: List.replicate k true := rfl

/-- the left part of the tape after the sweep, as a list (M's first cell excluded) -/
def zoneW (bl : List (Nat × Nat)) (m : Nat) : List Bool :=
  pzRList bl ++ F :: F :: List.replicate (m+2) true

theorem app_zoneW (bl : List (Nat × Nat)) (m : Nat) :
    app (zoneW bl m) (true ::: blank) = pzR bl (F ::: F ::: ones (m+3) blank) := by
  simp [zoneW, app_append, app_pzRList, app_replicate, ones_T_blank]

theorem zoneW_clean (bl : List (Nat × Nat)) (m : Nat) :
    Clean3 (zoneW bl m) ∧ Clean3 (F :: zoneW bl m) := by
  have := Clean3.pzR bl (List.replicate (m+1) true) (Clean3.rep _)
  simp only [zoneW, rep_succ_T]; exact this

theorem zoneW_rev (bl : List (Nat × Nat)) (m : Nat) :
    (zoneW bl m).reverse = List.replicate (m+2) true ++ F :: F :: pzList bl := by
  simp [zoneW, List.reverse_append, pzRList_reverse, List.reverse_replicate]

/-- Arithmetic of the S block -/
theorem s_arith (m n : Nat) (h1 : n*n ≤ m) (h2 : m < (n+1)*(n+1)) :
    m - n*n ≤ 2*n ∧ (2*n - (m - n*n) = 0 ↔ m + 1 = (n+1)*(n+1)) := by
  have := sq_succ n; constructor <;> omega

theorem from_step {m n : Nat} {f : Bool} {X : Cfg St}
    (h : Rch ⟨hg6, F ::: blank, F ::: F ::: app (CW m n f) blank⟩ X) : Rch1 (chk m n f) X :=
  Reach1.of_step_reach delta (chk_step m n f) h

/-- `m+1` prime: S moves, F := 1, M is copied; the new block has its hole at the last index. -/
theorem cyc_prime (m n : Nat) (f : Bool) (hI : Inv m n f) (hp : PrimeDvd (m+1)) :
    Rch1 (chk m n f) (chk (m+1) n true) ∧ Inv (m+1) n true := by
  obtain ⟨hn, h1, h2, hf⟩ := hI
  have hsq := sq_succ n
  have hnn : 1 ≤ n * n := Nat.mul_le_mul hn hn
  have hm : 1 ≤ m := by omega
  have hw : wraps (blocks m) = false := by
    cases h : wraps (blocks m)
    · rfl
    · exact absurd hp ((wraps_blocks m hm).1 h)
  have hns : m + 1 ≠ (n+1)*(n+1) := fun e => sq_not_prime n hn (e ▸ hp)
  obtain ⟨a, hA⟩ : ∃ a, 2*n - (m - n*n) = a + 1 := ⟨2*n - (m - n*n) - 1, by omega⟩
  have hA' : 2*n - (m + 1 - n*n) = a := by omega
  have hB' : m + 1 - n*n = (m - n*n) + 1 := by omega
  refine ⟨from_step (Rch.tr (sweep_all m n f) ?_), ⟨hn, by omega, by omega, ?_⟩⟩
  · rw [hw, hA]
    let bl := (blocks m).map stp
    let B := m - n*n
    refine Rch.tr (s_prime a B _ f) ?_
    -- home, copy M
    let w := F :: ((blkList a (B+1)).reverse ++ F :: zoneW bl m)
    have hwc : Clean3 w := by
      have hb := Clean3.revblk a (B+1) (zoneW_clean bl m).2
      show Clean3 (F :: ((blkList a (B+1)).reverse ++ F :: zoneW bl m))
      rw [blkList_reverse] at hb ⊢; exact Clean3.z1' hb
    have ew : F ::: blkR a (B+1) (F ::: pzR bl (F ::: F ::: ones (m+3) blank)) = app w (true ::: blank) := by
      simp only [w, app_cons, app_append, app_blkList_rev, app_zoneW]
    let Z' := F ::: pz bl (F ::: blk a (B+1) (F ::: true ::: blank))
    have hR : app w.reverse (true ::: blank) = true ::: ones m (true ::: (F ::: Z')) := by
      simp only [w, Z', List.reverse_cons, List.reverse_append, zoneW_rev, List.reverse_reverse,
        app_append, app_cons, app_nil, app_replicate, app_pzList, app_blkList, List.append_assoc,
        List.cons_append, List.singleton_append, List.nil_append]
      rw [show m + 2 = (m + 1) + 1 from rfl, ones_succ, ones_succ']
    rw [ew]
    refine Rch.tr (home_copy hwc _ m _ hR) ?_
    refine Rch.tr (cpy_all Z' m 1 0 2) ?_
    -- home to the next checkpoint
    let w2 := true :: F :: (List.replicate (m+1) true ++ F :: F :: List.replicate (m+2) true)
    have hw2 : Clean3 w2 := by
      refine Clean3.one (Clean3.z1' ?_)
      rw [rep_succ_T]
      exact Clean3.one (Clean3.rep_app m (Clean3.z2 (by rw [rep_succ_T]; exact Clean3.one (Clean3.rep _))))
    let R2 := F :: F :: (pzList bl ++ F :: (blkList a (B+1) ++ [F, true]))
    have e1 : (true ::: F ::: ones (1 + 0 + m) (F ::: F ::: ones (2 + m + 1) blank) : Strm) =
        app w2 (true ::: blank) := by
      simp only [w2, app_cons, app_append, app_replicate, ones_T_blank]
      rw [show 1 + 0 + m = m + 1 by omega, show 2 + m + 1 = m + 2 + 1 by omega]
    have e2 : (F ::: Z' : Strm) = app R2 blank := by
      simp only [Z', R2, app_cons, app_append, app_pzList, app_blkList, app_nil]
    rw [e1, e2]
    refine Rch.tr (home_chk hw2 R2) ?_
    have eW : true :: w2.reverse ++ R2 = CW (m+1) n true := by
      rw [CW, blocks_succ_prime m hp, hA', hB']
      simp [w2, R2, pzList, blkList, List.reverse_append, List.reverse_replicate, List.replicate_succ,
        List.append_assoc, rep_cons]
    rw [eW]; exact Reach.refl delta _
  · constructor
    · intro _; exact ⟨m+1, hp, by omega, Nat.le_refl _⟩
    · intro _; rfl

/-- `m+1` composite and not a square: S's hole moves, F unchanged. -/
theorem cyc_comp (m n : Nat) (f : Bool) (hI : Inv m n f) (hnp : ¬ PrimeDvd (m+1))
    (hns : m + 1 ≠ (n+1)*(n+1)) :
    Rch1 (chk m n f) (chk (m+1) n f) ∧ Inv (m+1) n f := by
  obtain ⟨hn, h1, h2, hf⟩ := hI
  have hsq := sq_succ n
  have hnn : 1 ≤ n * n := Nat.mul_le_mul hn hn
  have hm : 1 ≤ m := by omega
  have hw : wraps (blocks m) = true := (wraps_blocks m hm).2 hnp
  obtain ⟨a, hA⟩ : ∃ a, 2*n - (m - n*n) = a + 1 := ⟨2*n - (m - n*n) - 1, by omega⟩
  have hA' : 2*n - (m + 1 - n*n) = a := by omega
  have hB' : m + 1 - n*n = (m - n*n) + 1 := by omega
  refine ⟨from_step (Rch.tr (sweep_all m n f) ?_), ⟨hn, by omega, by omega, ?_⟩⟩
  · rw [hw, hA]
    let bl := (blocks m).map stp
    let B := m - n*n
    refine Rch.tr (s_comp a B _ f) ?_
    let w := List.replicate a true ++ true :: F :: zoneW bl m
    have hwc : Clean3 w := Clean3.rep_app a (Clean3.one (zoneW_clean bl m).2)
    let R := F :: (List.replicate (B+1) true ++ [true, F, f])
    have e1 : ones a (true ::: F ::: pzR bl (F ::: F ::: ones (m+3) blank)) = app w (true ::: blank) := by
      simp only [w, app_append, app_cons, app_replicate, app_zoneW]
    have e2 : (F ::: ones (B+1) (true ::: F ::: f ::: blank) : Strm) = app R blank := by
      simp only [R, app_cons, app_append, app_replicate, app_nil]
    rw [e1, e2]
    refine Rch.tr (home_chk hwc R) ?_
    have eW : true :: w.reverse ++ R = CW (m+1) n f := by
      rw [CW, blocks_succ_comp m hnp, hA', hB']
      simp [w, R, zoneW_rev, blkList, List.reverse_append, List.reverse_replicate, List.replicate_succ,
        List.append_assoc, rep_cons]
    rw [eW]; exact Reach.refl delta _
  · rw [hf]; constructor
    · rintro ⟨p, hp, hp1, hp2⟩; exact ⟨p, hp, hp1, by omega⟩
    · rintro ⟨p, hp, hp1, hp2⟩
      refine ⟨p, hp, hp1, ?_⟩
      rcases Nat.lt_or_ge p (m+1) with h | h
      · omega
      · obtain rfl : p = m + 1 := by omega
        exact absurd hp hnp

theorem app_FF (l : List Bool) : app (l ++ [F, F]) blank = app l blank := by
  induction l with
  | nil => simp [cons_blank]
  | cons b l ih => simp only [List.cons_append, app_cons, ih]

/-- `m+1 = (n+1)²` and F = 1: S grows by two, F is cleared. -/
theorem cyc_square (m n : Nat) (hI : Inv m n true) (hsq' : m + 1 = (n+1)*(n+1)) :
    Rch1 (chk m n true) (chk (m+1) (n+1) false) ∧ Inv (m+1) (n+1) false := by
  obtain ⟨hn, h1, h2, hf⟩ := hI
  have hsq := sq_succ n
  have hsq2 := sq_succ (n+1)
  have hnn : 1 ≤ n * n := Nat.mul_le_mul hn hn
  have hm : 1 ≤ m := by omega
  have hnp := sq_not_prime n hn
  rw [← hsq'] at hnp
  have hw : wraps (blocks m) = true := (wraps_blocks m hm).2 hnp
  have hA : 2*n - (m - n*n) = 0 := by omega
  have hA' : 2*(n+1) - (m + 1 - (n+1)*(n+1)) = 2*n + 2 := by omega
  have hB' : m + 1 - (n+1)*(n+1) = 0 := by omega
  have hB : m - n*n = 2*n := by omega
  refine ⟨from_step (Rch.tr (sweep_all m n true) ?_), ⟨by omega, by omega, by omega, ?_⟩⟩
  · rw [hw, hA]
    let bl := (blocks m).map stp
    refine Rch.tr (s_square _ _) ?_
    let w := F :: (List.replicate (m - n*n + 3) true ++ F :: zoneW bl m)
    have hwc : Clean3 w := by
      refine Clean3.z1' ?_
      exact Clean3.one (Clean3.rep_app _ (zoneW_clean bl m).2)
    have e1 : (F ::: ones (m - n*n + 3) (F ::: pzR bl (F ::: F ::: ones (m+3) blank)) : Strm) =
        app w (true ::: blank) := by
      simp only [w, app_append, app_cons, app_replicate, app_zoneW]
    have e2 : (true ::: blank : Strm) = app [true] blank := rfl
    rw [e1, e2]
    refine Rch.tr (home_chk hwc [true]) ?_
    have eW : CW (m+1) (n+1) false = (true :: w.reverse ++ [true]) ++ [F, F] := by
      rw [CW, blocks_succ_comp m hnp, hA', hB']
      simp [w, hB, zoneW_rev, blkList, List.reverse_append, List.reverse_replicate, List.replicate_succ,
        List.append_assoc, rep_cons]
    unfold chk; rw [eW]; unfold chkW; rw [app_FF]; exact Reach.refl delta _
  · constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨p, _, hp1, hp2⟩; omega

/-- `m+1 = (n+1)²` and F = 0: no prime in `(n², (n+1)²)`, the machine halts. -/
theorem cyc_halt (m n : Nat) (hI : Inv m n false) (hsq' : m + 1 = (n+1)*(n+1)) :
    HaltAt (chk m n false) := by
  obtain ⟨hn, h1, h2, hf⟩ := hI
  have hsq := sq_succ n
  have hnn : 1 ≤ n * n := Nat.mul_le_mul hn hn
  have hm : 1 ≤ m := by omega
  have hnp := sq_not_prime n hn
  rw [← hsq'] at hnp
  have hw : wraps (blocks m) = true := (wraps_blocks m hm).2 hnp
  have hA : 2*n - (m - n*n) = 0 := by omega
  have hr : Rch (chk m n false) ⟨q3, pzR ((blocks m).map stp) (F ::: F ::: ones (m+3) blank),
      F ::: blk 0 (m - n*n) (F ::: false ::: blank)⟩ :=
    (from_step (Rch.tr (sweep_all m n false) (by rw [hw, hA]; exact Reach.refl delta _))).reach
  exact HaltAt.back hr (s_halt _ _)

end TM.LegendreSieve
