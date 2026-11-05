import TinyCryptids.BrocardPrimes.Copy
import TinyCryptids.BrocardPrimes.Scan
namespace TM.BrocardPrimes
open St

/-! # The tape as a list of cells, and the sweep from a checkpoint -/

def blkList (a b : Nat) : List Bool :=
  true :: (List.replicate a true ++ F :: (List.replicate b true ++ [true]))

def pzList : List (Nat × Nat) → List Bool
  | [] => []
  | (a, b) :: l => blkList a b ++ F :: F :: pzList l

def pzRList : List (Nat × Nat) → List Bool
  | [] => []
  | (a, b) :: l => pzRList l ++ F :: F :: (blkList a b).reverse

theorem rep_snoc (n : Nat) : List.replicate n true ++ [true] = true :: List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

theorem rep_cons (n : Nat) (r : List Bool) :
    List.replicate n true ++ true :: r = true :: (List.replicate n true ++ r) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

theorem rep_succ_T (k : Nat) : List.replicate (k+1) true = true :: List.replicate k true := rfl

theorem blkList_reverse (a b : Nat) :
    (blkList a b).reverse = true :: (List.replicate b true ++ F :: (List.replicate a true ++ [true])) := by
  simp [blkList, List.reverse_append, List.reverse_replicate, rep_snoc]

theorem app_blkList (a b : Nat) (s : Strm) : app (blkList a b) s = blk a b s := by
  simp [blkList, blk, app_append, app_replicate]

theorem app_blkList_rev (a b : Nat) (L : Strm) : app (blkList a b).reverse L = blkR a b L := by
  rw [blkList_reverse]; simp [blkR, app_append, app_replicate]

theorem app_pzList (l : List (Nat × Nat)) (s : Strm) : app (pzList l) s = pz l s := by
  induction l with
  | nil => rfl
  | cons x l ih => obtain ⟨a, b⟩ := x; simp [pzList, pz, app_append, app_blkList, ih]

theorem app_pzRList (l : List (Nat × Nat)) (L : Strm) : app (pzRList l) L = pzR l L := by
  induction l generalizing L with
  | nil => rfl
  | cons x l ih => obtain ⟨a, b⟩ := x; simp [pzRList, pzR, app_append, app_blkList_rev, ih]

theorem pzRList_reverse (l : List (Nat × Nat)) : (pzRList l).reverse = pzList l := by
  induction l with
  | nil => rfl
  | cons x l ih => obtain ⟨a, b⟩ := x; simp [pzRList, pzList, List.reverse_append, ih]

theorem pzR_snoc (l : List (Nat × Nat)) (a b : Nat) (L : Strm) :
    pzR (l ++ [(a, b)]) L = F ::: F ::: blkR a b (pzR l L) := by
  induction l generalizing L with
  | nil => rfl
  | cons x l ih => obtain ⟨c, d⟩ := x; simp only [List.cons_append, pzR]; exact ih _

theorem pzList_append (l l' : List (Nat × Nat)) : pzList (l ++ l') = pzList l ++ pzList l' := by
  induction l with
  | nil => rfl
  | cons x l ih => obtain ⟨a, b⟩ := x; simp [pzList, ih]

theorem app_FF (l : List Bool) : app (l ++ [F, F]) blank = app l blank := by
  induction l with
  | nil => simp [cons_blank]
  | cons b l ih => simp only [List.cons_append, app_cons, ih]

/-! ## `Clean3` facts -/

theorem Clean3.rep_app (n : Nat) {l : List Bool} (h : Clean3 l) : Clean3 (List.replicate n true ++ l) :=
  (Clean3.rep n).append h

theorem Clean3.revblk (a b : Nat) {r : List Bool} (h : Clean3 r) : Clean3 ((blkList a b).reverse ++ r) := by
  rw [blkList_reverse]
  simp only [List.cons_append, List.append_assoc, List.singleton_append, rep_cons]
  exact Clean3.one (Clean3.rep_app b (Clean3.z1 (Clean3.rep_app a h)))

theorem Clean3.blk (a b : Nat) {r : List Bool} (h : Clean3 r) : Clean3 (blkList a b ++ r) := by
  simp only [blkList, List.cons_append, List.append_assoc, List.singleton_append]
  refine Clean3.one (Clean3.rep_app a ?_)
  rw [rep_cons]; exact Clean3.z1 (Clean3.rep_app b h)

theorem Clean3.z1' {l : List Bool} (h : Clean3 (true :: l)) : Clean3 (F :: true :: l) := by
  cases h with | one h => exact Clean3.z1 h

theorem Clean3.z2' {l : List Bool} (h : Clean3 (true :: l)) : Clean3 (F :: F :: true :: l) := by
  cases h with | one h => exact Clean3.z2 h

theorem Clean3.z3' {l : List Bool} (h : Clean3 (true :: l)) : Clean3 (F :: F :: F :: true :: l) := by
  cases h with | one h => exact Clean3.z3 h

/-- a processed zone followed by `00` and a 1: clean, also with one or two more 0s in front -/
theorem Clean3.pzR (l : List (Nat × Nat)) : ∀ r : List Bool, Clean3 r →
    Clean3 (pzRList l ++ F :: F :: true :: r) ∧ Clean3 (F :: (pzRList l ++ F :: F :: true :: r)) := by
  induction l with
  | nil => intro r h; exact ⟨Clean3.z2 h, Clean3.z3 h⟩
  | cons x l ih =>
    intro r h
    obtain ⟨a, b⟩ := x
    have hb := Clean3.revblk a b (Clean3.z2 h)
    rw [blkList_reverse] at hb
    simp only [List.cons_append] at hb
    cases hb with
    | one hb' =>
      have := ih _ hb'
      simp only [pzRList, List.append_assoc, List.cons_append, blkList_reverse] at this ⊢
      exact this

theorem Clean3.zz {l : List Bool} (h : Clean3 l) (hl : l.head? = some true) : Clean3 (F :: F :: l) := by
  cases h with
  | one h => exact Clean3.z2 h
  | _ => simp at hl

/-- a zone written rightwards, then `00` and a 1 -/
theorem Clean3.pz (l : List (Nat × Nat)) : ∀ r : List Bool, Clean3 (true :: r) →
    Clean3 (pzList l ++ true :: r) := by
  induction l with
  | nil => intro r h; exact h
  | cons x l ih =>
    intro r h
    obtain ⟨a, b⟩ := x
    simp only [pzList, List.append_assoc, List.cons_append]
    refine Clean3.blk a b ?_
    refine Clean3.zz (ih r h) ?_
    rcases l with _ | ⟨⟨c, d⟩, l⟩
    · rfl
    · simp [pzList, blkList]

/-! ## Checkpoints

At checkpoint `m` (with `n = isqrt m`, a counter `1^(c+1)`):

    M 00 [blocks above the marker] 1 00 [blocks below] 0 S 0 1^(c+1)
-/

noncomputable def upB (m n : Nat) : List (Nat × Nat) := (up m n).map (pb m)
noncomputable def loB (m n : Nat) : List (Nat × Nat) := (lo m n).map (pb m)

/-- the S block: region `2n+1`, hole at index `2n - (m - n^2)` -/
def sx (m n : Nat) : Nat := 2*n - (m - n*n)
def sy (m n : Nat) : Nat := m - n*n

def tailW (c x y : Nat) : List Bool :=
  F :: (blkList x y ++ F :: List.replicate (c+1) true)

noncomputable def CW (m n c : Nat) : List Bool :=
  List.replicate (m+2) true ++ F :: F :: (pzList (upB m n) ++ true :: F :: F ::
    (pzList (loB m n) ++ tailW c (sx m n) (sy m n)))

noncomputable def chk (m n c : Nat) : Cfg St := chkW (CW m n c)

def tailS (c x y : Nat) : Strm := F ::: blk x y (F ::: ones (c+1) blank)

theorem app_tailW (c x y : Nat) : app (tailW c x y) blank = tailS c x y := by
  simp [tailW, tailS, app_append, app_replicate, app_blkList]

theorem app_CW (m n c : Nat) :
    app (CW m n c) blank = ones (m+2) (F ::: F ::: pz (upB m n) (true ::: F ::: F :::
      pz (loB m n) (tailS c (sx m n) (sy m n)))) := by
  simp [CW, app_append, app_replicate, app_pzList, app_tailW]

theorem chk_step (m n c : Nat) :
    step delta (chk m n c) = some ⟨hg6, F ::: blank, F ::: F ::: app (CW m n c) blank⟩ := rfl

/-- the marker is crossed like a separator -/
theorem marker_cross (c : Bool) (L R : Strm) :
    Rch ⟨S3 c, L, true ::: F ::: F ::: R⟩ ⟨S3 c, F ::: F ::: true ::: L, R⟩ := by
  cases c <;> (gR; gR; gR; fin)

/-- the left part of the tape after the sweep -/
noncomputable def leftS (m n : Nat) : Strm :=
  pzR ((loB m n).map stp) (F ::: F ::: true ::: pzR ((upB m n).map stp) (F ::: F ::: ones (m+3) blank))

/-- grow M, then sweep both zones; the mode records whether some prime divides m+1 -/
theorem sweep_all (m n c : Nat) :
    Rch ⟨hg6, F ::: blank, F ::: F ::: app (CW m n c) blank⟩
      ⟨S3 (wraps (upB m n) || wraps (loB m n)), leftS m n, tailS c (sx m n) (sy m n)⟩ := by
  rw [app_CW]
  gR; gR; sRn (m+2); gR; gR
  simp only [cons_blank]; rw [← ones_succ']
  have h1 := zone (upB m n) false (ones (m+3) blank)
    (true ::: F ::: F ::: pz (loB m n) (tailS c (sx m n) (sy m n)))
  simp only [Bool.false_or] at h1
  refine Rch.tr h1 ?_
  refine Rch.tr (marker_cross _ _ _) ?_
  have h2 := zone (loB m n) (wraps (upB m n))
    (true ::: pzR ((upB m n).map stp) (F ::: F ::: ones (m+3) blank)) (tailS c (sx m n) (sy m n))
  exact h2

end TM.BrocardPrimes
