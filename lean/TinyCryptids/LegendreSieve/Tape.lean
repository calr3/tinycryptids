import TinyCryptids.LegendreSieve.Copy
import TinyCryptids.LegendreSieve.Math
namespace TM.LegendreSieve
open St

/-! ## The tape as a list of cells -/

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

/-! ## `Clean3` for the words crossed on the way home -/

theorem Clean3.rep_app (n : Nat) {l : List Bool} (h : Clean3 l) : Clean3 (List.replicate n true ++ l) :=
  (Clean3.rep n).append h

theorem rep_cons (n : Nat) (r : List Bool) :
    List.replicate n true ++ true :: r = true :: (List.replicate n true ++ r) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

theorem Clean3.revblk (a b : Nat) {r : List Bool} (h : Clean3 r) : Clean3 ((blkList a b).reverse ++ r) := by
  rw [blkList_reverse]
  simp only [List.cons_append, List.append_assoc, List.singleton_append, rep_cons]
  exact Clean3.one (Clean3.rep_app b (Clean3.z1 (Clean3.rep_app a h)))

/-- The processed P zone followed by `00` and a 1: clean, also with one more 0 in front. -/
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

/-! ## Checkpoints -/

/-- The tape at checkpoint `m` (with `n*n ≤ m < (n+1)*(n+1)` and F-bit `f`). -/
noncomputable def CW (m n : Nat) (f : Bool) : List Bool :=
  List.replicate (m+2) true ++ F :: F :: (pzList (blocks m) ++
    F :: (blkList (2*n - (m - n*n)) (m - n*n) ++ [F, f]))

noncomputable def chk (m n : Nat) (f : Bool) : Cfg St := chkW (CW m n f)

theorem app_CW (m n : Nat) (f : Bool) :
    app (CW m n f) blank = ones (m+2) (F ::: F ::: pz (blocks m)
      (F ::: blk (2*n - (m - n*n)) (m - n*n) (F ::: f ::: blank))) := by
  simp [CW, app_append, app_replicate, app_pzList, app_blkList]

theorem chk_step (m n : Nat) (f : Bool) :
    step delta (chk m n f) = some ⟨hg6, F ::: blank, F ::: F ::: app (CW m n f) blank⟩ := rfl

/-- grow M, then sweep the P zone; the mode records whether some prime divides m+1 -/
theorem sweep_all (m n : Nat) (f : Bool) :
    Rch ⟨hg6, F ::: blank, F ::: F ::: app (CW m n f) blank⟩
      ⟨S3 (wraps (blocks m)), pzR ((blocks m).map stp) (F ::: F ::: ones (m+3) blank),
        F ::: blk (2*n - (m - n*n)) (m - n*n) (F ::: f ::: blank)⟩ := by
  rw [app_CW]
  gR; gR; sRn (m+2); gR; gR
  simp only [cons_blank]; rw [← ones_succ']
  have := zone (blocks m) false (ones (m+3) blank)
    (F ::: blk (2*n - (m - n*n)) (m - n*n) (F ::: f ::: blank))
  simp only [Bool.false_or] at this
  exact this

end TM.LegendreSieve
