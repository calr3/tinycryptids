import TinyCryptids.Singmaster.Tape

/-!
# Comparing one entry with N

Left of the head, between N and the entry E, is a word `D` (the triangle so far and E's
separator).  The tape around the comparison:

    C 0 N D E Y        C = Cw c, N = Nw a b (hole at cell a), E with a hole at cell r

E's cursor moves right, N's cursor moves left, in lockstep (`round`).
-/

namespace TM.Singmaster
open St TinyCryptids

local notation "F" => false
local notation "T" => true
local notation "rep" => List.replicate

/-- C with `c` matches: hole at cell `c + 1` of 9 cells -/
def Cw (c : Nat) : List Bool := rep (c + 1) T ++ F :: rep (7 - c) T
/-- left of N, nearest first: the separator, then C -/
def XL (c : Nat) : List Bool := F :: (Cw c).reverse
/-- N with its hole at cell `a` -/
def Nw (a b : Nat) : List Bool := rep a T ++ F :: rep b T

theorem Nw_rev (a b : Nat) : (Nw a b).reverse = rep b T ++ F :: rep a T := by
  simp [Nw, List.reverse_replicate]

/-- what the finders need of `D` -/
def DOK (D : List Bool) : Prop :=
  (∀ l, GC l → GC (D ++ T :: l)) ∧ (∀ l, GC l → GC (D.reverse ++ T :: l))

theorem GC.rep (n : Nat) {l : List Bool} (h : GC l) : GC (rep n T ++ l) :=
  GC.append (GC.replicate n) h

/-- a round in progress: E's hole at `r`, the head on the cell after it -/
def rnd (D : List Bool) (c e r a b : Nat) (Y : List Bool) : Cfg St :=
  cl eZ1 (F :: rep r T ++ D.reverse ++ (Nw a b).reverse ++ XL c) (rep (e + 1 - r) T ++ Y)

theorem round (D : List Bool) (hD : DOK D) (c e r a b : Nat) (Y : List Bool)
    (h1 : 1 ≤ r) (h2 : r + 1 ≤ e) (h3 : 2 ≤ a) (hb : 1 ≤ b) :
    Rch (rnd D c e r a b Y) (rnd D c e (r + 1) (a - 1) (b + 1) Y) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = r + 1 + k := ⟨e - r - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  unfold rnd
  rw [show r' + 1 + 1 + k + 1 - (r' + 1) = k + 2 by omega,
    show r' + 1 + 1 + k + 1 - (r' + 1 + 1) = k + 1 by omega, Nw_rev, Nw_rev,
    show a' + 2 - 1 = a' + 1 by omega]
  simp only [List.replicate_succ, List.cons_append, List.append_assoc]
  gr; gl; gl; gl
  -- left finder from E to N's hole
  have hw : GC (T :: rep r' T ++ D.reverse ++ rep (b' + 1) T) := by
    simpa [List.replicate_succ, List.append_assoc] using GC.one (GC.rep r' (hD.2 _ (GC.replicate b')))
  have e1 : cl nP (rep r' T ++ (D.reverse ++ (T :: (rep b' T ++ F :: T :: T :: (rep a' T ++ XL c)))))
      (T :: T :: F :: T :: (rep k T ++ Y)) =
      cL nP ((T :: rep r' T ++ D.reverse ++ rep (b' + 1) T) ++ (F :: T :: T :: (rep a' T ++ XL c)))
        (T :: F :: T :: (rep k T ++ Y)) := by
    simp [cL, cl, cfgL, app_append, List.replicate_succ]
  rw [e1]
  refine Rch.tr (fl_cross FN_ hw _ _) ?_
  show Rch (cl nP (T :: T :: (rep a' T ++ XL c)) (F :: _)) _
  gl; gl; gr; gr; gr
  have hw2 : GC (rep (b' + 1) T ++ D ++ T :: rep (r' + 1) T) := by
    rw [List.append_assoc]; exact GC.rep _ (hD.1 _ (GC.replicate _))
  have e2 : (T :: rep r' T ++ D.reverse ++ rep (b' + 1) T).reverse ++ T :: F :: T :: (rep k T ++ Y) =
      (rep (b' + 1) T ++ D ++ T :: rep (r' + 1) T) ++ F :: T :: (rep k T ++ Y) := by
    simp [List.reverse_replicate, List.replicate_succ]
    done
  rw [e2]
  refine Rch.tr (fr_cross FE_ hw2 _ _) ?_
  gr
  have e3 : (rep (b' + 1) T ++ D ++ T :: rep (r' + 1) T).reverse = T :: T :: rep r' T ++ D.reverse ++ rep (b' + 1) T := by
    simp [List.reverse_replicate, List.replicate_succ]
    done
  rw [e3]
  lfin

/-- after the comparison: on the first cell after E -/
def post (D : List Bool) (c N e : Nat) (Y : List Bool) : Cfg St :=
  cl FE2 (rep (e + 2) T ++ D.reverse ++ (Nw N 1).reverse ++ XL c) Y

/-- N's cursor back to cell N, then E's hole filled and on to E's end -/
theorem tail (D0 : List Bool) (hD : DOK (F :: D0)) (c e r a b : Nat) (Y : List Bool)
    (h1 : 1 ≤ r) (h2 : r ≤ e) (hb : 1 ≤ b) :
    Rch (cl T0 (rep a T ++ XL c) (F :: rep b T ++ (F :: D0) ++ rep r T ++ F :: rep (e + 1 - r) T ++ F :: Y))
      (post (F :: D0) c (a + b - 1) e (F :: Y)) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  gr; norm
  refine Rch.tr (srn (q := T1) rfl (b' + 1) _ _) ?_
  simp only [List.replicate_succ, List.cons_append, List.append_assoc, rep_cons']
  gl; gl; gr
  have hw : GC (T :: (F :: D0 ++ T :: rep r' T)) := GC.one (hD.1 _ (GC.replicate r'))
  refine Rch.tr (fr_cross' FF_ hw _ (F :: rep (e + 1 - (r' + 1)) T ++ F :: Y) (by norm)) ?_
  rw [show e + 1 - (r' + 1) = (e - r' - 1) + 1 by omega]
  gr; simp only [List.replicate_succ, List.append_eq, List.cons_append]; gl; gr
  rw [← List.cons_append, ← List.replicate_succ]
  refine Rch.tr (srn (q := FE2) rfl (e - r' - 1 + 1) _ _) ?_
  unfold post
  rw [show a + (b' + 1) - 1 = a + b' by omega, Nw_rev, show e + 2 = (e - r' - 1 + 1) + 1 + (r' + 1) by omega]
  simp only [← List.append_replicate_replicate]
  lfin
  rw [Nat.add_comm b' a]; fin

theorem rounds (D : List Bool) (hD : DOK D) (c e N : Nat) (Y : List Bool) :
    ∀ k, 1 + k ≤ e → 1 + k ≤ N → Rch (rnd D c e 1 N 1 Y) (rnd D c e (1 + k) (N - k) (1 + k) Y)
  | 0, _, _ => Reach.refl delta _
  | k + 1, h1, h2 => by
    refine Rch.tr (rounds D hD c e N Y k (by omega) (by omega)) ?_
    have := round D hD c e (1 + k) (N - k) (1 + k) Y (by omega) (by omega) (by omega) (by omega)
    rwa [show N - k - 1 = N - (k + 1) by omega, show 1 + k + 1 = 1 + (k + 1) by omega] at this

theorem cmp_start (D : List Bool) (c e N : Nat) (Y : List Bool) :
    Rch (cl X5 (T :: D.reverse ++ (Nw N 1).reverse ++ XL c) (rep (e + 1) T ++ Y)) (rnd D c e 1 N 1 Y) := by
  simp only [List.replicate_succ, List.cons_append]
  gr; unfold rnd; lfin

/-- N's cursor exhausted first: E > N -/
theorem n_exh (D0 : List Bool) (hD : DOK (F :: D0)) (c e r b : Nat) (Y : List Bool)
    (h1 : 1 ≤ r) (h2 : r + 1 ≤ e) (hb : 1 ≤ b) :
    Rch (rnd (F :: D0) c e r 1 b (F :: Y)) (post (F :: D0) c b e (F :: Y)) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = r + 1 + k := ⟨e - r - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  unfold rnd
  rw [show r' + 1 + 1 + k + 1 - (r' + 1) = k + 2 by omega, Nw_rev]
  simp only [List.replicate_succ, List.cons_append, List.append_assoc, List.reverse_cons]
  gr; gl; gl; gl
  have hw : GC (T :: rep r' T ++ ((F :: D0).reverse ++ T :: rep b' T)) :=
    GC.one (GC.rep _ (hD.2 _ (GC.replicate _)))
  refine Rch.tr (fl_cross' FN_ hw (F :: T :: XL c) _ (by lfin)) ?_
  rw [← cl_cL]
  unfold XL
  gl; gl; gr; gr
  have := tail D0 hD c (r' + 1 + 1 + k) (r' + 2) 1 (b' + 1) Y (by omega) (by omega) (by omega)
  rw [show 1 + (b' + 1) - 1 = b' + 1 by omega, show r' + 1 + 1 + k + 1 - (r' + 2) = k + 1 by omega] at this
  refine Rch.tr ?_ this
  unfold XL
  lfin

/-- E's cursor exhausted: to N's hole in "done" mode -/
theorem e_exh_to (D0 : List Bool) (hD : DOK (F :: D0)) (c e a b : Nat) (Y : List Bool)
    (he : 1 ≤ e) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Rch (rnd (F :: D0) c e e a b (F :: Y))
      (cL Bd (rep (a - 1) T ++ XL c) (T :: F :: rep b T ++ (F :: D0) ++ rep e T ++ F :: T :: F :: Y)) := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  unfold rnd
  rw [show e' + 1 + 1 - (e' + 1) = 1 by omega, Nw_rev]
  simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
    List.append_assoc, List.reverse_cons]
  gr; gl; gl; gl
  have hw : GC (T :: rep e' T ++ ((F :: D0).reverse ++ T :: rep b' T)) :=
    GC.one (GC.rep _ (hD.2 _ (GC.replicate _)))
  refine Rch.tr (fl_cross' FD_ hw (F :: T :: (rep a' T ++ XL c)) _ (by lfin)) ?_
  rw [← cl_cL]
  gl; glc
  rw [show a' + 1 - 1 = a' by omega]
  lfin

/-- E exhausted, N's cursor not at cell 1: E < N -/
theorem e_exh_lt (D0 : List Bool) (hD : DOK (F :: D0)) (c e a b : Nat) (Y : List Bool)
    (he : 1 ≤ e) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    Rch (rnd (F :: D0) c e e a b (F :: Y)) (post (F :: D0) c (a + b - 1) e (F :: Y)) := by
  refine Rch.tr (e_exh_to D0 hD c e a b Y he (by omega) hb) ?_
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
  rw [show a' + 2 - 1 = a' + 1 by omega, List.replicate_succ, List.cons_append, ← cl_cL]
  gr; gr
  have := tail D0 hD c e e (a' + 2) b Y he (Nat.le_refl _) hb
  rw [show e + 1 - e = 1 by omega] at this
  refine Rch.tr ?_ this
  lfin

/-- E exhausted with N's cursor at cell 1: a match, C += 1 -/
theorem e_exh_eq (D0 : List Bool) (hD : DOK (F :: D0)) (c e b : Nat) (Y : List Bool)
    (he : 1 ≤ e) (hb : 1 ≤ b) (hc : c < 6) :
    Rch (rnd (F :: D0) c e e 1 b (F :: Y)) (post (F :: D0) (c + 1) b e (F :: Y)) := by
  refine Rch.tr (e_exh_to D0 hD c e 1 b Y he (Nat.le_refl _) hb) ?_
  obtain ⟨j, hj⟩ : ∃ j, 7 - c = j + 2 := ⟨5 - c, by omega⟩
  simp only [Nat.sub_self, List.replicate_zero, List.nil_append, XL, Cw, List.reverse_append,
    List.reverse_cons, List.reverse_replicate, hj]
  rw [← cl_cL, List.replicate_succ, List.cons_append]
  gl
  rw [cl_cL]
  refine Rch.tr (sln' (q := CW) rfl (j + 2) (F :: rep (c + 1) T) _ (by lfin)) ?_
  rw [← cl_cL]
  simp only [List.replicate_succ, List.cons_append]
  gr; gr; gl; gr
  refine Rch.tr (srn' (q := CR) rfl (j + 1) _ _ rfl) ?_
  gr; gr
  have := tail D0 hD (c + 1) e e 1 b Y he (Nat.le_refl _) hb
  rw [show e + 1 - e = 1 by omega, show 1 + b - 1 = b by omega] at this
  refine Rch.tr ?_ this
  simp only [XL, Cw, show 7 - (c + 1) = j + 1 by omega]
  lfin

theorem e_exh_halt (D0 : List Bool) (hD : DOK (F :: D0)) (e b : Nat) (Y : List Bool)
    (he : 1 ≤ e) (hb : 1 ≤ b) :
    HaltAt (rnd (F :: D0) 6 e e 1 b (F :: Y)) := by
  refine HaltAt.back (e_exh_to D0 hD 6 e 1 b Y he (Nat.le_refl _) hb) ?_
  simp only [Nat.sub_self, List.replicate_zero, List.nil_append, XL, Cw, List.reverse_append,
    List.reverse_cons, List.reverse_replicate]
  rw [← cl_cL]
  rw [show rep (7 - 6) T = [T] from rfl]
  simp only [List.cons_append, List.nil_append, List.singleton_append]
  hl; hl; hr; hr; hr
  exact ⟨_, _, Reach.refl delta _⟩

/-- on cell 1 of the entry E, about to compare it with N -/
def atE (D : List Bool) (c N e : Nat) (Y : List Bool) : Cfg St :=
  cl X5 (T :: D.reverse ++ (Nw N 1).reverse ++ XL c) (rep (e + 1) T ++ Y)

theorem cmp_ne (D0 : List Bool) (hD : DOK (F :: D0)) (c N e : Nat) (Y : List Bool)
    (hN : 1 ≤ N) (he : 1 ≤ e) (hne : e ≠ N) :
    Rch (atE (F :: D0) c N e (F :: Y)) (post (F :: D0) c N e (F :: Y)) := by
  refine Rch.tr (cmp_start _ c e N _) ?_
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · refine Rch.tr (rounds _ hD c e N _ (e - 1) (by omega) (by omega)) ?_
    have := e_exh_lt D0 hD c e (N - (e - 1)) (1 + (e - 1)) Y he (by omega) (by omega)
    rw [show 1 + (e - 1) = e by omega] at this ⊢
    rwa [show N - (e - 1) + e - 1 = N by omega] at this
  · refine Rch.tr (rounds _ hD c e N _ (N - 1) (by omega) (by omega)) ?_
    have := n_exh D0 hD c e (1 + (N - 1)) (1 + (N - 1)) Y (by omega) (by omega) (by omega)
    rw [show N - (N - 1) = 1 by omega]
    rwa [show 1 + (N - 1) = N by omega] at this ⊢

theorem cmp_eq (D0 : List Bool) (hD : DOK (F :: D0)) (c N : Nat) (Y : List Bool)
    (hN : 1 ≤ N) (hc : c < 6) :
    Rch (atE (F :: D0) c N N (F :: Y)) (post (F :: D0) (c + 1) N N (F :: Y)) := by
  refine Rch.tr (cmp_start _ c N N _) ?_
  refine Rch.tr (rounds _ hD c N N _ (N - 1) (by omega) (by omega)) ?_
  have := e_exh_eq D0 hD c N (1 + (N - 1)) Y hN (by omega) hc
  rw [show N - (N - 1) = 1 by omega, show 1 + (N - 1) = N by omega] at *
  exact this

theorem cmp_halt (D0 : List Bool) (hD : DOK (F :: D0)) (N : Nat) (Y : List Bool) (hN : 1 ≤ N) :
    HaltAt (atE (F :: D0) 6 N N (F :: Y)) := by
  refine HaltAt.back (cmp_start _ 6 N N _) ?_
  refine HaltAt.back (rounds _ hD 6 N N _ (N - 1) (by omega) (by omega)) ?_
  have := e_exh_halt D0 hD N (1 + (N - 1)) Y hN (by omega)
  rw [show N - (N - 1) = 1 by omega, show 1 + (N - 1) = N by omega] at *
  exact this

end TM.Singmaster
