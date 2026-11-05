import TinyCryptids.LehmerTau.Walk
import TinyCryptids.LehmerTau.Trip

/-!
# The odometer (the "run")

Right of S0 lie the var digits: a block of `f + 2` cells, position `p < f`: no hole for
`p = 0`, a hole at cell `p + 1` otherwise. Left of S0 lie blocks that are either plain (no
hole) or active K digits: `f + 2` cells with a hole at cell `c`, position `c − 1`.

The run counts through all tuples of positions, the last var digit fastest, then the other var
digits, then the K digits right to left; each count adds a cell to the leftmost block (the
accumulator). This file has the single steps: advance or wrap a var digit, pass S0, advance or
wrap a K digit.
-/

namespace TM.LehmerTau
open St

local notation "F" => false

/-! ## var digits -/

/-- position `p ≥ 1`, not the last: the hole moves right; the head ends left of it, in `AL1` -/
theorem v_adv (G Rr : Strm) (f p : Nat) (hf : p + 1 < f) :
    Rch ⟨CA, ones (f - p - 1) (F ::: ones (p + 1) G), true ::: Rr⟩
      ⟨AL1, ones (p + 1) G, true ::: F ::: ones (f - p - 1) Rr⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, f = p + 2 + k := ⟨f - p - 2, by omega⟩
  rw [show p + 2 + k - p - 1 = k + 1 by omega]
  gL; gL; sLn k; gL; gR; gR
  rw [ones_cons_true]; gL
  rw [ones_succ' k Rr]; fin

/-- position 0 (no hole), `f ≥ 2`: the hole goes to cell 2 -/
theorem v_adv0 (G Rr : Strm) (f : Nat) (hf : 2 ≤ f) :
    Rch ⟨CA, ones (f + 1) (F ::: F ::: G), true ::: Rr⟩
      ⟨AL1, ones 1 (F ::: F ::: G), true ::: F ::: ones (f - 1) Rr⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 2 := ⟨f - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega]
  gL; gL; sLn (k + 2); gL; gR; gR; gR; gR
  rw [ones_cons_true]; gR
  rw [ones_cons_true]; gL; gL; fin

/-- the last position (hole at cell `f`, `f ≥ 2`): no hole; the head goes to the previous
block's last cell -/
theorem v_wrap (G Rr : Strm) (f : Nat) :
    Rch ⟨CA, F ::: ones f (F ::: F ::: G), true ::: Rr⟩ (cfgL CA G (F ::: F ::: ones (f + 2) Rr)) := by
  gL; gL; sLn f; gL; gL
  rw [ones_succ', ones_succ']; fin

/-- factor 1 (always position 0): wrap -/
theorem v_wrap1 (G Rr : Strm) :
    Rch ⟨CA, ones 2 (F ::: F ::: G), true ::: F ::: Rr⟩ (cfgL CA G (F ::: F ::: ones 3 (F ::: Rr))) := by
  gL; gL; gL; gL; gR; gR; gR; gR; gR; gL; sLn 3; gL; gL; fin

/-- S0 reached: on to the K digits -/
theorem v_s0 (G R : Strm) :
    Rch (cfgL CA (true ::: true ::: F ::: F ::: G) (F ::: R))
      (cfgL KF1 (true ::: true ::: F ::: F ::: G) (F ::: R)) := by
  gL; gL; gL; gR; gR; gR; gR; gL; fin

/-! ## K digits -/

theorem HKF : HoleL delta KF1 KF2 KF3 := ⟨rfl, rfl, rfl, rfl⟩

/-- found the hole at cell `c < f`: it moves right -/
theorem k_adv (G Rr : Strm) (f c : Nat) (hc : 1 ≤ c) (hcf : c < f) :
    Rch (cfgL KF2 (ones c (F ::: F ::: G)) (F ::: ones (f + 1 - c) Rr))
      ⟨AL1, ones (c - 1) (F ::: F ::: G), true ::: true ::: F ::: ones (f - c) Rr⟩ := by
  obtain ⟨b, rfl⟩ : ∃ b, c = b + 1 := ⟨c - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, f = b + 2 + k := ⟨f - b - 2, by omega⟩
  rw [show b + 2 + k + 1 - (b + 1) = k + 2 by omega, show b + 2 + k - (b + 1) = k + 1 by omega,
    show b + 1 - 1 = b by omega]
  gR; gR; gR; gL; gL; gL; fin

/-- found the hole at the last cell `f`: back to cell 1, on to the next digit -/
theorem k_wrap (G Rr : Strm) (f : Nat) (hf : 1 ≤ f) :
    Rch (cfgL KF2 (ones f (F ::: F ::: G)) (F ::: ones 1 (F ::: Rr)))
      (cfgL KF1 (F ::: F ::: G) (true ::: F ::: ones f (F ::: Rr))) := by
  obtain ⟨b, rfl⟩ : ∃ b, f = b + 1 := ⟨f - 1, by omega⟩
  gR; gR; gR; gL; gL; gL; sLn (b + 1); gR; gR
  rw [ones_cons_true]; gL; gL
  rw [ones_succ' b]; fin

/-! ## the tape during a run -/

def rep (n : Nat) : List Bool := List.replicate n true

/-- a block left of S0: plain (`n` cells) or an active K digit (`f + 2` cells, hole at `c`) -/
inductive KB
  | pl (n : Nat)
  | dg (f c : Nat)

def KB.w : KB → List Bool
  | .pl n => rep n
  | .dg f c => rep c ++ F :: rep (f + 1 - c)

def KB.ok : KB → Prop
  | .pl n => 1 ≤ n
  | .dg f c => 1 ≤ c ∧ c ≤ f

/-- the blocks left of S0, read leftward from the one next to S0, each followed by its
separator -/
def lpR : List KB → List Bool
  | [] => []
  | b :: l => b.w.reverse ++ F :: F :: lpR l

/-- a var digit's block without its last cell -/
def vwi (f p : Nat) : List Bool := if p = 0 then rep (f + 1) else rep (p + 1) ++ F :: rep (f - p - 1)

/-- var digits left to right (each with its separator in front) -/
def vp : List (Nat × Nat) → List Bool
  | [] => []
  | (f, p) :: l => F :: F :: (vwi f p ++ [true]) ++ vp l

/-- the tape left of S0's separator, read leftward -/
def LK (a : Nat) (kR : List KB) : List Bool := F :: F :: lpR kR ++ rep (a + 1)

/-- the tape left of the last cell, read leftward, for var digits `vsR` (the last one first) -/
def LW (a : Nat) (kR : List KB) : List (Nat × Nat) → List Bool
  | [] => true :: LK a kR
  | (f, p) :: l => (vwi f p).reverse ++ F :: F :: true :: LW a kR l

/-- the whole tape -/
def TW (a : Nat) (kR : List KB) (vsR : List (Nat × Nat)) : List Bool := (LW a kR vsR).reverse ++ [true]

/-- head on the last cell of the tape -/
def lastCfg (W : List Bool) : Cfg St := ⟨CA, app W.dropLast.reverse blank, true ::: blank⟩

/-- head on the last cell of var digit `(f, p)`; `preR` left of it (read leftward), `post` right -/
def CV (a : Nat) (kR : List KB) (preR : List (Nat × Nat)) (f p : Nat) (post : List (Nat × Nat)) : Cfg St :=
  ⟨CA, app (LW a kR ((f, p) :: preR)) blank, true ::: app (vp post) blank⟩

/-- the K digits are scanned: `KF1` on the separator left of the blocks already passed -/
def KS (a : Nat) (kR : List KB) (R : Strm) : Cfg St := cfgL KF1 (app (LK a kR) blank) R

/-- the run is over (head two cells left of the tape) -/
def ENDc (W : List Bool) : Cfg St := ⟨PE1, blank, F ::: F ::: app W blank⟩

/-! ## the counter -/

def incV : List (Nat × Nat) → Option (List (Nat × Nat))
  | [] => none
  | (f, p) :: l => if p + 1 < f then some ((f, p + 1) :: l) else (incV l).map ((f, 0) :: ·)

def incK : List KB → Option (List KB)
  | [] => none
  | .pl n :: l => (incK l).map (.pl n :: ·)
  | .dg f c :: l => if c < f then some (.dg f (c + 1) :: l) else (incK l).map (.dg f 1 :: ·)

def zv (l : List (Nat × Nat)) : List (Nat × Nat) := l.map (fun x => (x.1, 0))

def rsK : List KB → List KB
  | [] => []
  | .pl n :: l => .pl n :: rsK l
  | .dg f _ :: l => .dg f 1 :: rsK l

/-! ## words -/

theorem rep_rev (n : Nat) : (rep n).reverse = rep n := List.reverse_replicate n true
theorem app_rep (n : Nat) (s : Strm) : app (rep n) s = ones n s := app_replicate n s
theorem rep_succ (n : Nat) : rep (n + 1) = true :: rep n := rfl
theorem rep_add (m n : Nat) : rep (m + n) = rep m ++ rep n := by
  induction m with
  | zero => simp [rep]
  | succ m ih => rw [show m + 1 + n = (m + n) + 1 by omega, rep_succ, rep_succ, ih]; rfl
theorem rep_succ' (n : Nat) : rep (n + 1) = rep n ++ [true] := rep_add n 1

theorem LK_succ (a : Nat) (kR : List KB) : LK (a + 1) kR = LK a kR ++ [true] := by
  unfold LK; rw [rep_succ']; simp

theorem LW_succ (a : Nat) (kR : List KB) : ∀ vs, LW (a + 1) kR vs = LW a kR vs ++ [true]
  | [] => by simp [LW, LK_succ]
  | (f, p) :: l => by simp [LW, LW_succ a kR l]

theorem TW_succ (a : Nat) (kR : List KB) (vs : List (Nat × Nat)) :
    TW (a + 1) kR vs = true :: TW a kR vs := by
  simp [TW, LW_succ]

theorem lastCfg_TW (a : Nat) (kR : List KB) (vs : List (Nat × Nat)) :
    lastCfg (TW a kR vs) = ⟨CA, app (LW a kR vs) blank, true ::: blank⟩ := by
  simp [lastCfg, TW]

theorem tl_blank : tl blank = blank := rfl

/-! ## the trip to the far left and back -/

theorem FAL : FarL delta AL1 AL2 AL3 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FRG : FarR delta RG1 RG2 RG3 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- one count: a cell at the far left, then back to the last cell -/
theorem trip (x : Bool) (u v : List Bool) (h1 : Clean12 (x :: u))
    (h2 : Clean12 (u.reverse ++ x :: v ++ [true])) :
    Rch ⟨AL1, app u blank, x ::: app (v ++ [true]) blank⟩
      ⟨CA, app (v.reverse ++ x :: u ++ [true]) blank, true ::: blank⟩ := by
  have e : (⟨AL1, app u blank, x ::: app (v ++ [true]) blank⟩ : Cfg St) =
      cfgL AL1 (app (x :: u) blank) (app (v ++ [true]) blank) := rfl
  rw [e]
  refine Rch.tr (FAL.go h1 _) ?_
  gR; gR; gR
  have e2 : app (x :: u).reverse (app (v ++ [true]) blank) = app (u.reverse ++ x :: v ++ [true]) blank := by
    simp [app_append]
  rw [e2]
  refine Rch.tr (FRG.go h2 (true ::: F ::: F ::: tl blank)) ?_
  have e3 : (u.reverse ++ x :: v ++ [true]).reverse = true :: (v.reverse ++ x :: u) := by simp
  rw [e3]
  gL0; gL; gL
  show Rch ⟨CA, app (v.reverse ++ x :: u) (true ::: F ::: F ::: tl blank), true ::: F ::: F ::: F ::: tl blank⟩ _
  simp only [tl_blank, cons_blank, app_append, app_cons, app_nil]; fin

/-! ## the tape has no three 0s in a row -/

def VOk (d : Nat × Nat) : Prop := 1 ≤ d.1 ∧ d.2 < d.1

theorem c12_rep (n : Nat) {r : List Bool} (h : Clean12 r) : Clean12 (rep n ++ r) := by
  induction n with
  | zero => exact h
  | succ n ih => exact Clean12.one ih

theorem c12_hole (c m : Nat) {r : List Bool} (h : Clean12 r) : Clean12 (rep c ++ F :: rep (m + 1) ++ r) := by
  simp only [List.append_assoc, List.cons_append]
  exact c12_rep c (Clean12.z1 (c12_rep m h))

theorem c12_sep {x : List Bool} (h : Clean12 (true :: x)) : Clean12 (F :: F :: true :: x) := by
  cases h with
  | one h => exact Clean12.z2 h

theorem KB.w_cons (b : KB) (hb : b.ok) : ∃ w, b.w = true :: w := by
  cases b with
  | pl n => obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [KB.ok] at hb; omega⟩; exact ⟨rep m, rfl⟩
  | dg f c =>
    simp [KB.ok] at hb
    obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
    exact ⟨rep m ++ F :: rep (f + 1 - (m + 1)), rfl⟩

theorem KB.c12 (b : KB) (hb : b.ok) {r : List Bool} (h : Clean12 r) : Clean12 (b.w ++ r) := by
  cases b with
  | pl n => exact c12_rep n h
  | dg f c =>
    simp [KB.ok] at hb
    have := c12_hole c (f - c) h
    rw [show f - c + 1 = f + 1 - c by omega] at this
    simpa [KB.w] using this

theorem KB.c12r (b : KB) (hb : b.ok) {r : List Bool} (h : Clean12 r) : Clean12 (b.w.reverse ++ r) := by
  cases b with
  | pl n => rw [KB.w, rep_rev]; exact c12_rep n h
  | dg f c =>
    simp [KB.ok] at hb
    obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
    have := c12_hole (f + 1 - (m + 1)) m h
    simpa [KB.w, rep_rev, List.reverse_append] using this

theorem KB.w_rcons (b : KB) (hb : b.ok) : ∃ w, b.w.reverse = true :: w := by
  cases b with
  | pl n =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [KB.ok] at hb; omega⟩
    exact ⟨rep m, by rw [KB.w, rep_rev]; rfl⟩
  | dg f c =>
    simp [KB.ok] at hb
    obtain ⟨m, hm⟩ : ∃ m, f + 1 - c = m + 1 := ⟨f - c, by omega⟩
    refine ⟨rep m ++ F :: rep c, ?_⟩
    rw [KB.w, hm, List.reverse_append, List.reverse_cons, rep_rev, rep_rev, rep_succ]; simp

theorem c12_LK (a : Nat) : ∀ (kR : List KB), (∀ b ∈ kR, b.ok) → Clean12 (LK a kR)
  | [], _ => by
    show Clean12 (F :: F :: true :: rep a)
    exact Clean12.z2 (by simpa using c12_rep a Clean12.nil)
  | b :: l, h => by
    have hl := c12_LK a l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hb := h b (List.mem_cons_self _ _)
    obtain ⟨w, hw⟩ := KB.w_rcons b hb
    have := KB.c12r b hb hl
    unfold LK at this ⊢
    simp only [lpR, List.append_assoc, List.cons_append] at this ⊢
    rw [hw] at this ⊢
    exact c12_sep this

theorem vwi_rev (f p : Nat) (hp : p < f) :
    (vwi f p).reverse = if p = 0 then rep (f + 1) else rep (f - p - 1) ++ F :: rep (p + 1) := by
  unfold vwi
  split
  · rw [rep_rev]
  · simp [List.reverse_append, rep_rev]

theorem c12_LW (a : Nat) (kR : List KB) (hk : ∀ b ∈ kR, b.ok) :
    ∀ vs : List (Nat × Nat), (∀ d ∈ vs, VOk d) → Clean12 (LW a kR vs)
  | [], _ => Clean12.one (c12_LK a kR hk)
  | (f, p) :: l, h => by
    have hl := c12_LW a kR hk l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hd := h (f, p) (List.mem_cons_self _ _)
    simp only [VOk] at hd
    simp only [LW]
    rw [vwi_rev f p hd.2]
    split
    · exact c12_rep _ (Clean12.z2 hl)
    · obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
      simpa [List.append_assoc] using c12_hole (f - (m + 1) - 1) (m + 1) (Clean12.z2 hl)

theorem lpR_rev_cons (b : KB) (l : List KB) : (lpR (b :: l)).reverse = (lpR l).reverse ++ F :: F :: b.w := by
  simp [lpR, List.reverse_append]

theorem c12_lpRr : ∀ (kR : List KB), (∀ b ∈ kR, b.ok) → Clean12 (lpR kR).reverse
  | [], _ => Clean12.nil
  | b :: l, h => by
    rw [lpR_rev_cons]
    refine Clean12.append (c12_lpRr l (fun x hx => h x (List.mem_cons_of_mem _ hx))) ?_
    have hb := h b (List.mem_cons_self _ _)
    obtain ⟨w, hw⟩ := KB.w_cons b hb
    have := KB.c12 b hb (r := []) Clean12.nil
    rw [List.append_nil, hw] at this; rw [hw]
    cases this with | one h => exact Clean12.z2 h

theorem TW_nil (a : Nat) (kR : List KB) :
    TW a kR [] = rep (a + 1) ++ (lpR kR).reverse ++ [F, F, true, true] := by
  simp [TW, LW, LK, List.reverse_append, rep_rev]

theorem TW_cons (a : Nat) (kR : List KB) (f p : Nat) (l : List (Nat × Nat)) :
    TW a kR ((f, p) :: l) = TW a kR l ++ F :: F :: vwi f p ++ [true] := by
  simp [TW, LW, List.reverse_append]

theorem c12_F_rep (k : Nat) : Clean12 (F :: (rep k ++ [true])) := by
  cases k with
  | zero => exact Clean12.z1 Clean12.nil
  | succ k => exact Clean12.z1 (c12_rep k (Clean12.one Clean12.nil))

theorem c12_TW (a : Nat) (kR : List KB) (hk : ∀ b ∈ kR, b.ok) :
    ∀ vs : List (Nat × Nat), (∀ d ∈ vs, VOk d) → Clean12 (TW a kR vs)
  | [], _ => by
    rw [TW_nil, List.append_assoc]
    exact c12_rep _ (Clean12.append (c12_lpRr kR hk)
      (Clean12.z2 (Clean12.one Clean12.nil)))
  | (f, p) :: l, h => by
    rw [TW_cons, List.append_assoc]
    refine Clean12.append (c12_TW a kR hk l (fun x hx => h x (List.mem_cons_of_mem _ hx))) ?_
    have hd := h (f, p) (List.mem_cons_self _ _)
    simp only [VOk] at hd
    simp only [List.cons_append]
    unfold vwi
    split
    · rw [rep_succ]
      exact Clean12.z2 (c12_rep f (Clean12.one Clean12.nil))
    · simp only [rep_succ, List.cons_append, List.append_assoc]
      exact Clean12.z2 (c12_rep p (c12_F_rep _))

theorem Wd_TW (a : Nat) (kR : List KB) (vs : List (Nat × Nat))
    (hk : ∀ b ∈ kR, b.ok) (hv : ∀ d ∈ vs, VOk d) : Wd (TW a kR vs) := by
  refine ⟨c12_TW a kR hk vs hv, ?_⟩
  simp only [TW, List.reverse_append, List.reverse_reverse, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  exact Clean12.one (c12_LW a kR hk vs hv)

/-! ## the carry over the var digits -/

theorem TW_append (a : Nat) (kR : List KB) :
    ∀ l m : List (Nat × Nat), TW a kR (l.reverse ++ m) = TW a kR m ++ vp l
  | [], m => by simp [vp]
  | (f, p) :: l, m => by
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, TW_append a kR l, TW_cons]
    simp [vp]

def CS (a : Nat) (kR : List KB) (vs : List (Nat × Nat)) : Cfg St := lastCfg (TW a kR vs)

theorem lastCfg_cons (x : Bool) (u v : List Bool) :
    lastCfg (true :: (u.reverse ++ x :: v ++ [true])) = ⟨CA, app (v.reverse ++ x :: u ++ [true]) blank, true ::: blank⟩ := by
  unfold lastCfg
  rw [show true :: (u.reverse ++ x :: v ++ [true]) = (true :: (u.reverse ++ x :: v)) ++ [true] by simp,
    List.dropLast_concat]
  simp

/-- a count, from `AL1`, with the tape `W` after it: `CS` with one more cell in the accumulator -/
theorem count1 (x : Bool) (u v : List Bool) (a : Nat) (kR : List KB) (vs : List (Nat × Nat))
    (hk : ∀ b ∈ kR, b.ok) (hv : ∀ d ∈ vs, VOk d) (hW : u.reverse ++ x :: v ++ [true] = TW a kR vs) :
    Rch ⟨AL1, app u blank, x ::: app (v ++ [true]) blank⟩ (CS (a + 1) kR vs) := by
  have hd := Wd_TW a kR vs hk hv
  rw [← hW] at hd
  have h1 := hd.left (u := u.reverse ++ [x]) (v := v ++ [true]) (by simp)
  rw [List.reverse_append, List.reverse_reverse] at h1
  have := trip x u v h1 hd.1
  rw [← lastCfg_cons, hW, ← TW_succ] at this
  exact this

/-- `count1` for any nonempty right part: its last cell is the tape's last (a 1) -/
theorem count1' (x : Bool) (u r : List Bool) (a : Nat) (kR : List KB) (vs : List (Nat × Nat))
    (hk : ∀ b ∈ kR, b.ok) (hv : ∀ d ∈ vs, VOk d) (hr : r ≠ []) (hW : u.reverse ++ x :: r = TW a kR vs) :
    Rch ⟨AL1, app u blank, x ::: app r blank⟩ (CS (a + 1) kR vs) := by
  have e := List.dropLast_concat_getLast hr
  have hl : r.getLast hr = true := by
    have h2 : (u.reverse ++ x :: r).getLast (by simp) = (TW a kR vs).getLast (by simp [TW]) := by
      congr 1
    rw [List.getLast_append_of_ne_nil (by simp), List.getLast_cons hr] at h2
    rw [h2]; simp [TW]
  rw [hl] at e
  rw [← e] at hW ⊢
  exact count1 x u r.dropLast a kR vs hk hv (by simpa [List.append_assoc] using hW)

theorem vp_head (post : List (Nat × Nat)) : app (vp post) blank = F ::: tl (app (vp post) blank) := by
  funext n; cases n with
  | zero => cases post <;> rfl
  | succ n => rfl

theorem vp_cons0 (f : Nat) (post : List (Nat × Nat)) :
    app (vp ((f, 0) :: post)) blank = F ::: F ::: ones (f + 2) (app (vp post) blank) := by
  simp only [vp, vwi, if_pos, app_cons, app_append, app_rep, app_nil, ite_true]
  rw [ones_succ' (f + 1)]

theorem repl_absorb (k : Nat) (l : List Bool) :
    List.replicate k true ++ true :: l = List.replicate (k + 1) true ++ l := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, ih]

theorem vok_app {l m : List (Nat × Nat)} (hl : ∀ d ∈ l, VOk d) (hm : ∀ d ∈ m, VOk d) :
    ∀ d ∈ l ++ m, VOk d := by
  intro d hd; rcases List.mem_append.1 hd with h | h; exact hl d h; exact hm d h

theorem vok_rev {l : List (Nat × Nat)} (hl : ∀ d ∈ l, VOk d) : ∀ d ∈ l.reverse, VOk d :=
  fun d hd => hl d (List.mem_reverse.1 hd)

/-- a var digit advances: one count -/
theorem cv_adv (a : Nat) (kR : List KB) (hk : ∀ b ∈ kR, b.ok) (preR : List (Nat × Nat)) (f p : Nat)
    (post : List (Nat × Nat)) (hv : ∀ d ∈ preR, VOk d) (hpo : ∀ d ∈ post, VOk d) (hf : p + 1 < f) :
    Rch (CV a kR preR f p post) (CS (a + 1) kR (post.reverse ++ (f, p + 1) :: preR)) := by
  have hnew : ∀ d ∈ post.reverse ++ (f, p + 1) :: preR, VOk d := by
    refine vok_app (vok_rev hpo) ?_
    intro d hd; rcases List.mem_cons.1 hd with rfl | h
    · exact ⟨by omega, hf⟩
    · exact hv d h
  unfold CV
  show Rch ⟨CA, app ((vwi f p).reverse ++ F :: F :: true :: LW a kR preR) blank, true ::: app (vp post) blank⟩ _
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · obtain ⟨k, rfl⟩ : ∃ k, f = k + 2 := ⟨f - 2, by omega⟩
    have h1 : app ((vwi (k + 2) 0).reverse ++ F :: F :: true :: LW a kR preR) blank =
        ones (k + 3) (F ::: F ::: app (true :: LW a kR preR) blank) := by
      simp [vwi, app_append, app_rep, rep_rev]
    rw [h1]
    refine Rch.tr (v_adv0 _ _ (k + 2) (by omega)) ?_
    have := count1' true (rep 1 ++ F :: F :: true :: LW a kR preR) (F :: rep (k + 1) ++ vp post) a kR
      (post.reverse ++ (k + 2, 0 + 1) :: preR) hk hnew (by simp) ?_
    · simpa [app_append, app_rep] using this
    · rw [TW_append, TW_cons]
      simp [TW, vwi, rep_succ', List.append_assoc, rep, repl_absorb]
  · obtain ⟨k, rfl⟩ : ∃ k, f = p + 2 + k := ⟨f - p - 2, by omega⟩
    have h1 : app ((vwi (p + 2 + k) p).reverse ++ F :: F :: true :: LW a kR preR) blank =
        ones (p + 2 + k - p - 1) (F ::: ones (p + 1) (app (F :: F :: true :: LW a kR preR) blank)) := by
      rw [vwi_rev _ _ (by omega), if_neg (by omega)]
      simp [app_append, app_rep]
    rw [h1]
    refine Rch.tr (v_adv _ _ (p + 2 + k) p (by omega)) ?_
    have := count1' true (rep (p + 1) ++ F :: F :: true :: LW a kR preR) (F :: rep (k + 1) ++ vp post) a kR
      (post.reverse ++ (p + 2 + k, p + 1) :: preR) hk hnew (by simp) ?_
    · rw [show p + 2 + k - p - 1 = k + 1 by omega]
      simpa [app_append, app_rep] using this
    · rw [TW_append, TW_cons]
      have hv2 : vwi (p + 2 + k) (p + 1) = rep (p + 2) ++ F :: rep k := by
        unfold vwi; rw [if_neg (by omega), show p + 2 + k - (p + 1) - 1 = k by omega]
      rw [hv2]
      simp [TW, rep_succ', List.append_assoc, rep, repl_absorb]

/-- a var digit at its last position wraps: the head goes to the previous block -/
theorem cv_wrap (a : Nat) (kR : List KB) (preR : List (Nat × Nat)) (f p : Nat)
    (post : List (Nat × Nat)) (hf : p + 1 = f) :
    Rch (CV a kR preR f p post) ⟨CA, app (LW a kR preR) blank, true ::: app (vp ((f, 0) :: post)) blank⟩ := by
  unfold CV
  show Rch ⟨CA, app ((vwi f p).reverse ++ F :: F :: true :: LW a kR preR) blank, true ::: app (vp post) blank⟩ _
  rw [vp_cons0]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · subst hf
    have h1 : app ((vwi 1 0).reverse ++ F :: F :: true :: LW a kR preR) blank =
        ones 2 (F ::: F ::: app (true :: LW a kR preR) blank) := by
      simp [vwi, app_append, app_rep, rep_rev]
    rw [h1, vp_head post]
    exact Rch.tr (v_wrap1 _ _) (by rw [← vp_head]; fin)
  · subst hf
    have h1 : app ((vwi (p + 1) p).reverse ++ F :: F :: true :: LW a kR preR) blank =
        F ::: ones (p + 1) (F ::: F ::: app (true :: LW a kR preR) blank) := by
      rw [vwi_rev _ _ (by omega), if_neg (by omega), show p + 1 - p - 1 = 0 by omega]
      simp [app_append, app_rep, rep, app_replicate]
    rw [h1]
    exact Rch.tr (v_wrap _ _ (p + 1)) (by fin)

theorem zv_cons (f p : Nat) (l : List (Nat × Nat)) : zv ((f, p) :: l) = (f, 0) :: zv l := rfl

/-- the carry over the var digits, from var digit `(f, p)` with `post` (already wrapped) right of it -/
theorem VC (a : Nat) (kR : List KB) (hk : ∀ b ∈ kR, b.ok) :
    ∀ (preR : List (Nat × Nat)) (f p : Nat) (post : List (Nat × Nat)),
    (∀ d ∈ (f, p) :: preR, VOk d) → (∀ d ∈ post, VOk d) →
    (∀ l', incV ((f, p) :: preR) = some l' → Rch (CV a kR preR f p post) (CS (a + 1) kR (post.reverse ++ l'))) ∧
    (incV ((f, p) :: preR) = none →
      Rch (CV a kR preR f p post) (KS a kR (app (rep 2 ++ vp ((zv ((f, p) :: preR)).reverse ++ post)) blank))) := by
  intro preR
  induction preR with
  | nil =>
    intro f p post hv hpo
    have hd := hv (f, p) (List.mem_cons_self _ _)
    simp only [VOk] at hd
    by_cases hf : p + 1 < f
    · refine ⟨fun l' hl => ?_, fun hl => ?_⟩
      · simp [incV, hf] at hl; subst hl
        exact cv_adv a kR hk [] f p post (by simp) hpo hf
      · simp [incV, hf] at hl
    · refine ⟨fun l' hl => ?_, fun _ => ?_⟩
      · simp [incV, hf] at hl
      · refine Rch.tr (cv_wrap a kR [] f p post (by omega)) ?_
        rw [vp_cons0]
        show Rch (cfgL CA (true ::: true ::: F ::: F ::: app (lpR kR ++ rep (a + 1)) blank)
          (F ::: F ::: ones (f + 2) (app (vp post) blank))) _
        refine Rch.tr (v_s0 _ _) ?_
        gL; gL
        unfold KS LK
        simp only [zv, List.map, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
          app_append, app_cons, app_nil]
        rw [vp_cons0]; simp only [rep, app_replicate]; fin
  | cons d preR ih =>
    intro f p post hv hpo
    obtain ⟨g, q⟩ := d
    have hd := hv (f, p) (List.mem_cons_self _ _)
    simp only [VOk] at hd
    have hv' : ∀ x ∈ (g, q) :: preR, VOk x := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    by_cases hf : p + 1 < f
    · refine ⟨fun l' hl => ?_, fun hl => ?_⟩
      · simp [incV, hf] at hl; subst hl
        exact cv_adv a kR hk ((g, q) :: preR) f p post hv' hpo hf
      · simp [incV, hf] at hl
    · have hpo' : ∀ x ∈ (f, 0) :: post, VOk x := by
        intro x hx; rcases List.mem_cons.1 hx with rfl | h
        · exact ⟨hd.1, hd.1⟩
        · exact hpo x h
      have st := cv_wrap a kR ((g, q) :: preR) f p post (by omega)
      have IH := ih g q ((f, 0) :: post) hv' hpo'
      refine ⟨fun l' hl => ?_, fun hl => ?_⟩
      · simp only [incV, if_neg hf, Option.map_eq_some'] at hl
        obtain ⟨l'', h1, rfl⟩ := hl
        have := IH.1 l'' h1
        simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at this
        exact Rch.tr st this
      · simp only [incV, if_neg hf, Option.map_eq_none'] at hl
        have := IH.2 hl
        simp only [zv_cons, List.reverse_cons, List.append_assoc, List.singleton_append] at this ⊢
        exact Rch.tr st this

/-! ## the carry over the K digits -/

/-- blocks already passed (nearest S0 first), left to right with their separators -/
def dwords : List KB → List Bool
  | [] => []
  | b :: l => dwords l ++ b.w ++ [F, F]

theorem dwords_snoc (b : KB) : ∀ l : List KB, dwords (l ++ [b]) = b.w ++ F :: F :: dwords l
  | [] => by simp [dwords]
  | d :: l => by simp [dwords, dwords_snoc b l, List.append_assoc]

theorem LK_rev_cons (a : Nat) (b : KB) (l : List KB) :
    (LK a (b :: l)).reverse = (LK a l).reverse ++ b.w ++ [F, F] := by
  simp [LK, lpR, List.reverse_append, List.append_assoc]

theorem LK_rev_app (a : Nat) (kR : List KB) : ∀ done : List KB,
    (LK a (done ++ kR)).reverse = (LK a kR).reverse ++ dwords done
  | [] => by simp [dwords]
  | b :: l => by
    rw [List.cons_append, LK_rev_cons, LK_rev_app a kR l]; simp [dwords, List.append_assoc]

theorem TW_K (a : Nat) (K : List KB) (vs : List (Nat × Nat)) :
    TW a K vs = (LK a K).reverse ++ true :: true :: vp vs.reverse := by
  have := TW_append a K vs.reverse []
  rw [List.reverse_reverse, List.append_nil] at this
  rw [this, TW_nil]; simp [LK, List.reverse_append, rep_rev, List.append_assoc]

theorem clean_sep_rep (n : Nat) (hn : 1 ≤ n) : Clean (F :: F :: rep n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Clean.sep (Clean.replicate m)

theorem KS_pl (a n : Nat) (hn : 1 ≤ n) (l : List KB) (r : List Bool) :
    Rch (KS a (.pl n :: l) (app r blank)) (KS a l (app (rep n ++ F :: F :: r) blank)) := by
  unfold KS
  have := HKF.cross (clean_sep_rep n hn) (app (LK a l) blank) (app r blank)
  have e : app (LK a (.pl n :: l)) blank = app (F :: F :: rep n) (app (LK a l) blank) := by
    simp [LK, lpR, KB.w, rep_rev, app_append]
  rw [e]; refine Rch.tr this ?_
  simp [app_append, rep_rev]; fin

/-- an active K digit: find its hole -/
theorem KS_find (a f c : Nat) (hc : 1 ≤ c) (hcf : c ≤ f) (l : List KB) (r : List Bool) :
    Rch (KS a (.dg f c :: l) (app r blank))
      (cfgL KF2 (ones c (F ::: F ::: app (lpR l ++ rep (a + 1)) blank))
        (F ::: ones (f + 1 - c) (F ::: F ::: app r blank))) := by
  unfold KS
  obtain ⟨b, rfl⟩ : ∃ b, c = b + 1 := ⟨c - 1, by omega⟩
  have hw := clean_sep_rep (f + 1 - (b + 1)) (by omega)
  have := HKF.find hw (ones b (F ::: F ::: app (lpR l ++ rep (a + 1)) blank)) (app r blank)
  have e : app (LK a (.dg f (b + 1) :: l)) blank =
      app (F :: F :: rep (f + 1 - (b + 1))) (F ::: true ::: ones b (F ::: F ::: app (lpR l ++ rep (a + 1)) blank)) := by
    simp [LK, lpR, KB.w, rep_rev, app_append, List.reverse_append, app_rep, rep, app_replicate, ones_succ]
  rw [e]; refine Rch.tr this ?_
  simp [app_append, rep_rev, app_rep]; fin

theorem KS_nil (a : Nat) (r : List Bool) :
    Rch (KS a [] (app r blank)) (ENDc ((LK a []).reverse ++ r)) := by
  unfold KS ENDc
  have hw : Clean (F :: F :: rep (a + 1)) := clean_sep_rep (a + 1) (by omega)
  have := HKF.far hw (app r blank)
  have e : app (LK a []) blank = app (F :: F :: rep (a + 1)) blank := by simp [LK, lpR]
  rw [e]; refine Rch.tr this ?_
  gR
  simp [LK, lpR, app_append, rep_rev, cons_blank]; fin

/-- the carry over the K digits; `done` have been passed (and wrapped) -/
theorem KSc (a : Nat) (vs : List (Nat × Nat)) (hv : ∀ d ∈ vs, VOk d) :
    ∀ (kR done : List KB), (∀ b ∈ kR, b.ok) → (∀ b ∈ done, b.ok) →
    (∀ k', incK kR = some k' →
      Rch (KS a kR (app (dwords done ++ true :: true :: vp vs.reverse) blank)) (CS (a + 1) (done ++ k') vs)) ∧
    (incK kR = none →
      Rch (KS a kR (app (dwords done ++ true :: true :: vp vs.reverse) blank)) (ENDc (TW a (done ++ rsK kR) vs))) := by
  intro kR
  induction kR with
  | nil =>
    intro done _ _
    refine ⟨fun k' h => by simp [incK] at h, fun _ => ?_⟩
    refine Rch.tr (KS_nil a _) ?_
    have := LK_rev_app a [] done; rw [List.append_nil] at this
    rw [TW_K]; simp only [rsK, List.append_nil, this, List.append_assoc]; fin
  | cons b l ih =>
    intro done hk hd
    have hb := hk b (List.mem_cons_self _ _)
    have hl : ∀ x ∈ l, x.ok := fun x hx => hk x (List.mem_cons_of_mem _ hx)
    cases b with
    | pl n =>
      have hd' : ∀ x ∈ done ++ [KB.pl n], x.ok := by
        intro x hx; rcases List.mem_append.1 hx with h | h
        · exact hd x h
        · simp at h; subst h; exact hb
      have st := KS_pl a n hb l (dwords done ++ true :: true :: vp vs.reverse)
      rw [show rep n ++ F :: F :: (dwords done ++ true :: true :: vp vs.reverse) =
          dwords (done ++ [KB.pl n]) ++ true :: true :: vp vs.reverse by
        rw [dwords_snoc]; simp [KB.w, List.append_assoc]] at st
      have IH := ih (done ++ [KB.pl n]) hl hd'
      refine ⟨fun k' h => ?_, fun h => ?_⟩
      · simp only [incK, Option.map_eq_some'] at h
        obtain ⟨k'', h1, rfl⟩ := h
        have := IH.1 k'' h1; simp only [List.append_assoc, List.singleton_append] at this
        exact Rch.tr st this
      · simp only [incK, Option.map_eq_none'] at h
        have := IH.2 h; simp only [List.append_assoc, List.singleton_append] at this
        exact Rch.tr st this
    | dg f c =>
      simp only [KB.ok] at hb
      have fd := KS_find a f c hb.1 hb.2 l (dwords done ++ true :: true :: vp vs.reverse)
      by_cases hcf : c < f
      · refine ⟨fun k' h => ?_, fun h => by simp [incK, hcf] at h⟩
        simp [incK, hcf] at h; subst h
        refine Rch.tr fd ?_
        refine Rch.tr (k_adv _ _ f c hb.1 hcf) ?_
        have hk' : ∀ x ∈ done ++ KB.dg f (c + 1) :: l, x.ok := by
          intro x hx; rcases List.mem_append.1 hx with h | h
          · exact hd x h
          · rcases List.mem_cons.1 h with rfl | h
            · simp [KB.ok]; omega
            · exact hl x h
        have := count1' true (rep (c - 1) ++ F :: F :: lpR l ++ rep (a + 1))
          (true :: F :: rep (f - c) ++ F :: F :: (dwords done ++ true :: true :: vp vs.reverse)) a
          (done ++ KB.dg f (c + 1) :: l) vs hk' hv (by simp) ?_
        · simpa [app_append, app_rep, List.append_assoc] using this
        · rw [TW_K, LK_rev_app, LK_rev_cons]
          obtain ⟨e, rfl⟩ : ∃ e, c = e + 1 := ⟨c - 1, by omega⟩
          simp [LK, KB.w, List.reverse_append, rep_rev, List.append_assoc, rep, repl_absorb]
      · obtain rfl : c = f := by omega
        have hd' : ∀ x ∈ done ++ [KB.dg c 1], x.ok := by
          intro x hx; rcases List.mem_append.1 hx with h | h
          · exact hd x h
          · simp at h; subst h; simp [KB.ok]; omega
        have st : Rch (KS a (.dg c c :: l) (app (dwords done ++ true :: true :: vp vs.reverse) blank))
            (KS a l (app (dwords (done ++ [KB.dg c 1]) ++ true :: true :: vp vs.reverse) blank)) := by
          refine Rch.tr fd ?_
          rw [show c + 1 - c = 1 by omega]
          refine Rch.tr (k_wrap _ _ c (by omega)) ?_
          unfold KS
          rw [dwords_snoc]
          simp [LK, KB.w, app_append, app_rep, rep, app_replicate]; fin
        have IH := ih (done ++ [KB.dg c 1]) hl hd'
        refine ⟨fun k' h => ?_, fun h => ?_⟩
        · simp only [incK, Nat.lt_irrefl, if_false, Option.map_eq_some'] at h
          obtain ⟨k'', h1, rfl⟩ := h
          have := IH.1 k'' h1; simp only [List.append_assoc, List.singleton_append] at this
          exact Rch.tr st this
        · simp only [incK, Nat.lt_irrefl, if_false, Option.map_eq_none'] at h
          have := IH.2 h; simp only [List.append_assoc, List.singleton_append, rsK] at this ⊢
          exact Rch.tr st this

/-! ## one advance of the whole counter -/

theorem CS_cons (a : Nat) (kR : List KB) (f p : Nat) (preR : List (Nat × Nat)) :
    CS a kR ((f, p) :: preR) = CV a kR preR f p [] := by
  unfold CS CV; rw [lastCfg_TW]; rfl

theorem zv_ok {l : List (Nat × Nat)} (h : ∀ d ∈ l, VOk d) : ∀ d ∈ zv l, VOk d := by
  intro d hd; simp only [zv, List.mem_map] at hd
  obtain ⟨x, hx, rfl⟩ := hd; exact ⟨(h x hx).1, (h x hx).1⟩

theorem adv (a : Nat) (kR : List KB) (vs : List (Nat × Nat)) (hk : ∀ b ∈ kR, b.ok)
    (hv : ∀ d ∈ vs, VOk d) (hne : vs ≠ []) :
    (∀ vs', incV vs = some vs' → Rch (CS a kR vs) (CS (a + 1) kR vs')) ∧
    (incV vs = none → ∀ k', incK kR = some k' → Rch (CS a kR vs) (CS (a + 1) k' (zv vs))) ∧
    (incV vs = none → incK kR = none → Rch (CS a kR vs) (ENDc (TW a (rsK kR) (zv vs)))) := by
  obtain ⟨⟨f, p⟩, preR, rfl⟩ : ∃ d l, vs = d :: l := by
    cases vs with | nil => exact absurd rfl hne | cons d l => exact ⟨d, l, rfl⟩
  have V := VC a kR hk preR f p [] hv (by simp)
  rw [CS_cons]
  refine ⟨fun vs' h => by simpa using V.1 vs' h, fun h k' hk' => ?_, fun h hk' => ?_⟩
  · have K := KSc a (zv ((f, p) :: preR)) (zv_ok hv) kR [] hk (by simp)
    have := K.1 k' hk'
    simp only [dwords, List.nil_append] at this
    exact Rch.tr (by simpa [rep] using V.2 h) this
  · have K := KSc a (zv ((f, p) :: preR)) (zv_ok hv) kR [] hk (by simp)
    have := K.2 hk'
    simp only [dwords, List.nil_append] at this
    exact Rch.tr (by simpa [rep] using V.2 h) this

/-! ## counting -/

def pV : List (Nat × Nat) → Nat
  | [] => 1
  | (f, _) :: l => f * pV l

def vV : List (Nat × Nat) → Nat
  | [] => 0
  | (f, p) :: l => p + f * vV l

def pK : List KB → Nat
  | [] => 1
  | .pl _ :: l => pK l
  | .dg f _ :: l => f * pK l

def vK : List KB → Nat
  | [] => 0
  | .pl _ :: l => vK l
  | .dg f c :: l => (c - 1) + f * vK l

theorem vV_lt : ∀ l : List (Nat × Nat), (∀ d ∈ l, VOk d) → vV l < pV l
  | [], _ => by simp [vV, pV]
  | (f, p) :: l, h => by
    have hd := h (f, p) (List.mem_cons_self _ _); simp only [VOk] at hd
    have ih := vV_lt l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := Nat.mul_le_mul_left f (show vV l + 1 ≤ pV l by omega)
    rw [Nat.mul_succ] at this
    simp only [vV, pV]; omega

theorem vK_lt : ∀ l : List KB, (∀ b ∈ l, b.ok) → vK l < pK l
  | [], _ => by simp [vK, pK]
  | .pl n :: l, h => by
    simpa [vK, pK] using vK_lt l (fun x hx => h x (List.mem_cons_of_mem _ hx))
  | .dg f c :: l, h => by
    have hd := h (.dg f c) (List.mem_cons_self _ _); simp only [KB.ok] at hd
    have ih := vK_lt l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := Nat.mul_le_mul_left f (show vK l + 1 ≤ pK l by omega)
    rw [Nat.mul_succ] at this
    simp only [vK, pK]; omega

theorem incV_some : ∀ (l l' : List (Nat × Nat)), (∀ d ∈ l, VOk d) → incV l = some l' →
    vV l' = vV l + 1 ∧ pV l' = pV l ∧ zv l' = zv l ∧ (∀ d ∈ l', VOk d)
  | [], _, _, h => by simp [incV] at h
  | (f, p) :: l, l', hv, h => by
    have hd := hv (f, p) (List.mem_cons_self _ _); simp only [VOk] at hd
    have hl : ∀ x ∈ l, VOk x := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    by_cases hf : p + 1 < f
    · simp [incV, hf] at h; subst h
      refine ⟨by simp [vV]; omega, by simp [pV], by simp [zv], ?_⟩
      intro x hx; rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hd.1, hf⟩
      · exact hl x hx
    · simp only [incV, if_neg hf, Option.map_eq_some'] at h
      obtain ⟨l'', h1, rfl⟩ := h
      obtain ⟨e1, e2, e3, e4⟩ := incV_some l l'' hl h1
      refine ⟨?_, by simp [pV, e2], by simp [zv] at e3 ⊢; exact e3, ?_⟩
      · simp only [vV, e1]; rw [Nat.mul_succ]; omega
      · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨hd.1, hd.1⟩
        · exact e4 x hx

theorem incV_none : ∀ (l : List (Nat × Nat)), (∀ d ∈ l, VOk d) → incV l = none → vV l + 1 = pV l
  | [], _, _ => by simp [vV, pV]
  | (f, p) :: l, hv, h => by
    have hd := hv (f, p) (List.mem_cons_self _ _); simp only [VOk] at hd
    have hl : ∀ x ∈ l, VOk x := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    by_cases hf : p + 1 < f
    · simp [incV, hf] at h
    · simp only [incV, if_neg hf, Option.map_eq_none'] at h
      have := incV_none l hl h
      simp only [vV, pV]; rw [← this, Nat.mul_succ]; omega

theorem incK_some : ∀ (l l' : List KB), (∀ b ∈ l, b.ok) → incK l = some l' →
    vK l' = vK l + 1 ∧ pK l' = pK l ∧ rsK l' = rsK l ∧ (∀ b ∈ l', b.ok)
  | [], _, _, h => by simp [incK] at h
  | .pl n :: l, l', hv, h => by
    have hb := hv (.pl n) (List.mem_cons_self _ _)
    have hl : ∀ x ∈ l, x.ok := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    simp only [incK, Option.map_eq_some'] at h
    obtain ⟨l'', h1, rfl⟩ := h
    obtain ⟨e1, e2, e3, e4⟩ := incK_some l l'' hl h1
    refine ⟨by simp [vK, e1], by simp [pK, e2], by simp [rsK, e3], ?_⟩
    intro x hx; rcases List.mem_cons.1 hx with rfl | hx
    · exact hb
    · exact e4 x hx
  | .dg f c :: l, l', hv, h => by
    have hd := hv (.dg f c) (List.mem_cons_self _ _); simp only [KB.ok] at hd
    have hl : ∀ x ∈ l, x.ok := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    by_cases hf : c < f
    · simp [incK, hf] at h; subst h
      refine ⟨by simp [vK]; omega, by simp [pK], by simp [rsK], ?_⟩
      intro x hx; rcases List.mem_cons.1 hx with rfl | hx
      · simp [KB.ok]; omega
      · exact hl x hx
    · simp only [incK, if_neg hf, Option.map_eq_some'] at h
      obtain ⟨l'', h1, rfl⟩ := h
      obtain ⟨e1, e2, e3, e4⟩ := incK_some l l'' hl h1
      refine ⟨?_, by simp [pK, e2], by simp [rsK, e3], ?_⟩
      · simp only [vK, e1]; rw [Nat.mul_succ]; omega
      · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
        · simp [KB.ok]; omega
        · exact e4 x hx

theorem incK_none : ∀ (l : List KB), (∀ b ∈ l, b.ok) → incK l = none → vK l + 1 = pK l
  | [], _, _ => by simp [vK, pK]
  | .pl n :: l, hv, h => by
    simp only [incK, Option.map_eq_none'] at h
    simpa [vK, pK] using incK_none l (fun x hx => hv x (List.mem_cons_of_mem _ hx)) h
  | .dg f c :: l, hv, h => by
    have hd := hv (.dg f c) (List.mem_cons_self _ _); simp only [KB.ok] at hd
    have hl : ∀ x ∈ l, x.ok := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    by_cases hf : c < f
    · simp [incK, hf] at h
    · simp only [incK, if_neg hf, Option.map_eq_none'] at h
      have := incK_none l hl h
      simp only [vK, pK]; rw [← this, Nat.mul_succ]; omega

theorem zv_zv (l : List (Nat × Nat)) : zv (zv l) = zv l := by simp [zv, List.map_map]
theorem vV_zv : ∀ l : List (Nat × Nat), vV (zv l) = 0
  | [] => rfl
  | (f, p) :: l => by show 0 + f * vV (zv l) = 0; rw [vV_zv l]; simp
theorem pV_zv : ∀ l : List (Nat × Nat), pV (zv l) = pV l
  | [] => rfl
  | (f, p) :: l => by show f * pV (zv l) = f * pV l; rw [pV_zv l]
theorem incV_ne : ∀ l l' : List (Nat × Nat), incV l = some l' → l' ≠ []
  | [], _, h => by simp [incV] at h
  | (f, p) :: l, l', h => by
    unfold incV at h; split at h
    · simp at h; subst h; simp
    · simp only [Option.map_eq_some'] at h; obtain ⟨_, _, rfl⟩ := h; simp
theorem zv_ne {l : List (Nat × Nat)} (h : l ≠ []) : zv l ≠ [] := by simpa [zv] using h

/-- the run from `CS` to its end: `n` more counts -/
theorem count : ∀ n a (kR : List KB) (vs : List (Nat × Nat)), (∀ b ∈ kR, b.ok) → (∀ d ∈ vs, VOk d) → vs ≠ [] →
    pV vs * pK kR - 1 - (vV vs + pV vs * vK kR) = n →
    Rch (CS a kR vs) (ENDc (TW (a + n) (rsK kR) (zv vs))) := by
  intro n
  induction n with
  | zero =>
    intro a kR vs hk hv hne hn
    have A := adv a kR vs hk hv hne
    have b1 := vV_lt vs hv; have b2 := vK_lt kR hk
    have hb : vV vs + pV vs * vK kR + 1 ≤ pV vs * pK kR := by
      have := Nat.mul_le_mul_left (pV vs) (show vK kR + 1 ≤ pK kR by omega); rw [Nat.mul_succ] at this; omega
    cases h1 : incV vs with
    | some vs' =>
      exfalso; obtain ⟨e1, e2, _, e4⟩ := incV_some vs vs' hv h1
      have := vV_lt vs' e4; have := Nat.mul_le_mul_left (pV vs) (show vK kR + 1 ≤ pK kR by omega)
      rw [Nat.mul_succ] at this; rw [e1, e2] at *; omega
    | none =>
      cases h2 : incK kR with
      | some k' =>
        exfalso; obtain ⟨e1, e2, _, e4⟩ := incK_some kR k' hk h2
        have h3 := incV_none vs hv h1
        have := vK_lt k' e4; rw [e1, e2] at this
        have := Nat.mul_le_mul_left (pV vs) (show vK kR + 1 + 1 ≤ pK kR by omega)
        rw [Nat.mul_succ, Nat.mul_succ] at this; omega
      | none => simpa using A.2.2 h1 h2
  | succ n ih =>
    intro a kR vs hk hv hne hn
    have A := adv a kR vs hk hv hne
    cases h1 : incV vs with
    | some vs' =>
      obtain ⟨e1, e2, e3, e4⟩ := incV_some vs vs' hv h1
      have hne' : vs' ≠ [] := incV_ne vs vs' h1
      have := ih (a + 1) kR vs' hk e4 hne' (by rw [e1, e2]; omega)
      rw [e3, show a + 1 + n = a + (n + 1) by omega] at this
      exact Rch.tr (A.1 vs' h1) this
    | none =>
      have h3 := incV_none vs hv h1
      cases h2 : incK kR with
      | some k' =>
        obtain ⟨e1, e2, e3, e4⟩ := incK_some kR k' hk h2
        have := ih (a + 1) k' (zv vs) e4 (zv_ok hv) (zv_ne hne)
          (by rw [vV_zv, pV_zv, e1, e2]; rw [Nat.mul_succ] at *; omega)
        rw [zv_zv, e3, show a + 1 + n = a + (n + 1) by omega] at this
        exact Rch.tr (A.2.1 h1 k' h2) this
      | none =>
        exfalso; have h4 := incK_none kR hk h2
        have : pV vs * pK kR = pV vs * vK kR + pV vs := by rw [← h4, Nat.mul_succ]
        omega

theorem vK_rs : ∀ l : List KB, rsK l = l → vK l = 0
  | [], _ => rfl
  | .pl n :: l, h => by simp only [rsK, List.cons.injEq, true_and] at h; simp [vK, vK_rs l h]
  | .dg f c :: l, h => by
    simp only [rsK, List.cons.injEq, KB.dg.injEq, true_and] at h
    simp [vK, vK_rs l h.2, ← h.1]

theorem pV_pos : ∀ l : List (Nat × Nat), (∀ d ∈ l, VOk d) → 1 ≤ pV l
  | [], _ => Nat.le_refl _
  | (f, p) :: l, h => by
    have := pV_pos l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hd := h (f, p) (List.mem_cons_self _ _)
    simp only [pV]; exact Nat.mul_le_mul hd.1 this

theorem pK_pos : ∀ l : List KB, (∀ b ∈ l, b.ok) → 1 ≤ pK l
  | [], _ => Nat.le_refl _
  | .pl n :: l, h => by simpa [pK] using pK_pos l (fun x hx => h x (List.mem_cons_of_mem _ hx))
  | .dg f c :: l, h => by
    have := pK_pos l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hd := h (.dg f c) (List.mem_cons_self _ _); simp only [KB.ok] at hd
    have hf : 1 ≤ f := by omega
    simp only [pK]; exact Nat.mul_le_mul hf this

/-- **The run.** From `AL1` anywhere on the tape (var digits at 0, K digits at rest), the
accumulator gains the product of all digits' factors -/
theorem run (a : Nat) (kR : List KB) (vs : List (Nat × Nat)) (hk : ∀ b ∈ kR, b.ok) (hv : ∀ d ∈ vs, VOk d)
    (hne : vs ≠ []) (hz : zv vs = vs) (hr : rsK kR = kR)
    (x : Bool) (u r : List Bool) (hr' : r ≠ []) (hW : u.reverse ++ x :: r = TW a kR vs) :
    Rch ⟨AL1, app u blank, x ::: app r blank⟩ (ENDc (TW (a + pV vs * pK kR) kR vs)) := by
  refine Rch.tr (count1' x u r a kR vs hk hv hr' hW) ?_
  have h0 : vV vs = 0 := by rw [← hz]; exact vV_zv vs
  have h1 := vK_rs kR hr
  have := count (pV vs * pK kR - 1) (a + 1) kR vs hk hv hne (by rw [h0, h1]; simp)
  rw [hr, hz] at this
  have := Nat.mul_le_mul (pV_pos vs hv) (pK_pos kR hk)
  rwa [show a + 1 + (pV vs * pK kR - 1) = a + pV vs * pK kR by omega] at *

end TM.LehmerTau
