import TinyCryptids.Singmaster.Compare

/-!
# The scan over the triangle

The triangle right of N is a list of items `(s, v)`: `s` zeros (2 between entries of a row,
3 before a row), then the block of `v`.  The scan compares each entry with N in turn.
-/

namespace TM.Singmaster
open St TinyCryptids

local notation "F" => false
local notation "T" => true
local notation "rep" => List.replicate

def blk (v : Nat) : List Bool := rep (v + 2) T

def itemsW : List (Nat × Nat) → List Bool
  | [] => []
  | (s, v) :: is => rep s F ++ blk v ++ itemsW is

/-- separators of two or three 0s, entries at least 1 -/
def IOK (is : List (Nat × Nat)) : Prop := ∀ x ∈ is, (x.1 = 2 ∨ x.1 = 3) ∧ 1 ≤ x.2

theorem itemsW_append (is js : List (Nat × Nat)) : itemsW (is ++ js) = itemsW is ++ itemsW js := by
  induction is with
  | nil => rfl
  | cons x is ih => obtain ⟨s, v⟩ := x; simp [itemsW, ih]

theorem gc_fwd : ∀ (is : List (Nat × Nat)), IOK is → ∀ (k : Nat) (l : List Bool), GC l →
    GC (itemsW is ++ rep (k + 2) F ++ T :: l)
  | [], _, k, l, hl => by simpa [itemsW, List.replicate_succ] using GC.gap k hl
  | (s, v) :: is, h, k, l, hl => by
    have ih := gc_fwd is (fun x hx => h x (List.mem_cons_of_mem _ hx)) k l hl
    obtain ⟨hs, _⟩ := h (s, v) (List.mem_cons_self _ _)
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by simp at hs; omega⟩
    have := GC.gap s' (GC.rep (v + 1) ih)
    simpa [itemsW, blk, List.replicate_succ] using this

theorem gc_rev : ∀ (is : List (Nat × Nat)), IOK is → ∀ (k : Nat) (l : List Bool), GC l →
    GC (rep (k + 2) F ++ (itemsW is).reverse ++ T :: l)
  | [], _, k, l, hl => by simpa [itemsW, List.replicate_succ] using GC.gap k hl
  | (s, v) :: is, h, k, l, hl => by
    obtain ⟨hs, _⟩ := h (s, v) (List.mem_cons_self _ _)
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by simp at hs; omega⟩
    have hl' : GC (rep (v + 1) T ++ rep (s' + 2) F ++ T :: l) := by
      rw [List.append_assoc]; exact GC.rep _ (by simpa [List.replicate_succ] using GC.gap s' hl)
    have := gc_rev is (fun x hx => h x (List.mem_cons_of_mem _ hx)) k _ hl'
    simpa [itemsW, blk, List.replicate_succ, List.reverse_replicate] using this

theorem dok (is : List (Nat × Nat)) (h : IOK is) (k : Nat) : DOK (itemsW is ++ rep (k + 2) F) :=
  ⟨fun l hl => by simpa using gc_fwd is h k l hl,
   fun l hl => by simpa using gc_rev is h k l hl⟩

theorem dhead : ∀ (is : List (Nat × Nat)), IOK is → ∀ k, ∃ D0, itemsW is ++ rep (k + 2) F = F :: D0
  | [], _, k => ⟨rep (k + 1) F, by simp [itemsW, List.replicate_succ]⟩
  | (s, v) :: is, h, k => by
    obtain ⟨hs, _⟩ := h (s, v) (List.mem_cons_self _ _)
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by simp at hs; omega⟩
    exact ⟨rep s' F ++ blk v ++ itemsW is ++ rep (k + 2) F, by simp [itemsW, List.replicate_succ]⟩

/-- on the first cell after the block of the last scanned item -/
def sc (W : List Bool) (c N : Nat) (Y : List Bool) : Cfg St :=
  cl FE2 (W.reverse ++ (Nw N 1).reverse ++ XL c) Y

/-- the end of the triangle, start of the next row -/
def endc (W : List Bool) (c N : Nat) : Cfg St :=
  cl G1 (T :: F :: F :: F :: W.reverse ++ (Nw N 1).reverse ++ XL c) []

theorem cross (W : List Bool) (c N s v : Nat) (Y : List Bool) (hs : s = 2 ∨ s = 3) :
    Rch (sc W c N (rep s F ++ blk v ++ Y)) (atE (W ++ rep s F) c N v Y) := by
  unfold sc atE blk
  rcases hs with rfl | rfl
  · simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
    gr; gr; gr; lfin
  · simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
    gr; gr; gr; gr; lfin

theorem to_end (W : List Bool) (c N : Nat) : Rch (sc W c N []) (endc W c N) := by
  unfold sc endc
  rw [cl_padR _ _ [] 4]
  simp only [List.replicate_succ, List.replicate_zero, List.nil_append]
  gr; gr; gr; gr; lfin

def cntv (N : Nat) (is : List (Nat × Nat)) : Nat := (is.filter (fun x => x.2 == N)).length

/-- the rest of the tape after an entry starts with a 0 (a separator, or blank) -/
theorem yF (is : List (Nat × Nat)) (h : IOK is) : ∃ Y', ∀ q L A,
    cl q L (A ++ itemsW is) = cl q L (A ++ F :: Y') := by
  cases is with
  | nil => exact ⟨[], fun q L A => by simpa [itemsW] using cl_padR q L A 1⟩
  | cons x is =>
    obtain ⟨s, v⟩ := x
    obtain ⟨hs, _⟩ := h (s, v) (List.mem_cons_self _ _)
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by simp at hs; omega⟩
    exact ⟨rep s' F ++ blk v ++ itemsW is, fun q L A => by simp [itemsW, List.replicate_succ]⟩

theorem cntv_cons (N s v : Nat) (is : List (Nat × Nat)) :
    cntv N ((s, v) :: is) = (if v = N then 1 else 0) + cntv N is := by
  by_cases h : v = N <;> simp [cntv, List.filter_cons, h] <;> omega

theorem scan (N : Nat) (hN : 1 ≤ N) : ∀ (is done : List (Nat × Nat)) (c : Nat), c ≤ 6 → IOK is → IOK done →
    (c + cntv N is ≤ 6 → Rch (sc (itemsW done) c N (itemsW is)) (endc (itemsW (done ++ is)) (c + cntv N is) N)) ∧
    (7 ≤ c + cntv N is → HaltAt (sc (itemsW done) c N (itemsW is)))
  | [], done, c, hc, _, _ => by
    refine ⟨fun _ => ?_, fun h => by simp [cntv] at h; omega⟩
    simpa [cntv] using to_end (itemsW done) c N
  | (s, v) :: is, done, c, hc, h, hd => by
    obtain ⟨hs, hv'⟩ := h (s, v) (List.mem_cons_self _ _)
    have h' : IOK is := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hd' : IOK (done ++ [(s, v)]) := by
      intro x hx; rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hd x hx
      · simp at hx; subst hx; exact ⟨hs, hv'⟩
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
    obtain ⟨D0, hD0⟩ := dhead done hd s'
    have hD := dok done hd s'
    rw [hD0] at hD
    have hx := cross (itemsW done) c N (s' + 2) v (itemsW is) hs
    rw [hD0] at hx
    -- the rest of the tape starts with a separator or is blank
    have hcont : ∀ c', c' + cntv N is ≤ 6 →
        Rch (post (F :: D0) c' N v (itemsW is)) (endc (itemsW (done ++ (s' + 2, v) :: is)) (c' + cntv N is) N) := by
      intro c' hc'
      have e1 : post (F :: D0) c' N v (itemsW is) = sc (itemsW (done ++ [(s' + 2, v)])) c' N (itemsW is) := by
        unfold post sc; rw [← hD0, itemsW_append]; simp [itemsW, blk]
      rw [e1]
      have := (scan N hN is (done ++ [(s' + 2, v)]) c' (by omega) h' hd').1 hc'
      simpa using this
    have hcontH : ∀ c', c' ≤ 6 → 7 ≤ c' + cntv N is → HaltAt (post (F :: D0) c' N v (itemsW is)) := by
      intro c' hc6 hc'
      have e1 : post (F :: D0) c' N v (itemsW is) = sc (itemsW (done ++ [(s' + 2, v)])) c' N (itemsW is) := by
        unfold post sc; rw [← hD0, itemsW_append]; simp [itemsW, blk]
      rw [e1]; exact (scan N hN is (done ++ [(s' + 2, v)]) c' (by omega) h' hd').2 hc'
    obtain ⟨Y', hY⟩ := yF is h'
    have hatE : ∀ c', atE (F :: D0) c' N v (itemsW is) = atE (F :: D0) c' N v (F :: Y') :=
      fun c' => hY _ _ _
    have hpost : ∀ c', post (F :: D0) c' N v (itemsW is) = post (F :: D0) c' N v (F :: Y') := by
      intro c'; have := hY FE2 (rep (v + 2) T ++ (F :: D0).reverse ++ (Nw N 1).reverse ++ XL c') []
      simpa [post] using this
    rw [cntv_cons]
    by_cases hv : v = N
    · subst hv
      simp only [if_true]
      refine ⟨fun hk => Rch.tr hx ?_, fun hk => HaltAt.back hx ?_⟩
      · rw [hatE]; refine Rch.tr (cmp_eq D0 hD c v Y' hN (by omega)) ?_
        rw [← hpost]; have := hcont (c + 1) (by omega); rwa [show c + 1 + cntv v is = c + (1 + cntv v is) by omega] at this
      · rw [hatE]
        rcases Nat.lt_or_ge c 6 with h6 | h6
        · refine HaltAt.back (cmp_eq D0 hD c v Y' hN h6) ?_
          rw [← hpost]; exact hcontH (c + 1) (by omega) (by omega)
        · rw [show c = 6 by omega]; exact cmp_halt D0 hD v Y' hN
    · simp only [hv, if_false, Nat.zero_add]
      refine ⟨fun hk => Rch.tr hx ?_, fun hk => HaltAt.back hx ?_⟩
      · rw [hatE]; refine Rch.tr (cmp_ne D0 hD c N v Y' hN hv' hv) ?_
        rw [← hpost]; exact hcont c hk
      · rw [hatE]; refine HaltAt.back (cmp_ne D0 hD c N v Y' hN hv' hv) ?_
        rw [← hpost]; exact hcontH c hc hk
