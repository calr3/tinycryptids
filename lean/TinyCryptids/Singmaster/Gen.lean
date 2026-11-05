import TinyCryptids.Singmaster.Scan

/-!
# Building the next row

The source row is read right to left; its blocks already processed are `P` (left to right),
the current block `x` has a hole at `h`; the new row (values `ws`) is at the end of the tape:

    Q  x(hole at h)  00 P₁ 00 P₂ …  000  newrow
-/

namespace TM.Singmaster
open St TinyCryptids

local notation "F" => false
local notation "T" => true
local notation "rep" => List.replicate

def rowW : List Nat → List Bool
  | [] => []
  | w :: ws => blk w ++ itemsW (ws.map (2, ·))

def Bh (x h : Nat) : List Bool := rep h T ++ F :: rep (x + 1 - h) T

def pW (P : List Nat) : List Bool := itemsW (P.map (2, ·))

theorem rowW_snoc : ∀ (ws : List Nat) (a b : Nat),
    rowW (ws ++ [a, b]) = rowW (ws ++ [a]) ++ F :: F :: blk b
  | [], a, b => by simp [rowW, itemsW]
  | w :: ws, a, b => by
    simp only [List.cons_append, rowW, List.map_append, itemsW_append, List.map_cons, List.map_nil]
    simp [itemsW]

theorem rowW_succ : ∀ (ws : List Nat) (a : Nat),
    (rowW (ws ++ [a + 1])).reverse = T :: (rowW (ws ++ [a])).reverse
  | [], a => by simp [rowW, itemsW, blk, List.replicate_succ]
  | w :: ws, a => by
    simp only [List.cons_append, rowW, List.map_append, itemsW_append, List.map_cons, List.map_nil]
    simp [itemsW, blk, List.replicate_succ]

/-! ## WC and GC facts -/

def SOK (is : List (Nat × Nat)) : Prop := ∀ x ∈ is, x.1 = 2 ∨ x.1 = 3

theorem sok_p (P : List Nat) : SOK (P.map (2, ·)) := by
  intro x hx; simp only [List.mem_map] at hx
  obtain ⟨v, _, rfl⟩ := hx; exact Or.inl rfl

theorem wc_items : ∀ (is : List (Nat × Nat)), SOK is → ∀ l, WC l → WC (itemsW is ++ l)
  | [], _, l, hl => hl
  | (s, v) :: is, h, l, hl => by
    have hs := h (s, v) (List.mem_cons_self _ _)
    have ih := wc_items is (fun x hx => h x (List.mem_cons_of_mem _ hx)) l hl
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by simp at hs; omega⟩
    have := WC.gap s' (by simp at hs; omega) (WC.append (WC.replicate (v + 1)) ih)
    simpa [itemsW, blk, List.replicate_succ] using this

theorem wc_row (ws : List Nat) (l : List Bool) (hl : WC l) : WC (rowW ws ++ l) := by
  cases ws with
  | nil => exact hl
  | cons w ws =>
    have := wc_items (ws.map (2, ·)) (sok_p ws) l hl
    simpa [rowW, blk, List.append_assoc] using WC.append (WC.replicate (w + 2)) this

theorem gc_rev0 : ∀ (is : List (Nat × Nat)), SOK is → ∀ l, GC l → GC ((itemsW is).reverse ++ T :: l)
  | [], _, l, hl => GC.one hl
  | (s, v) :: is, h, l, hl => by
    have hs := h (s, v) (List.mem_cons_self _ _)
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by simp at hs; omega⟩
    have hl' : GC (rep (v + 1) T ++ rep (s' + 2) F ++ T :: l) := by
      rw [List.append_assoc]; exact GC.rep _ (by simpa [List.replicate_succ] using GC.gap s' hl)
    have := gc_rev0 is (fun x hx => h x (List.mem_cons_of_mem _ hx)) _ hl'
    simpa [itemsW, blk, List.replicate_succ, List.reverse_replicate] using this

theorem gc_rev3 : ∀ (is : List (Nat × Nat)), SOK is → ∀ (k : Nat) (l : List Bool), GC l →
    GC (rep (k + 2) F ++ (itemsW is).reverse ++ T :: l)
  | [], _, k, l, hl => by simpa [itemsW, List.replicate_succ] using GC.gap k hl
  | (s, v) :: is, h, k, l, hl => by
    have hs := h (s, v) (List.mem_cons_self _ _)
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by simp at hs; omega⟩
    have hl' : GC (rep (v + 1) T ++ rep (s' + 2) F ++ T :: l) := by
      rw [List.append_assoc]; exact GC.rep _ (by simpa [List.replicate_succ] using GC.gap s' hl)
    have := gc_rev3 is (fun x hx => h x (List.mem_cons_of_mem _ hx)) k _ hl'
    simpa [itemsW, blk, List.replicate_succ, List.reverse_replicate] using this

/-- what `sP` crosses on its way back to the source hole -/
theorem gc_back (vs P : List Nat) (k : Nat) (l : List Bool) (hl : GC l) :
    GC ((rowW vs).reverse ++ rep 3 F ++ (pW P).reverse ++ rep (k + 1) T ++ l) := by
  have h3 : GC (rep 3 F ++ (pW P).reverse ++ T :: (rep k T ++ l)) :=
    gc_rev3 _ (sok_p P) 1 _ (GC.rep k hl)
  cases vs with
  | nil => simpa [rowW, List.replicate_succ] using h3
  | cons w ws =>
    have h4 : GC (rep (w + 1) T ++ (rep 3 F ++ (pW P).reverse ++ T :: (rep k T ++ l))) := GC.rep _ h3
    have := gc_rev0 (ws.map (2, ·)) (sok_p ws) _ h4
    simpa [rowW, blk, List.replicate_succ, List.reverse_replicate] using this

theorem wc3_row (w : Nat) (ws : List Nat) (l : List Bool) (hl : WC l) :
    WC (rep 3 F ++ (rowW (w :: ws) ++ l)) := by
  have := WC.gap 2 (by omega) (WC.append (WC.replicate (w + 1))
    (wc_items (ws.map (2, ·)) (sok_p ws) l hl))
  simpa [rowW, blk, List.replicate_succ] using this

theorem rowW_ne (ws0 : List Nat) (a : Nat) (l : List Nat) : ∃ w ws, ws0 ++ a :: l = w :: ws := by
  cases ws0 <;> exact ⟨_, _, rfl⟩

/-! ## the steps -/

/-- at the second-to-last cell of source block `x`, before its first cell is copied -/
def g7 (x : Nat) (Q : List Bool) (P ws : List Nat) : Cfg St :=
  cl G7 (rep x T ++ Q) (T :: T :: pW P ++ rep 3 F ++ rowW ws)

/-- back in the new row (`rowW vs` up to the head, `Rz` after it), the source hole at `h` -/
def spc (vs : List Nat) (Rz : List Bool) (P : List Nat) (x h : Nat) (Q : List Bool) : Cfg St :=
  cL sP ((rowW vs).reverse ++ rep 3 F ++ (pW P).reverse ++ (Bh x h).reverse ++ Q) Rz

/-- the first cell of a source block: `1 00 111` after the last 1 -/
theorem trans (x : Nat) (Q : List Bool) (P : List Nat) (w : Nat) (ws : List Nat) :
    Rch (g7 x Q P (w :: ws)) (spc (w :: ws) [T, F, F, T, T, T] P x x Q) := by
  unfold g7 spc
  gr
  have hw : WC (T :: (pW P ++ rep 3 F ++ rowW (w :: ws))) := by
    refine WC.one ?_
    rw [List.append_assoc]
    refine wc_items _ (sok_p P) _ ?_
    have := WC.gap 2 (by omega) (wc_row ws [] WC.nil |> fun h => WC.append (WC.replicate (w + 1))
      (by simpa [rowW] using wc_items (ws.map (2, ·)) (sok_p ws) [] WC.nil))
    simpa [rowW, blk, List.replicate_succ] using this
  refine Rch.tr (w4_cross' WT_ hw _ [] (by simp)) ?_
  rw [cl_padR _ _ _ 7]
  simp only [List.nil_append, List.replicate_succ, List.replicate_zero]
  gr; gr; gr; gr; gr; gl; gl; gl; gl; gl; glc
  rw [← cL_padR _ _ [T, F, F, T, T, T] 1]
  simp [Bh, show x + 1 - x = 1 by omega]
  fin

/-- another cell of the source block: the last two blocks of the new row grow by one -/
theorem back_ok (vs : List Nat) (Rz : List Bool) (P : List Nat) (x h : Nat) (Q : List Bool)
    (ws0 : List Nat) (a b : Nat) (hrow : rowW vs ++ Rz = rowW (ws0 ++ [a, b]))
    (h2 : 2 ≤ h) (hx : h ≤ x) :
    Rch (spc vs Rz P x h Q) (spc (ws0 ++ [a + 1]) (F :: F :: blk (b + 1)) P x (h - 1) Q) := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 2 := ⟨h - 2, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, x + 1 - (h' + 2) = k + 1 := ⟨x - h' - 2, by omega⟩
  unfold spc
  have hw := gc_back vs P k [] GC.nil
  rw [List.append_nil] at hw
  refine Rch.tr (fl_crossE FS_ hw (F :: rep (h' + 2) T ++ Q) Rz (by simp [Bh, hk, List.reverse_replicate])) ?_
  rw [List.cons_append, ← cl_cL]
  simp only [List.replicate_succ, List.cons_append]
  gl; gr; gl; gl; gr; gr
  have hw2 : WC (T :: (rep (k + 1) T ++ (pW P ++ (rep 3 F ++ (rowW vs ++ Rz))))) := by
    rw [hrow]
    obtain ⟨w, ws, hws⟩ := rowW_ne ws0 a [b]
    rw [hws]
    have h3 := wc3_row w ws [] WC.nil
    rw [List.append_nil] at h3
    exact WC.one (WC.append (WC.replicate _) (wc_items _ (sok_p P) _ h3))
  refine Rch.tr (w4_cross' WW_ hw2 _ [] (by simp [List.reverse_replicate, List.replicate_succ])) ?_
  rw [cl_padR _ _ _ 4, hrow, rowW_snoc]
  simp only [List.replicate_succ, List.replicate_zero, List.nil_append, List.reverse_cons,
    List.reverse_append, List.append_assoc, List.cons_append, blk, List.reverse_replicate,
    List.singleton_append, List.reverse_nil, rep_cons']
  gr; gr; gr; gl; gl; gl; gl; gl
  rw [cl_cL]
  refine Rch.tr (sln' (q := R4) rfl (b + 1) _ _ rfl) ?_
  rw [← cl_cL]
  gl; gr; gr; gl; glc
  rw [rowW_succ, show h' + 2 - 1 = h' + 1 by omega]
  simp [Bh, blk, List.replicate_succ, List.reverse_replicate, show x + 1 - (h' + 1) = k + 2 by omega]
  rw [show F :: F :: T :: T :: T :: (rep b T ++ [F, F]) = (F :: F :: T :: T :: T :: rep b T) ++
    rep 2 F by simp [List.replicate_succ], cL_padR]
  fin

theorem back_exh (vs : List Nat) (Rz : List Bool) (P : List Nat) (x : Nat) (Q1 : List Bool)
    (hx : 1 ≤ x) :
    Rch (spc vs Rz P x 1 (F :: F :: Q1))
      (cL Y3 Q1 (F :: F :: blk x ++ pW P ++ rep 3 F ++ rowW vs ++ Rz)) := by
  obtain ⟨k, rfl⟩ : ∃ k, x = k + 1 := ⟨x - 1, by omega⟩
  unfold spc
  have hw := gc_back vs P k [] GC.nil
  rw [List.append_nil] at hw
  refine Rch.tr (fl_crossE FS_ hw (F :: T :: F :: F :: Q1) Rz (by simp [Bh, List.reverse_replicate])) ?_
  rw [← cl_cL]
  gl; gr; gl; gl; glc
  rw [← cl_cL]; glc
  simp [blk, List.replicate_succ, List.reverse_replicate]; fin

theorem y3_next (x' : Nat) (Q2 Rw : List Bool) :
    Rch (cL Y3 (rep (x' + 2) T ++ Q2) Rw) (cl G7 (rep x' T ++ Q2) (T :: T :: Rw)) := by
  show Rch (cL Y3 (T :: T :: (rep x' T ++ Q2)) Rw) _
  rw [← cl_cL]; gl; fin

theorem y3_done (Q2 Rw : List Bool) :
    Rch (cL Y3 (F :: Q2) Rw) (cL gP Q2 (F :: Rw)) := by
  rw [← cl_cL]; glc; fin

theorem rowW_succ' (ws : List Nat) (a : Nat) : rowW (ws ++ [a + 1]) = rowW (ws ++ [a]) ++ [T] := by
  have := congrArg List.reverse (rowW_succ ws a)
  simpa using this

theorem steps (vs0 : List Nat) (Rz0 : List Bool) (P : List Nat) (x : Nat) (Q : List Bool)
    (ws0 : List Nat) (u : Nat) (h0 : rowW vs0 ++ Rz0 = rowW (ws0 ++ [u + 1, 1])) :
    ∀ i, i + 1 ≤ x → ∃ vs Rz, rowW vs ++ Rz = rowW (ws0 ++ [u + 1 + i, 1 + i]) ∧
      Rch (spc vs0 Rz0 P x x Q) (spc vs Rz P x (x - i) Q)
  | 0, _ => ⟨vs0, Rz0, by simpa using h0, Reach.refl delta _⟩
  | i + 1, hi => by
    obtain ⟨vs, Rz, hr, hR⟩ := steps vs0 Rz0 P x Q ws0 u h0 i (by omega)
    refine ⟨ws0 ++ [u + 1 + i + 1], F :: F :: blk (1 + i + 1), ?_, Rch.tr hR ?_⟩
    · rw [rowW_snoc]; rfl
    · have := back_ok vs Rz P x (x - i) Q ws0 (u + 1 + i) (1 + i) hr (by omega) (by omega)
      rwa [show x - i - 1 = x - (i + 1) by omega] at this

/-- one source block: its cells are copied into the last two blocks of the new row -/
theorem block (x : Nat) (Q : List Bool) (P ws0 : List Nat) (u : Nat) (hx : 1 ≤ x) :
    ∃ vs Rz, rowW vs ++ Rz = rowW (ws0 ++ [u + x, x]) ∧
      Rch (g7 x Q P (ws0 ++ [u])) (spc vs Rz P x 1 Q) := by
  obtain ⟨w, ws, hws⟩ := rowW_ne ws0 u []
  have ht := trans x Q P w ws
  rw [← hws] at ht
  have h0 : rowW (ws0 ++ [u]) ++ [T, F, F, T, T, T] = rowW (ws0 ++ [u + 1, 1]) := by
    rw [rowW_snoc, rowW_succ']; simp [blk]
  obtain ⟨vs, Rz, hr, hR⟩ := steps _ _ P x Q ws0 u h0 (x - 1) (by omega)
  refine ⟨vs, Rz, ?_, Rch.tr ht ?_⟩
  · rw [hr, show u + 1 + (x - 1) = u + x by omega, show 1 + (x - 1) = x by omega]
  · rwa [show x - (x - 1) = 1 by omega] at hR

/-- the next row, left to right, from `y₀, y₁, …` taken right to left -/
def pas (u : Nat) : List Nat → List Nat
  | [] => [u]
  | y :: ys => (u + y) :: pas y ys

theorem pascal_pas (ys : List Nat) : pascal ys = pas 0 ys := by
  suffices h : ∀ u, List.zipWith (· + ·) (ys ++ [0]) (u :: ys) = pas u ys by exact h 0
  induction ys with
  | nil => intro u; simp [pas]
  | cons y ys ih => intro u; simp [pas, ih, Nat.add_comm]

/-- left of the current source block: its separator, then the unprocessed blocks (nearest first) -/
def Qof (Far : List Bool) : List Nat → List Bool
  | [] => F :: F :: F :: Far
  | x :: r => F :: F :: rep (x + 2) T ++ Qof Far r

theorem gen_row (Far : List Bool) : ∀ (r : List Nat) (x : Nat) (P ws0 : List Nat) (u : Nat),
    1 ≤ x → (∀ y ∈ r, 1 ≤ y) →
    Rch (g7 x (Qof Far r) P (ws0 ++ [u]))
      (cL gP Far (F :: F :: F :: rowW (r.reverse ++ x :: P) ++ rep 3 F ++ rowW (ws0 ++ pas u (x :: r))))
  | [], x, P, ws0, u, hx, _ => by
    obtain ⟨vs, Rz, hr, hR⟩ := block x (Qof Far []) P ws0 u hx
    refine Rch.tr hR (Rch.tr (back_exh vs Rz P x (F :: Far) hx) ?_)
    refine Rch.tr (y3_done _ _) ?_
    simp only [List.append_assoc] at hr ⊢
    rw [hr]; simp [pas, rowW, pW, List.append_assoc]; fin
  | y :: r, x, P, ws0, u, hx, hr => by
    obtain ⟨vs, Rz, hrow, hR⟩ := block x (Qof Far (y :: r)) P ws0 u hx
    refine Rch.tr hR (Rch.tr (back_exh vs Rz P x _ hx) ?_)
    refine Rch.tr (y3_next y (Qof Far r) _) ?_
    have ih := gen_row Far r y (x :: P) (ws0 ++ [u + x]) x (hr y (List.mem_cons_self _ _))
      (fun z hz => hr z (List.mem_cons_of_mem _ hz))
    have e1 : (T :: T :: (F :: F :: blk x ++ pW P ++ rep 3 F ++ rowW vs ++ Rz)) =
        T :: T :: pW (x :: P) ++ rep 3 F ++ rowW ((ws0 ++ [u + x]) ++ [x]) := by
      simp only [List.append_assoc] at hrow ⊢
      rw [hrow]; simp [pW, itemsW, List.append_assoc]
    rw [e1]
    refine Rch.tr ih ?_
    simp [pas, List.append_assoc]; fin

theorem qof_row' (Far : List Bool) : ∀ (r : List Nat) (x : Nat),
    (rowW (r.reverse ++ [x])).reverse ++ F :: F :: F :: Far = rep (x + 2) T ++ Qof Far r
  | [], x => by simp [rowW, itemsW, blk, Qof]
  | y :: r, x => by
    have e : (y :: r).reverse ++ [x] = r.reverse ++ [y, x] := by simp
    rw [e, rowW_snoc r.reverse y x]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.append_assoc, List.singleton_append, List.cons_append]
    rw [qof_row' Far r y]
    simp [Qof, blk, List.reverse_replicate]

theorem qof_row (Far : List Bool) (init : List Nat) (x : Nat) :
    (rowW (init ++ [x])).reverse ++ F :: F :: F :: Far = rep (x + 2) T ++ Qof Far init.reverse := by
  have := qof_row' Far init.reverse x
  rwa [List.reverse_reverse] at this

def rowItems : List Nat → List (Nat × Nat)
  | [] => []
  | v :: vs => (3, v) :: vs.map (2, ·)

theorem itemsW_row (vs : List Nat) (h : vs ≠ []) : itemsW (rowItems vs) = rep 3 F ++ rowW vs := by
  cases vs with
  | nil => exact absurd rfl h
  | cons v vs => simp [rowItems, itemsW, rowW]

/-- from the end of the scan to the first cell of the last source block -/
theorem gen_start (I : List (Nat × Nat)) (init : List Nat) (x c N : Nat) :
    Rch (endc (itemsW (I ++ rowItems (init ++ [x]))) c N)
      (g7 x (Qof ((itemsW I).reverse ++ (Nw N 1).reverse ++ XL c) init.reverse) [] [0]) := by
  unfold endc g7
  rw [itemsW_append, itemsW_row _ (by simp)]
  rw [cl_padR _ _ _ 1]
  simp only [List.nil_append, List.replicate_succ, List.replicate_zero]
  gl; gl
  rw [cl_cL]
  refine Rch.tr (slz (q := G3) rfl 3 _ _) ?_
  have e := qof_row ((itemsW I).reverse ++ (Nw N 1).reverse ++ XL c) init x
  simp only [List.append_assoc] at e
  norm
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_assoc, List.cons_append, List.singleton_append]
  rw [e]
  show Rch (cL G3 (T :: T :: (rep x T ++ _)) _) _
  rw [← cl_cL]; gl
  simp [pW, itemsW, rowW, blk]; fin

/-- the row is done: N += 1 (C moves one cell left), C's hole back to cell 1, to N's end -/
theorem gen_end (I : List (Nat × Nat)) (hI : SOK I) (R : List Bool) (c N : Nat) (hc : c ≤ 6)
    (hN : 1 ≤ N) :
    Rch (cL gP ((itemsW I).reverse ++ (Nw N 1).reverse ++ XL c) (F :: F :: F :: R))
      (sc [] 0 (N + 1) (itemsW I ++ F :: F :: F :: R)) := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, 7 - c = j + 1 := ⟨6 - c, by omega⟩
  have hw := gc_rev0 I hI [] GC.nil
  refine Rch.tr (fl_crossE FG_ hw (F :: rep (N' + 1) T ++ XL c) _ (by simp [Nw_rev])) ?_
  rw [List.cons_append, ← cl_cL]
  simp only [List.replicate_succ, List.cons_append]
  gl; glc
  refine Rch.tr (sln' (q := GN1) rfl N' _ _ rfl) ?_
  simp only [XL, Cw, List.reverse_append, List.reverse_cons, List.reverse_replicate, hj,
    List.replicate_succ, List.cons_append, List.append_assoc, List.singleton_append]
  rw [← cl_cL]
  lnorm
  gl; glc
  refine Rch.tr (sln' (q := CW2) rfl j _ _ rfl) ?_
  rw [← cl_cL]
  gl; glc
  refine Rch.tr (sln' (q := CW2) rfl c [] _ (by simp)) ?_
  rw [cL_padL _ _ _ 2]
  simp only [List.nil_append, List.replicate_succ, List.replicate_zero]
  rw [← cl_cL]
  lnorm
  gl; gr; gr; gr
  rw [show c + j = 6 by omega]
  refine Rch.tr (srn' (q := CQ) rfl 7 _ _ rfl) ?_
  gr
  refine Rch.tr (fr_cross' FR_ (GC.replicate (N' + 2)) _ _ rfl) ?_
  gr; gr
  unfold sc
  rw [cl_padL _ ([].reverse ++ (Nw (N' + 1 + 1) 1).reverse ++ XL 0) _ 1]
  simp [Nw, XL, Cw, List.reverse_replicate, List.replicate_succ]
  fin

end TM.Singmaster
