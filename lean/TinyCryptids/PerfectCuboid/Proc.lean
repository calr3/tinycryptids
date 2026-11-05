import TinyCryptids.PerfectCuboid.Tac
import TinyCryptids.PerfectCuboid.Spec

/-!
# Processing a block: the counter S, the trips between a block and S, one unit

* `Ev`: lists whose zero-runs come in pairs; the parsers cross them (`crossR`, `crossL`).
* `Sb s`: the counter S for `s = (k, j)`: a leading 1, `2k + 1` cycle cells with the hole
  on cycle cell `j`, a terminator 1, then blank.
* `sadv`: S's step `s ↦ adv s`; `trip`: from the block's side to S and back to its hole `h`.
-/

namespace TM.PerfectCuboid

open St

local notation "F" => false
local notation "T" => true

/-! ## lists with paired zeros -/

inductive Ev : List Bool → Prop
  | nil : Ev []
  | one {l} : Ev l → Ev (T :: l)
  | zz {l} : Ev l → Ev (F :: F :: l)

theorem Ev.append {l m : List Bool} (hl : Ev l) (hm : Ev m) : Ev (l ++ m) := by
  induction hl with
  | nil => exact hm
  | one _ ih => exact Ev.one ih
  | zz _ ih => exact Ev.zz ih

theorem Ev.replicate (n : Nat) : Ev (List.replicate n T) := by
  induction n with
  | zero => exact Ev.nil
  | succ n ih => exact Ev.one ih

theorem Ev.reverse {l : List Bool} (h : Ev l) : Ev l.reverse := by
  induction h with
  | nil => exact Ev.nil
  | @one l _ ih => rw [List.reverse_cons]; exact Ev.append ih (Ev.one Ev.nil)
  | @zz l _ ih =>
    rw [List.reverse_cons, List.reverse_cons, List.append_assoc]
    exact Ev.append ih (Ev.zz Ev.nil)

theorem crossR {p1 p2 : St} (P : ParserR delta p1 p2) {w : List Bool} (hw : Ev w) (L R : Strm) :
    Rch ⟨p1, L, app w R⟩ ⟨p1, app w.reverse L, R⟩ := by
  induction hw generalizing L with
  | nil => fin
  | @one l _ ih =>
    refine Rch.tr (stepR (δ := delta) (R := app (T :: l) R) P.h1) ?_
    simpa [app_append] using ih (T ::: L)
  | @zz l _ ih =>
    refine Rch.tr (stepR (δ := delta) (R := app (F :: F :: l) R) P.h0) ?_
    refine Rch.tr (stepR (δ := delta) (R := app (F :: l) R) P.h2) ?_
    simpa [app_append] using ih (F ::: F ::: L)

theorem crossL {p1 p2 : St} (P : ParserL delta p1 p2) {w : List Bool} (hw : Ev w) (s R : Strm) :
    Rch (cfgL p1 (app w s) R) (cfgL p1 s (app w.reverse R)) := by
  induction hw generalizing R with
  | nil => fin
  | @one l _ ih =>
    refine Rch.tr (stepL' (δ := delta) (s := app (T :: l) s) P.h1) ?_
    simpa [app_append] using ih (T ::: R)
  | @zz l _ ih =>
    refine Rch.tr (stepL' (δ := delta) (s := app (F :: F :: l) s) P.h0) ?_
    refine Rch.tr (stepL' (δ := delta) (s := app (F :: l) s) P.h2) ?_
    simpa [app_append] using ih (F ::: F ::: R)

/-- a right parser crosses `w` and steps over the hole that follows -/
theorem findR {p1 p2 : St} (P : ParserR delta p1 p2) {w : List Bool} (hw : Ev w) (L X : Strm) :
    Rch ⟨p1, L, app w (F ::: X)⟩ ⟨p2, F ::: app w.reverse L, X⟩ :=
  Rch.tr (crossR P hw L _) (stepR (δ := delta) (R := F ::: X) P.h0)

/-- a left parser crosses `w` and steps over the hole that follows -/
theorem findL {p1 p2 : St} (P : ParserL delta p1 p2) {w : List Bool} (hw : Ev w) (s R : Strm) :
    Rch (cfgL p1 (app w (F ::: s)) R) (cfgL p2 s (F ::: app w.reverse R)) :=
  Rch.tr (crossL P hw _ R) (stepL' (δ := delta) (s := F ::: s) P.h0)

/-! ## steps in the `⟨q, L, R⟩` form -/

theorem sL2 {q q' : St} {L R : Strm} {b c w : Bool} (h : delta q b = some (w, Dir.L, q')) :
    Rch ⟨q, c ::: L, b ::: R⟩ ⟨q', L, c ::: w ::: R⟩ := stepL (δ := delta) (L := c ::: L) (R := b ::: R) h

macro "gl" : tactic => `(tactic| refine Rch.tr (sL2 (by rfl)) ?_)

/-- scan left over `n` ones (the head on a 1) -/
theorem scl {q : St} (h : delta q T = some (T, Dir.L, q)) (n : Nat) (L R : Strm) :
    Rch ⟨q, ones n L, T ::: R⟩ ⟨q, L, T ::: ones n R⟩ := by
  rw [← ones_cons_true]
  induction n generalizing R with
  | zero => fin
  | succ n ih =>
    refine Rch.tr (sL2 (L := ones n L) h) ?_
    have := ih (T ::: R); rw [← ones_succ'] at this; exact this

/-- scan right over `n` ones -/
theorem scr {q : St} (h : delta q T = some (T, Dir.R, q)) (n : Nat) (L R : Strm) :
    Rch ⟨q, L, ones n R⟩ ⟨q, ones n L, R⟩ := scanR h n L R

macro "sl" n:term : tactic => `(tactic| refine Rch.tr (scl (by rfl) $n _ _) ?_)
macro "sr" n:term : tactic => `(tactic| refine Rch.tr (scr (by rfl) $n _ _) ?_)

/-! ## a normal form for streams: runs of ones absorb their neighbours -/

theorem cons_ones (n : Nat) (X : Strm) : T ::: ones n X = ones (n + 1) X := rfl
theorem ones_cons (n : Nat) (X : Strm) : ones n (T ::: X) = ones (n + 1) X := (ones_succ' n X).symm

macro "norm" : tactic => `(tactic| simp only [cons_ones, ones_cons, ones_add, Nat.add_assoc])
theorem cons_congr' {b : Bool} {X Y : Strm} (h : X = Y) : b ::: X = b ::: Y := h ▸ rfl
theorem ones_congr' {n m : Nat} {X Y : Strm} (hn : n = m) (h : X = Y) : ones n X = ones m Y :=
  hn ▸ h ▸ rfl

/-- close an equality of streams that differ only in the arithmetic of run lengths -/
macro "streq" : tactic => `(tactic| ((try norm) <;>
  repeat (first | with_reducible rfl | (refine ones_congr' (by omega) ?_) | apply cons_congr')))

theorem rch_eq {q : St} {L L' R R' : Strm} (hL : L = L') (hR : R = R') :
    Rch ⟨q, L, R⟩ ⟨q, L', R'⟩ := by subst hL hR; fin

theorem PL : ParserL delta PL1 PL2 := ⟨rfl, rfl, rfl⟩
theorem PS : ParserR delta PS1 PS2 := ⟨rfl, rfl, rfl⟩

/-! ## the counter -/

def Sr (s : Nat × Nat) : Strm := ones s.2 (F ::: ones (2 * s.1 - s.2) (T ::: blank))
def Sb (s : Nat × Nat) : Strm := T ::: Sr s

/-- S's step, from the cell after the hole (where the right parser stops); back on S's
leading 1 in `PL1` -/
theorem sadv (s : Nat × Nat) (hs : Valid s) (G : Strm) :
    Rch ⟨PS2, F ::: ones s.2 (T ::: F ::: G), ones (2 * s.1 - s.2) (T ::: blank)⟩
      ⟨PL1, F ::: G, Sb (adv s)⟩ := by
  obtain ⟨k, j⟩ := s
  unfold Valid at hs; simp only at hs ⊢
  by_cases hj : j < 2 * k
  · obtain ⟨m, hm⟩ : ∃ m, 2 * k - j = m + 1 := ⟨2 * k - j - 1, by omega⟩
    have : adv (k, j) = (k, j + 1) := by simp [adv, hj]
    rw [this, hm]; unfold Sb Sr; simp only
    rw [show 2 * k - (j + 1) = m by omega]
    norm
    gR; gl; gl; gl
    sl j
    norm
    fin
  · have hj2 : j = 2 * k := by omega
    subst hj2
    have : adv (k, 2 * k) = (k + 1, 0) := by simp [adv]
    rw [this, Nat.sub_self]; unfold Sb Sr; simp only
    rw [show 2 * (k + 1) - 0 = 2 * k + 2 by omega]
    norm
    gR; refine blankR ?_; gR; refine blankR ?_; gl; gl; gl
    rw [show ones (2 * k + 1) (F ::: G) = T ::: ones (2 * k) (F ::: G) from rfl]
    gl
    sl (2 * k)
    gl; gR; gR
    rw [ones_cons_true (2 * k)]
    gl
    norm
    fin

/-! ## the trip: from the block to S, S's step, back to the block's hole -/

theorem PS_findS (w : List Bool) (hw : Ev w) (s : Nat × Nat) (Lft : Strm) :
    Rch ⟨PS1, Lft, app w (Sb s)⟩
      ⟨PS2, F ::: ones s.2 (T ::: app w.reverse Lft), ones (2 * s.1 - s.2) (T ::: blank)⟩ := by
  have e : app w (Sb s) = app (w ++ T :: List.replicate s.2 T) (F ::: ones (2 * s.1 - s.2) (T ::: blank)) := by
    simp [Sb, Sr, app_append, app_replicate]
  rw [e]
  refine Rch.tr (findR PS (Ev.append hw (Ev.one (Ev.replicate _))) Lft _) ?_
  simp [List.reverse_append, app_append, app_replicate, List.reverse_replicate]
  fin

/-- the trip of one unit: the hole `h` (with a 1 left of it), `w1` between `h` and the head,
`w2 ++ [F, F]` up to S -/
theorem trip (w1 w2 : List Bool) (h1 : Ev w1) (h2 : Ev w2) (s : Nat × Nat) (hs : Valid s)
    (Xl : Strm) :
    Rch ⟨PS1, app w1.reverse (F ::: T ::: Xl), app (w2 ++ [F, F]) (Sb s)⟩
      ⟨hA, T ::: Xl, F ::: app w1 (app (w2 ++ [F, F]) (Sb (adv s)))⟩ := by
  refine Rch.tr (PS_findS _ (Ev.append h2 (Ev.zz Ev.nil)) s _) ?_
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.singleton_append, app_cons]
  refine Rch.tr (sadv s hs _) ?_
  have hw : Ev (T :: F :: F :: (w2.reverse ++ w1.reverse)) :=
    Ev.one (Ev.zz (Ev.append (Ev.reverse h2) (Ev.reverse h1)))
  have := findL PL hw (T ::: Xl) (Sr (adv s))
  simp only [app_cons, app_append, cfgL] at this
  refine Rch.tr this ?_
  refine Rch.tr (sR (q := PL2) (by rfl)) ?_
  simp [List.reverse_append, app_append, Sb]
  fin

/-! ## one unit inside a block

During a block's processing its cells are: `a` ones, `m`, the spacer, the region of `2r + 1`
cells with `h` on region cell `t`. Right of the block: `F :: F :: w` (its separator, the
blocks after it, G), then S. -/

def RX (w : List Bool) (s : Nat × Nat) : Strm := F ::: F ::: app (w ++ [F, F]) (Sb s)

def Xw (a r t : Nat) (Lx : Strm) (w : List Bool) (s : Nat × Nat) : Cfg St :=
  ⟨hA, ones t (T ::: F ::: ones a (F ::: F ::: Lx)), F ::: ones (2 * r - t) (RX w s)⟩

/-- the trip from `PS1` with `n` ones of the region still ahead -/
theorem tripX (b : Bool) (hb : b = T) (n : Nat) (w : List Bool) (hw : Ev w) (s : Nat × Nat)
    (hs : Valid s) (Xl : Strm) :
    Rch ⟨PS1, b ::: F ::: T ::: Xl, ones n (RX w s)⟩
      ⟨hA, T ::: Xl, F ::: T ::: ones n (RX w (adv s))⟩ := by
  subst hb
  have := trip [T] (List.replicate n T ++ F :: F :: w) (Ev.one Ev.nil)
    (Ev.append (Ev.replicate n) (Ev.zz hw)) s hs Xl
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, app_cons, app_nil,
    List.append_assoc, List.cons_append, app_append, app_replicate] at this
  simpa [RX, app_append] using this

theorem tripX0 (n : Nat) (w : List Bool) (hw : Ev w) (s : Nat × Nat) (hs : Valid s) (Xl : Strm) :
    Rch ⟨PS1, F ::: T ::: Xl, ones n (RX w s)⟩ ⟨hA, T ::: Xl, F ::: ones n (RX w (adv s))⟩ := by
  have := trip [] (List.replicate n T ++ F :: F :: w) Ev.nil
    (Ev.append (Ev.replicate n) (Ev.zz hw)) s hs Xl
  simp only [List.reverse_nil, app_nil, List.append_assoc, List.cons_append, app_append,
    app_replicate] at this
  simpa [RX, app_append] using this

/-- `h` moves one cell right inside the region -/
theorem u_step (a r t : Nat) (ht : t + 2 ≤ 2 * r) (Lx : Strm) (w : List Bool) (hw : Ev w)
    (s : Nat × Nat) (hs : Valid s) :
    Rch (Xw a r t Lx w s) (Xw a r (t + 1) Lx w (adv s)) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * r - t = n + 2 := ⟨2 * r - t - 2, by omega⟩
  unfold Xw; rw [hn, show 2 * r - (t + 1) = n + 1 by omega]
  gR; gR; gR
  refine Rch.tr (tripX T rfl n w hw s hs _) ?_
  fin

/-- the block with only `h` (on its last cell): no region is left -/
def XE (L : Nat) (Lx : Strm) (w : List Bool) (s : Nat × Nat) : Cfg St :=
  ⟨hA, ones (L - 1) (F ::: F ::: Lx), F ::: RX w s⟩

/-- after `h` arrived home (the head on the separator): `m` moves two cells left, or the
block has no further region -/
theorem grow (a r : Nat) (ha : 1 ≤ a) (Lx : Strm) (w : List Bool) (hw : Ev w) (s : Nat × Nat)
    (hs : Valid s) :
    Rch ⟨hC, F ::: ones (2 * r) (T ::: F ::: ones a (F ::: F ::: Lx)), RX w s⟩
      (if 3 ≤ a then Xw (a - 2) (r + 1) (2 * r + 2) Lx w (adv s)
       else XE (a + 2 * r + 3) Lx w (adv s)) := by
  unfold RX
  gl
  rw [ones_cons_true (2 * r)]
  gl
  sl (2 * r)
  gl
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [ones_succ]
  gl
  rcases Nat.lt_or_ge a' 2 with h2 | h2
  · rw [if_neg (by omega)]
    unfold XE
    rcases Nat.lt_or_ge a' 1 with h1 | h1
    · obtain rfl : a' = 0 := by omega
      gl; gR
      norm
      sr (2 * r + 3)
      gR
      have := tripX0 0 w hw s hs (ones (2 * r + 2) (F ::: F ::: Lx))
      simp only [ones_zero, RX] at this
      refine Rch.tr this ?_
      apply rch_eq <;> streq
    · obtain rfl : a' = 1 := by omega
      gl; gl; gR
      norm
      sr (2 * r + 4)
      gR
      have := tripX0 0 w hw s hs (ones (2 * r + 3) (F ::: F ::: Lx))
      simp only [ones_zero, RX] at this
      refine Rch.tr this ?_
      apply rch_eq <;> streq
  · rw [if_pos (by omega)]
    obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by omega⟩
    rw [ones_succ, ones_succ]
    gl; gl; gR; gR
    norm
    sr (2 * r + 3)
    gR
    have := tripX0 0 w hw s hs (ones (2 * r + 2) (F ::: ones (b + 1) (F ::: F ::: Lx)))
    simp only [ones_zero, RX] at this
    unfold Xw
    rw [show b + 2 + 1 - 2 = b + 1 by omega, show 2 * (r + 1) - (2 * r + 2) = 0 by omega]
    refine Rch.tr ?_ (Rch.tr this ?_)
    · apply rch_eq <;> streq
    · simp only [ones_zero, RX]; apply rch_eq <;> streq

/-- `h` home with `r ≥ 1`: it moves to the region's first cell -/
theorem u_wrap (a r : Nat) (ha : 1 ≤ a) (hr : 1 ≤ r) (Lx : Strm) (w : List Bool) (hw : Ev w)
    (s : Nat × Nat) (hs : Valid s) :
    Rch (Xw a r (2 * r) Lx w s) (Xw a r 0 Lx w (adv s)) := by
  unfold Xw RX
  rw [Nat.sub_self, ones_zero]
  gR; gl
  norm
  sl (2 * r + 1)
  gl
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [ones_succ]
  gl; gR; gR; gR
  obtain ⟨n, hn⟩ : ∃ n, 2 * r = n + 1 := ⟨2 * r - 1, by omega⟩
  rw [hn]
  gR; gR
  have := tripX T rfl n w hw s hs (F ::: ones (a' + 1) (F ::: F ::: Lx))
  simp only [RX] at this
  refine Rch.tr (rch_eq rfl ?_) (Rch.tr this ?_)
  · streq
  · apply rch_eq <;> streq

/-- `h` home with `r = 0`: the region's only cell is home: the cycle is complete at once -/
theorem u_wrap0 (a : Nat) (ha : 1 ≤ a) (Lx : Strm) (w : List Bool) (hw : Ev w)
    (s : Nat × Nat) (hs : Valid s) :
    Rch (Xw a 0 0 Lx w s)
      (if 3 ≤ a then Xw (a - 2) 1 2 Lx w (adv s) else XE (a + 3) Lx w (adv s)) := by
  unfold Xw RX
  simp only [Nat.mul_zero, Nat.sub_self, ones_zero]
  gR; gl
  sl 1
  gl
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [ones_succ]
  gl; gR; gR; gR; gR
  have := grow (a' + 1) 0 ha Lx w hw s hs
  simp only [Nat.mul_zero, ones_zero, Nat.add_zero, RX] at this
  exact this

/-- `h` arrives home: the cycle of region `r` is complete -/
theorem u_last (a r t : Nat) (ha : 1 ≤ a) (ht : t + 1 = 2 * r) (Lx : Strm) (w : List Bool)
    (hw : Ev w) (s : Nat × Nat) (hs : Valid s) :
    Rch (Xw a r t Lx w s)
      (if 3 ≤ a then Xw (a - 2) (r + 1) (2 * r + 2) Lx w (adv s)
       else XE (a + 2 * r + 3) Lx w (adv s)) := by
  unfold Xw RX
  rw [show 2 * r - t = 1 by omega]
  gR; gR
  have := grow a r ha Lx w hw s hs
  simp only [RX] at this
  refine Rch.tr (rch_eq ?_ rfl) this
  rw [← ht]; streq

/-- the exhausted block: done, to the cell after its right separator -/
theorem xe_done (L : Nat) (hL : 1 ≤ L) (Lx : Strm) (w : List Bool) (s : Nat × Nat) :
    Rch (XE L Lx w s) ⟨n5, F ::: F ::: ones L (F ::: F ::: Lx), app (w ++ [F, F]) (Sb s)⟩ := by
  unfold XE RX
  gR; gl
  sl (L - 1)
  gl; gl; gR; gR
  rw [show T ::: ones (L - 1) (F ::: F ::: app (w ++ [F, F]) (Sb s)) =
    ones L (F ::: F ::: app (w ++ [F, F]) (Sb s)) by rw [cons_ones]; exact ones_congr' (by omega) rfl]
  sr L
  gR; gR
  fin

/-! ## a whole block -/

theorem adv_advN (n : Nat) (s : Nat × Nat) : adv (advN n s) = advN (n + 1) s := by
  rw [advN_add]; rfl

/-- inside region `r`: from its first cell to cell `i` -/
theorem u_steps (a r : Nat) (Lx : Strm) (w : List Bool) (hw : Ev w) :
    ∀ i (s : Nat × Nat), Valid s → i + 1 ≤ 2 * r → Rch (Xw a r 0 Lx w s) (Xw a r i Lx w (advN i s))
  | 0, s, _, _ => by fin
  | i + 1, s, hs, hi => by
    refine Rch.tr (u_steps a r Lx w hw i s hs (by omega)) ?_
    rw [← adv_advN]
    exact u_step a r i (by omega) Lx w hw _ (advN_valid i s hs)

/-- one region: `2r + 1` units, from `h` home to `h` home of the next region -/
theorem region (a r : Nat) (ha : 1 ≤ a) (Lx : Strm) (w : List Bool) (hw : Ev w)
    (s : Nat × Nat) (hs : Valid s) :
    Rch (Xw a r (2 * r) Lx w s)
      (if 3 ≤ a then Xw (a - 2) (r + 1) (2 * r + 2) Lx w (advN (2 * r + 1) s)
       else XE (a + 2 * r + 3) Lx w (advN (2 * r + 1) s)) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact u_wrap0 a ha Lx w hw s hs
  · refine Rch.tr (u_wrap a r ha hr Lx w hw s hs) ?_
    refine Rch.tr (u_steps a r Lx w hw (2 * r - 1) (adv s) (adv_valid s hs) (by omega)) ?_
    have := u_last a r (2 * r - 1) ha (by omega) Lx w hw _ (advN_valid (2 * r - 1) (adv s) (adv_valid s hs))
    have e : adv (advN (2 * r - 1) (adv s)) = advN (2 * r + 1) s := by
      rw [adv_advN]
      show advN (2 * r - 1 + 1 + 1) s = _
      rw [show 2 * r - 1 + 1 + 1 = 2 * r + 1 by omega]
    rw [e] at this
    exact this

/-- the units of the regions from `r` on, while `m` is on cell `a` -/
def U : Nat → Nat → Nat
  | a, r => if 3 ≤ a then 2 * r + 1 + U (a - 2) (r + 1) else 2 * r + 1
termination_by a => a
decreasing_by omega

theorem regions (Lx : Strm) (w : List Bool) (hw : Ev w) :
    ∀ a r (s : Nat × Nat), 1 ≤ a → Valid s →
      Rch (Xw a r (2 * r) Lx w s) (XE (a + 2 * r + 3) Lx w (advN (U a r) s))
  | a, r, s, ha, hs => by
    refine Rch.tr (region a r ha Lx w hw s hs) ?_
    by_cases h3 : 3 ≤ a
    · rw [if_pos h3]
      have := regions Lx w hw (a - 2) (r + 1) (advN (2 * r + 1) s) (by omega) (advN_valid _ _ hs)
      rw [← advN_add, show a - 2 + 2 * (r + 1) + 3 = a + 2 * r + 3 by omega,
        show 2 * (r + 1) = 2 * r + 2 by omega] at this
      rw [U, if_pos h3]; exact this
    · rw [if_neg h3, U, if_neg h3]; fin
termination_by a => a
decreasing_by omega

theorem sq_succ (n : Nat) : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega

theorem U_eq : ∀ a r, 1 ≤ a → U a r + r * r = (r + 1 + (a - 1) / 2) * (r + 1 + (a - 1) / 2)
  | a, r, ha => by
    rw [U]
    by_cases h3 : 3 ≤ a
    · rw [if_pos h3]
      have := U_eq (a - 2) (r + 1) (by omega)
      rw [show r + 1 + 1 + (a - 2 - 1) / 2 = r + 1 + (a - 1) / 2 by omega] at this
      rw [← this, sq_succ]; omega
    · rw [if_neg h3, show (a - 1) / 2 = 0 by omega, Nat.add_zero, sq_succ]; omega
termination_by a => a
decreasing_by omega

theorem U_v (L : Nat) (hL : 4 ≤ L) : U (L - 3) 0 = v L * v L := by
  have := U_eq (L - 3) 0 (by omega)
  rw [Nat.mul_zero, Nat.add_zero, show 0 + 1 + (L - 3 - 1) / 2 = v L by unfold v; omega] at this
  exact this

/-- a real block of `L ≥ 4` cells, set up (`h` home, `m` on cell `L - 3`): `v L ^ 2` units,
then to the cell after its right separator -/
theorem block (L : Nat) (hL : 4 ≤ L) (Lx : Strm) (w : List Bool) (hw : Ev w) (s : Nat × Nat)
    (hs : Valid s) :
    Rch (Xw (L - 3) 0 0 Lx w s)
      ⟨n5, F ::: F ::: ones L (F ::: F ::: Lx), app (w ++ [F, F]) (Sb (advN (v L * v L) s))⟩ := by
  have := regions Lx w hw (L - 3) 0 s (by omega) hs
  rw [U_v L hL, show L - 3 + 2 * 0 + 3 = L by omega] at this
  exact Rch.tr this (xe_done L (by omega) Lx w _)

end TM.PerfectCuboid
