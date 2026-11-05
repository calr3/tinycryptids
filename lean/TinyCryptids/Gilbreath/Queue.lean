import TinyCryptids.Gilbreath.Trial
import TinyCryptids.Gilbreath.Walk

/-!
# One step of the update: Z := |L - B|

Tape during an update (left to right):

    Z 00 L 00 mid B [≥ 4 zeros] Tr

* `Z = H(z)`: `1 0 1^(z+1)`, the value being made, hole at cell 1;
* `L`: `x + 3` cells with a cursor hole at cell `h` (`1 ≤ h ≤ x + 1`): the value `x`;
* `mid os ol = blocks3 os ++ [1, 0, 0] ++ blocks3 ol`: the finished values, the old `M`, the
  old values not yet used; `blocks3` writes each value `v` as `v + 2` cells then `000`;
* `B`: `y + 2` cells, the old value being consumed (from its right end);
* `Tr`: anything (the trial division region).
-/

namespace TM.Gilbreath
open St TinyCryptids

local notation "F" => false

def blocks3 : List Nat → List Bool
  | [] => []
  | v :: vs => List.replicate (v + 2) true ++ [F, F, F] ++ blocks3 vs

def mid (os ol : List Nat) : List Bool := blocks3 os ++ [true, F, F] ++ blocks3 ol

/-- left of the cell right of Z: Z read from its right end -/
def ZL (z : Nat) : Strm := ones (z + 1) (F ::: true ::: blank)

/-- on L's hole, about to advance it -/
def CA (z x h : Nat) (os ol : List Nat) (y e : Nat) (Tr : Strm) : Cfg St :=
  ⟨a1, ones h (F ::: F ::: ZL z), F ::: ones (x + 2 - h) (F ::: F ::: app (mid os ol) (ones (y + 2) (zeros (e + 4) Tr)))⟩

/-! ## the lists crossed -/

theorem rep_cons {α : Type} (a : α) : ∀ (v : Nat) (l : List α),
    List.replicate v a ++ a :: l = a :: (List.replicate v a ++ l)
  | 0, _ => rfl
  | v + 1, l => by simp [List.replicate_succ, rep_cons a v l]

theorem WC.tail {l : List Bool} (h : WC (true :: l)) : WC l := by
  cases h with
  | one h => exact h

theorem GC.b3rev : ∀ (vs : List Nat) {l : List Bool}, GC l → GC ((blocks3 vs).reverse ++ l)
  | [], _, hl => by simpa [blocks3] using hl
  | v :: vs, l, hl => by
    have : GC (F :: F :: (List.replicate 1 F ++ true :: (List.replicate (v + 1) true ++ l))) :=
      GC.gap 1 (GC.append (GC.replicate _) hl)
    have h2 := GC.b3rev vs this
    simpa [blocks3, List.reverse_append, List.reverse_replicate, List.replicate_succ, rep_cons] using h2

theorem GC.midrev (os ol : List Nat) (k : Nat) :
    GC ((mid os ol).reverse ++ F :: F :: List.replicate (k + 1) true) := by
  have h1 : GC (F :: F :: (List.replicate 0 F ++ true :: List.replicate k true)) :=
    GC.gap 0 (GC.replicate k)
  have h2 := GC.b3rev os (by simpa using h1)
  have h3 : GC (F :: F :: (List.replicate 0 F ++ true :: ((blocks3 os).reverse ++ F :: F :: List.replicate (k + 1) true))) :=
    GC.gap 0 h2
  have h4 := GC.b3rev ol (by simpa using h3)
  simpa [mid, List.reverse_append, List.replicate_succ] using h4

theorem WC.b3 : ∀ (vs : List Nat) {l : List Bool}, WC (true :: l) →
    ∃ l', blocks3 vs ++ true :: l = true :: l' ∧ WC (true :: l')
  | [], l, hl => ⟨l, by simp [blocks3], hl⟩
  | v :: vs, l, hl => by
    obtain ⟨l', e, h'⟩ := WC.b3 vs hl
    refine ⟨List.replicate (v + 1) true ++ F :: F :: F :: true :: l', ?_, ?_⟩
    · simp [blocks3, e, List.replicate_succ]
    · have := WC.gap 2 (by omega) (WC.tail h')
      have := WC.append (WC.replicate (v + 2)) this
      simpa [List.replicate_succ] using this

theorem WC.midl (os ol : List Nat) (k j : Nat) :
    WC (List.replicate k true ++ F :: F :: (mid os ol ++ List.replicate (j + 1) true)) := by
  obtain ⟨l1, e1, h1⟩ := WC.b3 ol (l := List.replicate j true) (by simpa using WC.replicate (j + 1))
  have h2 : WC (true :: (List.replicate 2 F ++ true :: l1)) := WC.one (WC.gap 1 (by omega) (WC.tail h1))
  obtain ⟨l2, e2, h3⟩ := WC.b3 os h2
  have h4 := WC.append (WC.replicate k) (WC.gap 1 (by omega) (WC.tail h3))
  have e3 : mid os ol ++ List.replicate (j + 1) true = true :: l2 := by
    rw [← e2, ← e1]; simp [mid, List.replicate_succ]
  rw [e3]; simpa using h4

theorem b3_end : ∀ vs : List Nat, vs = [] ∨ ∃ l, blocks3 vs = l ++ [F, F, F]
  | [] => Or.inl rfl
  | v :: vs => by
    refine Or.inr ?_
    rcases b3_end vs with rfl | ⟨l, hl⟩
    · exact ⟨List.replicate (v + 2) true, by simp [blocks3]⟩
    · exact ⟨List.replicate (v + 2) true ++ [F, F, F] ++ l, by simp [blocks3, hl]⟩

/-- `mid` ends with two 0s -/
theorem midrev_ff (os ol : List Nat) : ∃ l, (mid os ol).reverse = F :: F :: l := by
  rcases b3_end ol with rfl | ⟨l, hl⟩
  · exact ⟨true :: (blocks3 os).reverse, by simp [mid, blocks3]⟩
  · exact ⟨F :: l.reverse ++ F :: F :: true :: (blocks3 os).reverse, by simp [mid, hl]⟩

/-! ## the routines -/

theorem FA : FindR delta aP aZ1 aZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FAL : FindL delta AP AZ1 AZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FX : FindL delta XP XZ1 XZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FZ : FindL delta ZP ZZ1 ZZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem WW : WalkR delta w1 w2 w3 w4 wz := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem WV : WalkR delta v1 v2 v3 v4 vz := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem app_rep (n : Nat) (l : List Bool) (s : Strm) :
    app (List.replicate n true ++ l) s = ones n (app l s) := by rw [app_append, app_replicate]

/-- cursor advanced, B > 0: B loses its last cell -/
theorem p1a (z h k : Nat) (os ol : List Nat) (y e : Nat) (Tr : Strm) :
    Rch (CA z (h + k) h os ol (y + 1) e Tr) (CA z (h + k) (h + 1) os ol y (e + 1) Tr) := by
  unfold CA
  rw [show h + k + 2 - h = k + 2 by omega, show h + k + 2 - (h + 1) = k + 1 by omega]
  gR; gR; gL; gR
  have e1 : ones (k + 1) (F ::: F ::: app (mid os ol) (ones (y + 1 + 2) (zeros (e + 4) Tr))) =
      app (List.replicate (k + 1) true ++ F :: F :: (mid os ol ++ List.replicate (y + 2 + 1) true))
        (F ::: F ::: F ::: F ::: zeros e Tr) := by
    simp [app_append, app_replicate, app_zeros, zeros_add]; rfl
  show Rch ⟨w1, F ::: true ::: ones h (F ::: F ::: ZL z),
    ones (k + 1) (F ::: F ::: app (mid os ol) (ones (y + 1 + 2) (zeros (e + 4) Tr)))⟩ _
  rw [e1]
  refine Rch.tr (WW.cross (WC.midl os ol (k + 1) (y + 2)) _ _) ?_
  have e2 : app (List.replicate (k + 1) true ++ F :: F :: (mid os ol ++ List.replicate (y + 2 + 1) true)).reverse
      (F ::: true ::: ones h (F ::: F ::: ZL z)) =
      true ::: app (List.replicate (y + 2) true ++ ((mid os ol).reverse ++ F :: F :: List.replicate (k + 1) true))
        (F ::: true ::: ones h (F ::: F ::: ZL z)) := by
    simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, List.replicate_succ,
      ones_cons_true]
  rw [e2]
  refine Rch.tr (WW.find _ _) ?_
  gL; gL; gL
  refine Rch.tr (FAL.cross (GC.append (GC.replicate y) (GC.midrev os ol k)) _ _) ?_
  gL; gR
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, List.replicate_succ,
    ones_cons_true]
  fin

theorem GC.lz (h z : Nat) : GC (List.replicate h true ++ F :: F :: List.replicate (z + 1) true) :=
  GC.append (GC.replicate h) (by simpa using GC.gap 0 (GC.replicate z))

/-- right of L's cursor (`k + 1` more cells): walk to B's last cell (B has `y + 2` cells) -/
theorem walkB {w1 w2 w3 w4 wz : St} (H : WalkR delta w1 w2 w3 w4 wz) (k y e : Nat) (os ol : List Nat)
    (Tr Lf : Strm) :
    Rch ⟨w1, Lf, ones (k + 1) (F ::: F ::: app (mid os ol) (ones (y + 2) (zeros (e + 4) Tr)))⟩
      (cfgL wz (true ::: app (List.replicate (y + 1) true ++ ((mid os ol).reverse ++ F :: F :: List.replicate (k + 1) true)) Lf)
        (F ::: F ::: F ::: F ::: zeros e Tr)) := by
  have e1 : ones (k + 1) (F ::: F ::: app (mid os ol) (ones (y + 2) (zeros (e + 4) Tr))) =
      app (List.replicate (k + 1) true ++ F :: F :: (mid os ol ++ List.replicate (y + 1 + 1) true))
        (F ::: F ::: F ::: F ::: zeros e Tr) := by
    simp [app_append, app_replicate, app_zeros, zeros_add]; rfl
  rw [e1]
  refine Rch.tr (H.cross (WC.midl os ol (k + 1) (y + 1)) _ _) ?_
  have e2 : app (List.replicate (k + 1) true ++ F :: F :: (mid os ol ++ List.replicate (y + 1 + 1) true)).reverse Lf =
      true ::: app (List.replicate (y + 1) true ++ ((mid os ol).reverse ++ F :: F :: List.replicate (k + 1) true)) Lf := by
    simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, List.replicate_succ,
      ones_cons_true]
  rw [e2]
  exact H.find _ _

/-- from left of L's cursor (`h` ones on the left): to Z's hole, Z += 1, back to L's cursor -/
theorem zinc (z h : Nat) (R : Strm) :
    Rch (cfgL ZP (ones h (F ::: F ::: ZL z)) (true ::: F ::: true ::: R))
      ⟨a1, ones (h + 1) (F ::: F ::: ZL (z + 1)), F ::: true ::: R⟩ := by
  have e1 : ones h (F ::: F ::: ZL z) =
      app (List.replicate h true ++ F :: F :: List.replicate (z + 1) true) (F ::: true ::: blank) := by
    simp [app_append, app_replicate, ZL]
  rw [e1]
  refine Rch.tr (FZ.cross (GC.lz h z) _ _) ?_
  gL; gR; gL; gL
  show Rch (cfgL i3 blank _) _
  gR; gR; gR
  have e2 : app (List.replicate h true ++ F :: F :: List.replicate (z + 1) true).reverse (true ::: F ::: true ::: R) =
      app (List.replicate (z + 1) true ++ F :: F :: List.replicate (h + 1) true) (F ::: true ::: R) := by
    simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_cons_true, ones_succ]
  rw [e2]
  refine Rch.tr (FA.cross (GC.lz (z + 1) h) _ _) ?_
  gR; gL
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_cons_true, ZL]
  fin

/-- cursor advanced, B = 0: Z += 1 -/
theorem p1b (z h k : Nat) (os ol : List Nat) (e : Nat) (Tr : Strm) :
    Rch (CA z (h + k) h os ol 0 e Tr) (CA (z + 1) (h + k) (h + 1) os ol 0 e Tr) := by
  unfold CA
  rw [show h + k + 2 - h = k + 2 by omega, show h + k + 2 - (h + 1) = k + 1 by omega]
  gR; gR; gL; gR
  refine Rch.tr (walkB WW k 0 e os ol Tr _) ?_
  gL; gL
  show Rch (cfgL e2 (app ((mid os ol).reverse ++ F :: F :: List.replicate (k + 1) true)
    (F ::: true ::: ones h (F ::: F ::: ZL z))) (true ::: F ::: F ::: F ::: F ::: F ::: zeros e Tr)) _
  have hg := GC.append (GC.replicate 1) (GC.midrev os ol k)
  obtain ⟨l, hl⟩ := midrev_ff os ol
  rw [hl] at hg ⊢
  gR; gR; gL
  show Rch (cfgL XP (app (List.replicate 1 true ++ (F :: F :: l ++ F :: F :: List.replicate (k + 1) true))
    (F ::: true ::: ones h (F ::: F ::: ZL z))) (true ::: F ::: F ::: F ::: F ::: zeros e Tr)) _
  refine Rch.tr (FX.cross hg _ _) ?_
  gL; gL
  have e4 : app (List.replicate 1 true ++ (F :: F :: l ++ F :: F :: List.replicate (k + 1) true)).reverse
      (true ::: F ::: F ::: F ::: F ::: zeros e Tr) =
      true ::: ones k (F ::: F ::: app l.reverse (F ::: F ::: true ::: true ::: F ::: F ::: F ::: F ::: zeros e Tr)) := by
    simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_cons_true, List.replicate_succ]
  rw [e4]
  refine Rch.tr (zinc z h _) ?_
  have hm : mid os ol = l.reverse ++ [F, F] := by
    have := congrArg List.reverse hl; simpa using this
  rw [hm]
  simp [app_append, app_replicate, ones_cons_true]
  fin

/-- L exhausted, B > 0: B -= 1, Z += 1 -/
theorem p2a (z x : Nat) (os ol : List Nat) (y e : Nat) (Tr : Strm) :
    Rch (CA z x (x + 1) os ol (y + 1) e Tr) (CA (z + 1) x (x + 1) os ol y (e + 1) Tr) := by
  unfold CA
  rw [show x + 2 - (x + 1) = 1 by omega]
  gR; gR; gL; gL; gR
  refine Rch.tr (walkB WV 0 (y + 1) e os ol Tr _) ?_
  gL; gL; gL
  have hg := GC.append (GC.replicate y) (GC.midrev os ol 0)
  refine Rch.tr (FX.cross hg _ _) ?_
  gL; gL
  have e4 : app (List.replicate y true ++ ((mid os ol).reverse ++ F :: F :: List.replicate (0 + 1) true)).reverse
      (true ::: true ::: F ::: F ::: F ::: F ::: F ::: zeros e Tr) =
      true ::: F ::: F ::: app (mid os ol) (ones (y + 2) (zeros (e + 1 + 4) Tr)) := by
    simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_cons_true]; rfl
  rw [e4]
  exact zinc z x _

/-- the end of a step: B erased, the head on the last cell of `mid` -/
def SE (z x : Nat) (os ol : List Nat) (e : Nat) (Tr : Strm) : Cfg St :=
  cfgL s2 (app (mid os ol).reverse (F ::: F ::: true ::: F ::: ones (x + 1) (F ::: F ::: ZL z))) (zeros (e + 6) Tr)

/-- L exhausted, B = 0: B is erased -/
theorem p2b (z x : Nat) (os ol : List Nat) (e : Nat) (Tr : Strm) :
    Rch (CA z x (x + 1) os ol 0 e Tr) (SE z x os ol e Tr) := by
  unfold CA SE
  rw [show x + 2 - (x + 1) = 1 by omega]
  gR; gR; gL; gL; gR
  refine Rch.tr (walkB WV 0 0 e os ol Tr _) ?_
  gL; gL
  obtain ⟨l, hl⟩ := midrev_ff os ol
  simp only [hl]
  show Rch (cfgL u2 (F ::: F ::: app (l ++ F :: F :: List.replicate 1 true)
    (F ::: ones (x + 1) (F ::: F ::: ZL z))) (true ::: F ::: F ::: F ::: F ::: F ::: zeros e Tr)) _
  gR; gL
  simp [app_append]
  fin

/-! ## a whole step -/

theorem phase1 (x y : Nat) (os ol : List Nat) (e : Nat) (Tr : Strm) : ∀ j, j ≤ x →
    Rch (CA 0 x 1 os ol y e Tr) (CA (j - y) x (1 + j) os ol (y - j) (e + min j y) Tr) := by
  intro j
  induction j with
  | zero => intro _; simp; fin
  | succ j ih =>
    intro hj
    refine Rch.tr (ih (by omega)) ?_
    obtain ⟨k, hk⟩ : ∃ k, x = 1 + j + k := ⟨x - (1 + j), by omega⟩
    rw [hk]
    by_cases hy : j < y
    · have := p1a (j - y) (1 + j) k os ol (y - (j + 1)) (e + min j y) Tr
      rw [show y - (j + 1) + 1 = y - j by omega] at this
      rw [show j + 1 - y = j - y by omega, show 1 + (j + 1) = 1 + j + 1 by omega,
        show e + min (j + 1) y = e + min j y + 1 by omega]
      exact this
    · have := p1b (j - y) (1 + j) k os ol (e + min j y) Tr
      rw [show y - j = 0 by omega] at *
      rw [show j + 1 - y = j - y + 1 by omega, show 1 + (j + 1) = 1 + j + 1 by omega,
        show y - (j + 1) = 0 by omega, show min (j + 1) y = min j y by omega]
      exact this

theorem phase2 (z x : Nat) (os ol : List Nat) (y e : Nat) (Tr : Strm) : ∀ i, i ≤ y →
    Rch (CA z x (x + 1) os ol y e Tr) (CA (z + i) x (x + 1) os ol (y - i) (e + i) Tr) := by
  intro i
  induction i with
  | zero => intro _; fin
  | succ i ih =>
    intro hi
    refine Rch.tr (ih (by omega)) ?_
    have := p2a (z + i) x os ol (y - (i + 1)) (e + i) Tr
    rw [show y - (i + 1) + 1 = y - i by omega] at this
    exact this

/-- one step: Z := |L - B| -/
theorem step (x y : Nat) (os ol : List Nat) (e : Nat) (Tr : Strm) :
    ∃ e', Rch (CA 0 x 1 os ol y e Tr) (SE (ad x y) x os ol e' Tr) := by
  have h1 := phase1 x y os ol e Tr x (Nat.le_refl _)
  have h2 := phase2 (x - y) x os ol (y - x) (e + min x y) Tr (y - x) (Nat.le_refl _)
  have h3 := p2b (x - y + (y - x)) x os ol (e + min x y + (y - x)) Tr
  rw [Nat.sub_self] at h2
  rw [show 1 + x = x + 1 by omega] at h1
  refine ⟨e + min x y + (y - x), Rch.tr h1 (Rch.tr h2 ?_)⟩
  rw [ad_eq]; exact h3

end TM.Gilbreath
