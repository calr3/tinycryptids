import TinyCryptids.Gilbreath.Queue

/-!
# The update and G += 1

Between candidates the tape left of D's separator (the stream `XS g vs e`, read from the
right) is

    G 00 M 00 blocks3 vs [e zeros]

with `G = H(g)` (`1 0 1^(g+1)`) and `vs` the stored values from left to right.
-/

namespace TM.Gilbreath
open St TinyCryptids

local notation "F" => false

def RL (g : Nat) (vs : List Nat) : List Bool :=
  [true, F] ++ List.replicate (g + 1) true ++ [F, F, true, F, F] ++ blocks3 vs

def XS (g : Nat) (vs : List Nat) (e : Nat) : Strm := zeros e (app (RL g vs).reverse blank)

theorem rep_app {α : Type} (a : α) (l : List α) : ∀ n m : Nat,
    List.replicate n a ++ (List.replicate m a ++ l) = List.replicate (n + m) a ++ l
  | 0, m => by simp
  | n + 1, m => by
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp [List.replicate_succ, rep_app a l n m]

theorem GC.zz (n : Nat) {l : List Bool} (hl : GC l) : GC (List.replicate (n + 2) F ++ true :: l) := by
  simpa [List.replicate_succ] using GC.gap n hl

theorem GC.zb3 : ∀ (vs : List Nat) (i j : Nat) {l : List Bool}, GC l →
    GC (List.replicate (j + 1) F ++ ((blocks3 vs).reverse ++ List.replicate (i + 2) F ++ true :: l))
  | [], i, j, l, hl => by
    simp only [blocks3, List.reverse_nil, List.nil_append]
    rw [← List.append_assoc, List.append_replicate_replicate, show j + 1 + (i + 2) = (j + i + 1) + 2 by omega]
    exact GC.zz _ hl
  | v :: vs, i, j, l, hl => by
    have h1 : GC (List.replicate (v + 1) true ++ (List.replicate (i + 2) F ++ true :: l)) :=
      GC.append (GC.replicate _) (by simpa [List.replicate_succ] using GC.gap i hl)
    have := GC.zb3 vs 1 j h1
    simpa [blocks3, List.reverse_append, List.reverse_replicate, List.replicate_succ, rep_cons] using this

theorem GC.b3fwd : ∀ (vs : List Nat) (i j : Nat) {l : List Bool}, (i = 0 ∨ 2 ≤ i) → GC l →
    GC (List.replicate i F ++ (blocks3 vs ++ List.replicate (j + 2) F ++ true :: l))
  | [], i, j, l, _, hl => by
    simp only [blocks3, List.nil_append]
    rw [rep_app, show i + (j + 2) = (i + j) + 2 by omega]
    exact GC.zz _ hl
  | v :: vs, i, j, l, hi, hl => by
    have h1 := GC.b3fwd vs 3 j (Or.inr (by omega)) hl
    have h2 : GC (List.replicate (v + 2) true ++ (List.replicate 3 F ++ (blocks3 vs ++ List.replicate (j + 2) F ++ true :: l))) :=
      GC.append (GC.replicate _) h1
    rcases hi with rfl | hi
    · simpa [blocks3] using h2
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
      have := GC.gap k (l := List.replicate (v + 1) true ++ (List.replicate 3 F ++ (blocks3 vs ++ List.replicate (j + 2) F ++ true :: l)))
        (GC.append (GC.replicate _) h1)
      simpa [blocks3, List.replicate_succ, rep_cons] using this

/-- one step from any configuration whose cells compute (e.g. on the blank part) -/
macro "gL0" : tactic => `(tactic| refine Rch.tr (stepL (δ := delta) (by rfl)) ?_)
macro "gR0" : tactic => `(tactic| refine Rch.tr (stepR (δ := delta) (by rfl)) ?_)

/-- make Z = H(0) two cells left of the leftmost block `H(x)`, then to its hole -/
theorem mkz (x : Nat) (R : Strm) :
    Rch (cfgL z1 blank (true ::: F ::: ones (x + 1) R)) ⟨a1, ones 1 (F ::: F ::: ZL 0), F ::: ones (x + 1) R⟩ := by
  gL0; gL0; gL0; gL0; gR0; gR; gR; gR; gR; gR; gR; gL
  fin

theorem FE : FindL delta EP EZ1 EZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FN : FindL delta nP nZ1 nZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FY : FindL delta YP YZ1 YZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FF : FindL delta FP FZ1 FZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FG : FindL delta gP gZ1 gZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FRB : FindR delta rbP rbZ1 rbZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem GC.fft : GC [F, F, true] := by simpa using GC.gap 0 GC.nil

theorem b3_snoc (ol : List Nat) (v : Nat) :
    blocks3 (ol ++ [v]) = blocks3 ol ++ (List.replicate (v + 2) true ++ [F, F, F]) := by
  induction ol with
  | nil => simp [blocks3]
  | cons w ol ih => simp [blocks3, ih]

theorem mid_snoc_rev (os ol : List Nat) (v : Nat) :
    (mid os (ol ++ [v])).reverse =
      F :: F :: F :: (List.replicate (v + 2) true ++ ((blocks3 ol).reverse ++ F :: F :: true :: (blocks3 os).reverse)) := by
  have : blocks3 (ol ++ [v]) = blocks3 ol ++ (List.replicate (v + 2) true ++ [F, F, F]) := by
    induction ol with
    | nil => simp [blocks3]
    | cons w ol ih => simp [blocks3, ih]
  simp [mid, this, List.reverse_append, List.reverse_replicate]

/-- end of a step, another old value `v` follows: L becomes `P(x)`, the next step starts -/
theorem step_end (z x : Nat) (os ol : List Nat) (v e : Nat) (Tr : Strm) :
    Rch (SE z x os (ol ++ [v]) e Tr) (CA 0 z 1 (x :: os) ol v (e + 5) Tr) := by
  unfold SE
  rw [mid_snoc_rev]
  gL; gL; gL; gL; gL
  have hg : GC (List.replicate v true ++ ((blocks3 ol).reverse ++ F :: F :: true :: (blocks3 os).reverse) ++ [F, F, true]) := by
    have := GC.b3rev os GC.fft
    have := GC.gap 0 this
    have := GC.b3rev ol (by simpa using this)
    simpa using GC.append (GC.replicate v) this
  have e1 : app (List.replicate v true ++ ((blocks3 ol).reverse ++ F :: F :: true :: (blocks3 os).reverse))
      (F ::: F ::: true ::: F ::: ones (x + 1) (F ::: F ::: ZL z)) =
      app (List.replicate v true ++ ((blocks3 ol).reverse ++ F :: F :: true :: (blocks3 os).reverse) ++ [F, F, true])
        (F ::: ones (x + 1) (F ::: F ::: ZL z)) := by
    simp [app_append]
  show Rch (cfgL EP (app (List.replicate v true ++ ((blocks3 ol).reverse ++ F :: F :: true :: (blocks3 os).reverse))
      (F ::: F ::: true ::: F ::: ones (x + 1) (F ::: F ::: ZL z))) _) _
  rw [e1]
  refine Rch.tr (FE.cross hg _ _) ?_
  have e2 : ∀ R : Strm, app (List.replicate v true ++ ((blocks3 ol).reverse ++ F :: F :: true :: (blocks3 os).reverse) ++
      [F, F, true]).reverse R = true ::: F ::: F ::: app (List.replicate v true ++ ((blocks3 ol).reverse ++ F :: F ::
        true :: (blocks3 os).reverse)).reverse R := by
    intro R; simp [List.reverse_append, app_append]
  rw [e2]
  gL; gR; gR; gL
  show Rch (cfgL nP (ones (x + 2) (F ::: F ::: ZL z)) _) _
  have e3 : ones (x + 2) (F ::: F ::: ZL z) =
      app (List.replicate (x + 2) true ++ F :: F :: List.replicate (z + 1) true) (F ::: true ::: blank) := by
    simp [app_append, app_replicate, ZL]
  rw [e3]
  refine Rch.tr (FN.cross (GC.lz (x + 2) z) _ _) ?_
  gL; gL
  have e4 : ∀ R : Strm, app (List.replicate (x + 2) true ++ F :: F :: List.replicate (z + 1) true).reverse R =
      ones (z + 1) (F ::: F ::: ones (x + 2) R) := by
    intro R; simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate]
  rw [e4]
  refine Rch.tr (mkz z _) ?_
  unfold CA
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, mid, blocks3, ones_cons_true]
  fin

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

theorem b3rev_head (os : List Nat) : ∃ w, (blocks3 os).reverse ++ [F, F, true] = F :: w := by
  rcases b3_end os with rfl | ⟨l, hl⟩
  · exact ⟨[F, true], rfl⟩
  · exact ⟨F :: F :: (l.reverse ++ [F, F, true]), by simp [hl]⟩

/-- what lies right of Z after the last step: L as `P(x)`, the finished values, M erased -/
def FR (x : Nat) (os : List Nat) (e : Nat) (Tr : Strm) : Strm :=
  ones (x + 2) (F ::: F ::: F ::: app (blocks3 os) (F ::: F ::: F ::: zeros (e + 6) Tr))

/-- the last step is over (M is next): erase M, L becomes `P(x)`, to Z's cell 3 -/
theorem final_pre (z x : Nat) (os : List Nat) (e : Nat) (Tr : Strm) :
    Rch (SE z x os [] e Tr) ⟨f3, ones 3 blank, ones z (F ::: F ::: FR x os e Tr)⟩ := by
  unfold SE
  have em : (mid os []).reverse = F :: F :: true :: (blocks3 os).reverse := by simp [mid, blocks3]
  rw [em]
  gL; gL; gL
  obtain ⟨w, hw⟩ := b3rev_head os
  have hg : GC (F :: ((blocks3 os).reverse ++ [F, F, true])) := by
    simpa using GC.zb3 os 0 0 GC.nil
  have e1 : app (blocks3 os).reverse (F ::: F ::: true ::: F ::: ones (x + 1) (F ::: F ::: ZL z)) =
      app ((blocks3 os).reverse ++ [F, F, true]) (F ::: ones (x + 1) (F ::: F ::: ZL z)) := by
    simp [app_append]
  rw [e1, hw]; rw [hw] at hg
  show Rch (cfgL s3 (F ::: app w _) _) _
  gR; gL
  refine Rch.tr (FY.crossZ1 hg _ _) ?_
  have e2 : ∀ R : Strm, app (F :: F :: w).reverse R = true ::: F ::: F ::: app (blocks3 os) (F ::: R) := by
    intro R; rw [← hw]; simp [List.reverse_append, app_append]
  rw [e2]
  gL; gR; gR; gL
  show Rch (cfgL FP (ones (x + 2) (F ::: F ::: ZL z)) _) _
  have e3 : ones (x + 2) (F ::: F ::: ZL z) =
      app (List.replicate (x + 2) true ++ F :: F :: List.replicate (z + 1) true) (F ::: true ::: blank) := by
    simp [app_append, app_replicate, ZL]
  rw [e3]
  refine Rch.tr (FF.cross (GC.lz (x + 2) z) _ _) ?_
  have e4 : ∀ R : Strm, app (List.replicate (x + 2) true ++ F :: F :: List.replicate (z + 1) true).reverse R =
      true ::: ones z (F ::: F ::: ones (x + 2) R) := by
    intro R; simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ', ones_cons_true]
  rw [e4]
  gL0; gR; gR; gR
  unfold FR
  fin

theorem final_halt (z x : Nat) (os : List Nat) (e : Nat) (Tr : Strm) (hz : z ≠ 1) :
    HaltAt (SE z x os [] e Tr) := by
  refine HaltAt.back (final_pre z x os e Tr) ?_
  rcases (show z = 0 ∨ ∃ k, z = k + 2 by
    rcases z with _ | _ | k
    · exact Or.inl rfl
    · exact absurd rfl hz
    · exact Or.inr ⟨k, rfl⟩) with rfl | ⟨k, rfl⟩
  · unfold HaltAt; apply Exists.intro; apply Exists.intro
    gR; fin
  · unfold HaltAt; apply Exists.intro; apply Exists.intro
    gR; gR; fin

theorem final_ok (x : Nat) (os : List Nat) (e : Nat) (Y : Strm) :
    Rch (SE 1 x os [] e (true ::: F ::: true ::: Y))
      ⟨c1, true ::: F ::: true ::: F ::: F ::: XS 1 (1 :: x :: os) (e + 7), Y⟩ := by
  refine Rch.tr (final_pre 1 x os e _) ?_
  gR; gL; gL; sLn 3
  gL0; gL0; gL0; gL0; gL0; gL0; gL0; gL0; gR0
  show Rch ⟨rbZ2, true ::: blank, F ::: true ::: true ::: F ::: F ::: true ::: F ::: F ::: ones 3
    (F ::: F ::: F ::: FR x os e (true ::: F ::: true ::: Y))⟩ _
  gR; gR
  have hg : GC ([true, F, F, true] ++ (List.replicate 2 F ++ (blocks3 (1 :: x :: os) ++
      List.replicate (e + 7 + 2) F ++ [true]))) := by
    have := GC.b3fwd (1 :: x :: os) 2 (e + 7) (l := []) (Or.inr (Nat.le_refl _)) GC.nil
    exact GC.one (by simpa using GC.gap 0 this)
  have e1 : true ::: F ::: F ::: true ::: F ::: F ::: ones 3 (F ::: F ::: F ::: FR x os e (true ::: F ::: true ::: Y)) =
      app ([true, F, F, true] ++ (List.replicate 2 F ++ (blocks3 (1 :: x :: os) ++
        List.replicate (e + 7 + 2) F ++ [true]))) (F ::: true ::: Y) := by
    simp [FR, blocks3, app_append, app_replicate, app_zeros, zeros_add]
    rfl
  rw [e1]
  refine Rch.tr (FRB.cross hg _ _) ?_
  gR; gR
  unfold XS RL
  simp [blocks3, app_append, app_replicate, app_zeros, List.reverse_append, List.reverse_replicate]
  fin

/-- the list a left finder crosses from D's separator to G's hole -/
def GW (g : Nat) (vs : List Nat) (e : Nat) : List Bool :=
  List.replicate (e + 1) F ++ ((blocks3 vs).reverse ++ List.replicate 2 F ++ true :: (F :: F :: List.replicate (g + 1) true))

theorem GC.gw (g : Nat) (vs : List Nat) (e : Nat) : GC (GW g vs e) := GC.zb3 vs 0 e (GC.lz 0 g)

theorem XS_eq (g : Nat) (vs : List Nat) (e : Nat) :
    F ::: XS g vs e = app (GW g vs e) (F ::: true ::: blank) := by
  unfold XS GW RL
  simp [app_append, app_replicate, app_zeros, List.reverse_append, List.reverse_replicate]
  rfl

theorem GW_rev (g : Nat) (vs : List Nat) (e : Nat) (R : Strm) :
    app (GW g vs e).reverse R =
      ones (g + 1) (F ::: F ::: true ::: F ::: F ::: app (blocks3 vs) (zeros (e + 1) R)) := by
  unfold GW
  simp [app_append, app_replicate, app_zeros, List.reverse_append, List.reverse_replicate]

/-- a prime: from D's separator to G's hole; make Z and start the first step (L = G) -/
theorem prime_start (g : Nat) (ol : List Nat) (v e : Nat) (Y : Strm) :
    Rch (cfgL nP (F ::: F ::: XS g (ol ++ [v]) e) (true ::: Y))
      (CA 0 g 1 [] ol v (e + 1) (true ::: Y)) := by
  rw [XS_eq]
  show Rch (cfgL nP (app (F :: GW g (ol ++ [v]) e) (F ::: true ::: blank)) _) _
  have hg : GC (F :: GW g (ol ++ [v]) e) := by
    have := GC.gw g (ol ++ [v]) (e + 1); simpa [GW, List.replicate_succ] using this
  refine Rch.tr (FN.cross hg _ _) ?_
  gL; gL
  have e1 : app (F :: GW g (ol ++ [v]) e).reverse (true ::: Y) = app (GW g (ol ++ [v]) e).reverse (F ::: true ::: Y) := by
    simp [app_append]
  rw [e1, GW_rev]
  refine Rch.tr (mkz g _) ?_
  unfold CA
  simp [mid, b3_snoc, blocks3, app_append, app_replicate, app_zeros]
  rw [← zeros_succ']
  fin

/-- a composite: G += 1, then back to D's hole for the rebuild -/
theorem composite (g : Nat) (vs : List Nat) (e d r : Nat) :
    Rch (CP (XS g vs e) (d + 2) r)
      ⟨c1, true ::: F ::: true ::: F ::: F ::: XS (g + 1) vs e, ones (d + 1) (F ::: F ::: ones (r + 2) blank)⟩ := by
  unfold CP
  rw [XS_eq]
  have hg : GC (F :: GW g vs e) := by
    have := GC.gw g vs (e + 1); simpa [GW, List.replicate_succ] using this
  refine Rch.tr (FG.crossZ1 hg _ _) ?_
  gL; gR; gL; gL0; gR0
  show Rch ⟨rbZ2, true ::: blank, F ::: true ::: app (F :: GW g vs e).reverse
    (true ::: F ::: ones (d + 2) (F ::: F ::: ones (r + 2) blank))⟩ _
  gR; gR
  have e1 : app (F :: GW g vs e).reverse (true ::: F ::: ones (d + 2) (F ::: F ::: ones (r + 2) blank)) =
      ones (g + 1) (app ([F, F, true] ++ (List.replicate 2 F ++ (blocks3 vs ++ List.replicate (e + 2) F ++ [true])))
        (F ::: ones (d + 2) (F ::: F ::: ones (r + 2) blank))) := by
    simp [app_append, GW_rev, app_zeros, zeros_add]
    rw [← zeros_succ']
  rw [e1]
  sRn (g + 1)
  have hg2 : GC ([F, F, true] ++ (List.replicate 2 F ++ (blocks3 vs ++ List.replicate (e + 2) F ++ [true]))) := by
    simpa using GC.gap 0 (GC.b3fwd vs 2 e (l := []) (Or.inr (Nat.le_refl _)) GC.nil)
  refine Rch.tr (FRB.cross hg2 _ _) ?_
  gR; gR
  unfold XS RL
  simp [blocks3, app_append, app_replicate, app_zeros, List.reverse_append, List.reverse_replicate]
  rw [← ones_succ']
  fin

end TM.Gilbreath
