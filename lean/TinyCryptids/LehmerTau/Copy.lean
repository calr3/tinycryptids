import TinyCryptids.LehmerTau.Run

/-!
# The copy routine

A source block (`f + 2` cells) with a cursor (a hole) at cell `c` is copied to a new block at
the right end of the tape, one cell per trip; the counter X (13 cells, a hole at `h`) counts
the copies: `12 − h` of them.

The blocks right of the source and between X and the source are hole-free; they are given
by their sizes (`bw`).
-/

namespace TM.LehmerTau
open St

local notation "F" => false

/-- hole-free blocks of the given sizes, each with its separator in front -/
def bw : List Nat → List Bool
  | [] => []
  | n :: l => F :: F :: rep n ++ bw l

def NOk (ns : List Nat) : Prop := ∀ n ∈ ns, 1 ≤ n

theorem bw_append (l m : List Nat) : bw (l ++ m) = bw l ++ bw m := by
  induction l with
  | nil => rfl
  | cons n l ih => simp [bw, ih, List.append_assoc]

theorem clean_rep_bw : ∀ (ns : List Nat), NOk ns → ∀ k, 1 ≤ k → Clean (rep k ++ bw ns)
  | [], _, k, _ => by simpa [bw, rep] using Clean.replicate k
  | n :: l, h, k, hk => by
    have hn := h n (List.mem_cons_self _ _)
    have ih := clean_rep_bw l (fun x hx => h x (List.mem_cons_of_mem _ hx)) n hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have ih' : Clean (rep n' ++ bw l) := by cases ih with | one h => exact h
    show Clean (rep k ++ (F :: F :: true :: (rep n' ++ bw l)))
    exact Clean.append (Clean.replicate k) (Clean.sep ih')

theorem clean_bwr_rep : ∀ (ns : List Nat), NOk ns → ∀ k, 1 ≤ k → Clean ((bw ns).reverse ++ rep k)
  | [], _, k, _ => by simpa [bw, rep] using Clean.replicate k
  | n :: l, h, k, hk => by
    have hn := h n (List.mem_cons_self _ _)
    have ih := clean_bwr_rep l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have e : (bw (n :: l)).reverse ++ rep (k' + 1) = ((bw l).reverse ++ rep n) ++ (F :: F :: true :: rep k') := by
      simp [bw, List.reverse_append, rep_rev, List.append_assoc, rep, List.replicate_succ]
    rw [e]; exact (ih n hn).append (Clean.sep (Clean.replicate k'))

theorem FGB : FarR delta GB1 GB2 GB3 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FGA : FarR delta GA1 GA2 GA3 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem PBK : ParserL delta BK1 BK2 := ⟨rfl, rfl, rfl⟩

theorem NOk_snoc {ns : List Nat} (h : NOk ns) {m : Nat} (hm : 1 ≤ m) : NOk (ns ++ [m]) := by
  intro x hx; rcases List.mem_append.1 hx with h' | h'
  · exact h x h'
  · simp at h'; omega

/-- one cell of the copy: the cursor moves on, the copy gets a cell -/
theorem tick (L0 : Strm) (f c m : Nat) (ns : List Nat) (hns : NOk ns) (hc : 1 ≤ c) (hcf : c < f)
    (hm : 1 ≤ m) :
    Rch ⟨AV1, ones c L0, F ::: ones (f + 1 - c) (app (bw (ns ++ [m])) blank)⟩
      ⟨AV1, ones (c + 1) L0, F ::: ones (f - c) (app (bw (ns ++ [m + 1])) blank)⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, f = c + 1 + k := ⟨f - c - 1, by omega⟩
  rw [show c + 1 + k + 1 - c = k + 2 by omega, show c + 1 + k - c = k + 1 by omega]
  gR; gR; gL; gL; gR
  have hw : Clean12 (F :: (rep (k + 1) ++ bw (ns ++ [m]))) :=
    Clean12.z1 (Clean12.of_clean (by
      have := clean_rep_bw (ns ++ [m]) (NOk_snoc hns hm) (k + 1) (by omega)
      cases this with | one h => exact h))
  have e1 : (F ::: true ::: ones k (app (bw (ns ++ [m])) blank)) = app (F :: (rep (k + 1) ++ bw (ns ++ [m]))) blank := by
    simp [app_append, app_rep]; rfl
  rw [e1]
  refine Rch.tr (FGB.go hw _) ?_
  gL0; gL; gL
  have hl : Clean ((bw (ns ++ [m])).reverse ++ rep (k + 1)) := clean_bwr_rep _ (NOk_snoc hns hm) _ (by omega)
  have e2 : app (F :: (rep (k + 1) ++ bw (ns ++ [m]))).reverse (true ::: tl (F ::: ones c L0)) =
      app ((bw (ns ++ [m])).reverse ++ rep (k + 1)) (F ::: true ::: ones c L0) := by
    simp [app_append, List.reverse_append, rep_rev]
  rw [e2]
  refine Rch.tr (PBK.find hl _ _) ?_
  gR
  have e3 : bw (ns ++ [m + 1]) = bw (ns ++ [m]) ++ [true] := by
    simp [bw_append, bw, rep_succ', List.append_assoc]
  rw [e3]
  simp [app_append, List.reverse_append, rep_rev, app_rep, tl_blank, cons_blank]; fin

theorem clean_bw : ∀ (ns : List Nat), NOk ns → ∀ k, Clean (rep k ++ bw ns)
  | [], _, k => by simpa [bw, rep] using Clean.replicate k
  | n :: l, h, k => by
    have := clean_rep_bw (n :: l) h 1 (by omega)
    have h1 : Clean (bw (n :: l)) := by cases this with | one h => exact h
    exact Clean.append (Clean.replicate k) h1

theorem bw_head (l : List Nat) (h : l ≠ []) : app (bw l) blank = F ::: tl (app (bw l) blank) := by
  funext n; cases n with
  | zero => cases l with | nil => exact absurd rfl h | cons a l => rfl
  | succ n => rfl

theorem bw_headF (l : List Nat) (s : Strm) : app (bw l) (F ::: s) = F ::: tl (app (bw l) (F ::: s)) := by
  funext n; cases n with
  | zero => cases l <;> rfl
  | succ n => rfl

theorem ticks (L0 : Strm) (f : Nat) (ns : List Nat) (hns : NOk ns) :
    ∀ c, 1 ≤ c → c ≤ f →
      Rch ⟨AV1, ones 1 L0, F ::: ones f (app (bw (ns ++ [3])) blank)⟩
        ⟨AV1, ones c L0, F ::: ones (f + 1 - c) (app (bw (ns ++ [c + 2])) blank)⟩ := by
  intro c hc hcf
  induction c with
  | zero => omega
  | succ c ih =>
    rcases Nat.eq_zero_or_pos c with rfl | h
    · rw [show f + 1 - (0 + 1) = f by omega]; fin
    · refine Rch.tr (ih h (by omega)) ?_
      have := tick L0 f c (c + 2) ns hns h (by omega) (by omega)
      rw [show f + 1 - (c + 1) = f - c by omega]; exact this

/-- one copy of a source block of `f + 2` cells (cursor at cell 1): from the parser that found
the cursor, to `FX1` on the source's cell 0 with the cursor back at cell 1 -/
theorem copy1 (L1 : Strm) (f : Nat) (hf : 1 ≤ f) (ns : List Nat) (hns : NOk ns) :
    Rch ⟨FS2, F ::: ones 1 (F ::: L1), ones f (app (bw ns) blank)⟩
      (cfgL FX1 (true ::: F ::: L1) (F ::: ones f (app (bw (ns ++ [f + 2])) blank))) := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  gR
  have hw : Clean12 (rep g ++ bw ns) := Clean12.of_clean (clean_bw ns hns g)
  rw [show ones g (app (bw ns) blank) = app (rep g ++ bw ns) blank by simp [app_append, app_rep]]
  refine Rch.tr (FGA.go hw _) ?_
  gR0; gR0; gL0
  show Rch (cfgL BK1 (true ::: true ::: F ::: F ::: app (rep g ++ bw ns).reverse (true ::: F ::: ones 1 (F ::: L1)))
    (true ::: blank)) _
  have e : (true ::: true ::: F ::: F ::: app (rep g ++ bw ns).reverse (true ::: F ::: ones 1 (F ::: L1))) =
      app (rep 2 ++ F :: F :: ((bw ns).reverse ++ rep (g + 1))) (F ::: true ::: F ::: L1) := by
    simp [app_append, List.reverse_append, rep_rev, app_rep, rep_succ', ones_succ]
  rw [e]
  have hl : Clean (rep 2 ++ F :: F :: ((bw ns).reverse ++ rep (g + 1))) := by
    have := clean_bwr_rep (ns ++ [2]) (NOk_snoc hns (by omega)) (g + 1) (by omega)
    simpa [bw_append, bw, List.reverse_append, rep_rev, List.append_assoc] using this
  refine Rch.tr (PBK.find hl _ _) ?_
  gR
  refine Rch.tr (?_ : Rch _ ⟨AV1, ones 1 (F ::: L1), F ::: ones (g + 1) (app (bw (ns ++ [3])) blank)⟩) ?_
  · simp [app_append, List.reverse_append, rep_rev, app_rep, bw_append, bw, ones_succ]; fin
  refine Rch.tr (ticks (F ::: L1) (g + 1) ns hns (g + 1) (by omega) (Nat.le_refl _)) ?_
  rw [show g + 1 + 1 - (g + 1) = 1 by omega]
  rw [bw_head (ns ++ [g + 1 + 2]) (by simp)]
  gR; gR; gL; gL; gL; sLn (g + 1); gR; gR
  rw [ones_cons_true]; gL
  rw [← bw_head (ns ++ [g + 1 + 2]) (by simp), ← ones_succ']; fin

/-! ## the counter X -/

theorem PFS : ParserR delta FS1 FS2 := ⟨rfl, rfl, rfl⟩
theorem PFX : ParserL delta FX1 FX2 := ⟨rfl, rfl, rfl⟩
theorem PFD : ParserR delta FD1 FD2 := ⟨rfl, rfl, rfl⟩

/-- `FS1` on cell `h + 1` of X (hole at `h`); `bs1` between X and the source (`f + 2` cells,
cursor at cell 1), `ns` right of it -/
def XC (LL : Strm) (bs1 : List Nat) (f : Nat) (ns : List Nat) (h : Nat) : Cfg St :=
  ⟨FS1, F ::: ones h (F ::: F ::: LL),
    ones (12 - h) (app (bw bs1) (F ::: F ::: true ::: F ::: ones f (app (bw ns) blank)))⟩

/-- all copies made: `CR5` on the last cell of the block left of the source -/
def XE (LL : Strm) (bs1 : List Nat) (f : Nat) (ns : List Nat) : Cfg St :=
  cfgL CR5 (app ((bw bs1).reverse ++ rep 13) (F ::: F ::: LL)) (F ::: F ::: ones (f + 2) (app (bw ns) blank))

theorem clean_x (bs1 : List Nat) (h1 : NOk bs1) (k : Nat) :
    Clean (rep k ++ bw bs1 ++ [F, F, true]) := by
  have := clean_bw (bs1 ++ [1]) (NOk_snoc h1 (by omega)) k
  simpa [bw_append, bw, rep, List.append_assoc] using this

theorem clean_xr (bs1 : List Nat) (h1 : NOk bs1) (k : Nat) (hk : 1 ≤ k) :
    Clean (true :: F :: F :: (bw bs1).reverse ++ rep k) := by
  have := clean_bwr_rep (bs1 ++ [1]) (NOk_snoc h1 (by omega)) k hk
  simpa [bw_append, bw, rep, List.reverse_append, List.append_assoc] using this

/-- one copy and one step of X -/
theorem xstep (LL : Strm) (bs1 : List Nat) (h1 : NOk bs1) (f : Nat) (hf : 1 ≤ f) (ns : List Nat)
    (hns : NOk ns) (h : Nat) (hh : 1 ≤ h) (hh2 : h ≤ 11) :
    (h < 11 → Rch (XC LL bs1 f ns h) (XC LL bs1 f (ns ++ [f + 2]) (h + 1))) ∧
    (h = 11 → Rch (XC LL bs1 f ns h) (XE LL bs1 f (ns ++ [f + 2]))) := by
  have st1 : Rch (XC LL bs1 f ns h)
      (cfgL FX1 (true ::: F ::: F ::: app ((bw bs1).reverse ++ rep (12 - h)) (F ::: ones h (F ::: F ::: LL)))
        (F ::: ones f (app (bw (ns ++ [f + 2])) blank))) := by
    unfold XC
    have e : ones (12 - h) (app (bw bs1) (F ::: F ::: true ::: F ::: ones f (app (bw ns) blank))) =
        app (rep (12 - h) ++ bw bs1 ++ [F, F, true]) (F ::: true ::: ones (f - 1) (app (bw ns) blank)) := by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      simp [app_append, app_rep]; rfl
    rw [e]
    refine Rch.tr (PFS.find (clean_x bs1 h1 _) _ _) ?_
    have := copy1 (F ::: app ((bw bs1).reverse ++ rep (12 - h)) (F ::: ones h (F ::: F ::: LL))) f hf ns hns
    refine Rch.tr ?_ this
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [app_append, List.reverse_append, app_rep, rep_rev]; fin
  obtain ⟨e, rfl⟩ : ∃ e, h = e + 1 := ⟨h - 1, by omega⟩
  have st2 : Rch (cfgL FX1 (true ::: F ::: F ::: app ((bw bs1).reverse ++ rep (12 - (e + 1))) (F ::: ones (e + 1) (F ::: F ::: LL)))
        (F ::: ones f (app (bw (ns ++ [f + 2])) blank)))
      ⟨XA1, ones (e + 1) (F ::: F ::: LL), F ::: app (true :: F :: F :: (bw bs1).reverse ++ rep (12 - (e + 1))).reverse
        (F ::: ones f (app (bw (ns ++ [f + 2])) blank))⟩ := by
    have hc := clean_xr bs1 h1 (12 - (e + 1)) (by omega)
    have e1 : (true ::: F ::: F ::: app ((bw bs1).reverse ++ rep (12 - (e + 1))) (F ::: ones (e + 1) (F ::: F ::: LL))) =
        app (true :: F :: F :: (bw bs1).reverse ++ rep (12 - (e + 1))) (F ::: true ::: ones e (F ::: F ::: LL)) := by
      simp [app_append]; rfl
    rw [e1]
    refine Rch.tr (PFX.find hc _ _) ?_
    gR; fin
  refine ⟨fun hlt => Rch.tr st1 (Rch.tr st2 ?_), fun heq => Rch.tr st1 (Rch.tr st2 ?_)⟩
  · obtain ⟨k, hk⟩ : ∃ k, 12 - (e + 1) = k + 2 := ⟨10 - (e + 1), by omega⟩
    rw [hk]
    simp only [List.reverse_append, List.reverse_cons, rep_rev, List.append_assoc, List.reverse_reverse,
      app_append, app_rep, List.singleton_append, List.cons_append, List.nil_append, app_cons]
    gR; gR; gL; gL; gR; gR
    unfold XC
    rw [show 12 - (e + 1 + 1) = k + 1 by omega]
    simp [app_append, app_rep]; fin
  · obtain rfl : e = 10 := by omega
    simp only [show 12 - (10 + 1) = 1 from rfl, List.reverse_append, List.reverse_cons, rep_rev, List.append_assoc,
      List.reverse_reverse, app_append, app_rep, List.singleton_append, List.cons_append, List.nil_append, app_cons]
    gR; gR
    rw [ones_zero, bw_headF]
    gL; gL; gR
    rw [← bw_headF]
    have e2 : ones 1 (app (bw bs1) (F ::: F ::: true ::: F ::: ones f (app (bw (ns ++ [f + 2])) blank))) =
        app (rep 1 ++ bw bs1 ++ [F, F, true]) (F ::: true ::: ones (f - 1) (app (bw (ns ++ [f + 2])) blank)) := by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      simp [app_append, app_rep]; rfl
    show Rch ⟨FD1, true ::: ones (10 + 1) (F ::: F ::: LL),
      ones 1 (app (bw bs1) (F ::: F ::: true ::: F ::: ones f (app (bw (ns ++ [f + 2])) blank)))⟩ _
    rw [e2]
    refine Rch.tr (PFD.find (clean_x bs1 h1 1) _ _) ?_
    rw [show (rep 1 ++ bw bs1 ++ [F, F, true]).reverse = true :: F :: F :: ((bw bs1).reverse ++ rep 1) by
      simp [List.reverse_append, rep_rev]]
    gL; gL; gL; gL; gL
    unfold XE
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [app_append, List.reverse_append, app_rep, rep_rev]
    rw [show ones 13 (F ::: F ::: LL) = ones 1 (true ::: ones 11 (F ::: F ::: LL)) from rfl,
      show g + 1 + 2 = g + 3 from rfl]
    exact Reach.refl _ _

/-- all `12 − h` copies -/
theorem xloop (LL : Strm) (bs1 : List Nat) (h1 : NOk bs1) (f : Nat) (hf : 1 ≤ f) :
    ∀ (k : Nat) (ns : List Nat), NOk ns → ∀ h, 1 ≤ h → h + k = 11 →
      Rch (XC LL bs1 f ns h) (XE LL bs1 f (ns ++ List.replicate (12 - h) (f + 2))) := by
  intro k
  induction k with
  | zero =>
    intro ns hns h hh hk
    have := (xstep LL bs1 h1 f hf ns hns h hh (by omega)).2 (by omega)
    rw [show 12 - h = 1 by omega]; exact this
  | succ k ih =>
    intro ns hns h hh hk
    refine Rch.tr ((xstep LL bs1 h1 f hf ns hns h hh (by omega)).1 (by omega)) ?_
    have := ih (ns ++ [f + 2]) (NOk_snoc hns (by omega)) (h + 1) (by omega) (by omega)
    rw [show 12 - h = 12 - (h + 1) + 1 by omega, List.replicate_succ]
    simpa using this

end TM.LehmerTau
