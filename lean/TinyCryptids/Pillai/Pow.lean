import TinyCryptids.Pillai.Copy
import TinyCryptids.Pillai.Blk
namespace TM.Pillai
open St

/-! The power routine. The active base block has `β + 2` cells: cell 0, the marker (a hole) on
cell 1 and the cursor cells `1 .. β` (cells `2 .. β + 1`; the last one next to the separator). A
round starts with no cursor hole. The exponent block has `k + 2` cells, its cursor on cells
`1 .. k + 1` (on the last one it sits next to the separator), and a power starts with an
exponent step from the anchor on cell 1. Right of the base: more blocks, ending with A, then
R (`r` cells) after a single 0, its hole, and Q after another single 0. -/

theorem PMC : ParserR deltaQ MC1 MC2 := ⟨rfl, rfl, rfl⟩
theorem PNB : ParserL deltaQ NB1 NB2 := ⟨rfl, rfl, rfl⟩

/-- a left parser that finds a hole right next to a separator (three 0s) -/
theorem ParserL.find3 {p1 p2 : St} (P : ParserL deltaQ p1 p2) {w : List Bool} (hw : Clean w)
    (s R : Strm) :
    Rch (cfgL p1 (app w (F ::: F ::: F ::: true ::: s)) R)
      (cfgL p2 (true ::: s) (F ::: F ::: F ::: app w.reverse R)) := by
  refine Rch.tr (P.cross hw _ R) ?_
  refine Rch.tr (stepL' (δ := deltaQ) (s := F ::: F ::: F ::: true ::: s) P.h0) ?_
  refine Rch.tr (stepL' (δ := deltaQ) (s := F ::: F ::: true ::: s) P.h2) ?_
  exact stepL' (δ := deltaQ) (s := F ::: true ::: s) P.h0

/-- tape right of a base block: `00 X 0 R 0 Q` (X ends with A), R of value `r` -/
def rgt (X : List Bool) (r q : Nat) : Strm :=
  sep (app X (F ::: ones r (F ::: ones q blank)))

/-- after filling cursor cell `j` (or entering the round on cell 1): state `bA2` on cell `j + 1` -/
def bA2C (Lb : Strm) (β j : Nat) (X : List Bool) (r q : Nat) : Cfg St :=
  ⟨bA2, ones j Lb, ones (β - j) (rgt X r q)⟩

/-- the `MC` parser finds R's hole and punches the copy cursor on R's first cell -/
theorem mc_cross {X : List Bool} (hX : Blk X) (n r q : Nat) (L : Strm) (hr : 1 ≤ r) :
    Rch ⟨MC1, L, ones n (rgt X r q)⟩ (cpyS 0 r q (F ::: app X.reverse (F ::: F ::: ones n L))) := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hw : Clean (rep n ++ F :: F :: X) :=
    Clean.rep_append n (by simpa using hX.clean_sep_append (m := []) Clean.nil)
  have e : ones n (rgt X (r+1) q) =
      app (rep n ++ F :: F :: X) (F ::: true ::: ones r (F ::: ones q blank)) := by
    simp [rgt, sep, app_append, app_replicate, ones_succ]
  rw [e]
  refine Rch.tr (PMC.find hw _ _) ?_
  gR
  unfold cpyS
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate]
  fin

theorem nb_back {X : List Bool} (hX : Blk X) (n r q : Nat) (L : Strm) :
    Rch (cpyDone r q (app X.reverse (F ::: F ::: ones (n+1) (F ::: true ::: L))))
      ⟨bAt, true ::: L, F ::: ones (n+1) (rgt X r q)⟩ := by
  have hw : Clean (X.reverse ++ F :: F :: rep (n+1)) :=
    hX.reverse.clean_append (show Clean (F :: F :: true :: rep n) from Clean.sep (Clean.replicate n))
  have e : app X.reverse (F ::: F ::: ones (n+1) (F ::: true ::: L)) =
      app (X.reverse ++ F :: F :: rep (n+1)) (F ::: true ::: L) := by
    simp [app_append, app_replicate]
  unfold cpyDone; rw [e]
  refine Rch.tr (PNB.find hw _ _) ?_
  gR
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, rgt, sep]
  fin

theorem nb_back0 {X : List Bool} (hX : Blk X) (r q : Nat) (L : Strm) :
    Rch (cpyDone r q (app X.reverse (F ::: F ::: F ::: true ::: L)))
      ⟨bAt, true ::: L, F ::: rgt X r q⟩ := by
  have hw : Clean X.reverse := by simpa using hX.reverse.clean_append (m := []) Clean.nil
  unfold cpyDone
  refine Rch.tr (ParserL.find3 PNB hw _ _) ?_
  gR
  simp [app_append, List.reverse_append, rgt, sep]
  fin

/-- one more copy of R onto Q: the cursor moves from cell `j` to cell `j + 1` -/
theorem base_adv {X : List Bool} (hX : Blk X) (Lb : Strm) (β j r q : Nat)
    (hj : 1 ≤ j) (hjb : j < β) (hr : 1 ≤ r) :
    Rch (bA2C Lb β j X r q) (bA2C Lb β (j+1) X r (q + r)) := by
  obtain ⟨n, hn⟩ : ∃ n, β - j = n + 1 := ⟨β - j - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  unfold bA2C
  rw [hn, show β - (j' + 1 + 1) = n by omega]
  gR
  refine Rch.tr (mc_cross hX n r q _ hr) ?_
  refine Rch.tr (copy_full r q _ hr) ?_
  cases n with
  | zero =>
    refine Rch.tr (nb_back0 hX r (q + r) (ones j' Lb)) ?_
    gR; fin
  | succ n =>
    refine Rch.tr (nb_back hX n r (q + r) (ones j' Lb)) ?_
    gR; fin

theorem base_loop {X : List Bool} (hX : Blk X) (Lb : Strm) (β r : Nat) (hr : 1 ≤ r) :
    ∀ j q, 1 ≤ j → j ≤ β → Rch (bA2C Lb β j X r q) (bA2C Lb β β X r (q + r * (β - j))) := by
  suffices H : ∀ n j q, β - j = n → 1 ≤ j → j ≤ β →
      Rch (bA2C Lb β j X r q) (bA2C Lb β β X r (q + r * (β - j))) from
    fun j q h1 h2 => H _ j q rfl h1 h2
  intro n
  induction n with
  | zero =>
    intro j q h _ hjb
    obtain rfl : j = β := by omega
    rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero]; fin
  | succ n ih =>
    intro j q h hj hjb
    refine Rch.tr (base_adv hX Lb β j r q hj (by omega) hr) ?_
    have := ih (j+1) (q + r) (by omega) (by omega) (by omega)
    rw [show q + r + r * (β - (j + 1)) = q + r * (β - j) by
      rw [show β - j = (β - (j+1)) + 1 by omega, Nat.mul_succ]; omega] at this
    exact this

theorem PMM : ParserR deltaQ MM1 MM2 := ⟨rfl, rfl, rfl⟩
theorem PLF : ParserL deltaQ LF1 LF2 := ⟨rfl, rfl, rfl⟩
theorem PLG : ParserL deltaQ LG1 LG2 := ⟨rfl, rfl, rfl⟩

/-- the part of the tape left of a base block: `pre` (read leftwards) then the exponent block
(`k + 2` cells) with its cursor on cell `e` -/
def leftOf (pre : List Bool) (k e : Nat) (W : Strm) : Strm := app pre (ones (k + 1 - e) (F ::: ones e W))

/-- left of the cursor cells, read leftwards: the marker, cell 0 of the base block, `leftOf` -/
def BL (pre : List Bool) (k e : Nat) (W : Strm) : Strm := F ::: true ::: leftOf pre k e W

/-- lists allowed between the exponent block and the base block (read leftwards) -/
def PreOK (pre : List Bool) : Prop :=
  pre = [F, F] ∨ ∃ P, Blk P ∧ pre = F :: F :: (P ++ [F, F])

theorem PreOK.clean {pre : List Bool} (h : PreOK pre) (n : Nat) :
    Clean (pre ++ List.replicate (n+1) true) := by
  rcases h with rfl | ⟨P, hP, rfl⟩
  · rw [List.replicate_succ]; exact Clean.sep (Clean.replicate n)
  · have := hP.clean_sep_append (m := [false, false] ++ List.replicate (n+1) true)
      (by rw [List.replicate_succ]; exact Clean.sep (Clean.replicate n))
    simpa using this

theorem PreOK.clean_rev {pre : List Bool} (h : PreOK pre) (n : Nat) :
    Clean (List.replicate n true ++ (pre.reverse ++ [true])) := by
  refine Clean.rep_append n ?_
  rcases h with rfl | ⟨P, hP, rfl⟩
  · exact Clean.sep Clean.nil
  · have := hP.reverse.clean_sep_append (m := [false, false, true]) (Clean.sep Clean.nil)
    simpa using this

/-- generic crossing to R's hole for a right parser whose found-action writes 1 and moves right -/
theorem r_cross {p1 p2 qf : St} (P : ParserR deltaQ p1 p2) (hf : deltaQ p2 true = some (true, Dir.R, qf))
    {X : List Bool} (hX : Blk X) (n r q : Nat) (L : Strm) (hr : 1 ≤ r) :
    Rch ⟨p1, L, ones n (rgt X r q)⟩
      ⟨qf, true ::: F ::: app X.reverse (F ::: F ::: ones n L), ones (r - 1) (F ::: ones q blank)⟩ := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hw : Clean (rep n ++ F :: F :: X) :=
    Clean.rep_append n (by simpa using hX.clean_sep_append (m := []) Clean.nil)
  have e : ones n (rgt X (r+1) q) =
      app (rep n ++ F :: F :: X) (F ::: true ::: ones r (F ::: ones q blank)) := by
    simp [rgt, sep, app_append, app_replicate, ones_succ]
  rw [e]
  refine Rch.tr (P.find hw _ _) ?_
  refine Rch.tr (sR hf) ?_
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate]
  fin

/-- At the exponent cursor (cell `e`), state `eAt`; the base block has `β` cursor cells. -/
def eAtC (pre : List Bool) (k e β : Nat) (X : List Bool) (r : Nat) (W : Strm) : Cfg St :=
  ⟨eAt, ones e W, F ::: ones (k + 1 - e) (app pre.reverse (true ::: F ::: ones β (rgt X r 0)))⟩

/-- the left parser LG from the separator left of a block to the exponent cursor -/
theorem lg_find {pre : List Bool} (hp : PreOK pre) (k e : Nat) (W R : Strm) (he : 1 ≤ e)
    (hek : e ≤ k + 1) :
    Rch (cfgL LG1 (leftOf pre k e W) R) ⟨eAt, ones e W, F ::: ones (k + 1 - e) (app pre.reverse R)⟩ := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  unfold leftOf
  generalize hd : k + 1 - (e' + 1) = d
  cases d with
  | zero =>
    rcases hp with rfl | ⟨P, hP, rfl⟩
    · have e1 : app [F, F] (ones 0 (F ::: ones (e' + 1) W)) =
          app [] (F ::: F ::: F ::: true ::: ones e' W) := by
        simp [app, ones_succ]
      rw [e1]
      refine Rch.tr (ParserL.find3 PLG Clean.nil _ _) ?_
      gR
      simp [app, ones_succ]
      fin
    · have hw : Clean (F :: F :: P) := by simpa using hP.clean_sep_append (m := []) Clean.nil
      have e1 : app (F :: F :: (P ++ [F, F])) (ones 0 (F ::: ones (e' + 1) W)) =
          app (F :: F :: P) (F ::: F ::: F ::: true ::: ones e' W) := by
        simp [app_append, ones_succ, app]
      rw [e1]
      refine Rch.tr (ParserL.find3 PLG hw _ _) ?_
      gR
      simp [app_append, List.reverse_append, ones_succ, app]
      fin
  | succ d =>
    have hw := hp.clean d
    have e1 : app pre (ones (d + 1) (F ::: ones (e' + 1) W)) =
        app (pre ++ List.replicate (d + 1) true) (F ::: true ::: ones e' W) := by
      simp [app_append, app_replicate, ones_succ]
    rw [e1]
    refine Rch.tr (PLG.find hw _ _) ?_
    gR
    simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ]
    fin

/-- end of a round: the merge parser from the separator after the base block, `R 0 Q` merged,
back over R to its hole, then the marker and the exponent cursor -/
theorem round_end {X pre : List Bool} (hX : Blk X) (hp : PreOK pre) (k e β r q : Nat) (W : Strm)
    (he : 1 ≤ e) (hek : e ≤ k + 1) (hb : 1 ≤ β) (hr : 1 ≤ r) :
    Rch (bA2C (BL pre k e W) β β X r q) (eAtC pre k e β X (r + q) W) := by
  obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  unfold bA2C BL
  rw [Nat.sub_self, ones_zero]
  unfold rgt sep
  gR; gR
  have hw : Clean X := by simpa using hX.clean_append (m := []) Clean.nil
  refine Rch.tr (PMM.find hw _ _) ?_
  gR; sRn r'; gR; sRn q
  refine blankR ?_
  gL
  rw [ones_cons_true]
  gL
  rw [show ones q (ones r' (true ::: F ::: app X.reverse (F ::: F ::: ones (b + 1) (F ::: true ::: leftOf pre k e W))))
      = ones (q + r' + 1) (F ::: app X.reverse (F ::: F ::: ones (b + 1) (F ::: true ::: leftOf pre k e W))) by
    rw [ones_add, ← ones_succ']]
  sLn (q + r' + 1); gL
  have hw2 : Clean (X.reverse ++ F :: F :: rep (b + 1)) :=
    hX.reverse.clean_append (show Clean (F :: F :: true :: rep b) from Clean.sep (Clean.replicate b))
  have e2 : app X.reverse (F ::: F ::: ones (b + 1) (F ::: true ::: leftOf pre k e W)) =
      app (X.reverse ++ F :: F :: rep (b + 1)) (F ::: true ::: leftOf pre k e W) := by
    simp [app_append, app_replicate]
  rw [e2]
  refine Rch.tr (PLF.find hw2 _ _) ?_
  gL
  refine Rch.tr (lg_find hp k e W _ he hek) ?_
  unfold eAtC
  simp [rgt, sep, app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ,
    ones_cons_true, cons_blank]
  rw [show r' + 1 + q = (q + r') + 1 by omega, ones_succ]; fin

theorem PMB : ParserR deltaQ MB1 MB2 := ⟨rfl, rfl, rfl⟩
theorem PMN : ParserR deltaQ MN1 MN2 := ⟨rfl, rfl, rfl⟩

/-- the exponent cursor moves on: the next round starts (no base hole yet) -/
theorem e_adv {pre : List Bool} (hp : PreOK pre) (X : List Bool) (k e β r : Nat) (W : Strm) (hek : e ≤ k)
    (hb : 1 ≤ β) :
    Rch (eAtC pre k e β X r W) (bA2C (BL pre k (e + 1) W) β 1 X r 0) := by
  obtain ⟨d, hd⟩ : ∃ d, k + 1 - e = d + 1 := ⟨k - e, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', β = b' + 1 := ⟨β - 1, by omega⟩
  unfold eAtC bA2C BL leftOf
  rw [hd, show k + 1 - (e + 1) = d by omega, show b' + 1 - 1 = b' by omega]
  gR; gR
  have hw := hp.clean_rev d
  have e1 : ones d (app pre.reverse (true ::: F ::: ones (b' + 1) (rgt X r 0))) =
      app (rep d ++ (pre.reverse ++ [true])) (F ::: true ::: ones b' (rgt X r 0)) := by
    simp [app_append, app_replicate, ones_succ]
  rw [e1]
  refine Rch.tr (PMB.find hw _ _) ?_
  gR
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ]
  fin

/-- the power is done: state `nb0` on the marker; the exponent cursor is on cell 1 of the block
`pre` starts with (read leftwards, the block left of the base) -/
def nbC (pre : List Bool) (k β : Nat) (X : List Bool) (r : Nat) (W : Strm) : Cfg St :=
  ⟨nb0, ones 1 (leftOf pre k 1 W), F ::: ones β (rgt X r 0)⟩

/-- between the exponent block and the base: one block of `m + 2` cells -/
abbrev pre2 (m : Nat) : List Bool := F :: F :: (rep (m + 2) ++ [F, F])

theorem PreOK.pre2 (m : Nat) : PreOK (pre2 m) := Or.inr ⟨rep (m + 2), Blk.one (m + 1), rfl⟩

/-- the power is done: the exponent cursor moves on to cell 1 of the next block, then to the
marker -/
theorem e_next (X : List Bool) (k m β r : Nat) (W : Strm) (hb : 1 ≤ β) :
    Rch (eAtC (pre2 m) k (k + 1) β X r W) (nbC [F, F] m β X r (F ::: F ::: ones (k + 2) W)) := by
  obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
  unfold eAtC nbC
  rw [Nat.sub_self, ones_zero]
  simp only [pre2, List.reverse_cons, List.reverse_append, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.cons_append, List.singleton_append, app_cons, app_append,
    app_replicate, app_nil]
  gR; gR; gR; gR; gR
  have hw : Clean (rep m ++ [F, F, true]) := Clean.rep_append m (Clean.sep Clean.nil)
  have e1 : ones m (F ::: F ::: true ::: F ::: ones (b + 1) (rgt X r 0)) =
      app (rep m ++ [F, F, true]) (F ::: true ::: ones b (rgt X r 0)) := by
    simp [app_append, app_replicate, ones_succ]
  rw [e1]
  refine Rch.tr (PMN.find hw _ _) ?_
  gL
  simp [cfgL, leftOf, app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ]
  fin

theorem one_round {X pre : List Bool} (hX : Blk X) (hp : PreOK pre) (k e β r : Nat) (W : Strm)
    (he : 1 ≤ e) (hek : e ≤ k + 1) (hb : 1 ≤ β) (hr : 1 ≤ r) :
    Rch (bA2C (BL pre k e W) β 1 X r 0) (eAtC pre k e β X (r * β) W) := by
  refine Rch.tr (base_loop hX _ β r hr 1 0 (Nat.le_refl _) hb) ?_
  have := round_end hX hp k e β r (0 + r * (β - 1)) W he hek hb hr
  have ar : r + (0 + r * (β - 1)) = r * β := by
    obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
    simp [Nat.mul_succ]; omega
  rw [ar] at this
  exact this

theorem pow_all {X : List Bool} (hX : Blk X) (k m β : Nat) (W : Strm) (hb : 1 ≤ β) :
    ∀ e r, 1 ≤ e → e ≤ k + 1 → 1 ≤ r →
    Rch (eAtC (pre2 m) k e β X r W) (nbC [F, F] m β X (r * β ^ (k + 1 - e)) (F ::: F ::: ones (k + 2) W)) := by
  suffices H : ∀ n e r, k + 1 - e = n → 1 ≤ e → e ≤ k + 1 → 1 ≤ r →
      Rch (eAtC (pre2 m) k e β X r W)
        (nbC [F, F] m β X (r * β ^ (k + 1 - e)) (F ::: F ::: ones (k + 2) W)) from
    fun e r => H _ e r rfl
  intro n
  induction n with
  | zero =>
    intro e r h he hek hr
    obtain rfl : e = k + 1 := by omega
    rw [Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    exact e_next X k m β r W hb
  | succ n ih =>
    intro e r h he hek hr
    refine Rch.tr (e_adv (PreOK.pre2 m) X k e β r W (by omega) hb) ?_
    refine Rch.tr (one_round hX (PreOK.pre2 m) k (e + 1) β r W (by omega) (by omega) hb hr) ?_
    have := ih (e + 1) (r * β) (by omega) (by omega) (by omega) (Nat.mul_pos hr hb)
    rw [show k + 1 - (e + 1) = n by omega, Nat.mul_assoc, ← Nat.pow_succ'] at this
    rw [h]; exact this

/-- The complete power: from the exponent cursor on cell 1 with `R = 1`, reach `nb0` with
`R = β ^ k`, the cursor now on cell 1 of the next block. -/
theorem pow_full {X : List Bool} (hX : Blk X) (k m β : Nat) (W : Strm) (hb : 1 ≤ β) :
    Rch (eAtC (pre2 m) k 1 β X 1 W) (nbC [F, F] m β X (β ^ k) (F ::: F ::: ones (k + 2) W)) := by
  have := pow_all hX k m β W hb 1 1 (Nat.le_refl _) (by omega) (Nat.le_refl _)
  rwa [Nat.one_mul, Nat.add_sub_cancel] at this

end TM.Pillai
