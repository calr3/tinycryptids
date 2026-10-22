import TinyCryptids.Fermat.Copy
import TinyCryptids.Fermat.Blk
namespace TM.Fermat
open St

/-! The power routine. The active base block has `β + 2` cells: cell 0, the marker (a hole) on
cell 1 and the cursor cells `1 .. β` (cells `2 .. β + 1`; the last one next to the separator). A
round starts with no cursor hole. The exponent block has `k + 2` cells, its cursor on cells
`1 .. k + 1` (on the last one it sits next to the separator), and a power starts with an
exponent step from the anchor on cell 1. Right of the base: more blocks, ending with A, then
R (`r` cells) after a single 0, its hole, and Q after another single 0. -/

theorem PMC : ParserR delta MC1 MC2 := ⟨rfl, rfl, rfl⟩
theorem PNB : ParserL delta NB1 NB2 := ⟨rfl, rfl, rfl⟩

/-- a left parser that finds a hole right next to a separator (three 0s) -/
theorem ParserL.find3 {p1 p2 : St} (P : ParserL delta p1 p2) {w : List Bool} (hw : Clean w)
    (s R : Strm) :
    Rch (cfgL p1 (app w (F ::: F ::: F ::: true ::: s)) R)
      (cfgL p2 (true ::: s) (F ::: F ::: F ::: app w.reverse R)) := by
  refine Rch.tr (P.cross hw _ R) ?_
  refine Rch.tr (stepL' (δ := delta) (s := F ::: F ::: F ::: true ::: s) P.h0) ?_
  refine Rch.tr (stepL' (δ := delta) (s := F ::: F ::: true ::: s) P.h2) ?_
  exact stepL' (δ := delta) (s := F ::: true ::: s) P.h0

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

theorem PMM : ParserR delta MM1 MM2 := ⟨rfl, rfl, rfl⟩
theorem PLF : ParserL delta LF1 LF2 := ⟨rfl, rfl, rfl⟩
theorem PLG : ParserL delta LG1 LG2 := ⟨rfl, rfl, rfl⟩

/-- the part of the tape left of a base block: `pre` (read leftwards) then the exponent block
(`k + 2` cells) with its cursor on cell `e` -/
def leftOf (pre : List Bool) (k e : Nat) : Strm := app pre (ones (k + 1 - e) (F ::: ones e blank))

/-- left of the cursor cells, read leftwards: the marker, cell 0 of the base block, `leftOf` -/
def BL (pre : List Bool) (k e : Nat) : Strm := F ::: true ::: leftOf pre k e

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
theorem r_cross {p1 p2 qf : St} (P : ParserR delta p1 p2) (hf : delta p2 true = some (true, Dir.R, qf))
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
def eAtC (pre : List Bool) (k e β : Nat) (X : List Bool) (r : Nat) : Cfg St :=
  ⟨eAt, ones e blank, F ::: ones (k + 1 - e) (app pre.reverse (true ::: F ::: ones β (rgt X r 0)))⟩

/-- the left parser LG from the separator left of a block to the exponent cursor -/
theorem lg_find {pre : List Bool} (hp : PreOK pre) (k e : Nat) (R : Strm) (he : 1 ≤ e)
    (hek : e ≤ k + 1) :
    Rch (cfgL LG1 (leftOf pre k e) R) ⟨eAt, ones e blank, F ::: ones (k + 1 - e) (app pre.reverse R)⟩ := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  unfold leftOf
  generalize hd : k + 1 - (e' + 1) = d
  cases d with
  | zero =>
    rcases hp with rfl | ⟨P, hP, rfl⟩
    · have e1 : app [F, F] (ones 0 (F ::: ones (e' + 1) blank)) =
          app [] (F ::: F ::: F ::: true ::: ones e' blank) := by
        simp [app, ones_succ]
      rw [e1]
      refine Rch.tr (ParserL.find3 PLG Clean.nil _ _) ?_
      gR
      simp [app, ones_succ]
      fin
    · have hw : Clean (F :: F :: P) := by simpa using hP.clean_sep_append (m := []) Clean.nil
      have e1 : app (F :: F :: (P ++ [F, F])) (ones 0 (F ::: ones (e' + 1) blank)) =
          app (F :: F :: P) (F ::: F ::: F ::: true ::: ones e' blank) := by
        simp [app_append, ones_succ, app]
      rw [e1]
      refine Rch.tr (ParserL.find3 PLG hw _ _) ?_
      gR
      simp [app_append, List.reverse_append, ones_succ, app]
      fin
  | succ d =>
    have hw := hp.clean d
    have e1 : app pre (ones (d + 1) (F ::: ones (e' + 1) blank)) =
        app (pre ++ List.replicate (d + 1) true) (F ::: true ::: ones e' blank) := by
      simp [app_append, app_replicate, ones_succ]
    rw [e1]
    refine Rch.tr (PLG.find hw _ _) ?_
    gR
    simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ]
    fin

/-- end of a round: the merge parser from the separator after the base block, `R 0 Q` merged,
back over R to its hole, then the marker and the exponent cursor -/
theorem round_end {X pre : List Bool} (hX : Blk X) (hp : PreOK pre) (k e β r q : Nat)
    (he : 1 ≤ e) (hek : e ≤ k + 1) (hb : 1 ≤ β) (hr : 1 ≤ r) :
    Rch (bA2C (BL pre k e) β β X r q) (eAtC pre k e β X (r + q)) := by
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
  rw [show ones q (ones r' (true ::: F ::: app X.reverse (F ::: F ::: ones (b + 1) (F ::: true ::: leftOf pre k e))))
      = ones (q + r' + 1) (F ::: app X.reverse (F ::: F ::: ones (b + 1) (F ::: true ::: leftOf pre k e))) by
    rw [ones_add, ← ones_succ']]
  sLn (q + r' + 1); gL
  have hw2 : Clean (X.reverse ++ F :: F :: rep (b + 1)) :=
    hX.reverse.clean_append (show Clean (F :: F :: true :: rep b) from Clean.sep (Clean.replicate b))
  have e2 : app X.reverse (F ::: F ::: ones (b + 1) (F ::: true ::: leftOf pre k e)) =
      app (X.reverse ++ F :: F :: rep (b + 1)) (F ::: true ::: leftOf pre k e) := by
    simp [app_append, app_replicate]
  rw [e2]
  refine Rch.tr (PLF.find hw2 _ _) ?_
  gL
  refine Rch.tr (lg_find hp k e _ he hek) ?_
  unfold eAtC
  simp [rgt, sep, app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ,
    ones_cons_true, cons_blank]
  rw [show r' + 1 + q = (q + r') + 1 by omega, ones_succ]; fin

theorem PMB : ParserR delta MB1 MB2 := ⟨rfl, rfl, rfl⟩
theorem PMN : ParserR delta MN1 MN2 := ⟨rfl, rfl, rfl⟩

/-- the exponent cursor moves on: the next round starts (no base hole yet) -/
theorem e_adv {pre : List Bool} (hp : PreOK pre) (X : List Bool) (k e β r : Nat) (hek : e ≤ k)
    (hb : 1 ≤ β) :
    Rch (eAtC pre k e β X r) (bA2C (BL pre k (e + 1)) β 1 X r 0) := by
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

/-- the power is done: state `nb0` on the marker, the exponent cursor back on cell 1 -/
def nbC (pre : List Bool) (k β : Nat) (X : List Bool) (r : Nat) : Cfg St :=
  ⟨nb0, ones 1 (leftOf pre k 1), F ::: ones β (rgt X r 0)⟩

theorem e_done {pre : List Bool} (hp : PreOK pre) (X : List Bool) (k β r : Nat) (hb : 1 ≤ β) :
    Rch (eAtC pre k (k + 1) β X r) (nbC pre k β X r) := by
  obtain ⟨p, hpr⟩ : ∃ p, pre.reverse = F :: F :: p := by
    rcases hp with rfl | ⟨P, _, rfl⟩
    · exact ⟨[], rfl⟩
    · exact ⟨P.reverse ++ [F, F], by simp⟩
  obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
  unfold eAtC nbC
  rw [Nat.sub_self, ones_zero, hpr]
  gR; gL; sLn (k + 2); gR; gR; gR
  have hw := hp.clean_rev k
  have e1 : ones k (F ::: app (F :: p) (true ::: F ::: ones (b + 1) (rgt X r 0))) =
      app (rep k ++ (pre.reverse ++ [true])) (F ::: true ::: ones b (rgt X r 0)) := by
    rw [hpr]; simp [app_append, app_replicate, ones_succ]
  rw [e1]
  refine Rch.tr (PMN.find hw _ _) ?_
  gL
  have hpre : pre = p.reverse ++ [F, F] := by
    rw [← List.reverse_reverse pre, hpr]; simp
  rw [hpre]
  simp [cfgL, leftOf, app_append, app_replicate, List.reverse_append, List.reverse_replicate,
    cons_blank, ones_succ]
  fin

theorem one_round {X pre : List Bool} (hX : Blk X) (hp : PreOK pre) (k e β r : Nat)
    (he : 1 ≤ e) (hek : e ≤ k + 1) (hb : 1 ≤ β) (hr : 1 ≤ r) :
    Rch (bA2C (BL pre k e) β 1 X r 0) (eAtC pre k e β X (r * β)) := by
  refine Rch.tr (base_loop hX _ β r hr 1 0 (Nat.le_refl _) hb) ?_
  have := round_end hX hp k e β r (0 + r * (β - 1)) he hek hb hr
  have ar : r + (0 + r * (β - 1)) = r * β := by
    obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
    simp [Nat.mul_succ]; omega
  rw [ar] at this
  exact this

theorem pow_all {X pre : List Bool} (hX : Blk X) (hp : PreOK pre) (k β : Nat) (hb : 1 ≤ β) :
    ∀ e r, 1 ≤ e → e ≤ k + 1 → 1 ≤ r →
    Rch (eAtC pre k e β X r) (nbC pre k β X (r * β ^ (k + 1 - e))) := by
  suffices H : ∀ n e r, k + 1 - e = n → 1 ≤ e → e ≤ k + 1 → 1 ≤ r →
      Rch (eAtC pre k e β X r) (nbC pre k β X (r * β ^ (k + 1 - e))) from
    fun e r => H _ e r rfl
  intro n
  induction n with
  | zero =>
    intro e r h he hek hr
    obtain rfl : e = k + 1 := by omega
    rw [Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    exact e_done hp X k β r hb
  | succ n ih =>
    intro e r h he hek hr
    refine Rch.tr (e_adv hp X k e β r (by omega) hb) ?_
    refine Rch.tr (one_round hX hp k (e + 1) β r (by omega) (by omega) hb hr) ?_
    have := ih (e + 1) (r * β) (by omega) (by omega) (by omega) (Nat.mul_pos hr hb)
    rw [show k + 1 - (e + 1) = n by omega, Nat.mul_assoc, ← Nat.pow_succ'] at this
    rw [h]; exact this

/-- The complete power: from the anchor with `R = 1`, reach `nb0` with `R = β ^ k`. -/
theorem pow_full {X pre : List Bool} (hX : Blk X) (hp : PreOK pre) (k β : Nat) (hb : 1 ≤ β) :
    Rch (eAtC pre k 1 β X 1) (nbC pre k β X (β ^ k)) := by
  have := pow_all hX hp k β hb 1 1 (Nat.le_refl _) (by omega) (Nat.le_refl _)
  rwa [Nat.one_mul, Nat.add_sub_cancel] at this

end TM.Fermat
