import TinyCryptids.Beal.Copy
import TinyCryptids.Beal.Blk
namespace TM.Beal
open St

/-! The base loop, as in `TinyCryptids/Fermat/Pow.lean`: a base block of Beal is Fermat's
with one more 1 at its start (passed in `Lb`). -/

theorem PMC : ParserR delta MC1 MC2 := ⟨rfl, rfl, rfl⟩
theorem PNB : ParserL delta NB1 NB2 := ⟨rfl, rfl, rfl⟩

/-- tape right of a base block: `00 X 00 R 00 Q`, R value `r` with cursor at cell 1 -/
def rgt (X : List Bool) (r q : Nat) : Strm :=
  sep (app X (sep (true ::: false ::: ones r (sep (ones q blank)))))

/-- at the base cursor (cell `j` of a base block of value `β`), state `bAt` -/
def bAtC (Lb : Strm) (β j : Nat) (X : List Bool) (r q : Nat) : Cfg St :=
  ⟨bAt, ones j Lb, false ::: ones (β + 1 - j) (rgt X r q)⟩

theorem mc_cross {X : List Bool} (hX : Blk X) (n r q : Nat) (L : Strm) (hr : 1 ≤ r) :
    Rch ⟨MC1, L, ones n (rgt X r q)⟩
      ⟨c1, true ::: false ::: true ::: false ::: false ::: app X.reverse (false ::: false ::: ones n L),
        ones (r - 1) (sep (ones q blank))⟩ := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hw : Clean (List.replicate n true ++ false :: false :: (X ++ [false, false, true])) :=
    Clean.rep_append n (hX.clean_sep_append (Clean.sep Clean.nil))
  have e : ones n (rgt X (r+1) q) =
      app (List.replicate n true ++ false :: false :: (X ++ [false, false, true]))
        (false ::: true ::: ones r (sep (ones q blank))) := by
    simp [rgt, sep, app_append, app_replicate, ones_succ]
  rw [e]
  refine Rch.tr (PMC.find hw _ _) ?_
  gR
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate]
  fin

theorem nb_back {X : List Bool} (hX : Blk X) (n r q : Nat) (L : Strm) :
    Rch (cpyDone r q (false ::: app X.reverse (false ::: false ::: ones (n+1) (false ::: true ::: L))))
      ⟨bAt, true ::: L, false ::: ones (n+1) (rgt X r q)⟩ := by
  have hw : Clean (true :: false :: false :: (X.reverse ++ false :: false :: List.replicate (n+1) true)) := by
    refine Clean.one (hX.reverse.clean_sep_append ?_)
    rw [List.replicate_succ]; exact Clean.sep (Clean.replicate n)
  have e : true ::: false ::: false ::: app X.reverse (false ::: false ::: ones (n+1) (false ::: true ::: L)) =
      app (true :: false :: false :: (X.reverse ++ false :: false :: List.replicate (n+1) true))
        (false ::: true ::: L) := by
    simp [app_append, app_replicate]
  unfold cpyDone; rw [e]
  refine Rch.tr (PNB.find hw _ _) ?_
  gR
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, rgt, sep]
  fin

theorem base_adv {X : List Bool} (hX : Blk X) (Lb : Strm) (β j r q : Nat)
    (hj : 1 ≤ j) (hjb : j < β) (hr : 1 ≤ r) :
    Rch (bAtC Lb β j X r q) (bAtC Lb β (j+1) X r (q + r)) := by
  obtain ⟨k, rfl⟩ : ∃ k, β = j + 1 + k := ⟨β - j - 1, by omega⟩
  unfold bAtC
  rw [show j + 1 + k + 1 - j = k + 2 by omega, show j + 1 + k + 1 - (j + 1) = k + 1 by omega]
  gR; gR; gL; gR
  refine Rch.tr (mc_cross hX (k+1) r q _ hr) ?_
  refine Rch.tr (copy_full r q _ hr) ?_
  have := nb_back hX k r (q + r) (ones j Lb)
  exact this

theorem base_loop {X : List Bool} (hX : Blk X) (Lb : Strm) (β r q : Nat)
    (hb : 1 ≤ β) (hr : 1 ≤ r) : ∀ j, 1 ≤ j → j ≤ β →
    Rch (bAtC Lb β j X r q) (bAtC Lb β β X r (q + r * (β - j))) := by
  suffices H : ∀ n j q, β - j = n → 1 ≤ j → j ≤ β →
      Rch (bAtC Lb β j X r q) (bAtC Lb β β X r (q + r * (β - j))) from
    fun j hj hjb => H _ j q rfl hj hjb
  intro n
  induction n with
  | zero =>
    intro j q h hj hjb
    have : j = β := by omega
    subst this; simp; fin
  | succ n ih =>
    intro j q h hj hjb
    refine Rch.tr (base_adv hX Lb β j r q hj (by omega) hr) ?_
    have := ih (j+1) (q + r) (by omega) (by omega) (by omega)
    rw [show q + r + r * (β - (j + 1)) = q + r * (β - j) by
      rw [show β - j = (β - (j+1)) + 1 by omega, Nat.mul_succ]; omega] at this
    exact this

theorem PMM : ParserR delta MM1 MM2 := ⟨rfl, rfl, rfl⟩
theorem PLE : ParserL delta LE1 LE2 := ⟨rfl, rfl, rfl⟩
theorem PLF : ParserL delta LF1 LF2 := ⟨rfl, rfl, rfl⟩
theorem PLG : ParserL delta LG1 LG2 := ⟨rfl, rfl, rfl⟩

abbrev rep (n : Nat) : List Bool := List.replicate n true

/-- left of a base block, read leftwards: a separator, the block next to it (`m` cells), a
separator, the next exponent block (`n + 2` cells), a separator -/
def preL (n m : Nat) : List Bool := F :: F :: (rep m ++ F :: F :: (rep (n + 2) ++ [F, F]))

/-- ... then the exponent block (`E + 1` cells, its cursor on cell `e`) and `Lx` -/
def leftOf (n m E e : Nat) (Lx : Strm) : Strm := app (preL n m) (ones (E - e) (F ::: ones e Lx))

/-- a left parser that finds a hole right next to a separator (three 0s) -/
theorem ParserL.find3 {q1 q2 : St} (P : ParserL delta q1 q2) {w : List Bool} (hw : Clean w)
    (s R : Strm) :
    Rch (cfgL q1 (app w (F ::: F ::: F ::: true ::: s)) R)
      (cfgL q2 (true ::: s) (F ::: F ::: F ::: app w.reverse R)) := by
  refine Rch.tr (P.cross hw _ R) ?_
  refine Rch.tr (stepL' (δ := delta) (s := F ::: F ::: F ::: true ::: s) P.h0) ?_
  refine Rch.tr (stepL' (δ := delta) (s := F ::: F ::: true ::: s) P.h2) ?_
  exact stepL' (δ := delta) (s := F ::: true ::: s) P.h0

theorem ones_tt (q a : Nat) (Z : Strm) :
    ones q (true ::: true ::: ones a (true ::: Z)) = ones (q + a + 3) Z := by
  rw [show true ::: true ::: ones a (true ::: Z) = ones (a + 3) Z from by
    rw [← ones_succ']; rfl, ones_add]; congr 1

/-- generic crossing to the R hole for a right parser whose found-action moves right -/
theorem r_cross {q1 q2 qf : St} (P : ParserR delta q1 q2) (hf : delta q2 true = some (true, Dir.R, qf))
    {X : List Bool} (hX : Blk X) (n r q : Nat) (L : Strm) (hr : 1 ≤ r) :
    Rch ⟨q1, L, ones n (rgt X r q)⟩
      ⟨qf, true ::: false ::: true ::: false ::: false ::: app X.reverse (false ::: false ::: ones n L),
        ones (r - 1) (sep (ones q blank))⟩ := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hw : Clean (List.replicate n true ++ false :: false :: (X ++ [false, false, true])) :=
    Clean.rep_append n (hX.clean_sep_append (Clean.sep Clean.nil))
  have e : ones n (rgt X (r+1) q) =
      app (List.replicate n true ++ false :: false :: (X ++ [false, false, true]))
        (false ::: true ::: ones r (sep (ones q blank))) := by
    simp [rgt, sep, app_append, app_replicate, ones_succ]
  rw [e]
  refine Rch.tr (P.find hw _ _) ?_
  refine Rch.tr (sR hf) ?_
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate]
  fin

/-- at the exponent cursor (cell `e`), state `eAt` -/
def eAtC (n m E e β : Nat) (X : List Bool) (r : Nat) (Lx : Strm) : Cfg St :=
  ⟨eAt, ones e Lx, F ::: ones (E - e) (app (preL n m).reverse (true ::: true ::: F ::: ones β (rgt X r 0)))⟩

/-- end of a round: base cursor back to cell 2, merge Q into R, back to the exponent cursor -/
theorem round_end {X : List Bool} (hX : Blk X) (n m E e β r q : Nat) (Lx : Strm)
    (he : 1 ≤ e) (heE : e ≤ E) (hm : 1 ≤ m) (hb : 1 ≤ β) (hr : 1 ≤ r) :
    Rch (bAtC (true ::: leftOf n m E e Lx) β β X r q) (eAtC n m E e β X (r + q) Lx) := by
  unfold bAtC leftOf
  rw [show β + 1 - β = 1 by omega]
  gR; gR; gL
  show Rch (cfgL bD1 (true ::: true ::: ones β (true ::: app (preL n m) (ones (E - e) (F ::: ones e Lx)))) _) _
  rw [ones_cons_true]
  sLn (β + 3); gR; gR; gR; gR
  refine Rch.tr (r_cross PMM rfl hX β r q _ hr) ?_
  sRn (r - 1); gR; gR; sRn q
  refine blankR ?_
  rw [ones_tt q (r - 1)]
  rw [show q + (r - 1) + 3 = (q + r) + 2 by omega]
  gL; gL; gL
  rw [← app_replicate (q + r)]
  refine Rch.tr (PLE.find (Clean.replicate _) _ _) ?_
  gL
  obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
  have hw2 : Clean (F :: F :: (X.reverse ++ F :: F :: rep (b + 1))) :=
    hX.reverse.clean_sep_append (Clean.sep (Clean.replicate b))
  have e2 : ∀ Z : Strm, F ::: F ::: app X.reverse (F ::: F ::: ones (b + 1) (F ::: true ::: true ::: F ::: tl Z)) =
      app (F :: F :: (X.reverse ++ F :: F :: rep (b + 1))) (F ::: true ::: true ::: F ::: tl Z) := by
    intro Z; simp [app_append, app_replicate]
  rw [e2]
  refine Rch.tr (PLF.find hw2 _ _) ?_
  gL
  show Rch (cfgL LG1 (true ::: app (preL n m) (ones (E - e) (F ::: ones e Lx))) _) _
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold eAtC
  generalize E - (e' + 1) = k
  have hc : Clean (true :: F :: F :: (rep (m' + 1) ++ F :: F :: rep (n + 2))) :=
    Clean.one (Clean.sep (Clean.rep_append m' (Clean.sep (Clean.replicate (n + 1)))))
  cases k with
  | zero =>
    have e3 : true ::: app (preL n (m' + 1)) (ones 0 (F ::: ones (e' + 1) Lx)) =
        app (true :: F :: F :: (rep (m' + 1) ++ F :: F :: rep (n + 2))) (F ::: F ::: F ::: true ::: ones e' Lx) := by
      simp [preL, app_append, app_replicate, ones_succ]
    rw [e3]
    refine Rch.tr (ParserL.find3 PLG hc _ _) ?_
    gR
    simp [preL, rgt, sep, app_append, app_replicate, List.reverse_append, List.reverse_replicate, cons_blank,
      ones_succ]
    rw [Nat.add_comm q r]; fin
  | succ k =>
    have hc2 : Clean (true :: F :: F :: (rep (m' + 1) ++ F :: F :: (rep (n + 2) ++ F :: F :: rep (k + 1)))) :=
      Clean.one (Clean.sep (Clean.rep_append m' (Clean.sep (Clean.rep_append (n + 1)
        (Clean.sep (Clean.replicate k))))))
    have e3 : true ::: app (preL n (m' + 1)) (ones (k + 1) (F ::: ones (e' + 1) Lx)) =
        app (true :: F :: F :: (rep (m' + 1) ++ F :: F :: (rep (n + 2) ++ F :: F :: rep (k + 1))))
          (F ::: true ::: ones e' Lx) := by
      simp [preL, app_append, app_replicate, ones_succ]
    rw [e3]
    refine Rch.tr (PLG.find hc2 _ _) ?_
    gR
    simp [preL, rgt, sep, app_append, app_replicate, List.reverse_append, List.reverse_replicate, cons_blank,
      ones_succ]
    rw [Nat.add_comm q r]; fin

theorem PMB : ParserR delta MB1 MB2 := ⟨rfl, rfl, rfl⟩
theorem PMN : ParserR delta MN1 MN2 := ⟨rfl, rfl, rfl⟩

theorem clean_preRev (n m k : Nat) (hm : 1 ≤ m) :
    Clean (rep k ++ ((preL n m).reverse ++ [true, true])) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine Clean.rep_append k ?_
  have : (preL n (m' + 1)).reverse ++ [true, true] =
      F :: F :: (rep (n + 2) ++ F :: F :: (rep (m' + 1) ++ [F, F, true, true])) := by
    simp [preL, List.reverse_append, List.reverse_replicate]
  rw [this]
  exact Clean.sep (Clean.rep_append (n + 1) (Clean.sep (Clean.rep_append m' (Clean.sep (Clean.one Clean.nil)))))

theorem e_adv {X : List Bool} (n m E e β r : Nat) (Lx : Strm)
    (heE : e < E) (hm : 1 ≤ m) (hb : 1 ≤ β) :
    Rch (eAtC n m E e β X r Lx) (bAtC (true ::: leftOf n m E (e + 1) Lx) β 1 X r 0) := by
  obtain ⟨k, hk⟩ : ∃ k, E - e = k + 1 := ⟨E - e - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
  unfold eAtC bAtC leftOf
  rw [hk, show E - (e + 1) = k by omega, show b + 1 + 1 - 1 = b + 1 by omega]
  gR; gR
  have e1 : ones k (app (preL n m).reverse (true ::: true ::: F ::: ones (b + 1) (rgt X r 0))) =
      app (rep k ++ ((preL n m).reverse ++ [true, true])) (F ::: true ::: ones b (rgt X r 0)) := by
    simp [app_append, app_replicate, ones_succ]
  rw [e1]
  refine Rch.tr (PMB.find (clean_preRev n m k hm) _ _) ?_
  gL
  simp [preL, app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ]
  fin

/-- the power is done: the exponent cursor is on cell 1 of the next exponent block (`n + 2`
cells), the head on the base cursor (cell 2) in state `nb0` -/
def nbC (n m E β : Nat) (X : List Bool) (r : Nat) (Lx : Strm) : Cfg St :=
  ⟨nb0, ones 2 (F ::: F ::: ones m (F ::: F ::: ones n (F ::: true ::: F ::: F ::: ones (E + 1) Lx))),
    F ::: ones β (rgt X r 0)⟩

theorem e_done {X : List Bool} (n m E β r : Nat) (Lx : Strm) (hm : 1 ≤ m) (hb : 1 ≤ β) :
    Rch (eAtC n m E E β X r Lx) (nbC n m E β X r Lx) := by
  obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold eAtC nbC
  rw [Nat.sub_self]
  simp only [preL, List.reverse_cons, List.reverse_append, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.cons_append, List.singleton_append, app_append, app_cons,
    app_replicate, ones_zero, app_nil]
  gR; gR; gR; gR; gR
  have hw : Clean (rep n ++ F :: F :: (rep (m' + 1) ++ [F, F, true, true])) :=
    Clean.rep_append n (Clean.sep (Clean.rep_append m' (Clean.sep (Clean.one Clean.nil))))
  have e1 : ones n (F ::: F ::: ones (m' + 1) (F ::: F ::: true ::: true ::: F ::: ones (b + 1) (rgt X r 0))) =
      app (rep n ++ F :: F :: (rep (m' + 1) ++ [F, F, true, true])) (F ::: true ::: ones b (rgt X r 0)) := by
    simp [app_append, app_replicate, ones_succ]
  rw [e1]
  refine Rch.tr (PMN.find hw _ _) ?_
  gL
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ]
  fin

theorem one_round {X : List Bool} (hX : Blk X) (n m E e β r : Nat) (Lx : Strm)
    (he : 1 ≤ e) (heE : e ≤ E) (hm : 1 ≤ m) (hb : 1 ≤ β) (hr : 1 ≤ r) :
    Rch (bAtC (true ::: leftOf n m E e Lx) β 1 X r 0) (eAtC n m E e β X (r * β) Lx) := by
  refine Rch.tr (base_loop hX _ β r 0 hb hr 1 (Nat.le_refl _) hb) ?_
  have := round_end hX n m E e β r (0 + r * (β - 1)) Lx he heE hm hb hr
  have ar : r + (0 + r * (β - 1)) = r * β := by
    obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
    simp [Nat.mul_succ]; omega
  rw [ar] at this
  exact this

theorem pow_all {X : List Bool} (hX : Blk X) (n m E β : Nat) (Lx : Strm)
    (hE : 1 ≤ E) (hm : 1 ≤ m) (hb : 1 ≤ β) : ∀ e r, 1 ≤ e → e ≤ E → 1 ≤ r →
    Rch (bAtC (true ::: leftOf n m E e Lx) β 1 X r 0) (nbC n m E β X (r * β ^ (E + 1 - e)) Lx) := by
  suffices H : ∀ k e r, E - e = k → 1 ≤ e → e ≤ E → 1 ≤ r →
      Rch (bAtC (true ::: leftOf n m E e Lx) β 1 X r 0) (nbC n m E β X (r * β ^ (E + 1 - e)) Lx) from
    fun e r => H _ e r rfl
  intro k
  induction k with
  | zero =>
    intro e r h he heE hr
    have : e = E := by omega
    subst this
    refine Rch.tr (one_round hX n m e e β r Lx he heE hm hb hr) ?_
    rw [show e + 1 - e = 1 by omega, Nat.pow_one]
    exact e_done n m e β (r * β) Lx hm hb
  | succ k ih =>
    intro e r h he heE hr
    refine Rch.tr (one_round hX n m E e β r Lx he heE hm hb hr) ?_
    refine Rch.tr (e_adv n m E e β (r * β) Lx (by omega) hm hb) ?_
    have := ih (e + 1) (r * β) (by omega) (by omega) (by omega) (Nat.mul_pos hr hb)
    rw [show E + 1 - (e + 1) = E - e by omega, Nat.mul_assoc, ← Nat.pow_succ'] at this
    rw [show E + 1 - e = (E - e).succ by omega]; exact this

/-- The complete power: from round 1 with `R = 1`, reach `nb0` with `R = β ^ E`. -/
theorem pow_full {X : List Bool} (hX : Blk X) (n m E β : Nat) (Lx : Strm)
    (hE : 1 ≤ E) (hm : 1 ≤ m) (hb : 1 ≤ β) :
    Rch (bAtC (true ::: leftOf n m E 1 Lx) β 1 X 1 0) (nbC n m E β X (β ^ E) Lx) := by
  have := pow_all hX n m E β Lx hE hm hb 1 1 (Nat.le_refl _) hE (Nat.le_refl _)
  rwa [Nat.one_mul, Nat.add_sub_cancel] at this

end TM.Beal
