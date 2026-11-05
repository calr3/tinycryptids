import TinyCryptids.ErdosMoser.Copy
import TinyCryptids.ErdosMoser.Blk
namespace TM.ErdosMoser
open St

/-! The power routine of `TinyCryptids/Fermat/Pow.lean`, with the base block replaced by the
cells of M right of the marker: `p + 1` (a 1) and the cursor cells `1 .. β` (the last one next
to the separator, as the exponent cells of `TinyCryptids/Beal`). A round starts with no hole
(the cursor is on cell 1 then); the exponent block K has `k + 2` cells and the power starts
with an exponent step from its anchor on cell 1. -/

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

/-- tape right of M: `00 X 00 R 00 Q`, R value `r` with cursor at cell 1 -/
def rgt (X : List Bool) (r q : Nat) : Strm :=
  sep (app X (sep (true ::: false ::: ones r (sep (ones q blank)))))

/-- at the base cursor (cursor cell `j` holding `b`), state `bAt` -/
def bAtC (Lb : Strm) (β j : Nat) (b : Bool) (X : List Bool) (r q : Nat) : Cfg St :=
  ⟨bAt, ones j Lb, b ::: ones (β - j) (rgt X r q)⟩

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

theorem nb_back0 {X : List Bool} (hX : Blk X) (r q : Nat) (L : Strm) :
    Rch (cpyDone r q (false ::: app X.reverse (false ::: false ::: false ::: true ::: L)))
      ⟨bAt, true ::: L, false ::: rgt X r q⟩ := by
  have hw : Clean (true :: false :: false :: X.reverse) :=
    Clean.one (by simpa using hX.reverse.clean_sep_append (m := []) Clean.nil)
  have e : true ::: false ::: false ::: app X.reverse (false ::: false ::: false ::: true ::: L) =
      app (true :: false :: false :: X.reverse) (false ::: false ::: false ::: true ::: L) := by
    simp [app_append]
  unfold cpyDone; rw [e]
  refine Rch.tr (ParserL.find3 PNB hw _ _) ?_
  gR
  simp [app_append, List.reverse_append, rgt, sep]
  fin

theorem bAt_any (b : Bool) : delta bAt b = some (true, Dir.R, bA2) := by cases b <;> rfl

theorem base_adv {X : List Bool} (hX : Blk X) (Lb : Strm) (β j : Nat) (b : Bool) (r q : Nat)
    (hjb : j < β) (hr : 1 ≤ r) :
    Rch (bAtC Lb β j b X r q) (bAtC Lb β (j+1) false X r (q + r)) := by
  obtain ⟨n, hn⟩ : ∃ n, β - j = n + 1 := ⟨β - j - 1, by omega⟩
  unfold bAtC
  rw [hn, show β - (j + 1) = n by omega]
  refine Rch.tr (sR (bAt_any b)) ?_
  gR
  refine Rch.tr (mc_cross hX n r q _ hr) ?_
  refine Rch.tr (copy_full r q _ hr) ?_
  cases n with
  | zero => exact nb_back0 hX r (q + r) (ones j Lb)
  | succ n => exact nb_back hX n r (q + r) (ones j Lb)

theorem base_loop {X : List Bool} (hX : Blk X) (Lb : Strm) (β r : Nat) (hr : 1 ≤ r) :
    ∀ j b q, j < β → Rch (bAtC Lb β j b X r q) (bAtC Lb β β false X r (q + r * (β - j))) := by
  suffices H : ∀ n j b q, β - j = n + 1 →
      Rch (bAtC Lb β j b X r q) (bAtC Lb β β false X r (q + r * (β - j))) from
    fun j b q h => H _ j b q (by omega : β - j = (β - j - 1) + 1)
  intro n
  induction n with
  | zero =>
    intro j b q h
    have := base_adv hX Lb β j b r q (by omega) hr
    rw [show j + 1 = β by omega] at this
    rw [h, Nat.mul_one]; exact this
  | succ n ih =>
    intro j b q h
    refine Rch.tr (base_adv hX Lb β j b r q (by omega) hr) ?_
    have := ih (j+1) false (q + r) (by omega)
    rw [show q + r + r * (β - (j + 1)) = q + r * (β - j) by
      rw [show β - j = (β - (j+1)) + 1 by omega, Nat.mul_succ]; omega] at this
    exact this

theorem PMM : ParserR delta MM1 MM2 := ⟨rfl, rfl, rfl⟩
theorem PLE : ParserL delta LE1 LE2 := ⟨rfl, rfl, rfl⟩
theorem PLF : ParserL delta LF1 LF2 := ⟨rfl, rfl, rfl⟩
theorem PLG : ParserL delta LG1 LG2 := ⟨rfl, rfl, rfl⟩

abbrev rep (n : Nat) : List Bool := List.replicate n true

/-- left of M, read leftwards: the separator, then K (`k + 2` cells) with its cursor on `e` -/
def KL (k e : Nat) : Strm := F ::: F ::: ones (k + 1 - e) (F ::: ones e blank)

/-- left of the base block (M's cell `p + 1`), read leftwards: the marker, M's cells `0 .. p-1` -/
def ML (p k e : Nat) : Strm := F ::: ones p (KL k e)

/-- generic crossing to the R hole for a right parser whose found-action moves right -/
theorem r_cross {p1 p2 qf : St} (P : ParserR delta p1 p2) (hf : delta p2 true = some (true, Dir.R, qf))
    {X : List Bool} (hX : Blk X) (n r q : Nat) (L : Strm) (hr : 1 ≤ r) :
    Rch ⟨p1, L, ones n (rgt X r q)⟩
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

theorem ones_tt (q a : Nat) (Z : Strm) :
    ones q (true ::: true ::: ones a (true ::: Z)) = ones (q + a + 3) Z := by
  rw [show true ::: true ::: ones a (true ::: Z) = ones (a + 3) Z from by
    rw [← ones_succ']; rfl, ones_add]; congr 1

/-- at the exponent cursor (cell `e` of K), state `eAt`; M has its marker on `p` and `β + 1`
cells right of it -/
def eAtC (k e p β : Nat) (X : List Bool) (r : Nat) : Cfg St :=
  ⟨eAt, ones e blank, F ::: ones (k + 1 - e) (sep (ones p (F ::: ones (β + 1) (rgt X r 0))))⟩

/-- the left parser LG from M's cell `p - 2` (or the separator) to the exponent cursor -/
theorem lg_find (k e p : Nat) (R : Strm) (he : 1 ≤ e) (hek : e ≤ k + 1) :
    Rch (cfgL LG1 (ones p (KL k e)) R)
      ⟨eAt, ones e blank, F ::: ones (k + 1 - e) (sep (ones p R))⟩ := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  unfold KL
  generalize hd : k + 1 - (e' + 1) = d
  cases d with
  | zero =>
    have hw : Clean (rep p) := Clean.replicate p
    have e1 : ones p (F ::: F ::: ones 0 (F ::: ones (e' + 1) blank)) =
        app (rep p) (F ::: F ::: F ::: true ::: ones e' blank) := by
      simp [app_replicate, ones_succ]
    rw [e1]
    refine Rch.tr (ParserL.find3 PLG hw _ _) ?_
    gR
    simp [sep, app_replicate, List.reverse_replicate, ones_succ]
    fin
  | succ d =>
    have hw : Clean (rep p ++ F :: F :: rep (d + 1)) :=
      Clean.rep_append p (Clean.sep (Clean.replicate d))
    have e1 : ones p (F ::: F ::: ones (d + 1) (F ::: ones (e' + 1) blank)) =
        app (rep p ++ F :: F :: rep (d + 1)) (F ::: true ::: ones e' blank) := by
      simp [app_append, app_replicate, ones_succ]
    rw [e1]
    refine Rch.tr (PLG.find hw _ _) ?_
    gR
    simp [sep, app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ]
    fin

/-- end of a round: back to the marker, merge Q into R, back to the exponent cursor -/
theorem round_end {X : List Bool} (hX : Blk X) (k e p β r q : Nat) (b : Bool)
    (he : 1 ≤ e) (hek : e ≤ k + 1) (hp : 1 ≤ p) (hr : 1 ≤ r) :
    Rch (bAtC (ML p k e) β β b X r q) (eAtC k e p β X (r + q)) := by
  unfold bAtC ML
  rw [Nat.sub_self, ones_zero]
  refine Rch.tr (sR (bAt_any b)) ?_
  unfold rgt sep
  gL
  sLn (β + 1)
  gR; gR
  refine Rch.tr (r_cross PMM rfl hX β r q _ hr) ?_
  sRn (r - 1); gR; gR; sRn q
  refine blankR ?_
  rw [ones_tt q (r - 1)]
  rw [show q + (r - 1) + 3 = (q + r) + 2 by omega]
  gL; gL; gL
  rw [← app_replicate (q + r)]
  refine Rch.tr (PLE.find (Clean.replicate _) _ _) ?_
  gL
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  have hw2 : Clean (F :: F :: (X.reverse ++ F :: F :: rep (β + 1))) :=
    hX.reverse.clean_sep_append (Clean.sep (Clean.replicate β))
  have e2 : F ::: F ::: app X.reverse (F ::: F ::: ones β (true ::: F ::: tl (F ::: ones (p' + 1) (KL k e)))) =
      app (F :: F :: (X.reverse ++ F :: F :: rep (β + 1))) (F ::: true ::: ones p' (KL k e)) := by
    simp [app_append, app_replicate, ones_succ, ones_cons_true]
  rw [e2]
  refine Rch.tr (PLF.find hw2 _ _) ?_
  gL
  refine Rch.tr (lg_find k e p' _ he hek) ?_
  unfold eAtC
  simp [rgt, sep, app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ,
    ones_cons_true, cons_blank]
  first | fin | (rw [Nat.add_comm q r]; fin)

theorem PMB : ParserR delta MB1 MB2 := ⟨rfl, rfl, rfl⟩
theorem PMN : ParserR delta MN1 MN2 := ⟨rfl, rfl, rfl⟩

/-- the exponent cursor moves on: the next round starts (no base hole yet) -/
theorem e_adv (X : List Bool) (k e p β r : Nat) (hek : e ≤ k) (hp : 1 ≤ p) (hb : 1 ≤ β) :
    Rch (eAtC k e p β X r) (bAtC (ML p k (e + 1)) β 1 true X r 0) := by
  obtain ⟨d, hd⟩ : ∃ d, k + 1 - e = d + 1 := ⟨k - e, by omega⟩
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', β = b' + 1 := ⟨β - 1, by omega⟩
  unfold eAtC bAtC ML KL
  rw [hd, show k + 1 - (e + 1) = d by omega, show b' + 1 - 1 = b' by omega]
  gR; gR
  have hw : Clean (rep d ++ F :: F :: rep (p' + 1)) := Clean.rep_append d (Clean.sep (Clean.replicate p'))
  have e1 : ones d (sep (ones (p' + 1) (F ::: ones (b' + 1 + 1) (rgt X r 0)))) =
      app (rep d ++ F :: F :: rep (p' + 1)) (F ::: true ::: ones (b' + 1) (rgt X r 0)) := by
    simp [sep, app_append, app_replicate, ones_succ]
  rw [e1]
  refine Rch.tr (PMB.find hw _ _) ?_
  gR
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ]
  fin

/-- the power is done: state `N1` on the marker, the exponent cursor back on cell 1 -/
def nbC (k p β : Nat) (X : List Bool) (r : Nat) : Cfg St :=
  cfgL N1 (F ::: ones p (KL k 1)) (true ::: ones β (rgt X r 0))

theorem e_done (X : List Bool) (k p β r : Nat) (hp : 1 ≤ p) :
    Rch (eAtC k (k + 1) p β X r) (nbC k p β X r) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  unfold eAtC nbC
  rw [Nat.sub_self, ones_zero]
  gR; gL; sLn (k + 2); gR; gR; gR
  have hw : Clean (rep k ++ F :: F :: rep (p' + 1)) := Clean.rep_append k (Clean.sep (Clean.replicate p'))
  have e1 : ones k (F ::: F ::: ones (p' + 1) (F ::: ones (β + 1) (rgt X r 0))) =
      app (rep k ++ F :: F :: rep (p' + 1)) (F ::: true ::: ones β (rgt X r 0)) := by
    simp [app_append, app_replicate, ones_succ]
  rw [e1]
  refine Rch.tr (PMN.find hw _ _) ?_
  gL
  simp [KL, app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ,
    cons_blank]
  fin

theorem one_round {X : List Bool} (hX : Blk X) (k e p β r : Nat)
    (he : 1 ≤ e) (hek : e ≤ k + 1) (hp : 1 ≤ p) (hb : 1 ≤ β) (hr : 1 ≤ r) :
    Rch (bAtC (ML p k e) β 1 true X r 0) (eAtC k e p β X (r * β)) := by
  by_cases h1 : β = 1
  · subst h1
    have := round_end hX k e p 1 r 0 true he hek hp hr
    rwa [Nat.mul_one]
  · refine Rch.tr (base_loop hX _ β r hr 1 true 0 (by omega)) ?_
    have := round_end hX k e p β r (0 + r * (β - 1)) false he hek hp hr
    have ar : r + (0 + r * (β - 1)) = r * β := by
      obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
      simp [Nat.mul_succ]; omega
    rw [ar] at this
    exact this

theorem pow_all {X : List Bool} (hX : Blk X) (k p β : Nat) (hp : 1 ≤ p) (hb : 1 ≤ β) :
    ∀ e r, 1 ≤ e → e ≤ k + 1 → 1 ≤ r →
    Rch (eAtC k e p β X r) (nbC k p β X (r * β ^ (k + 1 - e))) := by
  suffices H : ∀ n e r, k + 1 - e = n → 1 ≤ e → e ≤ k + 1 → 1 ≤ r →
      Rch (eAtC k e p β X r) (nbC k p β X (r * β ^ (k + 1 - e))) from
    fun e r => H _ e r rfl
  intro n
  induction n with
  | zero =>
    intro e r h he hek hr
    have : e = k + 1 := by omega
    subst this
    rw [Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    exact e_done X k p β r hp
  | succ n ih =>
    intro e r h he hek hr
    refine Rch.tr (e_adv X k e p β r (by omega) hp hb) ?_
    refine Rch.tr (one_round hX k (e + 1) p β r (by omega) (by omega) hp hb hr) ?_
    have := ih (e + 1) (r * β) (by omega) (by omega) (by omega) (Nat.mul_pos hr hb)
    rw [show k + 1 - (e + 1) = n by omega, Nat.mul_assoc, ← Nat.pow_succ'] at this
    rw [h]; exact this

/-- The complete power: from the anchor with `R = 1`, reach `N1` with `R = β ^ k`. -/
theorem pow_full {X : List Bool} (hX : Blk X) (k p β : Nat) (hp : 1 ≤ p) (hb : 1 ≤ β) :
    Rch (eAtC k 1 p β X 1) (nbC k p β X (β ^ k)) := by
  have := pow_all hX k p β hp hb 1 1 (Nat.le_refl _) (by omega) (Nat.le_refl _)
  rwa [Nat.one_mul, Nat.add_sub_cancel] at this

end TM.ErdosMoser
