import TinyCryptids.AgohGiuga.Copy
import TinyCryptids.AgohGiuga.Blocks

/-!
# Powers by Horner's rule: `R := β * R`, once per advance of the exponent hole

Tape, left to right: the exponent block (value `e`, hole at `ep`), a gap `gE`, the base block
(value `β`, hole), a gap `gB`, the skipped block `S = 1^a 0 1^b` (a hole anywhere), `00`, the
result `R = 1 0 1^r` (cursor at cell 1), `00`, the copies `Q = 1^q`, blank.
(Ported from `../Firoozbakht/Horner.lean`, where the skipped block has its hole at cell 1.)
-/

namespace TM.AgohGiuga
open St

theorem Gap.rev_head {g : List Bool} (h : Gap g) : ∃ g', g.reverse = false :: g' := by
  rcases h with rfl | ⟨P, _, rfl⟩
  · exact ⟨[false], rfl⟩
  · exact ⟨false :: (P.reverse ++ [false, false]), by simp⟩

theorem Gap.head {g : List Bool} (h : Gap g) : ∃ g', g = false :: g' := by
  rcases h with rfl | ⟨P, _, rfl⟩
  · exact ⟨[false], rfl⟩
  · exact ⟨_, rfl⟩

/-- a left parser that only crosses 1s before its hole (no transition for `00`) -/
structure ParserL1 (p1 p2 : St) : Prop where
  h1 : delta p1 true = some (true, Dir.L, p1)
  h0 : delta p1 false = some (false, Dir.L, p2)

theorem ParserL1.find {p1 p2 : St} (P : ParserL1 p1 p2) (n : Nat) (s R : Strm) :
    Rch (cfgL p1 (app (List.replicate n true) (false ::: true ::: s)) R)
      (cfgL p2 (true ::: s) (false ::: app (List.replicate n true).reverse R)) := by
  rw [app_replicate, List.reverse_replicate, app_replicate]
  exact Rch.tr (scanL P.h1 n _ R) (sL P.h0)

/-- the skipped block: `a` ones, the hole, `b` ones -/
def skq (a b : Nat) : List Bool := List.replicate a true ++ false :: List.replicate b true

/-- the tape right of the base block -/
def rgt (gB : List Bool) (a b r q : Nat) : Strm :=
  app gB (app (skq a b) (sep (true ::: false ::: ones r (sep (ones q blank)))))

/-- the tape left of the base block: the gap, then the exponent block with its hole at `ep` -/
def lftE (Le : Strm) (e ep : Nat) (gE : List Bool) : Strm :=
  app gE.reverse (ones (e + 1 - ep) (false ::: ones ep Le))

/-- at the base hole (cell `j`) -/
def bAtC (Lb : Strm) (β j : Nat) (gB : List Bool) (a b r q : Nat) : Cfg St :=
  ⟨ba1, ones j Lb, false ::: ones (β + 1 - j) (rgt gB a b r q)⟩

theorem PMC : ParserR delta MC1 MC2 := ⟨rfl, rfl, rfl⟩
theorem PMD : ParserR delta MD1 MD2 := ⟨rfl, rfl, rfl⟩
theorem PMM : ParserR delta MM1 MM2 := ⟨rfl, rfl, rfl⟩
theorem PMN : ParserR delta MN1 MN2 := ⟨rfl, rfl, rfl⟩
theorem PNB : ParserL delta NB1 NB2 := ⟨rfl, rfl, rfl⟩
theorem PNC : ParserL delta NC1 NC2 := ⟨rfl, rfl, rfl⟩
theorem PHE : ParserL1 HE1 HE2 := ⟨rfl, rfl⟩
theorem PHF : ParserL delta HF1 HF2 := ⟨rfl, rfl, rfl⟩
theorem PHG : ParserL delta HG1 HG2 := ⟨rfl, rfl, rfl⟩
theorem PHH : ParserL delta HH1 HH2 := ⟨rfl, rfl, rfl⟩
theorem PMB : ParserR delta MB1 MB2 := ⟨rfl, rfl, rfl⟩

/-- two right parsers from the base to the R cursor (past the skipped hole) -/
theorem r_cross2 {p1 p2 p3 p4 qf : St} (P : ParserR delta p1 p2) (P' : ParserR delta p3 p4)
    (h2 : delta p2 true = some (true, Dir.R, p3)) (hf : delta p4 true = some (true, Dir.R, qf))
    {gB : List Bool} (hg : Gap gB) (n a b r q : Nat) (L : Strm) (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : 1 ≤ r) :
    Rch ⟨p1, L, ones n (rgt gB a b r q)⟩
      ⟨qf, true ::: false ::: true ::: false ::: false ::: app (skq a b).reverse (app gB.reverse (ones n L)),
        ones (r - 1) (sep (ones q blank))⟩ := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hw : Clean (List.replicate n true ++ (gB ++ List.replicate (a + 1) true)) :=
    Clean.rep_append n (by rw [List.replicate_succ]; exact hg.clean (Clean.replicate a))
  have e : ones n (rgt gB (a + 1) (b + 1) (r + 1) q) =
      app (List.replicate n true ++ (gB ++ List.replicate (a + 1) true))
        (false ::: true ::: ones b (false ::: false ::: true ::: false ::: ones (r + 1) (sep (ones q blank)))) := by
    simp only [rgt, skq, sep, app_append, app_replicate, app_cons, app_nil, ones_succ]
  rw [e]
  refine Rch.tr (P.find hw _ _) ?_
  refine Rch.tr (sR h2) ?_
  have hw2 : Clean (List.replicate b true ++ [false, false, true]) :=
    Clean.rep_append b (Clean.sep Clean.nil)
  have e2 : ones b (false ::: false ::: true ::: false ::: ones (r + 1) (sep (ones q blank))) =
      app (List.replicate b true ++ [false, false, true]) (false ::: true ::: ones r (sep (ones q blank))) := by
    simp only [app_append, app_replicate, app_cons, app_nil, ones_succ]
  rw [e2]
  refine Rch.tr (P'.find hw2 _ _) ?_
  refine Rch.tr (sR hf) ?_
  simp only [skq, List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil,
    List.nil_append, app_append, app_replicate, app_cons, app_nil, List.singleton_append,
    List.cons_append, List.append_assoc, ones_succ, ones_zero, ones_cons_true, Nat.add_sub_cancel]
  fin

/-- back from the R block (cursor reset) past the skipped hole to the base hole -/
theorem nb_back {gB : List Bool} (hg : Gap gB) (a b r q k j : Nat) (Lb : Strm) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Rch (cpyDone r q (false ::: app (skq a b).reverse (app gB.reverse
        (ones (k + 1) (false ::: ones (j + 1) Lb)))))
      ⟨ba1, ones (j + 1) Lb, false ::: ones (k + 1) (rgt gB a b r q)⟩ := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hw : Clean (true :: false :: false :: List.replicate (b + 1) true) :=
    Clean.one (by rw [List.replicate_succ]; exact Clean.sep (Clean.replicate b))
  have e : true ::: false ::: false ::: app (skq (a + 1) (b + 1)).reverse
      (app gB.reverse (ones (k + 1) (false ::: ones (j + 1) Lb))) =
      app (true :: false :: false :: List.replicate (b + 1) true)
        (false ::: true ::: ones a (app gB.reverse (ones (k + 1) (false ::: ones (j + 1) Lb)))) := by
    simp only [skq, List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc,
      List.singleton_append, List.cons_append, app_append, app_replicate, app_cons, List.nil_append,
      List.reverse_nil, app_nil, ones_succ]
  unfold cpyDone; rw [e]
  refine Rch.tr (PNB.find hw _ _) ?_
  gL
  have hw2 : Clean (List.replicate a true ++ (gB.reverse ++ List.replicate (k + 1) true)) :=
    Clean.rep_append a (by rw [List.replicate_succ]; exact hg.reverse.clean (Clean.replicate k))
  have e2 : ones a (app gB.reverse (ones (k + 1) (false ::: ones (j + 1) Lb))) =
      app (List.replicate a true ++ (gB.reverse ++ List.replicate (k + 1) true))
        (false ::: true ::: ones j Lb) := by
    simp only [app_append, app_replicate, ones_succ]
  rw [e2]
  refine Rch.tr (PNC.find hw2 _ _) ?_
  gR
  simp only [rgt, sep, skq, List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.singleton_append,
    List.append_assoc, app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero, ones_cons_true,
    tl_cons]
  fin

theorem base_adv {gB : List Bool} (hg : Gap gB) (Lb : Strm) (β j a b r q : Nat)
    (hj : 1 ≤ j) (hjb : j < β) (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : 1 ≤ r) :
    Rch (bAtC Lb β j gB a b r q) (bAtC Lb β (j + 1) gB a b r (q + r)) := by
  obtain ⟨k, hk⟩ : ∃ k, β + 1 - j = k + 2 := ⟨β - j - 1, by omega⟩
  unfold bAtC
  rw [hk, show β + 1 - (j + 1) = k + 1 by omega]
  gR; gR; gL; gR
  refine Rch.tr (r_cross2 PMC PMD rfl rfl hg (k + 1) a b r q _ ha hb hr) ?_
  refine Rch.tr (copy_full r q _ hr) ?_
  exact nb_back hg a b r (q + r) k j Lb ha hb

theorem base_loop {gB : List Bool} (hg : Gap gB) (Lb : Strm) (β a b r q : Nat)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : 1 ≤ r) : ∀ j, 1 ≤ j → j ≤ β →
    Rch (bAtC Lb β j gB a b r q) (bAtC Lb β β gB a b r (q + r * (β - j))) := by
  suffices H : ∀ n j q, β - j = n → 1 ≤ j → j ≤ β →
      Rch (bAtC Lb β j gB a b r q) (bAtC Lb β β gB a b r (q + r * (β - j))) from
    fun j hj hjb => H _ j q rfl hj hjb
  intro n
  induction n with
  | zero =>
    intro j q h hj hjb
    have : β = j := by omega
    subst this; simp; fin
  | succ n ih =>
    intro j q h hj hjb
    refine Rch.tr (base_adv hg Lb β j a b r q hj (by omega) ha hb hr) ?_
    have := ih (j + 1) (q + r) (by omega) (by omega) (by omega)
    rw [show q + r + r * (β - (j + 1)) = q + r * (β - j) by
      rw [show β - j = (β - (j + 1)) + 1 by omega, Nat.mul_succ]; omega] at this
    exact this

theorem ones_tt (q a : Nat) (Z : Strm) :
    ones q (true ::: true ::: ones a (true ::: Z)) = ones (q + a + 3) Z := by
  rw [show true ::: true ::: ones a (true ::: Z) = ones (a + 3) Z from by
    rw [← ones_succ']; rfl, ones_add, Nat.add_assoc]

/-- the base hole wraps; to the R cursor; merge `R 00 Q` into `R + Q` -/
theorem base_wrap {gB : List Bool} (hg : Gap gB) (Lb : Strm) (β a b r q : Nat)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : 1 ≤ r) :
    Rch (bAtC (false ::: Lb) β β gB a b r q)
      (cfgL HE1 (ones (r + q) (false ::: true ::: false ::: false ::: app (skq a b).reverse
        (app gB.reverse (ones β (false ::: true ::: false ::: Lb))))) blank) := by
  obtain ⟨g', hg'⟩ := hg.head
  unfold bAtC; rw [show β + 1 - β = 1 by omega]
  unfold rgt; rw [hg']; simp only [app_cons]
  gR; gR; gL
  sLn (β + 2)
  gR; gR; gR
  rw [← app_cons, ← hg']
  show Rch ⟨MM1, false ::: true ::: false ::: Lb, ones β (rgt gB a b r q)⟩ _
  refine Rch.tr (r_cross2 PMM PMN rfl rfl hg β a b r q _ ha hb hr) ?_
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel, sep]
  sRn r'
  gR; gR
  sRn q
  refine blankR ?_
  gL
  cases q with
  | zero =>
    gL; gL
    simp only [cons_blank]; rw [← ones_succ']; fin
  | succ q =>
    gL; rw [ones_cons_true]; gL
    simp only [cons_blank]
    rw [← ones_succ', ← ones_succ', ones_add, show q + 1 + (r' + 1) = r' + 1 + (q + 1) by omega]; fin

/-- the base block with its hole at cell 1 -/
def bH1 (β : Nat) : List Bool := true :: false :: List.replicate β true

/-- from the R cursor (or right of it) left to the exponent hole: past the R cursor, the
skipped hole and the base hole -/
theorem he_chain {gB gE : List Bool} (hgB : Gap gB) (hgE : Gap gE) (Le Rx : Strm)
    (e ep β a b t : Nat) (hep : 1 ≤ ep) (hepe : ep ≤ e) (hβ : 1 ≤ β) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Rch (cfgL HE1 (ones t (false ::: true ::: false ::: false ::: app (skq a b).reverse
        (app gB.reverse (ones β (false ::: true ::: lftE Le e ep gE))))) Rx)
      ⟨ea1, ones ep Le, false ::: ones (e + 1 - ep) (app gE (app (bH1 β) (app gB (app (skq a b)
        (false ::: false ::: true ::: false ::: ones t Rx)))))⟩ := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  obtain ⟨β, rfl⟩ : ∃ β', β = β' + 1 := ⟨β - 1, by omega⟩
  obtain ⟨ep, rfl⟩ : ∃ ep', ep = ep' + 1 := ⟨ep - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, e + 1 - (ep + 1) = k + 1 := ⟨e - ep - 1, by omega⟩
  have e1 : ones t (false ::: true ::: false ::: false ::: app (skq (a + 1) (b + 1)).reverse
      (app gB.reverse (ones (β + 1) (false ::: true ::: lftE Le e (ep + 1) gE)))) =
      app (List.replicate t true) (false ::: true ::: app (false :: false :: List.replicate (b + 1) true)
        (false ::: true ::: app (List.replicate a true ++ (gB.reverse ++ List.replicate (β + 1) true))
          (false ::: true ::: app (gE.reverse ++ List.replicate (k + 1) true)
            (false ::: true ::: ones ep Le)))) := by
    simp only [lftE, skq, hk, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, List.reverse_nil,
      app_append, app_replicate, app_cons, app_nil, ones_succ]
  rw [e1]
  refine Rch.tr (PHE.find t _ _) ?_
  gL
  refine Rch.tr (PHF.find (by rw [List.replicate_succ]; exact Clean.sep (Clean.replicate b)) _ _) ?_
  gL
  refine Rch.tr (PHG.find (Clean.rep_append a (by
    rw [List.replicate_succ]; exact hgB.reverse.clean (Clean.replicate β))) _ _) ?_
  gL
  refine Rch.tr (PHH.find (by rw [List.replicate_succ]; exact hgE.reverse.clean (Clean.replicate k)) _ _) ?_
  gR
  rw [hk]
  simp only [bH1, skq, List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.singleton_append,
    List.append_assoc, app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero, ones_cons_true,
    tl_cons]
  fin

/-- at the exponent hole (cell `ep`); base hole at cell 1; `R = r`, no copies -/
def eAtC (Le : Strm) (e ep : Nat) (gE : List Bool) (β : Nat) (gB : List Bool) (a b r : Nat) : Cfg St :=
  ⟨ea1, ones ep Le, false ::: ones (e + 1 - ep) (app gE (app (bH1 β) (rgt gB a b r 0)))⟩

theorem sep_blank : sep (ones 0 blank) = blank := by simp [sep, cons_blank]

/-- one round: `R := β * R`, the exponent hole moves one cell right -/
theorem exp_round {gB gE : List Bool} (hgB : Gap gB) (hgE : Gap gE) (Le : Strm)
    (e ep β a b r : Nat) (hep : 1 ≤ ep) (hepe : ep < e) (hβ : 1 ≤ β) (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : 1 ≤ r) :
    Rch (eAtC Le e ep gE β gB a b r) (eAtC Le e (ep + 1) gE β gB a b (β * r)) := by
  obtain ⟨k, hk⟩ : ∃ k, e + 1 - ep = k + 2 := ⟨e - ep - 1, by omega⟩
  unfold eAtC; rw [hk]
  gR; gR; gL; gR
  show Rch ⟨MB1, false ::: ones (ep + 1) Le, ones (k + 1) (app gE (app (bH1 β) (rgt gB a b r 0)))⟩ _
  have hw : Clean (List.replicate (k + 1) true ++ (gE ++ [true])) :=
    Clean.rep_append _ (hgE.clean Clean.nil)
  have e1 : ones (k + 1) (app gE (app (bH1 β) (rgt gB a b r 0))) =
      app (List.replicate (k + 1) true ++ (gE ++ [true]))
        (false ::: true ::: ones (β - 1) (rgt gB a b r 0)) := by
    obtain ⟨β', rfl⟩ : ∃ β', β = β' + 1 := ⟨β - 1, by omega⟩
    simp only [bH1, app_append, app_replicate, app_cons, app_nil, ones_succ, Nat.add_sub_cancel]
  rw [e1]
  refine Rch.tr (PMB.find hw _ _) ?_
  gL
  have hl : lftE Le e (ep + 1) gE = app (gE.reverse ++ List.replicate (k + 1) true)
      (false ::: ones (ep + 1) Le) := by
    simp only [lftE, show e + 1 - (ep + 1) = k + 1 by omega, app_append, app_replicate]
  have hbl := base_loop hgB (lftE Le e (ep + 1) gE) β a b r 0 ha hb hr 1 (Nat.le_refl _) hβ
  unfold bAtC at hbl
  rw [show β + 1 - 1 = β by omega] at hbl
  refine Rch.tr (?_ : Rch _ ⟨ba1, ones 1 (lftE Le e (ep + 1) gE), false ::: ones β (rgt gB a b r 0)⟩) ?_
  · rw [hl]
    simp only [List.reverse_append, List.reverse_replicate, app_append, app_replicate]
    obtain ⟨β', rfl⟩ : ∃ β', β = β' + 1 := ⟨β - 1, by omega⟩
    simp only [Nat.add_sub_cancel, ones_succ]
    fin
  refine Rch.tr hbl ?_
  obtain ⟨g', hg'⟩ := hgE.rev_head
  have hl2 : lftE Le e (ep + 1) gE = false ::: app g' (ones (e + 1 - (ep + 1)) (false ::: ones (ep + 1) Le)) := by
    simp only [lftE, hg', app_cons]
  rw [hl2]
  refine Rch.tr (base_wrap hgB _ β a b r _ ha hb hr) ?_
  rw [← hl2]
  have := he_chain hgB hgE Le blank e (ep + 1) β a b (β * r) (by omega) (by omega) hβ ha hb
  have ha : r + (0 + r * (β - 1)) = β * r := by
    obtain ⟨β', rfl⟩ : ∃ β', β = β' + 1 := ⟨β - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.succ_mul, Nat.mul_comm r β']; omega
  rw [ha]
  refine Rch.tr this ?_
  simp only [rgt, sep_blank]
  simp only [sep, ones_zero, cons_blank]
  fin

theorem exp_wrap (Le : Strm) (e : Nat) (gE : List Bool) (β : Nat) (gB : List Bool) (a b r : Nat) (he : 1 ≤ e)
    (hgE : Gap gE) :
    Rch (eAtC (false ::: Le) e e gE β gB a b r)
      ⟨PD1, false ::: true ::: false ::: Le, ones e (app gE (app (bH1 β) (rgt gB a b r 0)))⟩ := by
  obtain ⟨g', hg'⟩ := hgE.head
  unfold eAtC; rw [show e + 1 - e = 1 by omega, hg']
  simp only [app_cons]
  gR; gR; gL
  sLn (e + 2)
  gR; gR; gR
  rw [← app_cons]; fin

/-- `n` rounds of `R := β * R` -/
def hrn (β : Nat) : Nat → Nat → Nat
  | r, 0 => r
  | r, n + 1 => hrn β (β * r) n

theorem hrn_pow (β : Nat) : ∀ n r, hrn β r n = β ^ n * r := by
  intro n
  induction n with
  | zero => intro r; simp [hrn]
  | succ n ih =>
    intro r
    show hrn β (β * r) n = _
    rw [ih, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm β r, ← Nat.mul_assoc]

theorem hrn_pos (β : Nat) (hβ : 1 ≤ β) : ∀ n r, 1 ≤ r → 1 ≤ hrn β r n := by
  intro n
  induction n with
  | zero => intro r h; exact h
  | succ n ih => intro r h; exact ih _ (Nat.le_trans h (Nat.le_mul_of_pos_left r hβ))

theorem exp_loop {gB gE : List Bool} (hgB : Gap gB) (hgE : Gap gE) (Le : Strm)
    (e β a b : Nat) (hβ : 1 ≤ β) (ha : 1 ≤ a) (hb : 1 ≤ b) : ∀ n ep r, e - ep = n → 1 ≤ ep → ep ≤ e → 1 ≤ r →
    Rch (eAtC Le e ep gE β gB a b r) (eAtC Le e e gE β gB a b (hrn β r n)) := by
  intro n
  induction n with
  | zero =>
    intro ep r h h1 h2 _
    have : e = ep := by omega
    subst this; fin
  | succ n ih =>
    intro ep r h h1 h2 hr
    refine Rch.tr (exp_round hgB hgE Le e ep β a b r h1 (by omega) hβ ha hb hr) ?_
    exact ih (ep + 1) _ (by omega) (by omega) (by omega) (Nat.le_trans hr (Nat.le_mul_of_pos_left r hβ))

/-- **Powers**: from the exponent hole at cell `ep` and `R = 1`, the result `R = β ^ (e - ep)`;
the head ends at cell 2 of the exponent block (its hole back at cell 1), state `PD1` -/
theorem horner {gB gE : List Bool} (hgB : Gap gB) (hgE : Gap gE) (Le : Strm)
    (e ep β a b : Nat) (hep : 1 ≤ ep) (hepe : ep ≤ e) (hβ : 1 ≤ β) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Rch (eAtC (false ::: Le) e ep gE β gB a b 1)
      ⟨PD1, false ::: true ::: false ::: Le, ones e (app gE (app (bH1 β) (rgt gB a b (β ^ (e - ep)) 0)))⟩ := by
  have := exp_loop hgB hgE (false ::: Le) e β a b hβ ha hb (e - ep) ep 1 rfl hep hepe (Nat.le_refl _)
  rw [hrn_pow, Nat.mul_one] at this
  exact Rch.tr this (exp_wrap Le e gE β gB a b _ (by omega) hgE)

end TM.AgohGiuga
