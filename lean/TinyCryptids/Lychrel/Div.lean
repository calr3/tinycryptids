import TinyCryptids.Lychrel.DStep

/-!
# Division by 10: the hole walk through T

The tape right of D: `00`, a context `cx` (empty when T is X; else X and a gap), then T
(`t + 3` cells, hole at cell `c`), `h` zeros, A (`a + 1` cells), and Q (absent, or
after `00`, `q` cells).
-/

namespace TM.Lychrel
open St

local notation "F" => false

def Qp : Option Nat → Strm
  | none => blank
  | some q => F ::: F ::: ones q blank

def Qn : Option Nat → Option Nat
  | none => some 3
  | some q => some (q + 1)

/-- T with its hole at cell `c`, then `h` zeros, A and Q -/
def TAQ (t c h a : Nat) (Q : Option Nat) : Strm :=
  ones c (F ::: ones (t + 2 - c) (zeros h (ones (a + 1) (Qp Q))))

/-- about to step the counter (at D's hole), T's hole at cell `c` -/
def DV (cx : List Bool) (t c p h a : Nat) (Q : Option Nat) : Cfg St :=
  ⟨fA, ones (p + 1) blank, F ::: ones (10 - p) (F ::: F ::: app cx (TAQ t c h a Q))⟩

/-- the segments the finders cross between D and T -/
structure CX (cx : List Bool) : Prop where
  r : ∀ n c, GC (List.replicate (n + 1) true ++ F :: F :: (cx ++ List.replicate (c + 1) true))
  l : ∀ n c, GC (List.replicate (c + 1) true ++ (cx.reverse ++ F :: F :: List.replicate (n + 1) true))

theorem FN : FindR delta nP nZ1 nZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FW : FindR delta wP wZ1 wZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FF : FindL delta hFP hFZ1 hFZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FK : FindL delta bkP bkZ1 bkZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem FB : FindL delta hBP hBZ1 hBZ2 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem app_ones_list (n : Nat) (l : List Bool) (s : Strm) :
    app (List.replicate n true ++ l) s = ones n (app l s) := by rw [app_append, app_replicate]

theorem app_rev_simp (l : List Bool) (s : Strm) (b : Bool) :
    app (l ++ [b]) s = app l (b ::: s) := by rw [app_append]; rfl

theorem ones_tr (n : Nat) (s : Strm) : ones n (true ::: s) = ones (n + 1) s := (ones_succ' n s).symm
theorem zeros_fa (n : Nat) (s : Strm) : zeros n (false ::: s) = zeros (n + 1) s := (zeros_succ' n s).symm

theorem GC.zl (k : Nat) {l : List Bool} (hl : GC l) :
    GC (List.replicate (k + 2) false ++ true :: l) := by
  have := GC.gap k hl
  simpa [List.replicate_succ] using this

/-- advance T's hole from cell `c + 1` (head on it), then back to D's hole -/
theorem adv_hf (cx : List Bool) (hcx : CX cx) (c n p m : Nat) (X : Strm) :
    Rch ⟨a1, app (List.replicate (c + 1) true ++ (cx.reverse ++ F :: F :: List.replicate (n + 1) true))
        (F ::: ones (p + 1) blank), F ::: ones (m + 2) X⟩
      ⟨fA, ones (p + 1) blank, F ::: ones (n + 1) (F ::: F ::: app cx (ones (c + 2) (F ::: ones (m + 1) X)))⟩ := by
  gR; gR; gL; gL
  show Rch (cfgL hFP (true ::: app (List.replicate (c + 1) true ++ (cx.reverse ++ F :: F :: List.replicate (n + 1) true))
      (F ::: ones (p + 1) blank)) (F ::: true ::: ones m X)) _
  have e2 : (true ::: app (List.replicate (c + 1) true ++ (cx.reverse ++ F :: F :: List.replicate (n + 1) true))
      (F ::: ones (p + 1) blank)) =
      app (List.replicate (c + 1 + 1) true ++ (cx.reverse ++ F :: F :: List.replicate (n + 1) true))
        (F ::: ones (p + 1) blank) := by
    simp [app_append, app_replicate, ones_succ]
  rw [e2]
  refine Rch.tr (FF.cross (hcx.l n (c + 1)) _ _) ?_
  gL; gR
  simp [app_append, app_replicate, List.reverse_append, List.reverse_replicate, ones_succ]
  fin

/-- from D's cell right of the new hole (no wrap), find T's hole and advance it -/
theorem n_adv (cx : List Bool) (hcx : CX cx) (c n p m : Nat) (X : Strm) :
    Rch ⟨nP, F ::: ones (p + 1) blank, ones (n + 1) (F ::: F ::: app cx (ones (c + 1) (F ::: ones (m + 2) X)))⟩
      ⟨fA, ones (p + 1) blank, F ::: ones (n + 1) (F ::: F ::: app cx (ones (c + 2) (F ::: ones (m + 1) X)))⟩ := by
  have e1 : ones (n + 1) (F ::: F ::: app cx (ones (c + 1) (F ::: ones (m + 2) X))) =
      app (List.replicate (n + 1) true ++ F :: F :: (cx ++ List.replicate (c + 1) true))
        (F ::: ones (m + 2) X) := by
    simp [app_append, app_replicate]
  rw [e1]
  refine Rch.tr (FN.cross (hcx.r n c) _ _) ?_
  gR; gL
  have e2 : (List.replicate (n + 1) true ++ F :: F :: (cx ++ List.replicate (c + 1) true)).reverse =
      List.replicate (c + 1) true ++ (cx.reverse ++ F :: F :: List.replicate (n + 1) true) := by
    simp [List.reverse_append, List.reverse_replicate]
  rw [e2]
  exact adv_hf cx hcx c n p m X

/-- the cells Q gets on the left stream of `bkP` after an append -/
def qcells : Option Nat → Nat
  | none => 2
  | some q => q

theorem qcells_pos (Q : Option Nat) (hQ : ∀ q, Q = some q → 1 ≤ q) : 1 ≤ qcells Q := by
  cases Q with
  | none => decide
  | some q => exact hQ q rfl

/-- right of T's hole: append to Q, come back to the hole -/
theorem excursion (Lx : Strm) (m h a : Nat) (Q : Option Nat) (hh : 2 ≤ h)
    (hQ : ∀ q, Q = some q → 1 ≤ q) :
    Rch ⟨wZ1, F ::: true ::: Lx, ones (m + 1) (zeros h (ones (a + 1) (Qp Q)))⟩
      ⟨a1, true ::: Lx, F ::: ones (m + 1) (zeros h (ones (a + 1) (Qp (Qn Q))))⟩ := by
  obtain ⟨g, rfl⟩ : ∃ g, h = g + 2 := ⟨h - 2, by omega⟩
  have key : ∀ (qc : Nat) (R : Strm), 1 ≤ qc →
      Rch (cfgL bkP (ones qc (F ::: F ::: ones (a + 1) (zeros (g + 2) (ones (m + 1) (F ::: true ::: Lx))))) R)
        ⟨a1, true ::: Lx, F ::: ones (m + 1) (zeros (g + 2) (ones (a + 1) (F ::: F ::: ones qc R)))⟩ := by
    intro qc R hqc
    obtain ⟨qd, rfl⟩ : ∃ qd, qc = qd + 1 := ⟨qc - 1, by omega⟩
    have hw : GC (List.replicate (qd + 1) true ++ F :: F :: (List.replicate (a + 1) true ++
        (List.replicate (g + 2) false ++ List.replicate (m + 1) true))) := by
      refine GC.append (GC.replicate _) ?_
      have := GC.gap (l := List.replicate a true ++ (List.replicate (g + 2) false ++ List.replicate (m + 1) true)) 0
        (GC.append (GC.replicate a) (GC.zl g (GC.replicate m)))
      simpa [List.replicate_succ] using this
    have e1 : ones (qd + 1) (F ::: F ::: ones (a + 1) (zeros (g + 2) (ones (m + 1) (F ::: true ::: Lx)))) =
        app (List.replicate (qd + 1) true ++ F :: F :: (List.replicate (a + 1) true ++
          (List.replicate (g + 2) false ++ List.replicate (m + 1) true))) (F ::: true ::: Lx) := by
      simp [app_append, app_replicate, app_zeros]
    rw [e1]
    refine Rch.tr (FK.cross hw _ _) ?_
    gL; gR
    simp [app_append, app_replicate, app_zeros, List.reverse_append, List.reverse_replicate]
    fin
  gR; sRn m
  show Rch ⟨e1, _, F ::: zeros (g + 1) (true ::: ones a (Qp Q))⟩ _
  gR; zRn (g + 1); gR; sRn a
  cases Q with
  | none =>
    simp only [Qp, Qn]
    refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR
    refine blankR ?_; gL
    show Rch (cfgL bkP (ones 2 (F ::: F ::: ones a (true ::: zeros (g + 1) (F ::: ones m
      (true ::: F ::: true ::: Lx))))) (true ::: blank)) _
    rw [ones_tr a, zeros_fa (g + 1), ones_tr m]
    exact key 2 (true ::: blank) (by decide)
  | some q =>
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := hQ q rfl; omega⟩
    simp only [Qp, Qn]
    gR; gR; gR; sRn r; refine blankR ?_; gL
    rw [ones_tr r, ones_tr a, zeros_fa (g + 1), ones_tr m,
      show ones (r + 1 + 1) blank = ones (r + 1) (true ::: blank) from ones_succ' (r + 1) blank]
    exact key (r + 1) (true ::: blank) (by omega)

/-! ## one step of the walk -/

theorem dv_step (cx : List Bool) (hcx : CX cx) (t c p h a : Nat) (Q : Option Nat)
    (hc : 1 ≤ c) (hct : c ≤ t) (hp : p ≤ 8) :
    Rch (DV cx t c p h a Q) (DV cx t (c + 1) (p + 1) h a Q) := by
  obtain ⟨k, hk⟩ : ∃ k, p + k = 8 := ⟨8 - p, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, t + 2 - (c' + 1) = m + 2 := ⟨t - c' - 1, by omega⟩
  unfold DV TAQ
  rw [show 10 - p = k + 2 by omega, show 10 - (p + 1) = k + 1 by omega, hm,
    show t + 2 - (c' + 1 + 1) = m + 1 by omega]
  refine Rch.tr (fstep p k _) ?_
  exact n_adv cx hcx c' k (p + 1) m _

theorem dv_wrap (cx : List Bool) (hcx : CX cx) (t c h a : Nat) (Q : Option Nat)
    (hc : 1 ≤ c) (hct : c ≤ t) (hh : 2 ≤ h) (hQ : ∀ q, Q = some q → 1 ≤ q) :
    Rch (DV cx t c 9 h a Q) (DV cx t (c + 1) 0 h a (Qn Q)) := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, t + 2 - (c' + 1) = m + 2 := ⟨t - c' - 1, by omega⟩
  unfold DV TAQ
  rw [show 10 - 9 = 1 by rfl, show 10 - 0 = 10 by rfl, hm, show t + 2 - (c' + 1 + 1) = m + 1 by omega]
  refine Rch.tr (fstep_wrap _) ?_
  have e1 : ones 10 (F ::: F ::: app cx (ones (c' + 1) (F ::: ones (m + 2) (zeros h (ones (a + 1) (Qp Q)))))) =
      app (List.replicate (9 + 1) true ++ F :: F :: (cx ++ List.replicate (c' + 1) true))
        (F ::: ones (m + 2) (zeros h (ones (a + 1) (Qp Q)))) := by
    rw [app_append, app_replicate]; simp [app_append, app_replicate]
  rw [e1]
  refine Rch.tr (FW.cross (hcx.r 9 c') _ _) ?_
  gR
  have e2 : (List.replicate (9 + 1) true ++ F :: F :: (cx ++ List.replicate (c' + 1) true)).reverse =
      List.replicate (c' + 1) true ++ (cx.reverse ++ F :: F :: List.replicate (9 + 1) true) := by
    simp [List.reverse_append, List.reverse_replicate]
  rw [e2, app_ones_list]
  show Rch ⟨wZ1, F ::: true ::: ones c' (app (cx.reverse ++ F :: F :: List.replicate (9 + 1) true)
    (F ::: ones 1 blank)), _⟩ _
  refine Rch.tr (excursion _ (m + 1) h a Q hh hQ) ?_
  rw [show (true ::: ones c' (app (cx.reverse ++ F :: F :: List.replicate (9 + 1) true) (F ::: ones 1 blank))) =
    app (List.replicate (c' + 1) true ++ (cx.reverse ++ F :: F :: List.replicate (9 + 1) true))
      (F ::: ones (0 + 1) blank) by simp [app_append, app_replicate, ones_succ]]
  exact adv_hf cx hcx c' 9 0 m _

/-! ## the last step: the hole reaches T's last cell -/

/-- the walk is over: head on T's last cell -/
def WD (cx : List Bool) (t p h a : Nat) (Q : Option Nat) : Cfg St :=
  cfgL wd1 (ones (t + 3) (app cx.reverse (F ::: F ::: ones (10 - p) (F ::: ones (p + 1) blank))))
    (zeros h (ones (a + 1) (Qp Q)))

theorem a1_done (L X : Strm) (h : Nat) (hh : 1 ≤ h) :
    Rch ⟨a1, L, F ::: true ::: zeros h X⟩ (cfgL wd1 (true ::: true ::: L) (zeros h X)) := by
  obtain ⟨g, rfl⟩ : ∃ g, h = g + 1 := ⟨h - 1, by omega⟩
  gR; gR; gL; fin

theorem wd_eq (cx : List Bool) (t n p : Nat) :
    (true ::: true ::: app (List.replicate (t + 1) true ++ (cx.reverse ++ F :: F :: List.replicate (n + 1) true))
      (F ::: ones (p + 1) blank)) =
      ones (t + 3) (app cx.reverse (F ::: F ::: ones (n + 1) (F ::: ones (p + 1) blank))) := by
  simp [app_append, app_replicate, ones_succ]

theorem dv_last (cx : List Bool) (hcx : CX cx) (t p h a : Nat) (Q : Option Nat)
    (hp9 : p ≤ 9) (hh : 2 ≤ h) (hQ : ∀ q, Q = some q → 1 ≤ q) :
    Rch (DV cx t (t + 1) p h a Q)
      (WD cx t ((p + 1) % 10) h a (if p = 9 then Qn Q else Q)) := by
  by_cases hp : p ≤ 8
  · obtain ⟨k, hk⟩ : ∃ k, p + k = 8 := ⟨8 - p, by omega⟩
    rw [if_neg (by omega), Nat.mod_eq_of_lt (by omega)]
    unfold DV TAQ WD
    rw [show 10 - p = k + 2 by omega, show 10 - (p + 1) = k + 1 by omega,
      show t + 2 - (t + 1) = 1 by omega]
    refine Rch.tr (fstep p k _) ?_
    have e1 : ones (k + 1) (F ::: F ::: app cx (ones (t + 1) (F ::: ones 1 (zeros h (ones (a + 1) (Qp Q)))))) =
        app (List.replicate (k + 1) true ++ F :: F :: (cx ++ List.replicate (t + 1) true))
          (F ::: true ::: zeros h (ones (a + 1) (Qp Q))) := by
      simp [app_append, app_replicate]; rfl
    rw [e1]
    refine Rch.tr (FN.cross (hcx.r k t) _ _) ?_
    gR; gL
    refine Rch.tr (a1_done _ _ h (by omega)) ?_
    rw [show (List.replicate (k + 1) true ++ F :: F :: (cx ++ List.replicate (t + 1) true)).reverse =
      List.replicate (t + 1) true ++ (cx.reverse ++ F :: F :: List.replicate (k + 1) true) by
        simp [List.reverse_append, List.reverse_replicate]]
    show Rch (cfgL wd1 (true ::: true ::: app (List.replicate (t + 1) true ++
      (cx.reverse ++ F :: F :: List.replicate (k + 1) true)) (F ::: ones (p + 1 + 1) blank)) _) _
    rw [wd_eq]; fin
  · obtain rfl : p = 9 := by omega
    rw [if_pos rfl]
    unfold DV TAQ WD
    rw [show 10 - 9 = 1 by rfl, show (9 + 1) % 10 = 0 by rfl, show 10 - 0 = 10 by rfl,
      show t + 2 - (t + 1) = 1 by omega]
    refine Rch.tr (fstep_wrap _) ?_
    have e1 : ones 10 (F ::: F ::: app cx (ones (t + 1) (F ::: ones 1 (zeros h (ones (a + 1) (Qp Q)))))) =
        app (List.replicate (9 + 1) true ++ F :: F :: (cx ++ List.replicate (t + 1) true))
          (F ::: ones (0 + 1) (zeros h (ones (a + 1) (Qp Q)))) := by
      rw [app_append, app_replicate]; simp [app_append, app_replicate]
    rw [e1]
    refine Rch.tr (FW.cross (hcx.r 9 t) _ _) ?_
    gR
    rw [show (List.replicate (9 + 1) true ++ F :: F :: (cx ++ List.replicate (t + 1) true)).reverse =
      List.replicate (t + 1) true ++ (cx.reverse ++ F :: F :: List.replicate (9 + 1) true) by
        simp [List.reverse_append, List.reverse_replicate], app_ones_list]
    show Rch ⟨wZ1, F ::: true ::: ones t (app (cx.reverse ++ F :: F :: List.replicate (9 + 1) true)
      (F ::: ones 1 blank)), _⟩ _
    refine Rch.tr (excursion _ 0 h a Q hh hQ) ?_
    refine Rch.tr (a1_done _ _ h (by omega)) ?_
    rw [show (true ::: true ::: true ::: ones t (app (cx.reverse ++ F :: F :: List.replicate (9 + 1) true)
      (F ::: ones 1 blank))) = ones (t + 3) (app cx.reverse (F ::: F ::: ones 10 (F ::: ones (0 + 1) blank))) by
        simp [app_append, app_replicate, ones_succ]]
    fin

/-! ## the whole walk -/

def Qk (k : Nat) : Option Nat := if k = 0 then none else some ((k + 9) / 10 + 2)

theorem Qk_pos (k : Nat) : ∀ q, Qk k = some q → 1 ≤ q := by
  intro q hq; unfold Qk at hq; split at hq
  · exact absurd hq (by simp)
  · simp at hq; omega

theorem dv_walk (cx : List Bool) (hcx : CX cx) (t h a : Nat) (hh : 2 ≤ h) :
    ∀ k, k ≤ t → Rch (DV cx t 1 9 h a none) (DV cx t (k + 1) ((9 + k) % 10) h a (Qk k)) := by
  intro k
  induction k with
  | zero => intro _; fin
  | succ k ih =>
    intro hk
    refine Rch.tr (ih (by omega)) ?_
    have hm := Nat.mod_lt (9 + k) (show 10 > 0 by decide)
    by_cases hp : (9 + k) % 10 ≤ 8
    · have e : (9 + (k + 1)) % 10 = (9 + k) % 10 + 1 := by omega
      have eq : Qk (k + 1) = Qk k := by
        unfold Qk
        have : k ≠ 0 := by intro h0; subst h0; simp at hp
        rw [if_neg (by omega), if_neg this]
        congr 2; omega
      rw [e, eq]
      exact dv_step cx hcx t (k + 1) _ h a _ (by omega) (by omega) hp
    · have e9 : (9 + k) % 10 = 9 := by omega
      have e : (9 + (k + 1)) % 10 = 0 := by omega
      have eq : Qk (k + 1) = Qn (Qk k) := by
        unfold Qk Qn
        rw [if_neg (by omega)]
        by_cases hk0 : k = 0
        · subst hk0; rfl
        · rw [if_neg hk0]; simp; omega
      rw [e, eq, e9]
      exact dv_wrap cx hcx t (k + 1) h a _ (by omega) (by omega) hh (Qk_pos k)

/-- the division: from the hole at cell 1 (p = 9, no Q) to the end of the walk:
Q has `t / 10 + 3` cells and `p = t % 10` -/
theorem divide (cx : List Bool) (hcx : CX cx) (t h a : Nat) (hh : 2 ≤ h) :
    Rch (DV cx t 1 9 h a none) (WD cx t (t % 10) h a (some (t / 10 + 3))) := by
  refine Rch.tr (dv_walk cx hcx t h a hh t (Nat.le_refl _)) ?_
  have hm := Nat.mod_lt (9 + t) (show 10 > 0 by decide)
  have := dv_last cx hcx t ((9 + t) % 10) h a (Qk t) (by omega) hh (Qk_pos t)
  have e1 : ((9 + t) % 10 + 1) % 10 = t % 10 := by omega
  have e2 : (if (9 + t) % 10 = 9 then Qn (Qk t) else Qk t) = some (t / 10 + 3) := by
    unfold Qk Qn
    by_cases h9 : (9 + t) % 10 = 9
    · rw [if_pos h9]
      by_cases ht : t = 0
      · subst ht; rfl
      · rw [if_neg ht]; simp; omega
    · rw [if_neg h9, if_neg (by omega)]; simp; omega
  rw [e1, e2] at this
  exact this

end TM.Lychrel