import TinyCryptids.Erdos.Tac
import TinyCryptids.Erdos.Spec

/-!
# One round on the tape

A digit takes two cells: 0 is `01`, 1 is `10`, 2 is `11`. The tape of a round is

    x y 0 0 | d₀ d₁ … d_k | blank          (least significant digit d₀ first)

where `0 0` (cells -2, -1) separates the digits from the counter `x y` (cells -4, -3;
`c = 2x + y`). A round starts in `E` just right of the top digit (`S c ds`). It scans left
for a 2 (`E F G`); if it finds one it walks on to the separator (`K N I`), otherwise
it increments the counter (`H L M`), halting when the counter is already 3. Then it
doubles the number in one pass to the right (`C D J` with carry 0, `A O M B` with carry 1)
and is back in `E`.
-/

namespace TM.Erdos

open Dig

/-- first and second cell of a digit -/
def ca : Dig → Bool
  | z => false
  | o => true
  | t => true

def cb : Dig → Bool
  | z => true
  | o => false
  | t => true

/-- the digits `ds` to the left of the head, the last one nearest -/
def pushL : List Dig → Strm → Strm
  | [], s => s
  | d :: ds, s => pushL ds (cb d ::: ca d ::: s)

/-- the digits `ds` to the right of the head, the first one nearest -/
def putR : List Dig → Strm → Strm
  | [], s => s
  | d :: ds, s => ca d ::: cb d ::: putR ds s

theorem pushL_append (l m : List Dig) (s : Strm) : pushL (l ++ m) s = pushL m (pushL l s) := by
  induction l generalizing s with
  | nil => rfl
  | cons d l ih => exact ih _

theorem putR_append (l m : List Dig) (s : Strm) : putR (l ++ m) s = putR l (putR m s) := by
  induction l with
  | nil => rfl
  | cons d l ih => show ca d ::: cb d ::: putR (l ++ m) s = _; rw [ih]; rfl

/-- the counter cells `y x` (nearest first) for `c = 0, 1, 2, 3` -/
def cbits : Nat → Strm
  | 0 => false ::: false ::: blank
  | 1 => true ::: false ::: blank
  | 2 => false ::: true ::: blank
  | _ => true ::: true ::: blank

/-- the separator and the counter, nearest first -/
def ctr (c : Nat) : Strm := false ::: false ::: cbits c

/-- round start: digits `ds`, counter `c`, the head just right of the top digit -/
def S (c : Nat) (ds : List Dig) : Cfg St := ⟨St.E, pushL ds (ctr c), blank⟩

def cst : Bool → St
  | false => St.C
  | true => St.A

theorem blankR {q : St} {L : Strm} {X : Cfg St} (h : Rch ⟨q, L, false ::: blank⟩ X) :
    Rch ⟨q, L, blank⟩ X := by rw [← cons_blank]; exact h

/-! ## doubling pass -/

theorem pass_end (ds : List Dig) (P : Strm) :
    Rch ⟨St.C, pushL ds P, blank⟩ ⟨St.E, pushL ds P, blank⟩ := by
  refine blankR ?_; goR
  refine blankR ?_
  refine Rch.tr (stepL (δ := delta) (L := false ::: pushL ds P) (R := false ::: blank) rfl) ?_
  show Rch ⟨St.E, pushL ds P, false ::: false ::: blank⟩ _
  rw [cons_blank, cons_blank]; exact Reach.refl delta _

/-- The pass from the digit `rest`'s first cell, with carry `c`, writes `dbl c rest`. -/
theorem pass : ∀ (rest done : List Dig) (c : Bool) (P : Strm),
    Rch ⟨cst c, pushL done P, putR rest blank⟩ ⟨St.E, pushL (done ++ dbl c rest) P, blank⟩ := by
  intro rest
  induction rest with
  | nil =>
    intro done c P
    cases c
    · simpa [dbl] using pass_end done P
    · refine blankR ?_; goR
      refine blankR ?_; goR
      have := pass_end (done ++ [o]) P
      simpa [dbl, pushL_append, pushL] using this
  | cons d r ih =>
    intro done c P
    have nx : ∀ (d' : Dig) (c' : Bool),
        Rch ⟨cst c', cb d' ::: ca d' ::: pushL done P, putR r blank⟩
          ⟨St.E, pushL (done ++ d' :: dbl c' r) P, blank⟩ := by
      intro d' c'
      have := ih (done ++ [d']) c' P
      rw [pushL_append, List.append_assoc] at this
      exact this
    cases c <;> cases d
    · goR; goR; exact nx z false
    · goR; goR; exact nx t false
    · goR; goR; exact nx o true
    · goR; goR; exact nx o false
    · goR
      refine Rch.tr (stepL (δ := delta) (L := true ::: pushL done P)
        (R := false ::: putR r blank) rfl) ?_
      goR; goR; exact nx z true
    · goR; goR; exact nx t true

/-! ## scans to the left -/

theorem scan_cross : ∀ (ds : List Dig), t ∉ ds → ∀ (L0 R : Strm),
    Rch (cfgL St.F (pushL ds L0) R) (cfgL St.F L0 (putR ds R)) := by
  intro ds
  induction ds with
  | nil => intro _ L0 R; exact Reach.refl delta _
  | cons d r ih =>
    intro h L0 R
    have hr : t ∉ r := fun h' => h (List.mem_cons_of_mem _ h')
    refine Rch.tr (ih hr (cb d ::: ca d ::: L0) R) ?_
    cases d
    · goL; goL; exact Reach.refl delta _
    · goL; goL; exact Reach.refl delta _
    · exact absurd (List.mem_cons_self _ _) h

theorem kn_cross : ∀ (ds : List Dig) (L0 R : Strm),
    Rch (cfgL St.K (pushL ds L0) R) (cfgL St.K L0 (putR ds R)) := by
  intro ds
  induction ds with
  | nil => intro L0 R; exact Reach.refl delta _
  | cons d r ih =>
    intro L0 R
    refine Rch.tr (ih (cb d ::: ca d ::: L0) R) ?_
    cases d <;> (goL; goL; exact Reach.refl delta _)

/-- the first step of a round -/
theorem enter (c : Nat) (ds : List Dig) :
    Rch1 (S c ds) (cfgL St.F (pushL ds (ctr c)) (false ::: blank)) :=
  Sys.Reach1.single rfl

theorem split_last {ds : List Dig} (h : t ∈ ds) : ∃ pre post, ds = pre ++ t :: post ∧ t ∉ post := by
  induction ds with
  | nil => exact absurd h (List.not_mem_nil _)
  | cons d r ih =>
    by_cases hr : t ∈ r
    · obtain ⟨pre, post, e, hp⟩ := ih hr
      exact ⟨d :: pre, post, by rw [e]; rfl, hp⟩
    · have hd : d = t := by
        rcases List.mem_cons.1 h with h | h
        · exact h.symm
        · exact absurd h hr
      exact ⟨[], r, by rw [hd]; rfl, hr⟩

/-- the pass after the counter, from the separator's second cell -/
theorem to_pass (c : Nat) (ds : List Dig) :
    Rch ⟨St.B, false ::: cbits c, false ::: putR ds (false ::: blank)⟩ (S c (dbl false ds)) := by
  goR
  rw [cons_blank]
  exact pass ds [] false (ctr c)

/-! ## rounds -/

/-- A 2 is found: the counter stays and the number doubles. -/
theorem round_two (c : Nat) {ds : List Dig} (h : t ∈ ds) : Rch1 (S c ds) (S c (dbl false ds)) := by
  obtain ⟨pre, post, rfl, hp⟩ := split_last h
  refine Reach1.trans_reach delta (enter c _) ?_
  rw [pushL_append]
  refine Rch.tr (scan_cross post hp _ _) ?_
  goL; goL
  refine Rch.tr (kn_cross pre _ _) ?_
  goL; goR
  have := to_pass c (pre ++ t :: post)
  rw [putR_append] at this
  exact this

/-- No 2: the counter goes up by one and the number doubles. -/
theorem round_no2 (c : Nat) (hc : c < 3) {ds : List Dig} (h : t ∉ ds) :
    Rch1 (S c ds) (S (c + 1) (dbl false ds)) := by
  refine Reach1.trans_reach delta (enter c _) ?_
  refine Rch.tr (scan_cross ds h _ _) ?_
  goL; goL
  obtain rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  · goR; goR; exact to_pass 1 ds
  · goL; goR; goR; goR; exact to_pass 2 ds
  · goR; goR; exact to_pass 3 ds

/-- No 2 with the counter at 3: the machine halts. -/
theorem round_halt {ds : List Dig} (h : t ∉ ds) : Halts delta (S 3 ds) := by
  refine Reach.halts delta (enter 3 ds).reach ?_
  refine Reach.halts delta (scan_cross ds h _ _) ?_
  refine Reach.halts delta (sL (by rfl)) ?_
  refine Reach.halts delta (sL (by rfl)) ?_
  refine Reach.halts delta (sL (by rfl)) ?_
  exact halt_none rfl

end TM.Erdos
