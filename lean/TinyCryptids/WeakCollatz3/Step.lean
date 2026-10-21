import TinyCryptids.WeakCollatz3.Tac
import TinyCryptids.WeakCollatz.Spec

/-!
# One shortcut step on the tape (3 symbols)

`CS M v` (`1 ≤ v ≤ M`): head on cell 0 in `disp`; cells `0 .. M - 2` hold 1 except the hole
(0) at cell `v - 1`, cell `M - 1` holds the end mark 2, everything else is blank. For `v = M`
the end mark is the hole (`RS M`). One macro step goes from `CS M v` to `CS M (tc v)`, to the
next round `RS (M + 1)`, or to the halting state:

* `v = 1` (`step_one`): `disp` writes a 2 on cell 0, `toHO` makes the end mark a 1, `hop`
  writes the new end mark, `home` turns the 2 on cell 0 into a 1.
* halving (`hl_loop`): `disp` writes a marker (0) on cell 0; per round trip the hole moves left
  and the marker right. For even `v` they end on neighbouring cells and the marker is the result
  hole (`hl_even`, `step_even`). When the hole is the end mark (`v = M`), the first round trip
  leaves the end mark in place (`he_step`, `he_even`, `he_odd`).
* odd `v = 2k + 1` (`step_odd`): they meet on cell `k`; the odd marker (2) is written there
  and the hole on `k + 1` (`hl_odd`); then the marker moves left one cell per round trip while
  the hole moves right two (`ol_step`). On the end mark the hole leaves the 2 (`ol_land`, the
  hole is on cell `M - 1`). `ol_run` sorts the outcomes: the marker passes cell 0 with the hole
  on cell `3k + 1 = tc v - 1` (`ol_end`), or with the hole on the end mark (`oe_end`, halt), or
  the hole must pass the end mark first (`ol_over`, `oe_over`: the next round).
-/

namespace TM3.WeakCollatz

open TinyCryptids TM.WeakCollatz St Sym

/-- the end of the block: the end mark, then blank -/
def EM : Strm := s2 ::: blank

/-- `a` ones, the hole, `r` ones, the end mark: the value `a + 1` in round `a + r + 2` -/
def CF (a r : Nat) : Cfg St := ⟨disp, blank, ones a (s0 ::: ones r EM)⟩

/-- round start: `M - 1` ones, the end mark (the hole of `v = M`) -/
def RS (M : Nat) : Cfg St := ⟨disp, blank, ones (M - 1) EM⟩

/-- the tape of value `v` in round `M` -/
def CS (M v : Nat) : Cfg St := if v < M then CF (v - 1) (M - 1 - v) else RS M

theorem cs_lt {M v : Nat} (h : v < M) : CS M v = CF (v - 1) (M - 1 - v) := by
  unfold CS; rw [if_pos h]

theorem cs_self (M : Nat) : CS M M = RS M := by
  unfold CS; rw [if_neg (Nat.lt_irrefl M)]

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

/-! ## going home -/

theorem go_home (n : Nat) (R : Strm) : Rch (cfgL home (ones n blank) R) ⟨disp, blank, ones n R⟩ := by
  sLn n
  gR
  show Rch ⟨disp, s0 ::: blank, _⟩ _
  rw [cons_blank]; fin

/-- `home` also turns a 2 into a 1 -/
theorem go_home2 (a b : Nat) (R : Strm) :
    Rch (cfgL home (ones a (s2 ::: ones b blank)) R) ⟨disp, blank, ones (a + b + 1) R⟩ := by
  sLn a
  gL
  refine Rch.tr (go_home b _) ?_
  rw [show s1 ::: ones a R = ones (a + 1) R from rfl, ones_add, show b + (a + 1) = a + b + 1 by omega]
  fin

/-! ## v = 1 -/

theorem step_one (M : Nat) (hM : 2 ≤ M) : Rch1 (CS M 1) (RS (M + 1)) := by
  rw [cs_lt (by omega)]
  unfold CF RS
  refine Reach1.trans_reach delta (sR1 (L := blank) rfl) ?_
  sRn (M - 1 - 1)
  gR
  refine blankR ?_
  gL
  refine Rch.tr (go_home2 (M - 1 - 1 + 1) 0 _) ?_
  rw [show M - 1 - 1 + 1 + 0 + 1 = M + 1 - 1 by omega]
  fin

/-! ## halving -/

/-- halving loop: the marker on cell `m`, head on cell `m + 1` in `toH`, then `d` ones,
the hole, `r` ones, the end mark -/
def HL (m d r : Nat) : Cfg St := ⟨toH, s0 ::: ones m blank, ones d (s0 ::: ones r EM)⟩

/-- the same with the end mark as the hole -/
def HE (m d : Nat) : Cfg St := ⟨toH, s0 ::: ones m blank, ones d EM⟩

theorem hl_step (m d r : Nat) : Rch (HL m (d + 2) r) (HL (m + 1) d (r + 1)) := by
  unfold HL
  sRn (d + 2)
  gL; gL
  sLn (d + 1)
  gR; gR
  fin

theorem he_step (m d : Nat) : Rch (HE m (d + 2)) (HL (m + 1) d 0) := by
  unfold HE HL
  sRn (d + 2)
  gL; gL
  sLn (d + 1)
  gR; gR
  fin

theorem hl_loop : ∀ j m d r, Rch (HL m (d + 2 * j) r) (HL (m + j) d (r + j)) := by
  intro j
  induction j with
  | zero => intro m d r; fin
  | succ j ih =>
    intro m d r
    rw [show d + 2 * (j + 1) = d + 2 * j + 2 by omega]
    refine Rch.tr (hl_step m _ r) ?_
    have := ih (m + 1) d (r + 1)
    rw [show m + 1 + j = m + (j + 1) by omega, show r + 1 + j = r + (j + 1) by omega] at this
    exact this

/-- the first step from a value `2 ≤ v < M`: the marker on cell 0 -/
theorem disp_mark (a r : Nat) : Rch1 (CF (a + 1) r) (HL 0 a r) :=
  sR1 (L := blank) rfl

/-- the first step from `v = M ≥ 2` -/
theorem disp_markE (a : Nat) : Rch1 (RS (a + 2)) (HE 0 a) :=
  sR1 (L := blank) rfl

/-- the hole is next to the marker: fill the hole, the marker is the result hole -/
theorem hl_even (m r : Nat) : Rch (HL m 0 r) (CF m (r + 1)) := by
  unfold HL
  gL; gL
  exact go_home m _

theorem he_even (m : Nat) : Rch (HE m 0) (CF m 0) := by
  unfold HE
  gL; gL
  exact go_home m _

theorem step_even (M v : Nat) (hv : v % 2 = 0) (h2 : 2 ≤ v) (hM : v ≤ M) :
    Rch1 (CS M v) (CS M (v / 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, v = 2 * k + 2 := ⟨v / 2 - 1, by omega⟩
  rw [show (2 * k + 2) / 2 = k + 1 by omega, cs_lt (M := M) (v := k + 1) (by omega),
    show k + 1 - 1 = k by omega]
  rcases Nat.lt_or_ge (2 * k + 2) M with hlt | hge
  · rw [cs_lt hlt, show 2 * k + 2 - 1 = (2 * k) + 1 by omega]
    refine Reach1.trans_reach delta (disp_mark _ _) ?_
    have := hl_loop k 0 0 (M - 1 - (2 * k + 2))
    rw [Nat.zero_add, Nat.zero_add] at this
    refine Rch.tr this (Rch.tr (hl_even k _) ?_)
    rw [show M - 1 - (2 * k + 2) + k + 1 = M - 1 - (k + 1) by omega]
    fin
  · obtain rfl : M = 2 * k + 2 := by omega
    rw [cs_self]
    refine Reach1.trans_reach delta (disp_markE _) ?_
    rcases k with _ | j
    · exact he_even 0
    · refine Rch.tr (he_step 0 (2 * j)) ?_
      have := hl_loop j 1 0 0
      rw [Nat.zero_add, Nat.zero_add] at this
      refine Rch.tr this (Rch.tr (hl_even (1 + j) _) ?_)
      rw [show 1 + j = j + 1 by omega, show 2 * (j + 1) + 2 - 1 - (j + 1 + 1) = j + 1 by omega]
      fin

/-! ## v odd -/

/-- odd loop: head on cell `c - 1` in `markO` (`c` ones up to it), then `e` ones, the hole,
`s` ones, the end mark -/
def OL (c e s : Nat) : Cfg St := cfgL markO (ones c blank) (ones e (s0 ::: ones s EM))

/-- the same with the hole on the end mark -/
def OE (c e : Nat) : Cfg St := cfgL markO (ones c blank) (ones e EM)

/-- the marker meets the hole on cell `m + 1`: the odd marker there, the hole on `m + 2`, the
head on the marker's next cell `m` -/
theorem hl_odd (m r : Nat) : Rch (HL m 1 r) (OL (m + 1) 1 r) := by
  unfold HL OL
  gR; gL; gL; gR; gR; gL; gL
  fin

theorem he_odd (m : Nat) : Rch (HE m 1) (OE (m + 1) 1) := by
  unfold HE OE
  gR; gL; gL; gR; gR; gL; gL
  fin

theorem ol_step (c e s : Nat) : Rch (OL (c + 1) e (s + 2)) (OL c (e + 3) s) := by
  unfold OL
  gR
  sRn e
  gR; gR; gL
  sLn (e + 2)
  gL
  fin

/-- the hole lands on the end mark -/
theorem ol_land (c e : Nat) : Rch (OL (c + 1) e 1) (OE c (e + 3)) := by
  unfold OL OE
  gR
  sRn e
  gR; gR; gL
  sLn (e + 2)
  gL
  fin

/-- the hole runs past the end mark: the next round -/
theorem ol_over (c e : Nat) : Rch (OL (c + 1) e 0) (RS (c + e + 4)) := by
  unfold OL RS
  gR
  sRn e
  gR; gR
  refine blankR ?_
  gL
  refine Rch.tr (go_home2 (e + 2) c _) ?_
  rw [show e + 2 + c + 1 = c + e + 4 - 1 by omega]
  fin

theorem oe_over (c e : Nat) : Rch (OE (c + 1) e) (RS (c + e + 3)) := by
  unfold OE RS
  gR
  sRn e
  gR
  refine blankR ?_
  gL
  refine Rch.tr (go_home2 (e + 1) c _) ?_
  rw [show e + 1 + c + 1 = c + e + 3 - 1 by omega]
  fin

/-- the marker passed cell 0: go home -/
theorem ol_end (e s : Nat) : Rch (OL 0 e s) (CF e s) := by
  unfold OL
  gR
  sRn e
  gL
  show Rch (cfgL home (ones e (s0 ::: blank)) _) _
  rw [cons_blank]
  exact go_home e _

/-- the marker passed cell 0 and the hole is on the end mark: halt -/
theorem oe_end (e : Nat) : HaltAt (OE 0 e) := by
  refine ⟨s1 ::: ones e (s0 ::: tl blank), blank, ?_⟩
  unfold OE
  gR
  sRn e
  gR
  fin

/-- the odd loop from `OL c e s` (round `c + e + s + 2`) -/
theorem ol_run : ∀ c e s,
    (2 * c ≤ s → Rch (OL c e s) (CF (e + 3 * c) (s - 2 * c))) ∧
    (s + 1 = 2 * c → HaltAt (OL c e s)) ∧
    (s + 1 < 2 * c → Rch (OL c e s) (RS (c + e + s + 3))) := by
  intro c
  induction c with
  | zero => intro e s; exact ⟨fun _ => ol_end e s, fun h => by omega, fun h => by omega⟩
  | succ c ih =>
    intro e s
    rcases s with _ | _ | s
    · refine ⟨fun h => by omega, fun h => by omega, fun _ => ?_⟩
      exact Rch.tr (ol_over c e) (by rw [show c + e + 4 = c + 1 + e + 0 + 3 by omega]; fin)
    · refine ⟨fun h => by omega, fun h => ?_, fun h => ?_⟩
      · obtain rfl : c = 0 := by omega
        exact HaltAt.back (ol_land 0 e) (oe_end _)
      · obtain ⟨c, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
        refine Rch.tr (ol_land (c + 1) e) (Rch.tr (oe_over c (e + 3)) ?_)
        rw [show c + (e + 3) + 3 = c + 1 + 1 + e + (0 + 1) + 3 by omega]
        fin
    · have st := ol_step c e s
      have := ih (e + 3) s
      refine ⟨fun h => Rch.tr st ?_, fun h => HaltAt.back st (this.2.1 (by omega)),
        fun h => Rch.tr st ?_⟩
      · refine Rch.tr (this.1 (by omega)) ?_
        rw [show e + 3 + 3 * c = e + 3 * (c + 1) by omega,
          show s - 2 * c = s + 1 + 1 - 2 * (c + 1) by omega]
        fin
      · refine Rch.tr (this.2.2 (by omega)) ?_
        rw [show c + (e + 3) + s + 3 = c + 1 + e + (s + 1 + 1) + 3 by omega]
        fin

theorem step_odd (M v : Nat) (hv : v % 2 = 1) (h3 : 3 ≤ v) (hM : v ≤ M) :
    (M < tc v → Rch1 (CS M v) (RS (M + 1))) ∧ (tc v = M → HaltAt (CS M v)) ∧
      (tc v < M → Rch1 (CS M v) (CS M (tc v))) := by
  obtain ⟨k, rfl⟩ : ∃ k, v = 2 * k + 3 := ⟨v / 2 - 1, by omega⟩
  have ht : tc (2 * k + 3) = 3 * k + 5 := by rw [tc_odd _ hv]; omega
  rw [ht]
  rcases Nat.lt_or_ge (2 * k + 3) M with hlt | hge
  · -- `v < M`: the odd loop from `OL (k + 1) 1 (r + k)`, `r = M - 2k - 4`
    obtain ⟨r, hr⟩ : ∃ r, r = M - 1 - (2 * k + 3) := ⟨_, rfl⟩
    have hs : Rch1 (CS M (2 * k + 3)) (OL (k + 1) 1 (r + k)) := by
      rw [cs_lt hlt, show 2 * k + 3 - 1 = (2 * k + 1) + 1 by omega, ← hr]
      refine Reach1.trans_reach delta (disp_mark _ _) ?_
      have := hl_loop k 0 1 r
      rw [show 1 + 2 * k = 2 * k + 1 by omega, Nat.zero_add] at this
      exact Rch.tr this (hl_odd _ _)
    have o := ol_run (k + 1) 1 (r + k)
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · refine Reach1.trans_reach delta hs (Rch.tr (o.2.2 (by omega)) ?_)
      rw [show k + 1 + 1 + (r + k) + 3 = M + 1 by omega]; fin
    · exact HaltAt.back hs.reach (o.2.1 (by omega))
    · refine Reach1.trans_reach delta hs (Rch.tr (o.1 (by omega)) ?_)
      rw [cs_lt h, show 1 + 3 * (k + 1) = 3 * k + 5 - 1 by omega,
        show r + k - 2 * (k + 1) = M - 1 - (3 * k + 5) by omega]
      fin
  · -- `v = M`: the hole runs past the end mark
    obtain rfl : M = 2 * k + 3 := by omega
    refine ⟨fun _ => ?_, fun h => by omega, fun h => by omega⟩
    rw [cs_self]
    refine Reach1.trans_reach delta (disp_markE (2 * k + 1)) ?_
    rcases k with _ | j
    · exact Rch.tr (he_odd 0) (oe_over 0 1)
    · rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by omega]
      refine Rch.tr (he_step 0 _) ?_
      have := hl_loop j 1 1 0
      rw [show 1 + 2 * j = 2 * j + 1 by omega, Nat.zero_add] at this
      refine Rch.tr this (Rch.tr (hl_odd _ _) ?_)
      refine Rch.tr ((ol_run (1 + j + 1) 1 j).2.2 (by omega)) ?_
      rw [show 1 + j + 1 + 1 + j + 3 = 2 * (j + 1) + 3 + 1 by omega]
      fin

/-! ## one step -/

theorem step_cases (n x : Nat) (h2 : 2 ≤ x) (hx : x ≤ n) :
    (Cond n (tc x) → tc x ≠ n → Rch1 (CS n x) (RS (n + 1))) ∧
      (tc x = n → HaltAt (CS n x)) ∧
      (¬ Cond n (tc x) → Rch1 (CS n x) (CS n (tc x))) := by
  rcases Nat.mod_two_eq_zero_or_one x with hx2 | hx2
  · have e := step_even n x hx2 h2 hx
    rw [tc_even x hx2]
    refine ⟨fun hc hne => ?_, fun h => ?_, fun _ => e⟩
    · rcases hc with hc | hc
      · rw [hc] at e
        exact Reach1.trans_reach delta e (step_one n (by omega)).reach
      · omega
    · omega
  · have o := step_odd n x hx2 (by omega) hx
    refine ⟨fun hc hne => ?_, fun h => o.2.1 h, fun hc => ?_⟩
    · rcases hc with hc | hc
      · rw [tc_odd x hx2] at hc; omega
      · exact o.1 (by omega)
    · exact o.2.2 (by unfold Cond at hc; omega)

/-- The round from `x`: it stops at the first `i` with `Cond n (it (i + 1) x)`. -/
theorem round_run (n : Nat) : ∀ i x, 2 ≤ x → x ≤ n →
    (∀ j, j < i → ¬ Cond n (it (j + 1) x)) → Cond n (it (i + 1) x) →
    (it (i + 1) x = n → HaltAt (CS n x)) ∧ (it (i + 1) x ≠ n → Rch1 (CS n x) (RS (n + 1))) := by
  intro i
  induction i with
  | zero =>
    intro x h2 hx _ hc
    have s := step_cases n x h2 hx
    exact ⟨s.2.1, s.1 hc⟩
  | succ i ih =>
    intro x h2 hx hfirst hc
    have h0 : ¬ Cond n (tc x) := hfirst 0 (by omega)
    have s := (step_cases n x h2 hx).2.2 h0
    have hy : 2 ≤ tc x ∧ tc x ≤ n := by
      have := tc_pos x (by omega); unfold Cond at h0; omega
    have := ih (tc x) hy.1 hy.2
      (fun j hj => by rw [← it_succ']; exact hfirst (j + 1) (by omega))
      (by rw [← it_succ']; exact hc)
    rw [← it_succ'] at this
    exact ⟨fun h => HaltAt.back s.reach (this.1 h), fun h => Reach1.trans_reach delta s (this.2 h).reach⟩

end TM3.WeakCollatz
