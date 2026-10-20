import TinyCryptids.WeakCollatz.Tac
import TinyCryptids.WeakCollatz.Spec

/-!
# One shortcut step on the tape

`CS M v` (`1 ≤ v ≤ M`): head on cell 0 in `disp`; cells `0 .. M - 1` hold 1
except the hole at cell `v - 1`; everything else is blank. One macro step goes
from `CS M v` to `CS M (tc v)`, to the next round `CS (M + 1) (M + 1)`, or to
the halting state:

* `v = 1` (`step_one`): fill the hole on cell 0, go home.
* halving (`hl_loop`): `disp` writes a marker on cell 0; per round trip the
  hole moves left and the marker right. For even `v` they end on neighbouring
  cells and the marker is the result hole (`hl_even`, `step_even`).
* odd `v = 2k + 1` (`step_odd`): they meet on cell `k`; the hole moves to
  `k + 1` and the marker to `k - 1` (`hl_odd`); then the marker moves left one
  cell per round trip while the hole moves right two (`ol_loop`). The hole ends
  at `3k + 1 = tc v - 1` (`ol_end`), unless it runs off the block first
  (`ol_over`).
-/

namespace TM.WeakCollatz

open TinyCryptids St

local notation "F" => false

/-- the hole at cell `a`, then `r` ones -/
def CF (a r : Nat) : Cfg St := ⟨disp, blank, ones a (F ::: ones r blank)⟩

/-- the tape of value `v` in round `M` -/
def CS (M v : Nat) : Cfg St := CF (v - 1) (M - v)

/-- round start -/
def RS (M : Nat) : Cfg St := CS M M

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

/-! ## going home -/

theorem go_home (n : Nat) (R : Strm) : Rch (cfgL home (ones n blank) R) ⟨disp, blank, ones n R⟩ := by
  sLn n
  gR
  show Rch ⟨disp, F ::: blank, _⟩ _
  rw [cons_blank]; fin

/-! ## v = 1 -/

theorem step_one (M : Nat) (hM : 1 ≤ M) : Rch1 (CS M 1) (RS (M + 1)) := by
  unfold CS RS CF
  rw [Nat.sub_self, ones_zero]
  refine Reach1.trans_reach delta (sL1 (s := blank) rfl) ?_
  refine Rch.tr (go_home 0 _) ?_
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  unfold CS CF
  rw [Nat.sub_self, show n + 1 + 1 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega, ones_zero,
    ones_zero, cons_blank]
  fin

/-! ## halving -/

/-- halving loop: the marker on cell `m`, head on cell `m + 1` in `toH`, then `d` ones,
the hole, `r` ones -/
def HL (m d r : Nat) : Cfg St := ⟨toH, F ::: ones m blank, ones d (F ::: ones r blank)⟩

theorem hl_step (m d r : Nat) : Rch (HL m (d + 2) r) (HL (m + 1) d (r + 1)) := by
  unfold HL
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

/-- the first step from a value `v ≥ 2`: the marker on cell 0 -/
theorem disp_mark (a r : Nat) : Rch1 (CF (a + 1) r) (HL 0 a r) :=
  stepR1 (δ := delta) (R := ones (a + 1) (F ::: ones r blank)) rfl

/-- the hole is next to the marker: fill the hole, the marker is the result hole -/
theorem hl_even (m r : Nat) : Rch (HL m 0 r) (CF m (r + 1)) := by
  unfold HL
  gL; gL
  exact go_home m _

theorem step_even (M v : Nat) (hv : v % 2 = 0) (h2 : 2 ≤ v) (hM : v ≤ M) :
    Rch1 (CS M v) (CS M (v / 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, v = 2 * k + 2 := ⟨v / 2 - 1, by omega⟩
  unfold CS
  rw [show 2 * k + 2 - 1 = (2 * k) + 1 by omega]
  refine Reach1.trans_reach delta (disp_mark _ _) ?_
  have := hl_loop k 0 0 (M - (2 * k + 2))
  rw [Nat.zero_add, Nat.zero_add] at this
  refine Rch.tr this ?_
  refine Rch.tr (hl_even k _) ?_
  rw [show (2 * k + 2) / 2 - 1 = k by omega, show M - (2 * k + 2) / 2 = M - (2 * k + 2) + k + 1 by omega]
  fin

/-! ## v odd -/

/-- odd loop: head on cell `c - 1` in `markO` (`c` ones up to it), then `e` ones, the hole, `s` ones -/
def OL (c e s : Nat) : Cfg St := cfgL markO (ones c blank) (ones e (F ::: ones s blank))

/-- the marker meets the hole on cell `m + 1`: the hole moves to `m + 2`, the marker to `m` -/
theorem hl_odd (m r : Nat) : Rch (HL m 1 r) (OL (m + 1) 1 r) := by
  unfold HL OL
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

theorem ol_loop : ∀ i c e s, Rch (OL (c + i) e (s + 2 * i)) (OL c (e + 3 * i) s) := by
  intro i
  induction i with
  | zero => intro c e s; fin
  | succ i ih =>
    intro c e s
    rw [show c + (i + 1) = c + 1 + i by omega, show s + 2 * (i + 1) = s + 2 + 2 * i by omega]
    refine Rch.tr (ih (c + 1) e (s + 2)) ?_
    rw [show e + 3 * (i + 1) = e + 3 * i + 3 by omega]
    exact ol_step c _ s

/-- the hole runs off the block: fill the marker, go home -/
theorem ol_over (c e s : Nat) (hs : s ≤ 1) : Rch (OL (c + 1) e s) (CF (c + e + s + 2) 0) := by
  unfold OL
  gR
  sRn e
  gR
  rcases s with _ | s
  · refine blankR ?_
    gL
    sLn (e + 1)
    gL
    refine Rch.tr (go_home c _) ?_
    unfold CF
    rw [cons_blank, ones_zero, cons_blank, ← ones_succ, ones_add, show c + (e + 1 + 1) = c + e + 0 + 2 by omega]
    fin
  · obtain rfl : s = 0 := by omega
    gR
    refine blankR ?_
    gL
    sLn (e + 2)
    gL
    refine Rch.tr (go_home c _) ?_
    unfold CF
    rw [cons_blank, ones_zero, cons_blank, ← ones_succ, ones_add, show c + (e + 2 + 1) = c + e + (0 + 1) + 2 by omega]
    fin

/-- the marker passed cell 0: look at the cell after the hole -/
theorem ol_end (e s : Nat) :
    (s = 0 → HaltAt (OL 0 e s)) ∧ (1 ≤ s → Rch (OL 0 e s) (CF e s)) := by
  have hf : Rch (OL 0 e s) ⟨peek, F ::: ones e blank, ones s blank⟩ := by
    unfold OL
    gR
    sRn e
    gR
    show Rch ⟨peek, F ::: ones e (F ::: blank), _⟩ _
    rw [cons_blank]; fin
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    refine HaltAt.back hf ⟨F ::: F ::: ones e blank, tl blank, ?_⟩
    refine blankR ?_
    gR; fin
  · obtain ⟨s, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    refine Rch.tr hf ?_
    gL; gL
    exact go_home e _

theorem step_odd (M v : Nat) (hv : v % 2 = 1) (h3 : 3 ≤ v) (hM : v ≤ M) :
    (M < tc v → Rch1 (CS M v) (RS (M + 1))) ∧ (tc v = M → HaltAt (CS M v)) ∧
      (tc v < M → Rch1 (CS M v) (CS M (tc v))) := by
  obtain ⟨k, rfl⟩ : ∃ k, v = 2 * k + 3 := ⟨v / 2 - 1, by omega⟩
  have ht : tc (2 * k + 3) = 3 * k + 5 := by rw [tc_odd _ hv]; omega
  rw [ht]
  obtain ⟨r, hr⟩ : ∃ r, r = M - (2 * k + 3) := ⟨_, rfl⟩
  -- from the start to the odd loop: the marker on cell `k`
  have hs : Rch1 (CS M (2 * k + 3)) (OL (k + 1) 1 (r + k)) := by
    unfold CS
    rw [show 2 * k + 3 - 1 = (2 * k + 1) + 1 by omega, ← hr]
    refine Reach1.trans_reach delta (disp_mark _ _) ?_
    have := hl_loop k 0 1 r
    rw [show 1 + 2 * k = 2 * k + 1 by omega, Nat.zero_add] at this
    exact Rch.tr this (hl_odd _ _)
  -- a full odd loop: the hole ends at `3k + 4`
  have hfull : k + 2 ≤ r → Rch1 (CS M (2 * k + 3)) (OL 0 (3 * k + 4) (r - k - 2)) := by
    intro hk
    refine Reach1.trans_reach delta hs ?_
    have := ol_loop (k + 1) 0 1 (r - k - 2)
    rw [show 0 + (k + 1) = k + 1 by omega, show r - k - 2 + 2 * (k + 1) = r + k by omega,
      show 1 + 3 * (k + 1) = 3 * k + 4 by omega] at this
    exact this
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · -- the hole runs off the block
    obtain ⟨i, e, he, he1⟩ : ∃ i e, r + k = e + 2 * i ∧ e ≤ 1 := ⟨(r + k) / 2, (r + k) % 2, by omega, by omega⟩
    obtain ⟨c, hc⟩ : ∃ c, k + 1 = c + 1 + i := ⟨k - i, by omega⟩
    refine Reach1.trans_reach delta hs ?_
    rw [he, hc]
    refine Rch.tr (ol_loop i (c + 1) 1 e) ?_
    refine Rch.tr (ol_over c _ e he1) ?_
    unfold RS CS
    rw [show c + (1 + 3 * i) + e + 2 = M + 1 - 1 by omega, Nat.sub_self]
    fin
  · obtain ⟨L, R, hh⟩ := (ol_end (3 * k + 4) (r - k - 2)).1 (by omega)
    exact ⟨L, R, Rch.tr (hfull (by omega)).reach hh⟩
  · refine Reach1.trans_reach delta (hfull (by omega)) ?_
    refine Rch.tr ((ol_end (3 * k + 4) (r - k - 2)).2 (by omega)) ?_
    unfold CS
    rw [show 3 * k + 5 - 1 = 3 * k + 4 by omega, show M - (3 * k + 5) = r - k - 2 by omega]
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

end TM.WeakCollatz
