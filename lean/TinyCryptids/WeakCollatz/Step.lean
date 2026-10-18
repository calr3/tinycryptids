import TinyCryptids.WeakCollatz.Tac
import TinyCryptids.WeakCollatz.Spec

/-!
# One Collatz step on the tape

The tape of round `n` is one block, cells `0 .. n + 1`, all 1 except the hole
`H` at cell `x` (`1 ≤ x ≤ n`); everything else is blank. A step starts with the
parity walk from cell 0 and ends at the parity branch of the next step (`PB`),
at the start of the next round (`RS (n + 1)`), or at the halting state.
-/

namespace TM.WeakCollatz

open TinyCryptids St

local notation "F" => false

def pst (x : Nat) : St := if x % 2 = 0 then p0 else p1

theorem pst_add2 (x : Nat) : pst (x + 2) = pst x := by
  unfold pst; rw [Nat.add_mod_right]

/-- parity branch: the head on the hole at `x`, in `p0` (x even) or `p1` (x odd) -/
def PB (n x : Nat) : Cfg St := ⟨pst x, ones x blank, F ::: ones (n + 1 - x) blank⟩

/-- round start: hole at `n` (its last value cell), head on cell `n - 1` in `gl` -/
def RS (n : Nat) : Cfg St := cfgL gl (ones n blank) (F ::: ones 1 blank)

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

/-! ## the parity walk -/

theorem parity : ∀ x (L R : Strm),
    Rch ⟨p0, L, ones x R⟩ ⟨pst x, ones x L, R⟩ ∧ Rch ⟨p1, L, ones x R⟩ ⟨pst (x + 1), ones x L, R⟩ := by
  intro x
  induction x with
  | zero => intro L R; exact ⟨Reach.refl delta _, Reach.refl delta _⟩
  | succ x ih =>
    intro L R
    constructor
    · gR
      have := (ih (true ::: L) R).2
      rw [← ones_succ'] at this; exact this
    · gR
      have := (ih (true ::: L) R).1
      rw [← ones_succ', ← pst_add2 x] at this; exact this

/-- `gl` goes to cell 0, then the parity walk reaches the hole -/
theorem home (n a b r : Nat) (h : a + b + r = n + 1) :
    Rch (cfgL gl (ones a blank) (ones b (F ::: ones r blank))) (PB n (a + b)) := by
  sLn a
  gR
  show Rch ⟨p0, F ::: blank, _⟩ _
  rw [cons_blank, ones_add]
  refine Rch.tr ((parity (a + b) blank _).1) ?_
  unfold PB
  rw [show n + 1 - (a + b) = r by omega]
  fin

theorem rs_pb (n : Nat) (hn : 1 ≤ n) : Rch1 (RS n) (PB n n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold RS
  refine Reach1.trans_reach delta (sL1 rfl) ?_
  exact home (m + 1) m 1 1 (by omega)

/-- grow the block by one cell; the hole goes to the new last value cell -/
theorem grow (k m : Nat) (h : 1 ≤ k + m) : Rch ⟨b1, ones k blank, ones m blank⟩ (RS (k + m - 1)) := by
  obtain ⟨j, hj⟩ : ∃ j, m + k = j + 1 := ⟨m + k - 1, by omega⟩
  sRn m
  refine blankR ?_
  gL
  rw [ones_add, hj]
  gL
  unfold RS
  rw [show k + m - 1 = j by omega]
  fin

/-! ## x even -/

/-- even loop: head on cell `a` in `gm1`, then `d` ones, the hole, `r` ones -/
def EL (a d r : Nat) : Cfg St := ⟨gm1, ones a blank, ones d (F ::: ones r blank)⟩

theorem el_step (a d r : Nat) (hd : 1 ≤ d) : Rch (EL (a + 2) d r) (EL a (d + 1) (r + 1)) := by
  obtain ⟨d, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  unfold EL
  gL; gR
  sRn (d + 1)
  gL; gL
  sLn d
  gL
  fin

theorem el_loop : ∀ k d r, 1 ≤ d → Rch (EL (2 * k) d r) (EL 0 (d + k) (r + k)) := by
  intro k
  induction k with
  | zero => intro d r _; fin
  | succ k ih =>
    intro d r hd
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    refine Rch.tr (el_step _ d r hd) ?_
    rw [show d + (k + 1) = d + 1 + k by omega, show r + (k + 1) = r + 1 + k by omega]
    exact ih (d + 1) (r + 1) (by omega)

theorem even_step (n x : Nat) (hx2 : x % 2 = 0) (h1 : 1 ≤ x) (hx : x ≤ n) :
    (x / 2 = 1 → Rch (PB n x) (RS (n + 1))) ∧ (x / 2 ≠ 1 → Rch (PB n x) (PB n (x / 2))) := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 2 := ⟨x / 2 - 1, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, n + 1 - (2 * k + 2) = r := ⟨_, rfl⟩
  have hp : pst (2 * k + 2) = p0 := by unfold pst; rw [if_pos (by omega)]
  have hloop : Rch (PB n (2 * k + 2)) ⟨c0, blank, ones (k + 1) (F ::: ones (r + 1 + k) blank)⟩ := by
    unfold PB
    rw [hp, hr]
    gL; gL
    refine Rch.tr (el_loop k 1 (r + 1) (Nat.le_refl _)) ?_
    rw [show 1 + k = k + 1 by omega]
    unfold EL
    gL; gR
    show Rch ⟨c0, F ::: blank, _⟩ _
    rw [cons_blank]; fin
  rw [show (2 * k + 2) / 2 = k + 1 by omega]
  constructor
  · intro hk
    obtain rfl : k = 0 := by omega
    refine Rch.tr hloop ?_
    gR; gR
    have := grow 2 (r + 1 + 0) (by omega)
    rw [show 2 + (r + 1 + 0) - 1 = n + 1 by omega] at this
    exact this
  · intro hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine Rch.tr hloop ?_
    gR; gR
    refine Rch.tr ((parity j _ _).1) ?_
    unfold PB
    rw [show j + 1 + 1 = j + 2 by omega, pst_add2,
        show n + 1 - (j + 2) = r + 1 + (j + 1) by omega, ← ones_succ', ← ones_succ']
    fin

/-! ## x odd -/

/-- odd loop: head on cell `g - 1` in `og`, then `d` ones from cell `g`, the hole, `r` ones -/
def OL (g d r : Nat) : Cfg St := cfgL og (ones g blank) (ones d (F ::: ones r blank))

theorem ol_step (g d r : Nat) : Rch (OL (g + 1) d (r + 2)) (OL g (d + 3) r) := by
  unfold OL
  gR
  sRn d
  gR; gR; gL
  sLn (d + 2)
  gL
  fin

theorem ol_loop : ∀ k g d r, Rch (OL (g + k) d (r + 2 * k)) (OL g (d + 3 * k) r) := by
  intro k
  induction k with
  | zero => intro g d r; fin
  | succ k ih =>
    intro g d r
    rw [show g + (k + 1) = g + 1 + k by omega, show r + 2 * (k + 1) = r + 2 + 2 * k by omega]
    refine Rch.tr (ih (g + 1) d (r + 2)) ?_
    rw [show d + 3 * (k + 1) = d + 3 * k + 3 by omega]
    exact ol_step g _ r

/-- H runs off the block: fill G, grow the block -/
theorem ol_over (g d r : Nat) (hr : r ≤ 1) : Rch (OL (g + 1) d r) (RS (g + d + r + 1)) := by
  unfold OL
  rcases r with _ | r
  · gR
    sRn d
    gR
    refine blankR ?_
    gL
    sLn (d + 1)
    gR
    rw [cons_blank]
    have := grow (g + 1) (d + 1) (by omega)
    rw [show g + 1 + (d + 1) - 1 = g + d + 0 + 1 by omega] at this
    exact this
  · obtain rfl : r = 0 := by omega
    gR
    sRn d
    gR; gR
    refine blankR ?_
    gL
    sLn (d + 2)
    gR
    rw [cons_blank]
    have := grow (g + 1) (d + 2) (by omega)
    rw [show g + 1 + (d + 2) - 1 = g + d + (0 + 1) + 1 by omega] at this
    exact this

/-- G runs off the left end: go to H and look at the two cells after it -/
theorem ol_end (d r : Nat) (hd : 1 ≤ d) :
    (r = 0 → Rch (OL 0 d r) (RS d)) ∧ (r = 1 → HaltAt (OL 0 d r)) ∧
      (2 ≤ r → Rch (OL 0 d r) (PB (d + r - 1) d)) := by
  have hf : Rch (OL 0 d r) ⟨pk1, F ::: ones d blank, ones r blank⟩ := by
    unfold OL
    gR
    sRn d
    gR
    show Rch ⟨pk1, F ::: ones d (F ::: blank), _⟩ _
    rw [cons_blank]; fin
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · subst h
    refine Rch.tr hf ?_
    refine blankR ?_
    gL; gL
    unfold RS; fin
  · subst h
    refine HaltAt.back hf ⟨F ::: true ::: F ::: ones d blank, tl blank, ?_⟩
    gR
    refine blankR ?_
    gR; fin
  · obtain ⟨r, rfl⟩ : ∃ e, r = e + 2 := ⟨r - 2, by omega⟩
    refine Rch.tr hf ?_
    gR; gL; gL; gL
    exact home (d + (r + 2) - 1) d 0 (r + 2) (by omega)

theorem odd_step (n x : Nat) (hx2 : x % 2 = 1) (hx : x ≤ n) :
    (n < 3 * x + 1 → Rch (PB n x) (RS (n + 1))) ∧ (3 * x + 1 = n → HaltAt (PB n x)) ∧
      (3 * x + 1 < n → Rch (PB n x) (PB n (3 * x + 1))) := by
  have hp : pst x = p1 := by unfold pst; rw [if_neg (by omega)]
  have hs : Rch (PB n x) (OL x 1 (n - x)) := by
    unfold PB OL
    rw [hp, show n + 1 - x = n - x + 1 by omega]
    gR; gL; gL
    fin
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rcases Nat.lt_or_ge (n - x) (2 * x) with h2 | h2
    · -- H runs off the block while G is still in it
      obtain ⟨k, e, hk⟩ : ∃ k e, n - x = e + 2 * k ∧ e ≤ 1 := ⟨(n - x) / 2, (n - x) % 2, by omega, by omega⟩
      obtain ⟨g, hg⟩ : ∃ g, x = g + 1 + k := ⟨x - 1 - k, by omega⟩
      refine Rch.tr hs ?_
      rw [hk.1, hg]
      refine Rch.tr (ol_loop k (g + 1) 1 e) ?_
      have := ol_over g (1 + 3 * k) e hk.2
      rw [show g + (1 + 3 * k) + e + 1 = n + 1 by omega] at this
      exact this
    · -- 3x + 1 = n + 1
      have hk : n - x = 0 + 2 * x := by omega
      refine Rch.tr hs ?_
      rw [hk]
      have := ol_loop x 0 1 0
      rw [Nat.zero_add] at this
      refine Rch.tr this ?_
      have := (ol_end (1 + 3 * x) 0 (by omega)).1 rfl
      rw [show 1 + 3 * x = n + 1 by omega] at this ⊢
      exact this
  · have hk : n - x = 1 + 2 * x := by omega
    refine HaltAt.back hs ?_
    rw [hk]
    have := ol_loop x 0 1 1
    rw [Nat.zero_add] at this
    exact HaltAt.back this ((ol_end (1 + 3 * x) 1 (by omega)).2.1 rfl)
  · obtain ⟨e, hk⟩ : ∃ e, n - x = e + 2 * x := ⟨n - 3 * x, by omega⟩
    refine Rch.tr hs ?_
    rw [hk]
    have := ol_loop x 0 1 e
    rw [Nat.zero_add] at this
    refine Rch.tr this ?_
    have := (ol_end (1 + 3 * x) e (by omega)).2.2 (by omega)
    rw [show 1 + 3 * x + e - 1 = n by omega] at this
    rw [show 3 * x + 1 = 1 + 3 * x by omega]
    exact this

/-! ## one step -/

theorem step_cases (n x : Nat) (h1 : 1 ≤ x) (hx : x ≤ n) :
    (Cond n (collatz x) → collatz x ≠ n → Rch (PB n x) (RS (n + 1))) ∧
      (collatz x = n → HaltAt (PB n x)) ∧
      (¬ Cond n (collatz x) → Rch (PB n x) (PB n (collatz x))) := by
  rcases Nat.mod_two_eq_zero_or_one x with hx2 | hx2
  · have e := even_step n x hx2 h1 hx
    rw [collatz_even x hx2]
    refine ⟨fun hc hne => ?_, fun h => ?_, fun hc => ?_⟩
    · rcases hc with hc | hc
      · exact e.1 hc
      · omega
    · omega
    · exact e.2 (fun h => hc (Or.inl h))
  · have o := odd_step n x hx2 hx
    rw [collatz_odd x hx2]
    refine ⟨fun hc hne => ?_, fun h => o.2.1 h, fun hc => ?_⟩
    · rcases hc with hc | hc
      · omega
      · exact o.1 (by omega)
    · exact o.2.2 (by unfold Cond at hc; omega)

/-- The round from `x`: it stops at the first `i` with `Cond n (it (i + 1) x)`. -/
theorem round_run (n : Nat) : ∀ i x, 1 ≤ x → x ≤ n →
    (∀ j, j < i → ¬ Cond n (it (j + 1) x)) → Cond n (it (i + 1) x) →
    (it (i + 1) x = n → HaltAt (PB n x)) ∧ (it (i + 1) x ≠ n → Rch (PB n x) (RS (n + 1))) := by
  intro i
  induction i with
  | zero =>
    intro x h1 hx _ hc
    have s := step_cases n x h1 hx
    exact ⟨s.2.1, s.1 hc⟩
  | succ i ih =>
    intro x h1 hx hfirst hc
    have h0 : ¬ Cond n (collatz x) := hfirst 0 (by omega)
    have hpos := collatz_pos x (by omega)
    have s := (step_cases n x h1 hx).2.2 h0
    have hy : 1 ≤ collatz x ∧ collatz x ≤ n := by unfold Cond at h0; omega
    have := ih (collatz x) hy.1 hy.2
      (fun j hj => by rw [← it_succ']; exact hfirst (j + 1) (by omega))
      (by rw [← it_succ']; exact hc)
    rw [← it_succ'] at this
    exact ⟨fun h => HaltAt.back s (this.1 h), fun h => Rch.tr s (this.2 h)⟩

end TM.WeakCollatz
