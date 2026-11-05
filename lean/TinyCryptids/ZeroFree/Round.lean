import TinyCryptids.ZeroFree.Tac
import TinyCryptids.ZeroFree.Codes

/-!
# One round on the tape

A digit `d` takes four cells: its parity, then the three cells of code A (`ax d`, `ay d`,
`az d`). The pass rewrites the group of an old digit `d` reached with carry `c` into
`c, qx d, qy d, qz d` (code B), which stands for the new digit `dd c d`; the scan,
right to left, rewrites it into code A of `dd c d` and looks for the digit 0.

Left of the digits are the separator `0 0` and the counter (`ctr c`): guard cells `1`
and bits `v_i`, nearest first `g0 v0 g1 v1 … g5 v5`.

    S c ds = round start: the counter `c`, the digits `ds` in code A, `C0` on the first
             parity cell.
-/

namespace TM.ZeroFree

open D

local notation "F" => false

/-- parity of a digit -/
def par : D → Bool
  | d0 | d2 | d4 | d6 | d8 => false
  | d1 | d3 | d5 | d7 | d9 => true

/-- digits in code A to the right of the head, the first one nearest -/
def putA : List D → Strm → Strm
  | [], s => s
  | d :: ds, s => par d ::: ax d ::: ay d ::: az d ::: putA ds s

/-- groups written by the pass (carry, old digit) to the left of the head, the last nearest -/
def pushB : List (Bool × D) → Strm → Strm
  | [], s => s
  | (c, d) :: gs, s => pushB gs (qz d ::: qy d ::: qx d ::: c ::: s)

theorem pushB_append (l m : List (Bool × D)) (s : Strm) : pushB (l ++ m) s = pushB m (pushB l s) := by
  induction l generalizing s with
  | nil => rfl
  | cons g l ih => obtain ⟨c, d⟩ := g; exact ih _

theorem putA_append (l m : List D) (s : Strm) : putA (l ++ m) s = putA l (putA m s) := by
  induction l with
  | nil => rfl
  | cons d l ih => show _ ::: _ ::: _ ::: _ ::: putA (l ++ m) s = _; rw [ih]; rfl

/-- the new digit of a group -/
def nd (g : Bool × D) : D := dd g.1 g.2

/-- the groups of a pass with carry `c` over `ds` -/
def trace (c : Bool) : List D → List (Bool × D)
  | [] => match c with
    | false => []
    | true => [(true, d0)]
  | d :: ds => (c, d) :: trace (hi d) ds

theorem trace_nd (c : Bool) (ds : List D) : (trace c ds).map nd = dbl c ds := by
  induction ds generalizing c with
  | nil => cases c <;> rfl
  | cons d ds ih => simp only [trace, dbl, List.map_cons, nd, ih]

/-- counter cells, nearest first: guard, bit, … -/
def bitsL : Nat → Nat → Strm
  | 0, _ => blank
  | k + 1, c => true ::: (c % 2 == 1) ::: bitsL k (c / 2)

def ctr (c : Nat) : Strm := F ::: F ::: bitsL 6 c

def S (c : Nat) (ds : List D) : Cfg St := ⟨St.C0, ctr c, putA ds blank⟩

def cst : Bool → St
  | false => St.C0
  | true => St.C1

theorem blankR {q : St} {L : Strm} {X : Cfg St} (h : Rch ⟨q, L, F ::: blank⟩ X) :
    Rch ⟨q, L, blank⟩ X := by rw [← cons_blank]; exact h

/-! ## the pass -/

/-- one digit: four steps right -/
theorem pass_digit (c : Bool) (d : D) (L R : Strm) :
    Rch ⟨cst c, L, putA [d] R⟩ ⟨cst (hi d), pushB [(c, d)] L, R⟩ := by
  cases c <;> cases d <;> (zfR; zfR; zfR; zfR; exact Reach.refl delta _)

/-- the blank group after the number: carry 0 starts the scan on the top digit -/
theorem pass_end0 (L : Strm) : Rch ⟨St.C0, L, blank⟩ (cfgL St.Sz L blank) := by
  refine blankR ?_; zfR
  refine blankR ?_; zfR
  refine blankR ?_; zfR
  refine blankR ?_
  refine Rch.tr (stepL (δ := delta) (L := F ::: F ::: F ::: L) (R := F ::: blank) rfl) ?_
  refine Rch.tr (stepL (δ := delta) (L := F ::: F ::: L) (R := F ::: F ::: blank) rfl) ?_
  refine Rch.tr (stepL (δ := delta) (L := F ::: L) (R := F ::: F ::: F ::: blank) rfl) ?_
  refine Rch.tr (stepL (δ := delta) (L := L) (R := F ::: F ::: F ::: F ::: blank) rfl) ?_
  show Rch (cfgL St.Sz L (F ::: F ::: F ::: F ::: blank)) _
  rw [cons_blank, cons_blank, cons_blank, cons_blank]; exact Reach.refl delta _

/-- carry 1 on the blank group: the new digit 1, then the end -/
theorem pass_end1 (L : Strm) :
    Rch ⟨St.C1, L, blank⟩ (cfgL St.Sz (pushB [(true, d0)] L) blank) := by
  refine blankR ?_; zfR
  refine blankR ?_; zfR
  refine blankR ?_; zfR
  refine blankR ?_
  refine Rch.tr (stepL (δ := delta) (L := F ::: F ::: true ::: L) (R := F ::: blank) rfl) ?_
  refine Rch.tr (stepL (δ := delta) (L := F ::: true ::: L) (R := F ::: F ::: blank) rfl) ?_
  refine Rch.tr (stepL (δ := delta) (L := true ::: L) (R := F ::: F ::: F ::: blank) rfl) ?_
  zfR; zfR; zfR; zfR
  exact pass_end0 (pushB [(true, d0)] L)

/-- The pass from the first cell of `ds` with carry `c`: it writes the groups
`trace c ds` and starts the scan on the top group. -/
theorem pass : ∀ (ds : List (D)) (done : List (Bool × D)) (c : Bool) (P : Strm),
    Rch ⟨cst c, pushB done P, putA ds blank⟩ (cfgL St.Sz (pushB (done ++ trace c ds) P) blank) := by
  intro ds
  induction ds with
  | nil =>
    intro done c P
    cases c
    · simpa [trace] using pass_end0 (pushB done P)
    · have := pass_end1 (pushB done P)
      rw [← pushB_append] at this; exact this
  | cons d ds ih =>
    intro done c P
    refine Rch.tr (pass_digit c d _ (putA ds blank)) ?_
    have := ih (done ++ [(c, d)]) (hi d) P
    rw [pushB_append, List.append_assoc] at this
    exact this

theorem pass_digit1 (c : Bool) (d : D) (L R : Strm) :
    Rch1 ⟨cst c, L, putA [d] R⟩ ⟨cst (hi d), pushB [(c, d)] L, R⟩ := by
  cases c <;> cases d <;>
    exact Reach1.trans_reach delta (stepR1 (δ := delta) rfl) (by zfR; zfR; zfR; exact Reach.refl delta _)

/-- the pass over a nonempty number takes at least one step -/
theorem pass1 (d : D) (ds : List D) (c : Bool) (P : Strm) :
    Rch1 ⟨cst c, P, putA (d :: ds) blank⟩ (cfgL St.Sz (pushB (trace c (d :: ds)) P) blank) :=
  Reach1.trans_reach delta (pass_digit1 c d P (putA ds blank)) (pass ds [(c, d)] (hi d) P)

/-! ## the scan -/

/-- the scan crosses a group whose new digit is not 0, rewriting it into code A -/
theorem scan_group (g : Bool × D) (h : nd g ≠ d0) (L R : Strm) :
    Rch (cfgL St.Sz (pushB [g] L) R) (cfgL St.Sz L (putA [nd g] R)) := by
  obtain ⟨c, d⟩ := g
  cases c <;> cases d <;> first
    | exact absurd rfl h
    | (zfL; zfL; zfL; zfL; exact Reach.refl delta _)

theorem found_group (g : Bool × D) (L R : Strm) :
    Rch (cfgL St.Fz (pushB [g] L) R) (cfgL St.Fz L (putA [nd g] R)) := by
  obtain ⟨c, d⟩ := g
  cases c <;> cases d <;> (zfL; zfL; zfL; zfL; exact Reach.refl delta _)

/-- the group of the digit 0: the scan switches to `Fz` -/
theorem zero_group (g : Bool × D) (h : nd g = d0) (L R : Strm) :
    Rch (cfgL St.Sz (pushB [g] L) R) (cfgL St.Fz L (putA [nd g] R)) := by
  obtain ⟨c, d⟩ := g
  cases c <;> cases d <;> first
    | exact absurd h (by decide)
    | (zfL; zfL; zfL; zfL; exact Reach.refl delta _)

theorem scan_cross : ∀ (gs : List (Bool × D)), d0 ∉ gs.map nd → ∀ (L R : Strm),
    Rch (cfgL St.Sz (pushB gs L) R) (cfgL St.Sz L (putA (gs.map nd) R)) := by
  intro gs
  induction gs with
  | nil => intro _ L R; exact Reach.refl delta _
  | cons g gs ih =>
    intro h L R
    simp only [List.map_cons, List.mem_cons, not_or] at h
    refine Rch.tr (ih h.2 _ R) ?_
    exact scan_group g (Ne.symm h.1) L _

theorem found_cross : ∀ (gs : List (Bool × D)) (L R : Strm),
    Rch (cfgL St.Fz (pushB gs L) R) (cfgL St.Fz L (putA (gs.map nd) R)) := by
  intro gs
  induction gs with
  | nil => intro L R; exact Reach.refl delta _
  | cons g gs ih =>
    intro L R
    exact Rch.tr (ih _ R) (found_group g L _)

theorem split_last {l : List D} (h : d0 ∈ l) :
    ∃ pre post, l = pre ++ d0 :: post ∧ d0 ∉ post := by
  induction l with
  | nil => exact absurd h (List.not_mem_nil _)
  | cons d r ih =>
    by_cases hr : d0 ∈ r
    · obtain ⟨pre, post, e, hp⟩ := ih hr
      exact ⟨d :: pre, post, by rw [e]; rfl, hp⟩
    · have hd : d = d0 := by
        rcases List.mem_cons.1 h with h | h
        · exact h.symm
        · exact absurd h hr
      exact ⟨[], r, by rw [hd]; rfl, hr⟩

theorem map_split {gs : List (Bool × D)} {pre post : List D}
    (h : gs.map nd = pre ++ d0 :: post) :
    ∃ gp g gq, gs = gp ++ g :: gq ∧ gp.map nd = pre ∧ nd g = d0 ∧ gq.map nd = post := by
  induction pre generalizing gs with
  | nil =>
    cases gs with
    | nil => exact absurd h (by simp)
    | cons g gq =>
      simp only [List.map_cons, List.nil_append, List.cons.injEq] at h
      exact ⟨[], g, gq, rfl, rfl, h.1, h.2⟩
  | cons p pre ih =>
    cases gs with
    | nil => exact absurd h (by simp)
    | cons g gs =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨gp, g', gq, e, h1, h2, h3⟩ := ih h.2
      exact ⟨g :: gp, g', gq, by rw [e]; rfl, by simp [h.1, h1], h2, h3⟩

/-- With a digit 0, the scan reaches the separator in `Fz`; then the next pass starts. -/
theorem scan_found (gs : List (Bool × D)) (h : d0 ∈ gs.map nd) (c : Nat) :
    Rch (cfgL St.Sz (pushB gs (ctr c)) blank) (S c (gs.map nd)) := by
  obtain ⟨pre, post, e, hp⟩ := split_last h
  obtain ⟨gp, g, gq, rfl, h1, h2, h3⟩ := map_split e
  rw [pushB_append]
  show Rch (cfgL St.Sz (pushB gq (pushB [g] (pushB gp (ctr c)))) blank) _
  refine Rch.tr (scan_cross gq (by rw [h3]; exact hp) _ blank) ?_
  refine Rch.tr (zero_group g h2 _ _) ?_
  refine Rch.tr (found_cross gp _ _) ?_
  zfL; zfR; zfR
  show Rch ⟨St.C0, ctr c, putA (gp.map nd) (putA [nd g] (putA (gq.map nd) blank))⟩ _
  rw [← putA_append, ← putA_append]
  simp only [S, List.map_append, List.map_cons, List.append_assoc, List.singleton_append]
  exact Reach.refl delta _

/-! ## the counter -/

/-- `j` pairs `0 1` (a bit 0, its guard) to the right, nearest first -/
def zp : Nat → Strm → Strm
  | 0, s => s
  | j + 1, s => F ::: true ::: zp j s

/-- the same cells after crossing them, to the left -/
def zpL : Nat → Strm → Strm
  | 0, s => s
  | j + 1, s => zpL j (true ::: F ::: s)

theorem cross_zp : ∀ (j : Nat) (L S : Strm), Rch ⟨St.R1, L, zp j S⟩ ⟨St.R1, zpL j L, S⟩
  | 0, L, S => Reach.refl delta _
  | j + 1, L, S => by
    show Rch ⟨St.R1, L, F ::: true ::: zp j S⟩ _
    zfR; zfR
    exact cross_zp j _ S

theorem bit_even {c : Nat} (h : c % 2 = 0) : (c % 2 == 1) = false := by rw [h]; rfl
theorem bit_odd {c : Nat} (h : c % 2 = 1) : (c % 2 == 1) = true := by rw [h]; rfl

/-- Increment: from the guard `g0`, the counter `c` (with `c + 1 < 2 ^ k`) becomes `c + 1`,
and the parser after it starts the next pass. -/
theorem inc : ∀ (k c j : Nat) (X : Strm), c + 1 < 2 ^ k →
    Rch (cfgL St.G (bitsL k c) (zp j (F ::: F ::: X))) ⟨St.C0, F ::: F ::: zpL j (bitsL k (c + 1)), X⟩
  | 0, c, _, _, h => absurd h (by simp)
  | k + 1, c, j, X, h => by
    show Rch (cfgL St.G (true ::: (c % 2 == 1) ::: bitsL k (c / 2)) _) _
    zfL
    rcases Nat.mod_two_eq_zero_or_one c with hc | hc
    · rw [bit_even hc]
      zfR; zfR
      show Rch ⟨St.R1, true ::: true ::: bitsL k (c / 2), zp j (F ::: F ::: X)⟩ _
      refine Rch.tr (cross_zp j _ _) ?_
      zfR; zfR
      have e : (c + 1) / 2 = c / 2 := by omega
      have b : ((c + 1) % 2 == 1) = true := bit_odd (by omega)
      show Rch _ ⟨St.C0, F ::: F ::: zpL j (true ::: ((c + 1) % 2 == 1) ::: bitsL k ((c + 1) / 2)), X⟩
      rw [e, b]; exact Reach.refl delta _
    · rw [bit_odd hc]
      zfL
      have ih := inc k (c / 2) (j + 1) X (by rw [Nat.pow_succ] at h; omega)
      have e : (c + 1) / 2 = c / 2 + 1 := by omega
      have b : ((c + 1) % 2 == 1) = false := bit_even (by omega)
      show Rch _ ⟨St.C0, F ::: F ::: zpL j (true ::: ((c + 1) % 2 == 1) ::: bitsL k ((c + 1) / 2)), X⟩
      rw [e, b]; exact ih

/-- the machine reaches its halting state -/
def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨St.halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

/-- The full counter overflows: the machine halts. -/
theorem overflow : ∀ (k : Nat) (R : Strm), HaltAt (cfgL St.G (bitsL k (2 ^ k - 1)) R)
  | 0, R => ⟨_, _, sL (s := blank) (b := F) (by rfl)⟩
  | k + 1, R => by
    have := Nat.two_pow_pos k
    have e : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by rw [Nat.pow_succ]; omega
    have b : ((2 ^ (k + 1) - 1) % 2 == 1) = true := bit_odd (by rw [Nat.pow_succ]; omega)
    show HaltAt (cfgL St.G (true ::: ((2 ^ (k + 1) - 1) % 2 == 1) ::: bitsL k ((2 ^ (k + 1) - 1) / 2)) R)
    rw [e, b]
    refine HaltAt.back (sL (by rfl)) ?_
    refine HaltAt.back (sL (by rfl)) ?_
    exact overflow k _

/-! ## rounds -/

/-- No digit 0 in the new number: the counter goes up by one. -/
theorem round_no0 (c : Nat) (hc : c < 63) (d : D) (ds : List D) (h : d0 ∉ dbl false (d :: ds)) :
    Rch1 (S c (d :: ds)) (S (c + 1) (dbl false (d :: ds))) := by
  have hp := pass1 d ds false (ctr c)
  rw [← trace_nd] at h ⊢
  refine Reach1.trans_reach delta hp ?_
  refine Rch.tr (scan_cross _ h _ blank) ?_
  zfL; zfL
  exact inc 6 c 0 _ (show c + 1 < 64 by omega)

/-- A digit 0 in the new number: the counter stays. -/
theorem round_0 (c : Nat) (d : D) (ds : List D) (h : d0 ∈ dbl false (d :: ds)) :
    Rch1 (S c (d :: ds)) (S c (dbl false (d :: ds))) := by
  have hp := pass1 d ds false (ctr c)
  rw [← trace_nd] at h ⊢
  exact Reach1.trans_reach delta hp (scan_found _ h c)

/-- No digit 0 with the counter at 63: the machine halts. -/
theorem round_halt (ds : List D) (h : d0 ∉ dbl false ds) : HaltAt (S 63 ds) := by
  have hp := pass ds [] false (ctr 63)
  rw [← trace_nd] at h
  refine HaltAt.back hp ?_
  refine HaltAt.back (scan_cross _ h _ blank) ?_
  refine HaltAt.back (sL (by rfl)) ?_
  refine HaltAt.back (sL (by rfl)) ?_
  exact overflow 6 _

/-- The first pass, from the seed: the number 1 = 2^0 (no digit 0), counter 27 + 1. -/
theorem first : Rch ⟨St.C1, ctr 27, blank⟩ (S 28 (pw 0)) := by
  have hp := pass [] [] true (ctr 27)
  refine Rch.tr hp ?_
  have h : d0 ∉ (trace true []).map nd := by decide
  refine Rch.tr (scan_cross _ h _ blank) ?_
  zfL; zfL
  exact inc 6 27 0 _ (by decide)

end TM.ZeroFree
