import TinyCryptids.Lychrel.Div

/-!
# Multiplication: P := 10 A + d

The tape right of D during the multiplication: `00`, X (`x + 3` cells), `g` zeros,
A (`a + 1` cells), `00`, Q (`q` cells), `00`, P (`r` cells).
-/

namespace TM.Lychrel
open St

local notation "F" => false

/-- right of D's last cell -/
def RtP (x g a q r : Nat) : Strm :=
  F ::: F ::: ones (x + 3) (zeros g (ones (a + 1) (F ::: F ::: ones q (F ::: F ::: ones r blank))))

/-- about to step the counter down (at D's hole) -/
def PL (x g a q r p : Nat) : Cfg St := ⟨bA, ones (p + 1) blank, F ::: ones (10 - p) (RtP x g a q r)⟩

/-- the left stream of the finder back to D, from the cell left of P's new last cell -/
theorem hb_back (x g a q r p : Nat) (hg : 2 ≤ g) (hq : 1 ≤ q) (hp : p ≤ 9) :
    Rch (cfgL hBP (ones r (F ::: F ::: ones q (F ::: F ::: ones (a + 1) (zeros g (ones (x + 3)
        (F ::: F ::: ones (10 - p) (F ::: ones (p + 1) blank))))))) (true ::: blank))
      (PL x g a q (r + 1) p) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 2 := ⟨g - 2, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n, 10 - p = n + 1 := ⟨9 - p, by omega⟩
  rw [hn]
  sLn r; gL; gL; gL; sLn q'; gL; gL; gL; sLn a; gL; gL; zLn g'; gL; sLn (x + 2); gL; gL; gL
  sLn n; gL; gR
  unfold PL RtP; rw [hn, ones_tr n, ones_tr (x + 2), zeros_fa g', zeros_fa (g' + 1), ones_tr a, ones_tr q',
    ones_tr r]
  fin

/-- the left stream from X's last cell back to D's hole and beyond -/
def LX (x p : Nat) : Strm := ones (x + 3) (F ::: F ::: ones (10 - p) (F ::: ones (p + 1) blank))

/-- in the gap after X (`k + 1` 0s of it already passed): append a cell to P, back to D -/
theorem dep4 (x k g a q r p : Nat) (hkg : 1 ≤ k + g) (hq : 1 ≤ q) (hp : p ≤ 9) :
    Rch ⟨rP4, zeros (k + 1) (LX x p), zeros g (ones (a + 1) (F ::: F ::: ones q (F ::: F ::: ones r blank)))⟩
      (PL x (k + 1 + g) a q (r + 1) p) := by
  zRn g; gR; sRn a; gR; gR; sRn q; gR; gR; sRn r; refine blankR ?_; gL
  rw [ones_tr a, zeros_add, Nat.add_comm g]
  exact hb_back x (k + 1 + g) a q r p (by omega) hq hp

/-- from D's cell right of the hole: append a cell to P, back to D -/
theorem dep1 (x g a q r p : Nat) (hg : 2 ≤ g) (hq : 1 ≤ q) (hp : p ≤ 9) :
    Rch ⟨rP1, F ::: ones (p + 1) blank, ones (10 - p) (RtP x g a q r)⟩
      (PL x g a q (r + 1) p) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  unfold RtP
  sRn (10 - p); gR; gR; gR; sRn (x + 2); gR
  rw [ones_tr (x + 2)]
  have := dep4 x 0 g' a q r p (by omega) hq hp
  rw [show 0 + 1 + g' = g' + 1 by omega] at this
  exact this

/-- from A's second cell: append a cell to P, ready to go back -/
theorem dep5 (Lft : Strm) (a q r : Nat) :
    Rch ⟨rP5, Lft, ones a (F ::: F ::: ones q (F ::: F ::: ones r blank))⟩
      (cfgL hBP (ones r (F ::: F ::: ones q (F ::: F ::: ones a Lft))) (true ::: blank)) := by
  sRn a; gR; gR; sRn q; gR; gR; sRn r; refine blankR ?_; gL; fin

/-- p ≥ 1: p -= 1, one more cell of P -/
theorem pl_n (x g a q r p : Nat) (hg : 2 ≤ g) (hq : 1 ≤ q) (hp1 : 1 ≤ p) (hp : p ≤ 9) :
    Rch (PL x g a q r p) (PL x g a q (r + 1) (p - 1)) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, 10 - (p' + 1) = k + 1 := ⟨8 - p', by omega⟩
  unfold PL
  rw [hk, show p' + 1 - 1 = p' by omega]
  refine Rch.tr (bstep p' k _) ?_
  rw [show k + 2 = 10 - p' by omega]
  exact dep1 x g a q r p' hg hq (by omega)

/-- p = 0 and A has a cell to spare: erase A's first cell, p := 9, one more cell of P -/
theorem pl_w (x g a q r : Nat) (hg : 1 ≤ g) (hq : 1 ≤ q) :
    Rch (PL x g (a + 1) q r 0) (PL x (g + 1) a q (r + 1) 9) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  unfold PL RtP
  rw [show 10 - 0 = 10 by rfl]
  refine Rch.tr (bstep_wrap _) ?_
  gR; gR; gR; gR; sRn (x + 2); gR; zRn g'; gR; gL; gR
  refine Rch.tr (dep5 _ (a + 1) q r) ?_
  show Rch (cfgL hBP (ones r (F ::: F ::: ones q (F ::: F ::: ones (a + 1) (F ::: zeros g' (F ::: ones (x + 2)
    (true ::: F ::: F ::: ones 1 (F ::: ones 10 blank))))))) (true ::: blank)) _
  rw [zeros_fa g', ones_tr (x + 2)]
  exact hb_back x (g' + 2) a q r 9 (by omega) hq (by omega)

theorem mul_drain (x g a q r : Nat) (hg : 2 ≤ g) (hq : 1 ≤ q) :
    ∀ p, p ≤ 9 → Rch (PL x g a q r p) (PL x g a q (r + p) 0) := by
  intro p
  induction p generalizing r with
  | zero => intro _; fin
  | succ p ih =>
    intro hp
    refine Rch.tr (pl_n x g a q r (p + 1) hg hq (by omega) hp) ?_
    rw [show p + 1 - 1 = p by omega, show r + (p + 1) = r + 1 + p by omega]
    exact ih (r + 1) (by omega)

theorem mul_all (x q : Nat) (hq : 1 ≤ q) :
    ∀ a g r, 2 ≤ g → Rch (PL x g a q r 0) (PL x (g + a) 0 q (r + 10 * a) 0) := by
  intro a
  induction a with
  | zero => intro g r _; fin
  | succ a ih =>
    intro g r hg
    refine Rch.tr (pl_w x g a q r (by omega) hq) ?_
    refine Rch.tr (mul_drain x (g + 1) a q (r + 1) (by omega) hq 9 (by omega)) ?_
    have := ih (g + 1) (r + 1 + 9) (by omega)
    rw [show g + 1 + a = g + (a + 1) by omega, show r + 1 + 9 + 10 * a = r + 10 * (a + 1) by omega] at this
    exact this

/-- the multiplication from the counter at `d` (P has its first cell) -/
theorem multiply (x g a q d : Nat) (hg : 2 ≤ g) (hq : 1 ≤ q) (hd : d ≤ 9) :
    Rch (PL x g a q 1 d) (PL x (g + a) 0 q (1 + d + 10 * a) 0) := by
  refine Rch.tr (mul_drain x g a q 1 hg hq d hd) ?_
  exact mul_all x q hq a g (1 + d) hg

end TM.Lychrel
