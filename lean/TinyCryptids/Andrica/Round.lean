import TinyCryptids.Andrica.Test

/-!
# One round after the test: countdown, phase, rebuild

Tape: `H 00 U 00 T 00 D 00 R`.

* `H` : `t + 1` cells, its hole at cell `x` (`1 ≤ x ≤ t - 1`);
* `U 00 T` : `u` and `t - u` cells (`u + 1 ≤ t`; `U` may be empty); `t - u` is the countdown;
* `D 00 R` : the pair, `D = 1 0 1^d` after a test.

Leaving the test, the head goes left to the U/T separator (a scan for a `00`; for a prime a
parser first crosses D's hole). A composite moves the separator one cell right (`comp`, or
`comp_halt` when T had one cell), a prime fills it and writes it at U's left end (`prime`). A
parser finds H's hole: it moves two cells right (`hadv`), or H grows (`hwrap`): H's last cell
joins the separator, the separator's last cell becomes U's new cell 0, and two new cells on the
left of H hold the new hole at cell 1. A parser finds D's hole and `rebuild` makes `D := 2` and
`R := m - 1` for the next number (`ret`).
-/

namespace TM.Andrica

open St

local notation "F" => false

theorem PPC : ParserL delta PC1 PC2 := by constructor <;> rfl
theorem PPH : ParserL delta PH1 PH2 := by constructor <;> rfl
theorem PPN : ParserR delta PN1 PN2 := by constructor <;> rfl

/-- H read from its last cell to the left: `t + 1` cells, the hole at cell `x` -/
def Hr (t x : Nat) : Strm := ones (t - x) (F ::: ones x blank)

/-- left of D's separator cell: the separator's other cell, T, the U/T separator, U, the H/U
separator, H (all read from the right) -/
def Lx (t x u : Nat) : Strm := F ::: ones (t - u) (F ::: F ::: ones u (F ::: F ::: Hr t x))

/-- the pair after a test, from D's cell 0 (hole at cell 1) -/
def Dst (d r : Nat) : Strm := true ::: F ::: ones d (F ::: F ::: ones (r + 2) (F ::: blank))

/-- round start: about to test `m` with `d = 2` -/
def RS (m t x u : Nat) : Cfg St := SHT (Lx t x u) blank 2 (m - 2)

/-- the head just left of the U/T separator, about to look for H's hole -/
def HE (t x u : Nat) (Y : Strm) : Cfg St :=
  cfgL PH1 (ones u (F ::: F ::: Hr t x)) (F ::: F ::: ones (t - u) (F ::: Y))

/-! ## the countdown -/

/-- composite: the U/T separator one cell right -/
theorem comp (t x u d r : Nat) (hu : u + 2 ≤ t) :
    Rch (CK (Lx t x u) blank d r) (HE t x (u + 1) (F ::: Dst d r)) := by
  obtain ⟨c, hc⟩ : ∃ c, t - u = c + 2 := ⟨t - u - 2, by omega⟩
  unfold CK Lx HE Dst
  rw [hc, show t - (u + 1) = c + 1 by omega]
  gL; gL
  sLn (c + 1)
  gL; gR; gR; gR
  rw [ones_cons_true]
  gL; gL; gL
  fin

/-- composite, T has one cell: it is gone and the machine halts -/
theorem comp_halt (t x u d r : Nat) (hu : u + 1 = t) : HaltAt (CK (Lx t x u) blank d r) := by
  unfold CK Lx HaltAt
  rw [show t - u = 1 by omega]
  apply Exists.intro; apply Exists.intro
  gL; gL; gL; gR; gR; gR; gR; fin

/-- prime: past D's hole to the U/T separator; fill it, write it at U's left end -/
theorem prime (t x u d : Nat) (hu : u + 1 ≤ t) (hd : 1 ≤ d) :
    Rch (CP (Lx t x u) blank d) (HE t x 0 (F ::: Dst d 0)) := by
  obtain ⟨c, hc⟩ : ∃ c, t - u = c + 1 := ⟨t - u - 1, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  unfold CP Lx HE Dst
  rw [hc]
  refine Rch.tr (PPC.find2 2 e _ _) ?_
  gL; gL; gL; gL
  sLn c
  gL; gR; gL
  show Rch (cfgL f3 (ones (u + 1) (F ::: F ::: Hr t x)) _) _
  sLn (u + 1); gR
  rw [ones_succ, ones_cons_true]
  gR; gL; gL
  rw [ones_add, ← ones_succ', show u + c + 1 = t - 0 by omega]; fin

/-! ## the phase block -/

/-- H's hole at cell `x`, the head on cell `x + 1`, about to look for D's hole -/
def AH (t x u : Nat) (Y : Strm) : Cfg St :=
  ⟨PN1, F ::: ones x blank, ones (t - x) (F ::: F ::: ones u (F ::: F ::: ones (t - u) (F ::: Y)))⟩

/-- H's hole two cells right -/
theorem hadv (t x u : Nat) (Y : Strm) (hx : 1 ≤ x) (ht : x + 3 ≤ t) :
    Rch (HE t x u Y) (AH t (x + 2) u Y) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, t - (y + 1) = c + 3 := ⟨t - y - 4, by omega⟩
  unfold HE AH Hr
  rw [hc, show t - (y + 1 + 2) = c + 1 by omega]
  refine Rch.tr (PPH.find2 u (c + 2) _ _) ?_
  gR; gR; gR; gR; gL; gR; fin

/-- the wrap from the separator's last cell (H all 1s): U gets a new cell 0, H loses its last
cell and gets two new cells on the left, the new hole at cell 1 -/
theorem hwrap_tail (t u : Nat) (Y : Strm) :
    Rch ⟨w1, F ::: ones (t + 1) blank, F ::: ones u (F ::: F ::: ones (t - u) (F ::: Y))⟩
      (AH (t + 1) 1 (u + 1) Y) := by
  unfold AH
  gL; gL
  rw [ones_succ]
  gL
  sLn t
  gL; gR; gR
  rw [show t + 1 - 1 = t by omega, show t + 1 - (u + 1) = t - u by omega]
  fin

/-- H's hole on one of its last two positions: H grows, and U with it -/
theorem hwrap (t x u : Nat) (Y : Strm) (hx : x ≤ t - 1) (ht : t ≤ x + 2) (h1 : 1 ≤ x) :
    Rch (HE t x u Y) (AH (t + 1) 1 (u + 1) Y) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  unfold HE Hr
  rcases Nat.lt_or_ge (y + 1 + 1) t with hlt | hge
  · obtain rfl : t = y + 3 := by omega
    rw [show y + 3 - (y + 1) = 2 by omega]
    refine Rch.tr (PPH.find2 u 1 _ _) ?_
    gR; gR; gR; gR; gR
    refine Rch.tr ?_ (hwrap_tail (y + 3) u Y)
    fin
  · obtain rfl : t = y + 2 := by omega
    rw [show y + 2 - (y + 1) = 1 by omega]
    refine Rch.tr (PPH.find2 u 0 _ _) ?_
    gR; gR; gR; gR
    refine Rch.tr ?_ (hwrap_tail (y + 2) u Y)
    fin

/-! ## back to the pair: D := 2, R := m - 1 -/

/-- rebuild from cell 3 of D (`d = g + 2`, hole at cell 1): `D := 2`, `R := m - 1` -/
theorem rebuild (X : Strm) (g r : Nat) :
    Rch ⟨c1, true ::: F ::: true ::: F ::: X, ones (g + 1) (F ::: F ::: ones (r + 2) (F ::: blank))⟩
      (SHT X blank 2 (g + r + 1)) := by
  unfold SHT
  sRn (g + 1); gR; gR; sRn (r + 2); gL
  show Rch (cfgL c4 (true ::: ones (r + 1) (true ::: true ::: ones (g + 1)
    (true ::: F ::: true ::: F ::: X))) (true ::: blank)) _
  rw [show true ::: ones (r + 1) (true ::: true ::: ones (g + 1) (true ::: F ::: true ::: F ::: X)) =
      ones (r + 2) (ones 2 (ones (g + 1) (ones 1 (F ::: true ::: F ::: X)))) from rfl,
    ones_add, ones_add, ones_add, show r + 2 + 2 + (g + 1) + 1 = g + r + 6 by omega]
  sLn (g + r + 6); gR; gR; gR; gR; gR
  rw [← ones_succ', cons_blank, show g + r + 2 + 1 = g + r + 1 + 2 by omega]; fin

/-- from H to the pair, then the rebuild -/
theorem ret (t x u d r : Nat) (hu : u + 1 ≤ t) (hd : 2 ≤ d) :
    Rch (AH t x u (F ::: Dst d r)) (SHT (Lx t x u) blank 2 (d + r - 1)) := by
  obtain ⟨n, hn⟩ : ∃ n, t - u = n + 1 := ⟨t - u - 1, by omega⟩
  obtain ⟨g, rfl⟩ : ∃ g, d = g + 2 := ⟨d - 2, by omega⟩
  unfold AH Dst Lx
  sRn (t - x); gR; gR; sRn u; gR; gR
  refine Rch.tr (PPN.find2 (t - u) 0 _ _) ?_
  gR
  have := rebuild (F ::: ones (t - u) (F ::: F ::: ones u (F ::: F ::: Hr t x))) g r
  rw [show g + r + 1 = g + 2 + r - 1 by omega] at this
  refine Rch.tr ?_ this
  unfold Hr
  fin

end TM.Andrica
