import TinyCryptids.SophieGermain.Tac

/-!
# The mod walk

Tape (`F` = blank; blank left of D and right of R):

    D 0 R

* `D` : `d` cells, the trial divisor `d ≥ 3`, all 1 except a hole at cell `c < d`; before a
  walk the hole is on cell 0, the blank cell left of D's `d - 1` ones;
* one 0, the separator;
* `R` : `r` cells; during the mod walk a hole moves right through it.

Each step of the walk moves D's hole **two** cells right (cyclically), so after the walk it
is on cell `2 r mod d`. Configurations are stated with the cells left of the head as a
stream read leftwards (nearest cell first). `Dp d c` is D read leftwards from its last cell.
-/

namespace TM.SophieGermain
open St

local notation "F" => false

/-- D read leftwards from its last cell: `d` cells, the hole at cell `c` -/
def Dp (d c : Nat) : Strm := ones (d - 1 - c) (F ::: ones c blank)

/-- The mod walk with `k` of its `r` steps done: `B2` on R's cell `k` (R has no hole; the
next step makes one there), or on the blank after R when `k = r`. -/
def W (d r c k : Nat) : Cfg St := ⟨B2, ones k (F ::: Dp d c), ones (r - k) blank⟩

/-- the start of the mod walk for `d`: the D hole on cell 0, `B2` on R's cell 0 -/
def WS (d r : Nat) : Cfg St := W d r 0 0

/-- one step: make the R hole on R's cell `k`, move the D hole two cells right
(cyclically), fill the R hole; `B2` ends on R's cell `k + 1` -/
theorem walk_step (d r c k : Nat) (hd : 3 ≤ d) (hc : c < d) (hk : k < r) :
    Rch (W d r c k) (W d r ((c + 2) % d) (k + 1)) := by
  obtain ⟨j, hj⟩ : ∃ j, r - k = j + 1 := ⟨r - k - 1, by omega⟩
  unfold W
  rw [hj, show r - (k + 1) = j by omega]
  unfold Dp
  gL
  sLn k
  gL
  sLn (d - 1 - c)
  gR
  by_cases hw : c + 2 < d
  · -- no wrap: the hole moves two cells right
    obtain ⟨e, he⟩ : ∃ e, d - 1 - c = e + 2 := ⟨d - 3 - c, by omega⟩
    rw [he, Nat.mod_eq_of_lt hw, show d - 1 - (c + 2) = e by omega]
    gR; gR; sRn e; gR; sRn k; gR; fin
  · by_cases hw1 : c + 2 = d
    · -- the hole was on cell d - 2: to cell 0
      subst hw1
      rw [Nat.mod_self, show c + 2 - 1 - c = 1 by omega, show c + 2 - 1 - 0 = c + 1 by omega]
      gR; gL
      show Rch (cfgL W1 (ones (c + 2) blank) _) _
      sLn (c + 2)
      gR; gR; sRn (c + 1); gR; sRn k; gR
      rw [tl_blank, cons_blank]; fin
    · -- the hole was on cell d - 1: to cell 1
      obtain rfl : d = c + 1 := by omega
      rw [show c + 2 = (c + 1) + 1 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 1 < c + 1),
        show c + 1 - 1 - c = 0 by omega, show c + 1 - 1 - 1 = c - 1 by omega]
      gL
      show Rch (cfgL W3 (ones (c + 1) blank) _) _
      sLn (c + 1)
      gR
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      gR; gR; rw [show c' + 1 - 1 = c' by omega]; sRn c'; gR; sRn k; gR
      rw [tl_blank, cons_blank]; fin

/-- the whole walk: from `r - i` steps done to `r` -/
theorem walk (d r : Nat) (hd : 3 ≤ d) : ∀ i c, i ≤ r → c < d →
    Rch (W d r c (r - i)) (W d r ((c + 2 * i) % d) r) := by
  intro i
  induction i with
  | zero => intro c _ hc; rw [Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hc, Nat.sub_zero]; fin
  | succ i ih =>
    intro c hi hc
    refine Rch.tr (walk_step d r c (r - (i + 1)) hd hc (by omega)) ?_
    have := ih ((c + 2) % d) (by omega) (Nat.mod_lt _ (by omega))
    rw [Nat.mod_add_mod, show c + 2 + 2 * i = c + 2 * (i + 1) by omega] at this
    rw [show r - (i + 1) + 1 = r - i by omega]
    exact this

theorem walk_all (d r : Nat) (hd : 3 ≤ d) : Rch (WS d r) (W d r ((2 * r) % d) r) := by
  have := walk d r hd r 0 (Nat.le_refl _) (by omega)
  rwa [Nat.sub_self, Nat.zero_add] at this

end TM.SophieGermain
