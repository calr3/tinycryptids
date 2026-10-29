import TinyCryptids.TwinPrimes4.Tac

/-!
# Routines of the 4-symbol twin prime machine

Symbols: `0` blank, `1` an R cell, `2` the D marker or the R cursor, `3` a D cell. Tape (blank
elsewhere):

    D R

* `D`: `d` cells, the trial divisor; 3s except the marker 2 on cell `c < d`;
* `R`: `r = m - d` cells, 1s; during the mod walk the cursor 2 moves left through it.

`Dp d c` is D read leftwards from its last cell.

* `walk`: the mod walk moves the marker from `c` to `(c + k) % d` in `k` steps.
* `check_fail`, `check_ok`: the marker on `d - 1` or `d - 3` leads to the next candidate
  (`CS (m + 1)`), otherwise to the walk for `d + 1` (`ZS (d + 1) (r - 1)`).
* `zs_beep`: with R empty (`d = m`) the run reaches the beep (`BeepAt`).
* `after_beep`: from the beep, the next candidate is `m + 3` (`BeepAt n j` leads to
  `ZS 2 (n + j + 1)`); `start_beep`: the blank tape reaches `BeepAt 0 0` in two steps.
-/

namespace TMK.TwinPrimes4
open St

/-- D read leftwards from its last cell: `d` cells, the marker on cell `c` -/
def Dp (d c : Nat) : Strm := rp 3 (d - 1 - c) (2 ∷ rp 3 c blank)

/-- The mod walk with `k` of its `r` steps left: `cur` on R's cell `k - 1` (R has no cursor;
the next step makes one there), or on D's last cell when `k = 0`. -/
def W (d r c k : Nat) : Cfg St := cfgL cur (rp 1 k (Dp d c)) (rp 1 (r - k) blank)

/-- `toR` on R's cell 0 (R has `r` cells), the marker on D's last cell: the start of the walk -/
def ZS (d r : Nat) : Cfg St := ⟨toR, Dp d (d - 1), rp 1 r blank⟩

/-- the start of candidate `m`: `d = 2`, `r = m - 2` -/
def CS (m : Nat) : Cfg St := ZS 2 (m - 2)

/-- just before a beep: `beep` reads the blank after `3 1`; the tape is `n` 3s, `j` 1s, `1 3 1` -/
def BeepAt (n j : Nat) : Cfg St := ⟨beep, 1 ∷ 3 ∷ rp 1 j (rp 3 n blank), blank⟩

theorem Dp_last (d : Nat) (hd : 1 ≤ d) : Dp d (d - 1) = 2 ∷ rp 3 (d - 1) blank := by
  unfold Dp; rw [show d - 1 - (d - 1) = 0 by omega]; rfl

/-! ## the mod walk -/

theorem walk_start (d r : Nat) : Rch (ZS d r) (W d r (d - 1) r) := by
  unfold ZS W
  sRn 1 r
  refine Rch.tr (sLr rfl) ?_
  rw [Nat.sub_self, rp_zero, cons_blank]
  fin

/-- one step: the cursor on R's cell `k`, the marker one cell right (cyclically), the cursor
filled; `cur` ends on the cell left of it -/
theorem walk_step (d r c k : Nat) (hc : c < d) (hk : k < r) :
    Rch (W d r c (k + 1)) (W d r ((c + 1) % d) k) := by
  obtain ⟨j, hj⟩ : ∃ j, r - k = j + 1 := ⟨r - k - 1, by omega⟩
  unfold W
  rw [hj, show r - (k + 1) = j by omega]
  show Rch (cfgL cur (1 ∷ rp 1 k (Dp d c)) (rp 1 j blank)) _
  gL
  sLn 1 k
  unfold Dp
  sLn 3 (d - 1 - c)
  show Rch ⟨toM, rp 3 c blank, 2 ∷ rp 3 (d - 1 - c) (rp 1 k (2 ∷ rp 1 j blank))⟩ _
  gR
  by_cases hw : c + 1 < d
  · -- no wrap: the marker moves one cell right
    obtain ⟨e, he⟩ : ∃ e, d - 1 - c = e + 1 := ⟨d - 2 - c, by omega⟩
    rw [he, Nat.mod_eq_of_lt hw, show d - 1 - (c + 1) = e by omega]
    show Rch ⟨adv, 3 ∷ rp 3 c blank, 3 ∷ rp 3 e (rp 1 k (2 ∷ rp 1 j blank))⟩ _
    gR
    sRn 3 e
    sRn 1 k
    show Rch (cfgL toR (2 ∷ rp 1 k (rp 3 e (2 ∷ 3 ∷ rp 3 c blank))) (rp 1 j blank)) _
    gL
    fin
  · -- wrap: `adv` reads R's cell 0 (a 1, or the cursor if k = 0), `wrap` runs to cell 0
    obtain rfl : c = d - 1 := by omega
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have hm : (e + 1 - 1 + 1) % (e + 1) = 0 := by
      rw [show e + 1 - 1 + 1 = e + 1 by omega, Nat.mod_self]
    simp only [hm, Nat.add_sub_cancel, Nat.sub_self, Nat.mod_self, Nat.sub_zero, rp_zero]
    have hwrap : ∀ x : Nat, ∀ Y : Strm, deltaNB adv x = some (x, TM.Dir.L, wrap) →
        Rch ⟨adv, 3 ∷ rp 3 e blank, x ∷ Y⟩ ⟨toR, rp 3 e (2 ∷ blank), x ∷ Y⟩ := by
      intro x Y hx
      show Rch (cfgL adv (x ∷ 3 ∷ rp 3 e blank) Y) _
      refine Rch.tr (sL hx) ?_
      show Rch (cfgL wrap (rp 3 (e + 1) blank) (x ∷ Y)) _
      sLn 3 (e + 1)
      refine Rch.tr (sRc rfl) ?_
      rw [cons_blank]
      show Rch ⟨adv, blank, 3 ∷ rp 3 e (x ∷ Y)⟩ _
      gR
      sRn 3 e
      fin
    cases k with
    | zero =>
      refine Rch.tr (hwrap 2 (rp 1 j blank) rfl) ?_
      show Rch (cfgL toR (2 ∷ rp 3 e (2 ∷ blank)) (rp 1 j blank)) _
      gL
      fin
    | succ k =>
      refine Rch.tr (hwrap 1 (rp 1 k (2 ∷ rp 1 j blank)) rfl) ?_
      show Rch ⟨toR, rp 3 e (2 ∷ blank), rp 1 (k + 1) (2 ∷ rp 1 j blank)⟩ _
      sRn 1 (k + 1)
      show Rch (cfgL toR (2 ∷ rp 1 (k + 1) (rp 3 e (2 ∷ blank))) (rp 1 j blank)) _
      gL
      fin

/-- the whole walk: `k` steps move the marker from `c` to `(c + k) % d` -/
theorem walk (d r : Nat) : ∀ k c, c < d → k ≤ r → Rch (W d r c k) (W d r ((c + k) % d) 0) := by
  intro k
  induction k with
  | zero => intro c hc _; rw [Nat.add_zero, Nat.mod_eq_of_lt hc]; fin
  | succ k ih =>
    intro c hc hk
    refine Rch.tr (walk_step d r c k hc (by omega)) ?_
    have := ih ((c + 1) % d) (Nat.mod_lt _ (by omega)) (by omega)
    rwa [Nat.mod_add_mod, show c + 1 + k = c + (k + 1) by omega] at this

/-! ## rebuilding: the next candidate -/

/-- `reb` turns the 3s left of a run of 1s into 1s, one zigzag per cell -/
theorem zig : ∀ n j (R : Strm),
    Rch (cfgL reb (rp 1 (j + 1) (rp 3 n blank)) R) (cfgL reb blank (rp 1 (n + j + 1) R)) := by
  intro n
  induction n with
  | zero =>
    intro j R
    sLn 1 (j + 1)
    rw [Nat.zero_add]; fin
  | succ n ih =>
    intro j R
    sLn 1 (j + 1)
    show Rch ⟨reb, rp 3 n blank, 3 ∷ rp 1 (j + 1) R⟩ _
    gR
    show Rch (cfgL reb (1 ∷ 1 ∷ rp 3 n blank) (rp 1 j R)) _
    gL
    refine Rch.tr (ih 0 (rp 1 (j + 1) R)) ?_
    rw [rp_add, show n + 0 + 1 + (j + 1) = n + 1 + j + 1 by omega]
    fin

/-- the 1s with a run of 3s left of them become candidate `n + j + i + 2`, `d = 2` -/
theorem rebuild (n j i : Nat) :
    Rch (cfgL reb (rp 1 (j + 1) (rp 3 n blank)) (rp 1 i blank)) (ZS 2 (n + j + i)) := by
  refine Rch.tr (zig n j _) ?_
  refine Rch.tr (sRc rfl) ?_
  rw [rp_add, show n + j + 1 + i = n + j + i + 1 by omega]
  show Rch ⟨grow, 3 ∷ blank, 1 ∷ rp 1 (n + j + i) blank⟩ _
  gR
  fin

/-! ## the check -/

theorem check_fail (d r c : Nat) (hd : 2 ≤ d) (hc : c < d) (hr : 1 ≤ r)
    (hf : c + 1 = d ∨ c + 3 = d) : Rch (W d r c 0) (CS (d + r + 1)) := by
  obtain ⟨i, rfl⟩ : ∃ i, r = i + 1 := ⟨r - 1, by omega⟩
  unfold W CS
  rw [Nat.sub_zero, rp_zero, show d + (i + 1) + 1 - 2 = d + i by omega]
  rcases hf with h | h
  · -- the marker on D's last cell: d ∣ m
    obtain rfl : c = d - 1 := by omega
    rw [Dp_last d (by omega)]
    gR
    show Rch (cfgL reb (1 ∷ 1 ∷ rp 3 (d - 1) blank) (rp 1 i blank)) _
    gL
    have := rebuild (d - 1) 0 (i + 1)
    rwa [show d - 1 + 0 + (i + 1) = d + i by omega] at this
  · -- the marker on cell d - 3: d ∣ m + 2
    obtain rfl : d = c + 3 := by omega
    unfold Dp
    rw [show c + 3 - 1 - c = 2 by omega]
    show Rch (cfgL cur (3 ∷ 3 ∷ 2 ∷ rp 3 c blank) (rp 1 (i + 1) blank)) _
    gL; gL
    show Rch ⟨chk3, rp 3 c blank, 2 ∷ 3 ∷ 3 ∷ rp 1 (i + 1) blank⟩ _
    gR; gR; gR
    show Rch (cfgL reb (1 ∷ 1 ∷ 1 ∷ 1 ∷ rp 3 c blank) (rp 1 i blank)) _
    gL
    have := rebuild c 2 (i + 1)
    rwa [show c + 2 + (i + 1) = c + 3 + i by omega] at this

theorem check_ok (d r c : Nat) (hd : 2 ≤ d) (hc : c < d) (hr : 1 ≤ r)
    (h1 : c + 1 ≠ d) (h3 : c + 3 ≠ d) : Rch (W d r c 0) (ZS (d + 1) (r - 1)) := by
  obtain ⟨i, rfl⟩ : ∃ i, r = i + 1 := ⟨r - 1, by omega⟩
  unfold W ZS
  rw [Nat.sub_zero, rp_zero, show i + 1 - 1 = i by omega, Dp_last (d + 1) (by omega),
    show d + 1 - 1 = d by omega]
  unfold Dp
  by_cases h2 : c + 2 = d
  · -- the marker on cell d - 2
    obtain rfl : d = c + 2 := by omega
    rw [show c + 2 - 1 - c = 1 by omega]
    show Rch (cfgL cur (3 ∷ 2 ∷ rp 3 c blank) (rp 1 (i + 1) blank)) _
    gL
    show Rch ⟨chk2, rp 3 c blank, 2 ∷ 3 ∷ rp 1 (i + 1) blank⟩ _
    gR; gR; gR
    fin
  · -- the marker further left: `wrap` runs to it
    obtain ⟨e, he⟩ : ∃ e, d - 1 - c = e + 3 := ⟨d - 4 - c, by omega⟩
    rw [he]
    show Rch (cfgL cur (3 ∷ 3 ∷ 3 ∷ rp 3 e (2 ∷ rp 3 c blank)) (rp 1 (i + 1) blank)) _
    gL; gL; gL
    sLn 3 e
    show Rch ⟨wrap, rp 3 c blank, 2 ∷ rp 3 e (3 ∷ 3 ∷ 3 ∷ rp 1 (i + 1) blank)⟩ _
    gR
    rw [show rp 3 e (3 ∷ 3 ∷ 3 ∷ rp 1 (i + 1) blank) = rp 3 (e + 3) (rp 1 (i + 1) blank) from
      ((rp_succ' 3 (e + 2) _).trans ((rp_succ' 3 (e + 1) _).trans (rp_succ' 3 e _))).symm]
    sRn 3 (e + 3)
    rw [show rp 3 (e + 3) (3 ∷ rp 3 c blank) = rp 3 d blank by
      rw [show (3 ∷ rp 3 c blank) = rp 3 (c + 1) blank from rfl, rp_add,
        show e + 3 + (c + 1) = d by omega]]
    gR
    fin

/-! ## the beep -/

/-- R empty (`d = m`): the walk ends at once, the check fails, and `reb` meets the blank right
of D: it writes a 3 there, `grow` a 1, and `beep` reads the next blank -/
theorem zs_beep (d : Nat) (hd : 1 ≤ d) : Rch (ZS d 0) (BeepAt (d - 1) 1) := by
  refine Rch.tr (walk_start d 0) ?_
  unfold W BeepAt
  rw [rp_zero, Nat.sub_zero, rp_zero, Dp_last d hd]
  gR
  refine Rch.tr (sRb rfl) ?_
  refine Rch.tr (sRb rfl) ?_
  fin

/-- the blank tape: `reb` writes a 3, `grow` a 1, and `beep` reads the next blank -/
theorem start_beep : Rch start (BeepAt 0 0) := by
  unfold start BeepAt
  refine Rch.tr (sRb rfl) ?_
  refine Rch.tr (sRb rfl) ?_
  fin

/-- the beep transition -/
theorem beep_step (n j : Nat) :
    Reach1 delta (BeepAt n j) (cfgL reb (1 ∷ 3 ∷ rp 1 j (rp 3 n blank)) (0 ∷ blank)) := by
  unfold BeepAt
  refine Sys.Reach1.single ?_
  show step delta ⟨beep, 1 ∷ 3 ∷ rp 1 j (rp 3 n blank), blank⟩ = _
  rfl

/-- after the beep: `reb` turns the tape into candidate `n + j + 3` -/
theorem after_beep (n j : Nat) :
    Rch (cfgL reb (1 ∷ 3 ∷ rp 1 j (rp 3 n blank)) (0 ∷ blank)) (ZS 2 (n + j + 1)) := by
  gL
  show Rch ⟨reb, rp 1 j (rp 3 n blank), 3 ∷ 1 ∷ 0 ∷ blank⟩ _
  gR
  show Rch (cfgL reb (1 ∷ 1 ∷ rp 1 j (rp 3 n blank)) (0 ∷ blank)) _
  gL
  rw [cons_blank]
  exact rebuild n j 1

end TMK.TwinPrimes4
