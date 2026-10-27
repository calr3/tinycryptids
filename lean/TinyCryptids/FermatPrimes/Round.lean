import TinyCryptids.FermatPrimes.Tac

/-!
# Routines of the design

Tape (`F` = blank; blank left of D):

    D 0 R 0 … 0 K

* `D` : `d` cells, the trial divisor `d ≥ 3`, all 1 except a hole at cell `c < d`; before a
  walk the hole is on cell 0, the blank cell left of D's `d - 1` ones;
* one 0, the separator;
* `R` : `r` cells, `d + r = m - 1`; during the mod walk a hole moves right through it;
* then `F ::: Y`: at least one blank cell, and the counter K further right
  (`Y = zeros g (ones j blank)` in `Main.lean`).

Configurations are stated with the cells left of the head as a stream read leftwards
(nearest cell first). `Dp d c` is D read leftwards from its last cell.
-/

namespace TM.FermatPrimes
open St

local notation "F" => false

/-- D read leftwards from its last cell: `d` cells, the hole at cell `c` -/
def Dp (d c : Nat) : Strm := ones (d - 1 - c) (F ::: ones c blank)

/-- The mod walk with `k` of its `r` steps done: `B2` on R's cell `k` (R has no hole; the
next step makes one there), or on the blank after R when `k = r`. -/
def W (d r c k : Nat) (Y : Strm) : Cfg St := ⟨B2, ones k (F ::: Dp d c), ones (r - k) (F ::: Y)⟩

/-- the start of the mod walk for `d`: the D hole on cell 0, `B2` on R's cell 0 -/
def WS (d r : Nat) (Y : Strm) : Cfg St := W d r 0 0 Y

/-- `q` reading 0 writes 1 and moves right, staying in `q` -/
theorem fillR {q : St} (h : delta q false = some (true, Dir.R, q)) (n : Nat) (L R : Strm) :
    Rch ⟨q, L, zeros n R⟩ ⟨q, ones n L, R⟩ := by
  induction n generalizing L with
  | zero => fin
  | succ n ih =>
    refine Rch.tr (sR (R := zeros n R) h) ?_
    have := ih (true ::: L); rw [← ones_succ'] at this; exact this

/-! ## the mod walk -/

theorem walk_step (d r c k : Nat) (Y : Strm) (hc : c < d) (hk : k < r) :
    Rch (W d r c k Y) (W d r ((c + 1) % d) (k + 1) Y) := by
  obtain ⟨j, hj⟩ : ∃ j, r - k = j + 1 := ⟨r - k - 1, by omega⟩
  unfold W
  rw [hj, show r - (k + 1) = j by omega]
  unfold Dp
  gL
  sLn k
  gL
  sLn (d - 1 - c)
  gR
  by_cases hw : c + 1 < d
  · obtain ⟨e, he⟩ : ∃ e, d - 1 - c = e + 1 := ⟨d - 2 - c, by omega⟩
    rw [he, Nat.mod_eq_of_lt hw, show d - 1 - (c + 1) = e by omega]
    gR; sRn e; gR; sRn k; gR; fin
  · obtain rfl : d = c + 1 := by omega
    rw [Nat.mod_self, show c + 1 - 1 - c = 0 by omega, show c + 1 - 1 - 0 = c by omega]
    gL
    show Rch (cfgL W1 (ones (c + 1) blank) _) _
    sLn (c + 1)
    gR; gR; sRn c; gR; sRn k; gR
    rw [tl_blank, cons_blank]; fin

theorem walk (d r : Nat) (Y : Strm) :
    ∀ i c, i ≤ r → c < d → Rch (W d r c (r - i) Y) (W d r ((c + i) % d) r Y) := by
  intro i
  induction i with
  | zero => intro c _ hc; rw [Nat.add_zero, Nat.mod_eq_of_lt hc, Nat.sub_zero]; fin
  | succ i ih =>
    intro c hi hc
    refine Rch.tr (walk_step d r c (r - (i + 1)) Y hc (by omega)) ?_
    have := ih ((c + 1) % d) (by omega) (Nat.mod_lt _ (by omega))
    rw [Nat.mod_add_mod, show c + 1 + i = c + (i + 1) by omega] at this
    rw [show r - (i + 1) + 1 = r - i by omega]
    exact this

theorem walk_all (d r : Nat) (Y : Strm) (hd : 1 ≤ d) : Rch (WS d r Y) (W d r (r % d) r Y) := by
  have := walk d r Y r 0 (Nat.le_refl _) (by omega)
  rwa [Nat.sub_self, Nat.zero_add] at this

/-! ## the rebuild for the next candidate -/

/-- `C4` in a block of `a + b` ones (`b ≥ 1` of them from the head on), then `F ::: Y`:
write `1 1` at the left end and the separator after them: the walk for `d = 3`,
`r = a + b - 1` -/
theorem rebuild (a b : Nat) (Y : Strm) (hb : 1 ≤ b) (h4 : 2 ≤ a + b) :
    Rch ⟨C4, ones a blank, ones b (F ::: Y)⟩ (WS 3 (a + b - 1) Y) := by
  obtain ⟨j, rfl⟩ : ∃ j, b = j + 1 := ⟨b - 1, by omega⟩
  show Rch (cfgL C4 (ones (a + 1) blank) (ones j (F ::: Y))) _
  sLn (a + 1)
  refine Rch.tr (sL (s := blank) (by rfl)) ?_
  gR; gR
  obtain ⟨n, hn⟩ : ∃ n, a + j = n + 1 := ⟨a + j - 1, by omega⟩
  rw [ones_add, show a + 1 + j = n + 2 by omega]
  gR
  unfold WS W Dp
  rw [show a + (j + 1) - 1 = n + 1 - 0 by omega]
  simp only [ones_zero, show 3 - 1 - 0 = 2 by omega]
  rw [cons_blank]; fin

/-! ## the end of the walk and the check -/

/-- the walk is done (`B2` on the blank after R, `r = j + 1`): erase R's last cell, scan
back to the separator and fill it; `X1` reads D's last cell. The gap grows by one. -/
theorem walk_end (d j c : Nat) (Y : Strm) :
    Rch (W d (j + 1) c (j + 1) Y) (cfgL X1 (Dp d c) (true ::: ones j (F ::: F ::: Y))) := by
  unfold W
  rw [Nat.sub_self, ones_zero]
  gL
  show Rch (cfgL E (ones (j + 1) (F ::: Dp d c)) (F ::: Y)) _
  gL
  sLn j
  gL; fin

/-- `d ∣ m` (`c = d - 1`): `X1` fills the hole, `C4` runs left from the separator -/
theorem check_last (c j : Nat) (Z : Strm) :
    Rch (cfgL X1 (Dp (c + 1) c) (true ::: ones j Z)) ⟨C4, ones (c + 1) blank, ones (j + 1) Z⟩ := by
  unfold Dp
  rw [show c + 1 - 1 - c = 0 by omega, ones_zero]
  gR; fin

/-- `d ∣ m - 1` (`c = 0`, `d ≥ 2`): `X1`, `X` erase to the hole, `Q` reads the blank left
of it; `HF` refills and turns back on the separator -/
theorem check_first (d j : Nat) (Z : Strm) (hd : 2 ≤ d) :
    Rch (cfgL X1 (Dp d 0) (true ::: ones j Z)) ⟨C4, ones (d - 1) blank, ones (j + 2) Z⟩ := by
  unfold Dp
  obtain ⟨e, he⟩ : ∃ e, d - 1 - 0 = e + 1 := ⟨d - 2, by omega⟩
  rw [he]
  gL
  refine Rch.tr (eraseL (δ := delta) (by rfl) e _ _) ?_
  gL
  show Rch (cfgL Q blank _) _
  refine Rch.tr (sR (L := blank) (by rfl)) ?_
  rw [zeros_cons_false]
  show Rch ⟨HF, F ::: blank, zeros (e + 2) (true ::: ones j Z)⟩ _
  · refine Rch.tr (fillR (by rfl) (e + 2) _ _) ?_
    refine Rch.tr (sL (s := ones (e + 2) (F ::: blank)) (by rfl)) ?_
    show Rch ⟨C4, ones (e + 1) (F ::: blank), true ::: true ::: ones j Z⟩ _
    rw [cons_blank, show d - 1 = e + 1 by omega]; fin

/-- `1 ≤ c ≤ d - 2`: d passed; `Q` reads a 1, `H1` refills the hole and the erased cells,
`G0` reads R's cell 0 after a block of `d + 1` ones -/
theorem check_ok (d j c : Nat) (Z : Strm) (h1 : 1 ≤ c) (h2 : c + 2 ≤ d) :
    Rch (cfgL X1 (Dp d c) (true ::: ones j Z)) ⟨G0, ones (d + 1) blank, ones j Z⟩ := by
  unfold Dp
  obtain ⟨e, he⟩ : ∃ e, d - 1 - c = e + 1 := ⟨d - 2 - c, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  rw [he]
  gL
  refine Rch.tr (eraseL (δ := delta) (by rfl) e _ _) ?_
  gL
  show Rch (cfgL Q (ones (c' + 1) blank) _) _
  gR
  rw [zeros_cons_false]
  show Rch ⟨H1, ones (c' + 1) blank, zeros (e + 2) (true ::: ones j Z)⟩ _
  · refine Rch.tr (fillR (by rfl) (e + 2) _ _) ?_
    gR
    rw [← ones_succ, ones_add, show e + 2 + 1 + (c' + 1) = d + 1 by omega]; fin

/-- R has `j + 1` more cells: `G0` writes the new separator, the walk for `d + 2` starts -/
theorem shift (d j : Nat) (Y : Strm) (hd : 1 ≤ d) :
    Rch ⟨G0, ones (d + 1) blank, ones (j + 1) (F ::: Y)⟩ (WS (d + 2) j Y) := by
  gR
  unfold WS W Dp
  simp only [ones_zero, Nat.sub_zero, show d + 2 - 1 - 0 = d + 1 by omega]
  rw [cons_blank]; fin

/-! ## a pass: the counter -/

/-- the pass: `G0` on the blank after a block of `n` ones, the counter (`j` cells) after `g`
more blanks -/
def PassCfg (n g j : Nat) : Cfg St := ⟨G0, ones n blank, F ::: zeros g (ones j blank)⟩

/-- `P1` runs to the counter and erases a cell; `P2` reads another, `P3` returns to the block
and `C4` runs left in it -/
theorem pass_more (d g j : Nat) (hd : 1 ≤ d) :
    Rch (PassCfg (d + 1) g (j + 2)) ⟨C4, ones (d - 1) blank, ones 2 (zeros (g + 2) (ones (j + 1) blank))⟩ := by
  unfold PassCfg
  gR
  refine Rch.tr (scanR0 (δ := delta) (by rfl) g _ _) ?_
  gR
  show Rch (cfgL P2 (true ::: F ::: zeros g (F ::: ones (d + 1) blank)) (ones j blank)) _
  refine Rch.tr (sL (s := F ::: zeros g (F ::: ones (d + 1) blank)) (by rfl)) ?_
  rw [zeros_cons_false]
  show Rch (cfgL P3 (zeros (g + 2) (ones (d + 1) blank)) (true ::: ones j blank)) _
  refine Rch.tr (scanL0 (δ := delta) (by rfl) (g + 2) _ _) ?_
  refine Rch.tr (sL (s := ones d blank) (by rfl)) ?_
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  show Rch ⟨C4, ones e blank, true ::: true ::: zeros (g + 2) (true ::: ones j blank)⟩ _
  rw [show e + 1 - 1 = e by omega]; fin

/-- the last cell of the counter: HALT -/
theorem pass_halt (n g : Nat) : HaltAt (PassCfg n g 1) := by
  unfold PassCfg
  refine HaltAt.back (Rch.tr (sR (by rfl)) (Rch.tr (scanR0 (δ := delta) (by rfl) g _ _) (sR (by rfl)))) ?_
  exact ⟨_, _, stepL (δ := delta) (by rfl)⟩

/-! ## the seed -/

/-- `S1` … `S6` write the counter, `S7` leaves a blank, `C4` and `H1` write `1 1`, and `G0`
reads the blank: the pass for `m = 3` -/
theorem seed : Rch start (PassCfg 2 0 6) := by
  unfold start PassCfg
  refine blankR ?_
  show Rch (cfgL S1 (F ::: blank) blank) _
  gL; gL; gL; gL; gL; gL; gL; gL
  show Rch (cfgL H1 blank (true ::: F ::: ones 6 blank)) _
  gR; gR; fin

end TM.FermatPrimes
