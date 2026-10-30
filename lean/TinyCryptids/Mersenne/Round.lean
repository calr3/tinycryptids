import TinyCryptids.Mersenne.Tac

/-!
# Routines of the design

Tape (`F` = blank; blank left of D and right of R):

    D 0 R

* `D` : `d` cells, the trial divisor `d ≥ 3`, all 1 except a hole at cell `c < d`; before a
  walk the hole is on cell 0, the blank cell left of D's `d - 1` ones;
* one 0, the separator;
* `R` : `r` cells, `d + r = m - 1`; during the mod walk a hole moves right through it.

Configurations are stated with the cells left of the head as a stream read leftwards
(nearest cell first). `Dp d c` is D read leftwards from its last cell.
-/

namespace TM.Mersenne
open St

local notation "F" => false

/-- D read leftwards from its last cell: `d` cells, the hole at cell `c` -/
def Dp (d c : Nat) : Strm := ones (d - 1 - c) (F ::: ones c blank)

/-- The mod walk with `k` of its `r` steps done: `B2` on R's cell `k` (R has no hole; the
next step makes one there), or on the blank after R when `k = r`. -/
def W (d r c k : Nat) : Cfg St := ⟨B2, ones k (F ::: Dp d c), ones (r - k) blank⟩

/-- the start of the mod walk for `d`: the D hole on cell 0, `B2` on R's cell 0 -/
def WS (d r : Nat) : Cfg St := W d r 0 0

/-- the start of candidate `m` (odd, `m ≥ 5`): the walk for `d = 3`, `r = m - 4` -/
def CS (m : Nat) : Cfg St := WS 3 (m - 4)

/-- the beep: one block of `n` ones (`n = m - 1`), `G0` on the blank after it -/
def BeepCfg (n : Nat) : Cfg St := ⟨G0, ones n blank, blank⟩

/-- `q` reading 0 writes 1 and moves right, staying in `q` -/
theorem fillR {q : St} (h : deltaNB q false = some (true, Dir.R, q)) (n : Nat) (L R : Strm) :
    Rch ⟨q, L, zeros n R⟩ ⟨q, ones n L, R⟩ := by
  induction n generalizing L with
  | zero => fin
  | succ n ih =>
    refine Rch.tr (sR (R := zeros n R) h) ?_
    have := ih (true ::: L); rw [← ones_succ'] at this; exact this

theorem eraseL' {q : St} (h : deltaNB q true = some (false, Dir.L, q)) (n : Nat) (s R : Strm) :
    Rch (cfgL q (ones n s) R) (cfgL q s (zeros n R)) := eraseL h n s R

/-! ## the mod walk -/

/-- one step: make the R hole on R's cell `k`, advance the D hole (cyclically), fill the
R hole; `B2` ends on R's cell `k + 1` -/
theorem walk_step (d r c k : Nat) (hc : c < d) (hk : k < r) :
    Rch (W d r c k) (W d r ((c + 1) % d) (k + 1)) := by
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
  · -- no wrap: the hole moves one cell right
    obtain ⟨e, he⟩ : ∃ e, d - 1 - c = e + 1 := ⟨d - 2 - c, by omega⟩
    rw [he, Nat.mod_eq_of_lt hw, show d - 1 - (c + 1) = e by omega]
    gR; sRn e; gR; sRn k; gR; fin
  · -- the hole was on D's last cell: back to cell 0
    obtain rfl : d = c + 1 := by omega
    rw [Nat.mod_self, show c + 1 - 1 - c = 0 by omega, show c + 1 - 1 - 0 = c by omega]
    gL
    show Rch (cfgL W1 (ones (c + 1) blank) _) _
    sLn (c + 1)
    gR; gR; sRn c; gR; sRn k; gR
    rw [tl_blank, cons_blank]; fin

/-- the whole walk: from `k` steps done to `r` -/
theorem walk (d r : Nat) : ∀ i c, i ≤ r → c < d → Rch (W d r c (r - i)) (W d r ((c + i) % d) r) := by
  intro i
  induction i with
  | zero => intro c _ hc; rw [Nat.add_zero, Nat.mod_eq_of_lt hc, Nat.sub_zero]; fin
  | succ i ih =>
    intro c hi hc
    refine Rch.tr (walk_step d r c (r - (i + 1)) hc (by omega)) ?_
    have := ih ((c + 1) % d) (by omega) (Nat.mod_lt _ (by omega))
    rw [Nat.mod_add_mod, show c + 1 + i = c + (i + 1) by omega] at this
    rw [show r - (i + 1) + 1 = r - i by omega]
    exact this

theorem walk_all (d r : Nat) (hd : 1 ≤ d) : Rch (WS d r) (W d r (r % d) r) := by
  have := walk d r r 0 (Nat.le_refl _) (by omega)
  rwa [Nat.sub_self, Nat.zero_add] at this

/-! ## the rebuild for the next candidate -/

/-- `C4` in a block of `a + b` ones (`b ≥ 1` of them from the head on): write `1 1` at
the left end and the separator after them: the start of candidate `a + b + 3` -/
theorem rebuild (a b : Nat) (hb : 1 ≤ b) (h4 : 2 ≤ a + b) :
    Rch ⟨C4, ones a blank, ones b blank⟩ (CS (a + b + 3)) := by
  obtain ⟨j, rfl⟩ : ∃ j, b = j + 1 := ⟨b - 1, by omega⟩
  show Rch (cfgL C4 (ones (a + 1) blank) (ones j blank)) _
  sLn (a + 1)
  refine Rch.tr (sL (s := blank) (by rfl)) ?_
  gR; gR
  obtain ⟨n, hn⟩ : ∃ n, a + j = n + 1 := ⟨a + j - 1, by omega⟩
  rw [ones_add, show a + 1 + j = n + 2 by omega]
  gR
  unfold CS WS W Dp
  rw [show a + (j + 1) + 3 - 4 = n + 1 by omega]
  simp only [ones_zero, Nat.sub_zero, show 3 - 1 - 0 = 2 by omega]
  rw [cons_blank]; fin

/-! ## the end of the walk, the check, and d := d + 2 -/

/-- the walk is done (`B2` on the blank after R, `r = j + 1`): erase R's last cell, scan
back to the separator and fill it; `X1` reads D's last cell -/
theorem walk_end (d j c : Nat) :
    Rch (W d (j + 1) c (j + 1))
      (cfgL X1 (Dp d c) (true ::: ones j blank)) := by
  unfold W
  rw [Nat.sub_self, ones_zero]
  refine blankR ?_
  gL
  show Rch (cfgL E (ones (j + 1) (F ::: Dp d c)) (F ::: blank)) _
  gL
  sLn j
  gL
  rw [cons_blank, cons_blank]; fin

/-- `d ∣ m` or `d ∣ m + 1` (`c = d - 1` or `c = d - 2`): fail, rebuild for `m + 2` -/
theorem check_fail (d j c : Nat) (hd : 3 ≤ d) (h : c + 1 = d ∨ c + 2 = d) :
    Rch (cfgL X1 (Dp d c) (true ::: ones j blank)) (CS (d + j + 1 + 3)) := by
  unfold Dp
  rcases h with rfl | rfl
  · rw [show c + 1 - 1 - c = 0 by omega, ones_zero]
    gR
    have := rebuild (c + 1) (j + 1) (by omega) (by omega)
    rw [show c + 1 + (j + 1) = c + 1 + j + 1 by omega] at this; exact this
  · rw [show c + 2 - 1 - c = 1 by omega]
    gL; gR; gR
    have := rebuild (c + 2) (j + 1) (by omega) (by omega)
    rw [show c + 2 + (j + 1) = c + 2 + j + 1 by omega] at this; exact this

/-- `X1` and `X2`, alternating, erase `2 i` cells leftwards -/
theorem alt (i : Nat) (s R : Strm) : Rch (cfgL X1 (ones (2 * i) s) R) (cfgL X1 s (zeros (2 * i) R)) := by
  induction i generalizing R with
  | zero => fin
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    gL; gL
    refine Rch.tr (ih _) ?_
    rw [zeros_succ', zeros_succ']; fin

/-- d passed: `C4` reads an erased cell (`k ≥ 2` of them, then the filled separator); it
writes 1 and steps back, `H1` steps on, `G0` erases the cell again, `B2` reads the next
erased cell and steps back, `E` writes 1 there; `H1` refills the rest -/
theorem ok_dance (a k j : Nat) (ha : 1 ≤ a) (hk : 2 ≤ k) :
    Rch ⟨C4, ones a blank, zeros k (true ::: ones j blank)⟩
      ⟨G0, ones (a + k + 1) blank, ones j blank⟩ := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  show Rch (cfgL C4 (F ::: ones (a' + 1) blank) (F ::: zeros k' (true ::: ones j blank))) _
  gL; gR; gR
  show Rch (cfgL B2 (F ::: F ::: true ::: ones a' blank) (zeros k' (true ::: ones j blank))) _
  gL; gR
  show Rch ⟨H1, true ::: true ::: ones a' blank, zeros (k' + 1) (true ::: ones j blank)⟩ _
  refine Rch.tr (fillR (by rfl) (k' + 1) _ _) ?_
  gR
  rw [← ones_succ a' blank, ← ones_succ (a' + 1) blank, ones_add, ← ones_succ,
    show k' + 1 + (a' + 1 + 1) + 1 = a' + 1 + (k' + 2) + 1 by omega]; fin

/-- `c ≤ d - 3`: d passed; the erased cells right of the hole are refilled, `G0` reads R's
cell 0 after a block of `d + 1` ones -/
theorem check_ok (d j c : Nat) (hc : c + 3 ≤ d) :
    Rch (cfgL X1 (Dp d c) (true ::: ones j blank)) ⟨G0, ones (d + 1) blank, ones j blank⟩ := by
  unfold Dp
  rcases Nat.mod_two_eq_zero_or_one (d - 1 - c) with he | ho
  · -- an even number of cells between the hole and the separator: X1 finds the hole
    obtain ⟨i, hi⟩ : ∃ i, d - 1 - c = 2 * i := ⟨(d - 1 - c) / 2, by omega⟩
    rw [hi]
    refine Rch.tr (alt i _ _) ?_
    gR
    have := ok_dance (c + 1) (2 * i) j (by omega) (by omega)
    rw [show c + 1 + 2 * i + 1 = d + 1 by omega] at this; exact this
  · -- odd: X2 finds the hole, X1 refills the cell right of it
    obtain ⟨i, hi⟩ : ∃ i, d - 1 - c = 2 * i + 1 := ⟨(d - 1 - c) / 2, by omega⟩
    rw [hi, ← ones_add]
    refine Rch.tr (alt i _ _) ?_
    gL; gR; gR
    have := ok_dance (c + 2) (2 * i) j (by omega) (by omega)
    rw [show c + 2 + 2 * i + 1 = d + 1 by omega] at this; exact this

/-- R has `j + 1` more cells: `G0` writes the new separator, the walk for `d + 2` starts -/
theorem shift (d j : Nat) (hd : 1 ≤ d) :
    Rch ⟨G0, ones (d + 1) blank, ones (j + 1) blank⟩ (WS (d + 2) j) := by
  gR
  unfold WS W Dp
  simp only [ones_zero, Nat.sub_zero, show d + 2 - 1 - 0 = d + 1 by omega]
  rw [cons_blank]; fin

/-! ## the beep and the seed -/

theorem beepCfg_q (n : Nat) : (BeepCfg n).q = G0 := rfl
theorem beepCfg_read (n : Nat) : (BeepCfg n).R 0 = false := rfl

/-- the beep transition (`delta`, not `deltaNB`): `G0` reads 0, writes 0 and moves left
into the block; the rebuild follows -/
theorem beep_step (n : Nat) : Reach delta (BeepCfg (n + 1)) ⟨C4, ones n blank, ones 1 blank⟩ := by
  have h := stepL (δ := delta) (q := G0) (q' := C4) (w := false)
    (L := ones (n + 1) blank) (R := blank) rfl
  unfold BeepCfg
  simp only [tl_blank] at h
  rw [cons_blank] at h
  exact h

/-- the seed: `C4` on a blank tape writes `1 1`, and `G0` reads the blank after them: the
beep for `m = 3` -/
theorem seed : Rch start (BeepCfg 2) := by
  unfold start BeepCfg
  refine blankR ?_
  show Rch (cfgL C4 (F ::: blank) blank) _
  gL; gR; gR; fin

end TM.Mersenne
