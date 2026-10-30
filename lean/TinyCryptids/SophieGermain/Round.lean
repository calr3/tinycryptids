import TinyCryptids.SophieGermain.Walk

/-!
# The round end: erase R's last cell, check, `d := d + 2`, rebuild

After the walk for `d` (D's hole on cell `c`, R of `j + 1` cells) `E` erases R's last cell,
`V` scans back to the separator and `X` to the hole, which it fills. `K1`, `K2`, `K3` read
the cells after the hole:

* the separator on `c + 1` (`c = d - 1`): OK;
* on `c + 2` or `c + 3`: FAIL, the separator is filled, and `V` scans to the left end;
* further on: `H` finds the separator: OK.

On OK, `G0` (after a block of `d + 1` ones) writes the new separator on R's cell 0, or
beeps if R is empty. The rebuild is the same check run on the blank left of the block: `X`
and `K1` write `1 1` there and `G0` writes the separator after them.
-/

namespace TM.SophieGermain
open St

local notation "F" => false

/-- the start of candidate `n` (odd, `n ≥ 5`): the walk for `d = 3`, `r = n - 4` -/
def CS (n : Nat) : Cfg St := WS 3 (n - 4)

/-- the beep: one block of `k` ones (`k = n - 1`), `G0` on the blank after it -/
def BeepCfg (k : Nat) : Cfg St := ⟨G0, ones k blank, blank⟩

/-- after the walk: `K1` right of the filled hole -/
def KC (d c j : Nat) : Cfg St := ⟨K1, ones (c + 1) blank, ones (d - 1 - c) (F ::: ones j blank)⟩

/-- the walk is done (`B2` on the blank after R, `r = j + 1`): erase R's last cell, scan
back to the separator and on to the hole, fill it -/
theorem walk_end (d j c : Nat) : Rch (W d (j + 1) c (j + 1)) (KC d c j) := by
  unfold W KC Dp
  rw [Nat.sub_self, ones_zero]
  refine blankR ?_
  gL
  show Rch (cfgL E (ones (j + 1) (F ::: ones (d - 1 - c) (F ::: ones c blank))) (F ::: blank)) _
  gR; gL; gL
  sLn j
  gL
  sLn (d - 1 - c)
  gR
  rw [cons_blank, cons_blank]; fin

/-- `V` reading a block of `a + b` ones (`a ≥ 1` of them left of the head and under it):
`X` and `K1` write `1 1` at its left end, `G0` the separator after them: candidate
`a + b + 3` -/
theorem rebuild (a b : Nat) (h2 : 2 ≤ a + b) :
    Rch (cfgL V (ones a blank) (ones b blank)) (CS (a + b + 3)) := by
  sLn a
  rw [ones_add]
  refine Rch.tr (sL (s := blank) (by rfl)) ?_
  refine Rch.tr (sR (by rfl)) ?_
  gR
  obtain ⟨n, hn⟩ : ∃ n, a + b = n + 1 := ⟨a + b - 1, by omega⟩
  rw [hn]
  gR
  unfold CS WS W Dp
  rw [show n + 1 + 3 - 4 = n by omega]
  simp only [ones_zero, Nat.sub_zero, show 3 - 1 - 0 = 2 by omega]
  rw [cons_blank]; fin

/-- the hole was on `d - 1`: OK, `G0` reads R's cell 0 after a block of `d + 1` ones -/
theorem check_ok1 (d j : Nat) (hd : 1 ≤ d) :
    Rch (KC d (d - 1) j) ⟨G0, ones (d + 1) blank, ones j blank⟩ := by
  unfold KC
  rw [Nat.sub_self, ones_zero]
  gR
  rw [show d - 1 + 1 = d by omega]; fin

/-- the hole on `c ≤ d - 4`: OK -/
theorem check_ok (d j c : Nat) (hc : c + 4 ≤ d) :
    Rch (KC d c j) ⟨G0, ones (d + 1) blank, ones j blank⟩ := by
  unfold KC
  obtain ⟨e, he⟩ : ∃ e, d - 1 - c = e + 3 := ⟨d - 4 - c, by omega⟩
  rw [he]
  gR; gR; gR; sRn e; gR
  rw [← ones_succ, ← ones_succ, ← ones_succ, ← ones_succ, ones_add,
    show e + 1 + (c + 1 + 1 + 1 + 1) = d + 1 by omega]
  fin

/-- the hole on `d - 2` (`d ∣ n`, R not empty) or `d - 3` (`d ∣ 2 n + 1`): FAIL, rebuild for
`n + 2` (`n = d + j + 2`) -/
theorem check_fail (d j c : Nat) (hd : 3 ≤ d) (h : (c + 2 = d ∧ 1 ≤ j) ∨ c + 3 = d) :
    Rch (KC d c j) (CS (d + j + 1 + 3)) := by
  unfold KC
  rcases h with ⟨rfl, hj⟩ | rfl
  · rw [show c + 2 - 1 - c = 1 by omega]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    gR; gR
    have := rebuild (c + 4) j' (by omega)
    rw [show c + 4 + j' + 3 = c + 2 + (j' + 1) + 1 + 3 by omega] at this
    exact this
  · rw [show c + 3 - 1 - c = 2 by omega]
    gR; gR; gL
    have := rebuild (c + 3) (j + 1) (by omega)
    rw [show c + 3 + (j + 1) + 3 = c + 3 + j + 1 + 3 by omega] at this
    exact this

/-- R has `j + 1` more cells: `G0` writes the new separator, the walk for `d + 2` starts -/
theorem shift (d j : Nat) (hd : 1 ≤ d) :
    Rch ⟨G0, ones (d + 1) blank, ones (j + 1) blank⟩ (WS (d + 2) j) := by
  gR
  unfold WS W Dp
  simp only [ones_zero, Nat.sub_zero, show d + 2 - 1 - 0 = d + 1 by omega]
  rw [cons_blank]; fin

/-! ## the beep and the seed -/

theorem beepCfg_q (k : Nat) : (BeepCfg k).q = G0 := rfl
theorem beepCfg_read (k : Nat) : (BeepCfg k).R 0 = false := rfl

/-- the beep transition (`delta`, not `deltaNB`): `G0` reads 0, writes 0 and moves left
into the block; `V` follows -/
theorem beep_step (k : Nat) :
    Reach delta (BeepCfg (k + 1)) (cfgL V (ones (k + 1) blank) blank) := by
  have h := stepL (δ := delta) (q := G0) (q' := V) (w := false)
    (L := ones (k + 1) blank) (R := blank) rfl
  unfold BeepCfg
  simp only [tl_blank] at h
  rw [cons_blank] at h
  exact h

/-- the seed: `B2` on a blank tape; `E`, `V` pass, `X` and `K1` write `1 1`, and `G0` reads
the blank after them: the beep for `n = 3` -/
theorem seed : Rch start (BeepCfg 2) := by
  unfold start BeepCfg
  refine blankR ?_
  show Rch (cfgL B2 (F ::: blank) blank) _
  refine Rch.tr (sL (s := blank) (by rfl)) ?_
  refine Rch.tr (sL (s := blank) (by rfl)) ?_
  refine Rch.tr (sL (s := blank) (by rfl)) ?_
  gR; gR
  rw [cons_blank, cons_blank]; fin

end TM.SophieGermain
