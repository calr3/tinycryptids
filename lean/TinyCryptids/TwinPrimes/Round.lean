import TinyCryptids.TwinPrimes.Tac

/-!
# Routines of the design

Tape (`F` = blank; blank left of D and right of R):

    D 0 R

* `D` : `d` cells, the trial divisor `d ≥ 2`, all 1 except a hole at cell `c < d`;
* one 0, the separator;
* `R` : `r` cells, `r = m - d`; during the mod walk a hole moves left through it.

Configurations are stated with the cells left of the head as a stream read leftwards
(nearest cell first). `Dp d c` is D read leftwards from its last cell.
-/

namespace TM.TwinPrimes
open St

local notation "F" => false

/-- D read leftwards from its last cell: `d` cells, the hole at cell `c` -/
def Dp (d c : Nat) : Strm := ones (d - 1 - c) (F ::: ones c blank)

/-- The mod walk with `k` of its `r` steps left: `B2` on R's cell `k - 1` (R has no hole;
the next step makes one there), or on the separator when `k = 0`. -/
def W (d r c : Nat) : Nat → Cfg St
  | 0 => ⟨B2, Dp d c, F ::: ones r blank⟩
  | k + 1 => ⟨B2, ones k (F ::: Dp d c), ones (r - k) blank⟩

/-- the start of the mod walk for `d`: the D hole on D's last cell, `B2` on R's last cell -/
def WS (d r : Nat) : Cfg St := W d r (d - 1) r

/-- the start of candidate `m`: the walk for `d = 2`, `r = m - 2` -/
def CS (m : Nat) : Cfg St := WS 2 (m - 2)

/-- just before the beep: D has `d + 1` cells with the hole on its last cell, then the
separator; R is empty and `G2` reads the blank after it -/
def BeepCfg (d : Nat) : Cfg St := ⟨G2, F ::: F ::: ones d blank, blank⟩

/-! ## the mod walk -/

/-- one step: make the R hole on R's cell `k`, advance the D hole (cyclically), fill the
R hole; `B2` ends on the cell left of it -/
theorem walk_core (d r c k : Nat) (hc : c < d) (hk : k < r) :
    Rch ⟨B2, ones k (F ::: Dp d c), ones (r - k) blank⟩
      (cfgL B2 (ones k (F ::: Dp d ((c + 1) % d))) (true ::: ones (r - k - 1) blank)) := by
  obtain ⟨j, hj⟩ : ∃ j, r - k = j + 1 := ⟨r - k - 1, by omega⟩
  rw [hj, show j + 1 - 1 = j by omega]
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
    gR; sRn e; gR; sRn k; gL; fin
  · -- the hole was on D's last cell: back to cell 0
    obtain rfl : d = c + 1 := by omega
    rw [Nat.mod_self, show c + 1 - 1 - c = 0 by omega, show c + 1 - 1 - 0 = c by omega]
    gL
    show Rch (cfgL W1 (ones (c + 1) blank) _) _
    sLn (c + 1)
    gR; gR; sRn c; gR; sRn k; gL
    rw [tl_blank, cons_blank]; fin

theorem walk_step (d r c k : Nat) (hc : c < d) (hk : k < r) :
    Rch (W d r c (k + 1)) (W d r ((c + 1) % d) k) := by
  obtain ⟨j, rfl⟩ : ∃ j, r = k + j + 1 := ⟨r - k - 1, by omega⟩
  have h := walk_core d (k + j + 1) c k hc (by omega)
  rw [show k + j + 1 - k = j + 1 by omega, show j + 1 - 1 = j by omega] at h
  cases k with
  | zero =>
    show Rch ⟨B2, ones 0 (F ::: Dp d c), ones (0 + j + 1 - 0) blank⟩
      ⟨B2, Dp d ((c + 1) % d), F ::: ones (0 + j + 1) blank⟩
    rw [show 0 + j + 1 - 0 = j + 1 by omega, show 0 + j + 1 = j + 1 by omega]
    exact h
  | succ k =>
    show Rch ⟨B2, ones (k + 1) (F ::: Dp d c), ones (k + 1 + j + 1 - (k + 1)) blank⟩
      ⟨B2, ones k (F ::: Dp d ((c + 1) % d)), ones (k + 1 + j + 1 - k) blank⟩
    rw [show k + 1 + j + 1 - (k + 1) = j + 1 by omega, show k + 1 + j + 1 - k = j + 2 by omega]
    exact h

/-- the whole walk: `k` steps from residue `c` -/
theorem walk (d r : Nat) : ∀ k c, k ≤ r → c < d → Rch (W d r c k) (W d r ((c + k) % d) 0) := by
  intro k
  induction k with
  | zero => intro c _ hc; rw [Nat.add_zero, Nat.mod_eq_of_lt hc]; fin
  | succ k ih =>
    intro c hk hc
    refine Rch.tr (walk_step d r c k hc (by omega)) ?_
    have := ih ((c + 1) % d) (by omega) (Nat.mod_lt _ (by omega))
    rwa [Nat.mod_add_mod, show c + 1 + k = c + (k + 1) by omega] at this

/-! ## the rebuild for the next candidate -/

/-- `C1` inside D (all filled), `b` cells before the separator, `a` cells of D behind the
head: fill the separator, add a cell at the left end, write `D = 10` and the separator:
the start of candidate `m + 1`, where `m = a + b + r` -/
theorem rebuild (a b r : Nat) (hm : 2 ≤ a + b + r) :
    Rch ⟨C1, ones a blank, ones b (F ::: ones r blank)⟩ (CS (a + b + r + 1)) := by
  obtain ⟨n, hn⟩ : ∃ n, a + b + r = n + 2 := ⟨a + b + r - 2, by omega⟩
  sRn b; gL
  rw [ones_add]
  sLn (b + a)
  gR
  rw [ones_cons_true, ← ones_succ, ones_add, show b + a + 1 + r = n + 3 by omega]
  gR; gR; gR
  sRn n
  refine blankR ?_
  gL
  unfold CS WS
  rw [show a + b + r + 1 - 2 = n + 1 by omega]
  show Rch _ ⟨B2, ones n (F ::: Dp 2 1), ones (n + 1 - n) blank⟩
  rw [show n + 1 - n = 1 by omega, ones_cons_true]
  simp only [Dp, tl_blank]
  rw [cons_blank]; fin

/-! ## d passed: d := d + 1, r := r - 1 -/

/-- `H1` in D (hole filled), `b` cells before the separator, `a` behind the head; `r ≥ 2`:
the separator becomes D's last cell (its hole), R's cell 0 the separator, and the walk for
`d + 1` starts -/
theorem shift_more (a b r : Nat) (hr : 2 ≤ r) :
    Rch ⟨H1, ones a blank, ones b (F ::: ones r blank)⟩ (WS (a + b + 1) (r - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 2 := ⟨r - 2, by omega⟩
  sRn b; gR; gR; gR
  sRn j
  refine blankR ?_
  gL
  unfold WS
  rw [show j + 2 - 1 = j + 1 by omega, show a + b + 1 - 1 = a + b by omega]
  show Rch _ ⟨B2, ones j (F ::: Dp (a + b + 1) (a + b)), ones (j + 1 - j) blank⟩
  rw [show j + 1 - j = 1 by omega, ones_cons_true, ones_add]
  simp only [Dp, show a + b + 1 - 1 - (a + b) = 0 by omega, ones_zero, Nat.add_comm b a]
  rw [cons_blank]; fin

/-- the same with `r = 1`: R becomes empty, `G2` reads the blank after it: the beep -/
theorem shift_beep (a b : Nat) :
    Rch ⟨H1, ones a blank, ones b (F ::: ones 1 blank)⟩ (BeepCfg (a + b)) := by
  sRn b; gR; gR
  unfold BeepCfg
  rw [ones_add, Nat.add_comm b a]; fin

/-! ## the check after the walk: D's cells d - 1, d - 2, d - 3 -/

/-- `d ∣ m` or `d ∣ m + 2` (`c = d - 1` or `c = d - 3`): fail, rebuild for `m + 1` -/
theorem check_fail (d r c : Nat) (hd : 2 ≤ d) (h : c + 1 = d ∨ c + 3 = d) :
    Rch (W d r c 0) (CS (d + r + 1)) := by
  unfold W Dp
  rcases h with rfl | rfl
  · rw [show c + 1 - 1 - c = 0 by omega, ones_zero]
    gL; gR
    have := rebuild (c + 1) 0 r (by omega)
    rw [Nat.add_zero] at this; exact this
  · rw [show c + 3 - 1 - c = 2 by omega]
    gL; gL; gL; gR
    have := rebuild (c + 1) 2 r (by omega)
    rw [show c + 1 + 2 = c + 3 by omega] at this; exact this

/-- `c = d - 2` or `c ≤ d - 4`: d passed; `H1` fills the hole's place on its way right -/
theorem check_ok (d r c : Nat) (hd : 2 ≤ d) (hc : c < d) (h : ¬ (c + 1 = d ∨ c + 3 = d)) :
    ∃ a b, a + b = d ∧ Rch (W d r c 0) ⟨H1, ones a blank, ones b (F ::: ones r blank)⟩ := by
  unfold W Dp
  by_cases h2 : c + 2 = d
  · subst h2
    rw [show c + 2 - 1 - c = 1 by omega]
    refine ⟨c + 1, 1, by omega, ?_⟩
    gL; gL; gR; fin
  · obtain ⟨e, he⟩ : ∃ e, d - 1 - c = e + 3 := ⟨d - 4 - c, by omega⟩
    rw [he]
    refine ⟨c + 1, e + 3, by omega, ?_⟩
    gL; gL; gL; gL
    sLn e
    gR; rw [← ones_add e 3]; fin

/-! ## the beep and the seed -/

theorem beepCfg_q (d : Nat) : (BeepCfg d).q = G2 := rfl
theorem beepCfg_read (d : Nat) : (BeepCfg d).R 0 = false := rfl

/-- the beep transition (`delta`, not `deltaNB`): `G2` reads 0, writes 0 and moves left onto
the separator; the walk with `r = 0` has ended -/
theorem beep_step (d : Nat) : Reach delta (BeepCfg d) (W (d + 1) 0 d 0) := by
  have h := stepL (δ := delta) (q := G2) (q' := B2) (w := false)
    (L := F ::: F ::: ones d blank) (R := blank) rfl
  unfold BeepCfg W Dp
  simp only [tl_cons, tl_blank, cons_zero, show d + 1 - 1 - d = 0 by omega, ones_zero] at h ⊢
  rw [cons_blank] at h
  exact h

/-- the seed: `Z2` on a blank tape writes a 1 and runs the FAIL path once (a pseudo-round),
which builds the start of candidate 3 -/
theorem seed : Rch start (CS 3) := by
  unfold start
  refine blankR ?_
  gL
  show Rch (cfgL B2 (F ::: blank) (true ::: blank)) _
  gL
  show Rch (cfgL X1 (F ::: blank) (F ::: true ::: blank)) _
  gR
  exact rebuild 1 0 1 (by omega)

end TM.TwinPrimes
