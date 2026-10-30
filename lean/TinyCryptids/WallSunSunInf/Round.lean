import TinyCryptids.WallSunSunInf.Odo

/-!
# The rounds (as `../WallSunSun2/Round.lean`, for `deltaNB`; the check beeps)

`RS m`: the start of round `m`, `B 00 E 00 D` with `B = 1^(m+1)`, `E = 1^(m+2)` and
`D = 1 0 1^m` (its hole on cell 1), the head on D's cell 0 in `e1`.
* `init` (as in `../WallSunSun/Round.lean`): E's hole on cell `m`, the odometer's first string.
* `check`: after the odometer, halt iff the counter is back at `m - 1` mod `m²`; else
  `to_next`: E grows by a cell, B by one (`next_hole`), D's hole is filled, D gets one more
  cell and its hole goes to cell 1 (`rebuild`, `fill`): `RS (m + 1)`.
-/

namespace TM.WallSunSunInf
open St TinyCryptids TM.Zeckendorf

local notation "F" => false

/-- B and E between rounds, from E's right end -/
def XE (m : Nat) : Strm := ones (m + 2) (F ::: F ::: ones (m + 1) blank)

/-- the start of round `m` -/
def RS (m : Nat) : Cfg St := cfgL e1 (true ::: F ::: F ::: XE m) (F ::: ones m blank)

/-- `e1` on the separator left of D (D has `d + 2` cells, its hole on cell 1) -/
def PX (X : Strm) (d : Nat) : Cfg St := cfgL e1 (F ::: F ::: X) (true ::: F ::: ones d blank)

theorem RS_PX (m : Nat) : Rch (RS m) (PX (XE m) m) := by unfold RS PX; gL; fin

theorem PPF : ParserR deltaNB PF1 PF2 := by constructor <;> rfl

theorem ones_eq {a b : Nat} (s : Strm) (h : a = b) : ones a s = ones b s := h ▸ rfl

theorem blankL {q : St} {R : Strm} {X : Cfg St} (h : Rch (cfgL q (F ::: blank) R) X) :
    Rch (cfgL q blank R) X := by rw [cons_blank] at h; exact h

theorem ones_cons_blank (s : Nat) : ones s (true ::: blank) = ones (s + 1) blank := (ones_succ' s blank).symm

/-! ## the end of a round -/

/-- from D's hole (cell `h + 1`, `j + 1` cells right of it): fill it, one more cell on the
right, the hole on cell 1 -/
theorem fill (X : Strm) (h j : Nat) :
    Rch ⟨f1, ones (h + 1) (F ::: F ::: X), F ::: ones (j + 1) blank⟩
      (cfgL e1 (true ::: F ::: F ::: X) (F ::: ones (h + j + 2) blank)) := by
  gR; sRn (j + 1); refine blankR ?_; gL
  show Rch (cfgL f3 (true ::: ones j (true ::: ones (h + 1) (F ::: F ::: X))) (true ::: blank)) _
  rw [← ones_succ, show ones (j + 1) (true ::: ones (h + 1) (F ::: F ::: X)) = ones (h + j + 3) (F ::: F ::: X) by
    simp only [← ones_succ, ← ones_succ', ones_add]
    exact ones_eq _ (by omega)]
  sLn (h + j + 3); gR
  rw [show h + j + 3 = h + j + 2 + 1 by omega]
  gR; gL
  rw [ones_cons_blank]
  fin

/-- PF from B's second cell to D's hole, then `fill` -/
theorem rebuild (c e h j : Nat) :
    Rch ⟨PF1, true ::: blank, ones (c + 1) (F ::: F ::: ones (e + 1) (F ::: F :::
        ones (h + 1) (F ::: ones (j + 1) blank)))⟩
      (cfgL e1 (true ::: F ::: F ::: ones (e + 1) (F ::: F ::: ones (c + 2) blank)) (F ::: ones (h + j + 2) blank)) := by
  rw [show ones (c + 2) blank = ones (c + 1) (true ::: blank) from (ones_cons_blank (c + 1)).symm]
  have cr := PPF.cross (clean_blk (c + 1) e) (true ::: blank)
    (F ::: F ::: ones (h + 1) (F ::: ones (j + 1) blank))
  rw [app_blk, app_blk_rev] at cr
  refine Rch.tr cr ?_
  have fd := PPF.find2 0 h (ones (e + 1) (F ::: F ::: ones (c + 1) (true ::: blank)))
    (ones j blank)
  simp only [ones_zero] at fd
  refine Rch.tr fd ?_
  gL
  exact fill (ones (e + 1) (F ::: F ::: ones (c + 1) (true ::: blank))) h j

/-- E with a hole (`a` cells right of it, `b + 1` left), B with `c + 1` cells -/
theorem next_hole (a b c : Nat) (R : Strm) :
    Rch (cfgL g1 (ones a (F ::: ones (b + 1) (F ::: F ::: ones (c + 1) blank))) R)
      ⟨PF1, true ::: blank, ones (c + 1) (F ::: F ::: ones (a + b + 3) R)⟩ := by
  sLn a; gL; gL; sLn b; gL; gL; gL; sLn c
  refine blankL ?_; gL; gR
  simp only [tl_blank]
  rw [show true ::: ones b (true ::: true ::: ones a R) = ones (a + b + 3) R by
    simp only [← ones_succ, ← ones_succ', ones_add]
    exact ones_eq _ (by omega), ← ones_succ]
  fin

/-- E's hole on cell `e + 1` (`p - e` cells right of it), D's on `d + 1`: round `p + 1` -/
theorem to_next (p e d : Nat) (_he : e < p) (hd : d < p) (a : Nat) (ha : a + e = p) :
    Rch (cfgL g1 (ones a (F ::: ones (e + 1) (F ::: F ::: ones (p + 1) blank)))
        (F ::: F ::: ones (d + 1) (F ::: ones (p - d) blank))) (RS (p + 1)) := by
  refine Rch.tr (next_hole a e p _) ?_
  obtain ⟨j, hj⟩ : ∃ j, p - d = j + 1 := ⟨p - d - 1, by omega⟩
  rw [hj, show a + e + 3 = p + 2 + 1 by omega]
  have := rebuild p (p + 2) d j
  unfold RS XE
  rw [show d + j + 2 = p + 1 by omega] at this
  exact this

/-! ## the start of the odometer -/

/-- the counting states for `p mod 5` -/
def mst : Nat → St
  | 0 => m0
  | 1 => m1
  | 2 => m2
  | 3 => m3
  | _ => m4

theorem mst_step (k : Nat) (hk : k < 5) :
    deltaNB (mst k) true = some (true, Dir.L, mst ((k + 1) % 5)) := by
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem mcyc (s R : Strm) : ∀ n k, k < 5 →
    Rch (cfgL (mst k) (ones n s) R) (cfgL (mst ((k + n) % 5)) s (ones n R)) := by
  intro n
  induction n generalizing R with
  | zero => intro k hk; rw [Nat.add_zero, Nat.mod_eq_of_lt hk]; fin
  | succ n ih =>
    intro k hk
    refine Rch.tr (sL (mst_step k hk)) ?_
    have := ih (true ::: R) ((k + 1) % 5) (Nat.mod_lt _ (by decide))
    rw [show ((k + 1) % 5 + n) % 5 = (k + (n + 1)) % 5 by omega, ← ones_succ'] at this
    exact this

/-- `p % 5 ∈ {1, 4}`: the odometer starts from `10…0` -/
def Hole (p : Nat) : Prop := p % 5 = 1 ∨ p % 5 = 4

instance (p : Nat) : Decidable (Hole p) := by unfold Hole; exact inferInstance

/-- the odometer's first string (least significant bit first) -/
def start0 (p : Nat) : List Bool :=
  if Hole p then List.replicate (p - 2) false ++ [true] else List.replicate (p - 1) false

theorem EV_init (p : Nat) (hp : 2 ≤ p) :
    EV p (p - 1) = ones p (F ::: ones 1 (F ::: F ::: ones 1 (F ::: ones p blank))) := by
  unfold EV EC
  rw [Nat.mod_eq_of_lt (show p - 1 < p by omega), Nat.div_eq_of_lt (show p - 1 < p by omega),
    Nat.zero_mod, show p - 1 + 1 = p by omega, show p - (p - 1) = 1 by omega, Nat.sub_zero]

/-- the prime `p`: E's hole on cell `p` (the counter `V = p - 1`), the first string, and the
first tick -/
theorem init (p : Nat) (hp : 2 ≤ p) :
    Rch (PX (XE p) p) (SC (start0 p) 0 (F ::: F ::: EV p p)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have tk0 := tick0 (q + 2) (q + 2 - 1) (q + 2) blank hp
  have tk := tick (q + 2) (q + 2 - 1) q (F ::: true ::: blank) hp
  rw [show q + 2 - 1 + 1 = q + 2 by omega] at tk0 tk
  rw [EV_init _ hp] at tk0 tk
  unfold PX XE SC start0
  gL; gL; gL; gL
  refine Rch.tr (mcyc _ _ (q + 2) 0 (by decide)) ?_
  rw [Nat.zero_add]
  by_cases hh : Hole (q + 2)
  · rw [if_pos hh]
    have h0 : deltaNB (mst ((q + 2) % 5)) false = some (false, Dir.L, h1) := by
      rcases hh with h | h <;> rw [h] <;> rfl
    refine Rch.tr (sL h0) ?_
    gL; sLn (q + 3); refine blankL ?_; gR; gR; gR
    simp only [tl_blank, cons_blank]
    refine Rch.tr tk ?_
    unfold BL
    simp only [Nat.add_sub_cancel, List.map_append, List.map_replicate, List.map_cons, List.map_nil,
      app_append, app_replicate, Bool.not_false, Bool.not_true, app_cons, app_nil]
    fin
  · rw [if_neg hh]
    have h0 : deltaNB (mst ((q + 2) % 5)) false = some (false, Dir.R, QE1) := by
      unfold Hole at hh
      have : (q + 2) % 5 < 5 := Nat.mod_lt _ (by decide)
      generalize (q + 2) % 5 = k at hh this
      match k, this with
      | 0, _ => rfl
      | 1, _ => omega
      | 2, _ => rfl
      | 3, _ => rfl
      | 4, _ => omega
    refine Rch.tr (sR h0) ?_
    refine Rch.tr tk0 ?_
    unfold BL
    simp only [show q + 2 - 1 = q + 1 by omega, List.map_replicate, Bool.not_false, app_replicate]
    rw [ones_cons_blank]; fin

end TM.WallSunSunInf

namespace TM.WallSunSunInf
open St TinyCryptids TM.Zeckendorf

local notation "F" => false

/-! ## the check -/

/-- after the odometer: the beep (`q9` reading 0) iff E's hole is on cell `p` and D's on cell 1;
then round `p + 1` -/
theorem check (p V : Nat) (hp : 2 ≤ p) :
    (V % p = p - 1 ∧ V / p % p = 0 → ∃ c, Rch (OV (p + 1) (F ::: F ::: EV p V)) c ∧ c.q = q9 ∧
      c.R 0 = false ∧ Reach delta c (RS (p + 1))) ∧
    (¬ (V % p = p - 1 ∧ V / p % p = 0) → Rch (OV (p + 1) (F ::: F ::: EV p V)) (RS (p + 1))) := by
  have he := Nat.mod_lt V (show p > 0 by omega)
  have hd := Nat.mod_lt (V / p) (show p > 0 by omega)
  unfold OV EV EC
  generalize V / p % p = d at hd ⊢
  generalize V % p = e at he ⊢
  have run : Rch ⟨q1, blank, ones (p + 1) (F ::: F ::: ones (e + 1) (F ::: ones (p - e) (F ::: F :::
      ones (d + 1) (F ::: ones (p - d) blank))))⟩
      ⟨q4, F ::: ones (e + 1) (F ::: F ::: ones (p + 1) blank), ones (p - e) (F ::: F :::
      ones (d + 1) (F ::: ones (p - d) blank))⟩ := by
    sRn (p + 1); gR; gR; sRn (e + 1); gR; fin
  obtain ⟨k, hk⟩ : ∃ k, p - e = k + 1 := ⟨p - e - 1, by omega⟩
  rw [hk] at run ⊢
  refine ⟨fun ⟨hx, hy⟩ => ?_, fun hn => Rch.tr run ?_⟩
  · subst hx; subst hy
    obtain rfl : k = 0 := by omega
    refine ⟨?c, Rch.tr run ?r, ?hq, ?hb, ?rest⟩
    case r => gR; gR; gR; gR; fin
    case hq => rfl
    case hb => rfl
    case rest =>
      refine Reach.trans delta (stepL (δ := delta) (by rfl)) (Reach.sub deltaNB_sub ?_)
      gL; gL; gL
      exact to_next p (p - 1) 0 he hd 1 (by omega)
  · gR
    rcases k with _ | k
    · -- E's hole on cell p: then D's hole is not on cell 1
      obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by
        rcases Nat.eq_zero_or_pos d with h | h
        · exact absurd ⟨by omega, h⟩ hn
        · omega⟩
      gR; gR; gR; gL; gL; gL; gL
      exact to_next p e (c + 1) he hd 1 (by omega)
    · -- before cell p
      gR; sRn k; gL
      rw [← ones_succ', ← ones_succ']
      exact to_next p e d he hd (k + 2) (by omega)

end TM.WallSunSunInf
