import TinyCryptids.Core.Routines
import TinyCryptids.WallSunSun2.Tac
import TinyCryptids.WallSunSun2.Spec

/-!
# The odometer and the base-`p` counter

During round `p` the tape is `B 00 E 00 D` (`../WallSunSun/Odo.lean` with no R block). B's inner cells hold a bit
string `l` (`Spec.lean`; a hole is a 1-bit), least significant bit at B's right end.
E and D are the low and the high digit of a base-`p` counter `V`: E's hole is at cell
`V % p + 1`, D's at cell `V / p % p + 1`. One round of the loop: `inc` (the head starts on
B's last inner cell and ends right of the cell it set), then `V += 1` and back.
-/

namespace TM.WallSunSun2
open St TinyCryptids TM.Zeckendorf

local notation "F" => false

/-! ## the bits of B -/

/-- B's inner cells from the head leftwards (`l`, a 1-bit is a hole), then B's left marker -/
def BL (l : List Bool) : Strm := app (l.map not) (true ::: blank)

theorem BL_replicate (k : Nat) (l : List Bool) :
    BL (List.replicate k false ++ l) = ones k (BL l) := by
  unfold BL; rw [List.map_append, app_append]; simp [app_replicate]

/-- `sc` on the bit `l.head`, `k` cleared cells and B's right marker to its right -/
def SC (l : List Bool) (k : Nat) (X : Strm) : Cfg St := cfgL sc (BL l) (ones (k + 1) X)
/-- `nb` on the bit after a candidate (a 0-bit) -/
def NB (l : List Bool) (k : Nat) (X : Strm) : Cfg St := cfgL nb (BL l) (ones (k + 2) X)
/-- the candidate was set (a hole); the head right of it, about to tick E -/
def QE (l : List Bool) (k : Nat) (X : Strm) : Cfg St := ⟨QE1, F ::: BL l, ones (k + 1) X⟩
/-- the last string is passed: B is all 1s, the head on its left marker -/
def OV (n : Nat) (X : Strm) : Cfg St := ⟨q1, blank, ones n X⟩

theorem rep_app {α : Type} (k : Nat) (a : α) (l : List α) :
    List.replicate k a ++ a :: l = List.replicate (k + 1) a ++ l := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, ih]

theorem overflow (j : Nat) (X : Strm) : Rch (cfgL nb blank (ones j X)) (OV j X) := by
  unfold OV
  show Rch (cfgL nb (F ::: blank) (ones j X)) _
  gL; gR; gR
  simp only [tl_blank, cons_blank]; fin

theorem nb_spec : ∀ (rest : List Bool) (k : Nat) (X : Strm), Valid (false :: rest) →
    (∀ l', cand (false :: rest) = some l' → ∃ k' r',
      List.replicate k false ++ l' = List.replicate k' false ++ true :: r' ∧ Rch (NB rest k X) (QE r' k' X)) ∧
    (cand (false :: rest) = none → Rch (NB rest k X) (OV (rest.length + k + 3) X))
  | [], k, X, _ => by
    refine ⟨fun l' h => ?_, fun h => by simp [cand] at h⟩
    simp [cand] at h; subst h
    refine ⟨k, [], rfl, ?_⟩
    unfold NB QE BL; simp only [List.map_nil, app_nil]
    gR; gR; fin
  | false :: r, k, X, _ => by
    refine ⟨fun l' h => ?_, fun h => by simp [cand] at h⟩
    simp [cand] at h; subst h
    refine ⟨k, false :: r, rfl, ?_⟩
    unfold NB QE
    show Rch (cfgL nb (true ::: BL r) (ones (k + 2) X)) _
    gR; gR; fin
  | [true], k, X, _ => by
    refine ⟨fun l' h => by simp [cand] at h, fun _ => ?_⟩
    unfold NB
    show Rch (cfgL nb (F ::: true ::: blank) (ones (k + 2) X)) _
    gL; gL
    have := overflow (k + 4) X
    rw [show [true].length + k + 3 = k + 4 by simp; omega]
    simpa [ones_succ] using this
  | true :: true :: _, _, _, hv => absurd ⟨rfl, rfl⟩ hv.2.1
  | true :: false :: r, k, X, hv => by
    have ih := nb_spec r (k + 2) X (Valid.tail (Valid.tail hv))
    have e : Rch (NB (true :: false :: r) k X) (NB r (k + 2) X) := by
      unfold NB
      show Rch (cfgL nb (F ::: true ::: BL r) (ones (k + 2) X)) _
      gL; gL; fin
    refine ⟨fun l' h => ?_, fun h => ?_⟩
    · simp only [cand, Option.map_eq_some'] at h
      obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨k', r', h1, h2⟩ := ih.1 x hx
      refine ⟨k', r', ?_, Rch.tr e h2⟩
      rw [← h1, rep_app, rep_app]
    · simp only [cand, Option.map_eq_none'] at h
      have := Rch.tr e (ih.2 h)
      simp only [List.length_cons] at this ⊢
      rw [show r.length + 1 + 1 + k + 3 = r.length + (k + 2) + 3 by omega]; exact this

theorem sc_spec : ∀ (l : List Bool) (k : Nat) (X : Strm), Valid l →
    (∀ l', inc l = some l' → ∃ k' r',
      List.replicate k false ++ l' = List.replicate k' false ++ true :: r' ∧ Rch (SC l k X) (QE r' k' X)) ∧
    (inc l = none → Rch (SC l k X) (OV (l.length + k + 2) X))
  | [], k, X, _ => by
    refine ⟨fun l' h => by simp [inc] at h, fun _ => ?_⟩
    unfold SC BL; simp only [List.map_nil, app_nil]
    gL
    have := overflow (k + 2) X
    simpa [ones_succ] using this
  | false :: r, k, X, hv => by
    have h := nb_spec r k X hv
    have e : Rch (SC (false :: r) k X) (NB r k X) := by
      unfold SC NB
      show Rch (cfgL sc (true ::: BL r) (ones (k + 1) X)) _
      gL; fin
    refine ⟨fun l' hl => ?_, fun hl => ?_⟩
    · obtain ⟨k', r', h1, h2⟩ := h.1 l' hl
      exact ⟨k', r', h1, Rch.tr e h2⟩
    · have := Rch.tr e (h.2 hl)
      simp only [List.length_cons] at this ⊢
      rw [show r.length + 1 + k + 2 = r.length + k + 3 by omega]; exact this
  | true :: r, k, X, hv => by
    have ih := sc_spec r (k + 1) X (Valid.tail hv)
    have e : Rch (SC (true :: r) k X) (SC r (k + 1) X) := by
      unfold SC
      show Rch (cfgL sc (F ::: BL r) (ones (k + 1) X)) _
      gL; fin
    refine ⟨fun l' hl => ?_, fun hl => ?_⟩
    · simp only [inc, Option.map_eq_some'] at hl
      obtain ⟨x, hx, rfl⟩ := hl
      obtain ⟨k', r', h1, h2⟩ := ih.1 x hx
      refine ⟨k', r', ?_, Rch.tr e h2⟩
      rw [← h1, rep_app]
    · simp only [inc, Option.map_eq_none'] at hl
      have := Rch.tr e (ih.2 hl)
      simp only [List.length_cons] at this ⊢
      rw [show r.length + 1 + k + 2 = r.length + (k + 1) + 2 by omega]; exact this

/-! ## the counter -/

/-- E from its cell 0 (hole at cell `e + 1`), then D (hole at cell `d + 1`) -/
def EC (p e d : Nat) : Strm :=
  ones (e + 1) (F ::: ones (p - e) (F ::: F ::: ones (d + 1) (F ::: ones (p - d) blank)))

/-- the counter `V` -/
def EV (p V : Nat) : Strm := EC p (V % p) (V / p % p)

theorem Da : DadvL delta a1 a2 a3 a4 aw1 aw2 aw3 rL QD1 :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
theorem PQE : ParserR delta QE1 QE2 := by constructor <;> rfl
theorem PQD : ParserR delta QD1 QD2 := by constructor <;> rfl
theorem PPB : ParserL delta PB1 PB2 := by constructor <;> rfl

/-- back from E's sep to `sc` on B's last inner cell -/
theorem back (k : Nat) (Lft R : Strm) :
    Rch (cfgL rL (F ::: F ::: ones (k + 1) Lft) R) (cfgL sc (ones k Lft) (true ::: F ::: F ::: R)) := by
  gL; gL; gL; fin

theorem div_succ (V p : Nat) (h : V % p + 1 < p) : (V + 1) / p = V / p := by
  have e := Nat.div_add_mod V p
  have hp : 0 < p := by omega
  rw [show V + 1 = (V % p + 1) + p * (V / p) by omega, Nat.add_mul_div_left _ _ hp,
    Nat.div_eq_of_lt h, Nat.zero_add]

theorem div_succ' (V p : Nat) (h : V % p + 1 = p) : (V + 1) / p = V / p + 1 := by
  have e := Nat.div_add_mod V p
  have hp : 0 < p := by omega
  rw [show V + 1 = p * (V / p + 1) by rw [Nat.mul_add]; omega, Nat.mul_div_cancel_left _ hp]

/-- one tick from E's cell 0: `V += 1` (on a wrap of E, D too); back to `sc` -/
theorem tick0 (p V k : Nat) (Lft : Strm) (hp : 2 ≤ p) :
    Rch ⟨QE1, F ::: F ::: ones (k + 1) Lft, EV p V⟩
      (cfgL sc (ones k Lft) (ones 1 (F ::: F ::: EV p (V + 1)))) := by
  have he := Nat.mod_lt V (show p > 0 by omega)
  have hd := Nat.mod_lt (V / p) (show p > 0 by omega)
  have ms := mod_succ V p
  unfold EV EC
  generalize hdd : V / p % p = dd at hd
  generalize hee : V % p = e at he ms
  -- to E's hole
  obtain ⟨j, hj⟩ : ∃ j, p - e = j + 1 := ⟨p - e - 1, by omega⟩
  rw [hj]
  refine Rch.tr (PQE.find0 (e + 1) _ _) ?_
  gL
  by_cases hw : e + 1 < p
  · -- no wrap
    have h1 := ms.1 hw
    have h2 : (V + 1) / p % p = dd := by rw [div_succ V p (by omega)]; exact hdd
    rw [h1, h2]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    refine Rch.tr (Da.nowrap e i _ _) ?_
    sLn (e + 2)
    refine Rch.tr (back k Lft _) ?_
    rw [show p - (e + 1) = i + 1 by omega]; fin
  · -- E wraps: tick D
    have h1 := ms.2 (by omega)
    have h2 : (V + 1) / p = V / p + 1 := div_succ' V p (by omega)
    rw [h1, h2]
    obtain rfl : j = 0 := by omega
    obtain rfl : p = e + 1 := by omega
    refine Rch.tr (Da.toDW.wrap (e + 1) (F ::: ones (k + 1) Lft) _) ?_
    obtain ⟨g, hg⟩ : ∃ g, e + 1 - dd = g + 1 := ⟨e - dd, by omega⟩
    rw [hg]
    refine Rch.tr (PQD.find2 (e + 1) dd _ _) ?_
    gL
    have md := mod_succ (V / (e + 1)) (e + 1)
    rw [hdd] at md
    by_cases hw2 : dd + 1 < e + 1
    · rw [md.1 hw2]
      obtain ⟨i, rfl⟩ : ∃ i, g = i + 1 := ⟨g - 1, by omega⟩
      gR; gR; gL; gL
      refine Rch.tr (PPB.find2 (dd + 2) e _ _) ?_
      gL
      refine Rch.tr (back k Lft _) ?_
      rw [show e + 1 - (dd + 1) = i + 1 by omega, show e + 1 - 0 = e + 1 by omega]
      fin
    · rw [md.2 (by omega)]
      obtain rfl : dd = e := by omega
      obtain rfl : g = 0 := by omega
      gR; rw [show ones 0 blank = F ::: blank from cons_blank.symm]; gR; gL
      sLn (dd + 3); gR; gR; gL
      refine Rch.tr (PPB.find2 1 dd _ _) ?_
      gL
      refine Rch.tr (back k Lft _) ?_
      rw [show dd + 1 - 0 = dd + 1 by omega, cons_blank]
      fin

/-- one tick from inside B (`k + 1` cells to B's right end) -/
theorem tick (p V k : Nat) (Lft : Strm) (hp : 2 ≤ p) :
    Rch ⟨QE1, Lft, ones (k + 1) (F ::: F ::: EV p V)⟩
      (cfgL sc (ones k Lft) (ones 1 (F ::: F ::: EV p (V + 1)))) := by
  sRn (k + 1); gR
  have : EV p V = true ::: tl (EV p V) := by unfold EV EC; rfl
  rw [this]; gR
  rw [← this]
  exact tick0 p V k Lft hp

/-! ## the loop -/

/-- the odometer from string `l` with counter `V`: `fib (n + 2) - 1 - val 0 l` ticks, then
the head on B's left marker -/
theorem loop (p n : Nat) (hp : 2 ≤ p) : ∀ t (l : List Bool) (V : Nat), l.length = n → Valid l →
    val 0 l + 1 + t = fib (n + 2) →
    Rch (SC l 0 (F ::: F ::: EV p V)) (OV (n + 2) (F ::: F ::: EV p (V + t))) := by
  intro t
  induction t with
  | zero =>
    intro l V hl hv ht
    rcases h : inc l with _ | l'
    · have := (sc_spec l 0 (F ::: F ::: EV p V) hv).2 h
      rw [hl] at this; exact this
    · obtain ⟨h1, h2, h3⟩ := inc_spec l l' h hv
      have := val_lt l' 0 h3
      simp only [Nat.zero_add, Nat.add_zero, h1, hl, show fib 1 = 1 from rfl] at this ht
      omega
  | succ t ih =>
    intro l V hl hv ht
    rcases h : inc l with _ | l'
    · have := inc_none l h hv; rw [hl] at this; omega
    · obtain ⟨h1, h2, h3⟩ := inc_spec l l' h hv
      obtain ⟨k', r', e1, e2⟩ := (sc_spec l 0 (F ::: F ::: EV p V) hv).1 l' h
      simp only [List.replicate_zero, List.nil_append] at e1
      have tk := tick p V k' (F ::: BL r') hp
      have ih' := ih l' (V + 1) (by rw [h1, hl]) h3 (by omega)
      rw [show V + 1 + t = V + (t + 1) by omega] at ih'
      refine Rch.tr e2 (Rch.tr tk ?_)
      have : SC l' 0 (F ::: F ::: EV p (V + 1)) =
          cfgL sc (ones k' (F ::: BL r')) (ones 1 (F ::: F ::: EV p (V + 1))) := by
        unfold SC; rw [e1, BL_replicate]; rfl
      rw [← this]; exact ih'

end TM.WallSunSun2
