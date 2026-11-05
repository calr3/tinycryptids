import TinyCryptids.Goormaghtigh.Base
import TinyCryptids.Goormaghtigh.Spec

/-!
# Main theorem: the design halts iff the Goormaghtigh conjecture fails
-/

namespace TM.Goormaghtigh

open TinyCryptids
open St

local notation "F" => false

/-! ## one base -/

/-- the walk of base `b + 2` from `r` (with `V = r + d`): it reaches `r = V` (a hit) or
overflows to the end of the base -/
theorem walk (b : Nat) (E : Strm) : ∀ d r, 1 ≤ r →
    (HitFrom (b + 2) (r + d) r → Rch (XC r d (LK (b + 2) E)) (XC (r + d) 0 (LK (b + 2) E))) ∧
    (¬ HitFrom (b + 2) (r + d) r → Rch (XC r d (LK (b + 2) E)) (KE E (b + 2) (r + d + 1))) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro r hr
    rcases d with _ | d
    · exact ⟨fun _ => by rw [Nat.add_zero]; fin, fun h => absurd (hitFrom_self _ _) h⟩
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hm : (r + 1) * (b + 2) = (r + 1) * (b + 1) + (r + 1) := Nat.mul_succ _ _
    have hs := hitFrom_step (b := b + 2) (V := r + 1 + (d + 1)) (r := r + 1) (by omega)
    by_cases hd : (r + 1) * (b + 1) ≤ d
    · have st := step_ok r b d E hd
      have := ih (d - (r + 1) * (b + 1)) (by omega) ((r + 1) * (b + 2) + 1) (by omega)
      rw [show (r + 1) * (b + 2) + 1 + (d - (r + 1) * (b + 1)) = r + 1 + (d + 1) by omega] at this
      exact ⟨fun h => Rch.tr st (this.1 (hs.1 h)), fun h => Rch.tr st (this.2 (fun h' => h (hs.2 h')))⟩
    · refine ⟨fun h => absurd (hs.1 h) (not_hitFrom_gt (by omega) (by omega)), fun _ => ?_⟩
      have := step_ovf r b d E (by omega)
      rw [show r + d + 3 = r + 1 + (d + 1) + 1 by omega] at this
      exact this

/-- a hit: `f` counts it (up to 2); F loses a cell if `f` was below 2 -/
theorem hit_upd (V b k fl f : Nat) (hf : f ≤ 2) (hfl : f ≤ 1 → 1 ≤ fl) :
    Rch (XC V 0 (LK b (Env (k + 1) fl f)))
      (KE (Env (k + 1) (if f ≤ 1 then fl - 1 else fl) (min (f + 1) 2)) b (V + 1)) := by
  rcases (show f = 0 ∨ f = 1 ∨ f = 2 by omega) with rfl | rfl | rfl
  · obtain ⟨fl, rfl⟩ : ∃ e, fl = e + 1 := ⟨fl - 1, by have := hfl (by decide); omega⟩
    exact hit0 V b k fl
  · obtain ⟨fl, rfl⟩ : ∃ e, fl = e + 1 := ⟨fl - 1, by have := hfl (by decide); omega⟩
    exact hit1 V b k fl
  · exact hit2 V b k fl

/-- hits, capped at 2 -/
noncomputable def fm (V b : Nat) : Nat := min (hc V b) 2

open Classical in
theorem fm_succ (V b : Nat) (hb : 2 ≤ b) :
    fm V (b + 1) = if Hit b V then min (fm V b + 1) 2 else fm V b := by
  unfold fm
  show min (hc V b + (if 2 ≤ b ∧ Hit b V then 1 else 0)) 2 = _
  by_cases h : Hit b V
  · rw [if_pos ⟨hb, h⟩, if_pos h]; omega
  · rw [if_neg (fun h' => h h'.2), if_neg h, Nat.add_zero]

/-- one base: from its start to its end, `f` and F updated -/
theorem base (k b g : Nat) (hg : g ≤ 2) (hb : 2 ≤ b) :
    Rch (CB (k + 1) b (4 - g - fm (k + 2 + b) b) (fm (k + 2 + b) b))
      (KE (Env (k + 1) (4 - g - fm (k + 2 + b) (b + 1)) (fm (k + 2 + b) (b + 1))) b (k + 3 + b)) := by
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
  have w := walk b (Env (k + 1) (4 - g - fm (k + 2 + (b + 2)) (b + 2)) (fm (k + 2 + (b + 2)) (b + 2)))
    (k + 1 + (b + 2)) 1 (by omega)
  rw [show 1 + (k + 1 + (b + 2)) = k + 2 + (b + 2) by omega] at w
  have hf := fm_succ (k + 2 + (b + 2)) (b + 2) (by omega)
  have hle : fm (k + 2 + (b + 2)) (b + 2) ≤ 2 := Nat.min_le_right _ _
  by_cases h : Hit (b + 2) (k + 2 + (b + 2))
  · rw [if_pos h] at hf
    rw [hf]
    refine Rch.tr (w.1 h) ?_
    have := hit_upd (k + 2 + (b + 2)) (b + 2) k (4 - g - fm (k + 2 + (b + 2)) (b + 2))
      (fm (k + 2 + (b + 2)) (b + 2)) hle (by omega)
    rw [show (if fm (k + 2 + (b + 2)) (b + 2) ≤ 1 then 4 - g - fm (k + 2 + (b + 2)) (b + 2) - 1
        else 4 - g - fm (k + 2 + (b + 2)) (b + 2)) = 4 - g - min (fm (k + 2 + (b + 2)) (b + 2) + 1) 2 by
        split <;> omega,
      show k + 2 + (b + 2) + 1 = k + 3 + (b + 2) by omega] at this
    exact this
  · rw [if_neg h] at hf
    rw [hf]
    have := w.2 h
    rw [show k + 2 + (b + 2) + 1 = k + 3 + (b + 2) by omega] at this
    exact this

/-- the bases `b .. V - 2` of `V` -/
theorem bloop (V g : Nat) (hg : g ≤ 2) : ∀ k b, k + 2 + b = V → 2 ≤ b →
    Rch (CB (k + 1) b (4 - g - fm V b) (fm V b))
      (KE (Env 1 (4 - g - fm V (V - 1)) (fm V (V - 1))) (V - 2) (V + 1)) := by
  intro k
  induction k with
  | zero =>
    intro b hV hb
    subst hV
    have := base 0 b g hg hb
    rw [show 0 + 2 + b - 1 = b + 1 by omega, show 0 + 2 + b - 2 = b by omega,
      show 0 + 2 + b + 1 = 0 + 3 + b by omega]
    exact this
  | succ k ih =>
    intro b hV hb
    subst hV
    refine Rch.tr (base (k + 1) b g hg hb) ?_
    have ks := kstep k b (4 - g - fm (k + 1 + 2 + b) (b + 1)) (fm (k + 1 + 2 + b) (b + 1)) (k + 1 + 1 + b)
    rw [show k + 1 + 1 + b + 2 = k + 1 + 3 + b by omega] at ks
    refine Rch.tr ks ?_
    have := ih (b + 1) (by omega) (by omega)
    unfold CB at this
    rw [show k + 1 + (b + 1) = k + 1 + 1 + b by omega] at this
    exact this

/-! ## one value -/

/-- the start of value `V` with `g` bad values below it: base 2, F with `4 - g` cells -/
def CV (V g : Nat) : Cfg St := CB (V - 3) 2 (4 - g) 0

theorem fm_two (V : Nat) : fm V 2 = 0 := by simp [fm, hc]

theorem fm_bad (V : Nat) : fm V (V - 1) = 2 ↔ bad V := by
  unfold fm bad; omega

theorem fm_le (V b : Nat) : fm V b ≤ 2 := Nat.min_le_right _ _

open Classical in
/-- after value `V`: halt if it is the third bad value, otherwise the start of `V + 1` -/
theorem round (V g : Nat) (hV : 4 ≤ V) (hg : g ≤ 2) :
    (bad V ∧ g = 2 → HaltAt (CV V g)) ∧
    (¬ (bad V ∧ g = 2) → Reach delta (CV V g) (CV (V + 1) (g + if bad V then 1 else 0))) := by
  have bl := bloop V g hg (V - 4) 2 (by omega) (by decide)
  rw [fm_two, Nat.sub_zero, show V - 4 + 1 = V - 3 by omega] at bl
  have hb := fm_bad V
  have hle := fm_le V (V - 1)
  have hcv : CV (V + 1) = fun g' => CB (V - 2) 2 (4 - g') 0 := by
    funext g'; unfold CV; rw [show V + 1 - 3 = V - 2 by omega]
  rw [hcv]
  unfold CV
  obtain ⟨b, hbV⟩ : ∃ b, V - 2 = b := ⟨_, rfl⟩
  rw [hbV] at bl ⊢
  rw [show V + 1 = b + 3 by omega] at bl
  rcases (show fm V (V - 1) = 0 ∨ fm V (V - 1) = 1 ∨ fm V (V - 1) = 2 by omega) with h | h | h
  · have nb : ¬ bad V := fun h' => by have := hb.2 h'; omega
    rw [h] at bl
    refine ⟨fun h' => absurd h'.1 nb, fun _ => ?_⟩
    rw [if_neg nb, Nat.add_zero]
    have := vend0 b (3 - g)
    rw [show 3 - g + 1 = 4 - g - 0 by omega] at this
    exact Rch.tr bl this
  · have nb : ¬ bad V := fun h' => by have := hb.2 h'; omega
    rw [h] at bl
    refine ⟨fun h' => absurd h'.1 nb, fun _ => ?_⟩
    rw [if_neg nb, Nat.add_zero]
    have := vend1 b (2 - g)
    rw [show 2 - g + 1 = 4 - g - 1 by omega, show 2 - g + 2 = 4 - g by omega] at this
    exact Rch.tr bl this
  · have bV : bad V := hb.1 h
    rw [h] at bl
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · obtain ⟨_, rfl⟩ := h'
      exact HaltAt.back bl (vend_halt b)
    · rw [if_pos bV]
      have := vend2 b (1 - g)
      rw [show 1 - g + 1 = 4 - g - 2 by have : g ≠ 2 := fun e => h' ⟨bV, e⟩; omega,
        show 1 - g + 2 = 4 - (g + 1) by have : g ≠ 2 := fun e => h' ⟨bV, e⟩; omega] at this
      exact Rch.tr bl this

theorem CV_ne (V g g' : Nat) (hV : 4 ≤ V) : CV V g ≠ CV (V + 1) g' := by
  intro e
  have := congrFun (congrArg Cfg.R e) (V - 1)
  simp only [CV, CB, XC] at this
  have l1 : ∀ a i, i < a → ones a blank i = true := by
    intro a; induction a with
    | zero => intro i h; omega
    | succ a ih => intro i h; cases i with
      | zero => rfl
      | succ i => exact ih i (by omega)
  have l2 : ∀ a, ones a blank a = false := by
    intro a; induction a with
    | zero => rfl
    | succ a ih => exact ih
  rw [show V - 3 + 2 = V - 1 by omega, show V + 1 - 3 + 2 = V by omega] at this
  rw [l2, l1 V (V - 1) (by omega)] at this
  exact Bool.false_ne_true this

/-! ## the main theorem -/

theorem not_bad_small {V : Nat} (h : V ≤ 4) : ¬ bad V := by
  intro hb; obtain ⟨x, y, h1, h2, h3, _, _⟩ := (bad_iff V).1 hb; omega

open Classical in
theorem gc_next (V : Nat) : gc (V + 1) = gc V + if bad V then 1 else 0 := rfl

theorem gc_four : gc 4 = 0 := by
  rw [gc_next, gc_next, gc_next, gc_next, if_neg (not_bad_small (by decide)),
    if_neg (not_bad_small (by decide)), if_neg (not_bad_small (by decide)),
    if_neg (not_bad_small (by decide))]
  rfl

/-- If a third bad value exists, the machine reaches its explicit halting state. -/
theorem haltAt_of (h : ∃ V, bad V ∧ gc V = 2) : HaltAt start := by
  obtain ⟨V0, hb0, hg0⟩ := h
  have h5 : 5 ≤ V0 := Classical.byContradiction fun h => not_bad_small (by omega) hb0
  suffices H : ∀ n V, V + n = V0 → 4 ≤ V → HaltAt (CV V (gc V)) by
    have e : CB 1 2 4 0 = CV 4 0 := rfl
    have := H (V0 - 4) 4 (by omega) (by decide)
    rw [gc_four] at this
    exact HaltAt.back (e ▸ seed_reach) this
  intro n
  induction n with
  | zero => intro V hV h4; rw [Nat.add_zero] at hV; subst hV; exact (round V _ h4 (by omega)).1 ⟨hb0, hg0⟩
  | succ n ih =>
    intro V hV h4
    have hg : gc V ≤ 2 := by have := gc_mono V (n + 1); rw [hV] at this; omega
    by_cases hb : bad V ∧ gc V = 2
    · exact (round V _ h4 hg).1 hb
    · refine HaltAt.back ((round V _ h4 hg).2 hb) ?_
      rw [← gc_next]
      exact ih (V + 1) (by omega) (by omega)

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- a run between two different configurations takes at least one step -/
theorem reach1_of_ne {a b : Cfg St} (h : Rch a b) (hne : a ≠ b) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem halts_iff_third : Halts delta start ↔ ∃ V, bad V ∧ gc V = 2 := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have prog : ∀ c, (∃ V, 4 ≤ V ∧ gc V ≤ 2 ∧ c = CV V (gc V)) →
        ∃ c', (∃ V, 4 ≤ V ∧ gc V ≤ 2 ∧ c' = CV V (gc V)) ∧ Rch1 c c' := by
      rintro c ⟨V, hV, hg, rfl⟩
      have nb : ¬ (bad V ∧ gc V = 2) := fun h => hno ⟨V, h⟩
      have r := (round V _ hV hg).2 nb
      rw [← gc_next] at r
      refine ⟨_, ⟨V + 1, by omega, ?_, rfl⟩, reach1_of_ne r (CV_ne V _ _ hV)⟩
      rw [gc_next]; split
      · next hb => have : gc V ≠ 2 := fun e => nb ⟨hb, e⟩; omega
      · omega
    refine not_halts_of_progress delta _ prog _ ⟨4, by decide, by rw [gc_four]; decide, rfl⟩
      (halts_det hH ?_)
    have := seed_reach; rw [show CB 1 2 4 0 = CV 4 (gc 4) by rw [gc_four]; rfl] at this; exact this
  · intro h; exact (haltAt_of h).halts

/-- **Main theorem.** Started on a blank tape, the design halts if and only if the
Goormaghtigh conjecture fails: some value other than 31 and 8191 is a repunit of length at
least 3 in two bases. -/
theorem halts_iff : Halts delta start ↔
    ∃ x y m n, 1 < y ∧ y < x ∧ 2 < m ∧ 2 < n ∧ rep x m = rep y n ∧ rep x m ≠ 31 ∧ rep x m ≠ 8191 := by
  rw [halts_iff_third, third_iff, conj_iff]

/-- the halting state is reached when the conjecture fails (used by the merged machines) -/
theorem haltAt_of_conj (h : ∃ x y m n, 1 < y ∧ y < x ∧ 2 < m ∧ 2 < n ∧ rep x m = rep y n ∧
    rep x m ≠ 31 ∧ rep x m ≠ 8191) : HaltAt start :=
  haltAt_of (third_iff.2 (conj_iff.1 h))

end TM.Goormaghtigh
