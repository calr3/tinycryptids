import TinyCryptids.ABC.Blocks
import TinyCryptids.ABC.Tac
import TinyCryptids.ABC.Walk

/-!
# `GCD(D, X)`: lockstep holes

The counter block `D` (value `c`, left) and the cycled block `X` (value `v`, right), with a
gap `g` between them.  In a
round the cycled hole goes once round `X`; before each of its `v` advances the counter hole
advances once.  After round `j` the counter hole is on `(j * v) % c + 1`; the rounds go on
until it is on position 1 (`gcd > 1`, state `H1`) or 2 (`gcd = 1`, state `E1`)
(`first_hit`, `Walk.lean`).
-/

namespace TM.ABC
open St

/-- the next position of a cyclic hole with positions `1..c` -/
def nx (c i : Nat) : Nat := if i < c then i + 1 else 1

def nxs (c : Nat) : Nat → Nat → Nat
  | i, 0 => i
  | i, n + 1 => nxs c (nx c i) n

theorem nx_range {c i : Nat} (h1 : 1 ≤ i) (h2 : i ≤ c) : 1 ≤ nx c i ∧ nx c i ≤ c := by
  unfold nx; split <;> omega

/-- from position `n % c + 1`, `k` advances lead to `(n + k) % c + 1` -/
theorem nxs_mod (c : Nat) (hc : 1 ≤ c) : ∀ k n, nxs c (n % c + 1) k = (n + k) % c + 1 := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    show nxs c (nx c (n % c + 1)) k = _
    have e : nx c (n % c + 1) = (n + 1) % c + 1 := by
      unfold nx
      have hlt := Nat.mod_lt n (show 0 < c by omega)
      have hd := Nat.mod_add_div n c
      split
      · have : (n + 1) % c = n % c + 1 := by
          rw [show n + 1 = (n % c + 1) + c * (n / c) by omega, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt (by omega)]
        omega
      · have : (n + 1) % c = 0 := by
          rw [show n + 1 = c * (n / c + 1) by rw [Nat.mul_add, Nat.mul_one]; omega,
            Nat.mul_mod_right]
        omega
    rw [e, ih (n + 1)]; congr 2; omega

theorem nxs_dvd (c v : Nat) (hc : 1 ≤ c) : nxs c 1 v = 1 ↔ c ∣ v := by
  have := nxs_mod c hc v 0
  rw [Nat.zero_mod, Nat.zero_add, Nat.zero_add] at this
  rw [this]
  constructor
  · intro h; exact Nat.dvd_of_mod_eq_zero (by omega)
  · intro h; rw [Nat.mod_eq_zero_of_dvd h]

theorem nxs_range (c : Nat) : ∀ n i, 1 ≤ i → i ≤ c → 1 ≤ nxs c i n ∧ nxs c i n ≤ c := by
  intro n
  induction n with
  | zero => intro i h1 h2; exact ⟨h1, h2⟩
  | succ n ih =>
    intro i h1 h2
    have := nx_range (c := c) h1 h2
    exact ih _ this.1 this.2

theorem PPC : ParserR deltaQ PC1 PC2 := ⟨rfl, rfl, rfl⟩
theorem PPN : ParserL deltaQ PN1 PN2 := ⟨rfl, rfl, rfl⟩
theorem PPK : ParserL deltaQ PK1 PK2 := ⟨rfl, rfl, rfl⟩

local notation "F" => false
local notation "T" => true

/-- the tape right of the counter: the gap, then the cycled block with its hole at `j` -/
def cyR (Rc : Strm) (v j : Nat) (g : List Bool) : Strm :=
  app g (ones j (F ::: ones (v + 1 - j) Rc))

/-- the counter hole at cell `i` was just filled; head on cell `i + 1` -/
def cyc2 (Lc : Strm) (v j : Nat) (g : List Bool) (c i : Nat) (Rc : Strm) : Cfg St :=
  ⟨ca2, ones (i + 1) Lc, ones (c + 1 - i) (cyR Rc v j g)⟩

/-- the counter hole at cell `a`, head on cell `a + 1`, state `PC1` -/
def pcC (Lc : Strm) (v j : Nat) (g : List Bool) (c a : Nat) (Rc : Strm) : Cfg St :=
  ⟨PC1, F ::: ones a Lc, ones (c + 1 - a) (cyR Rc v j g)⟩

/-- counter advance without wrap -/
theorem ctr_nowrap (Lc Rc : Strm) (g : List Bool) (v j c i : Nat) (hi : i < c) :
    Rch (cyc2 Lc v j g c i Rc) (pcC Lc v j g c (i + 1) Rc) := by
  obtain ⟨k, hk⟩ : ∃ k, c + 1 - i = k + 2 := ⟨c - 1 - i, by omega⟩
  unfold cyc2 pcC; rw [hk, show c + 1 - (i + 1) = k + 1 by omega]
  gR; gL; gR; fin

/-- counter advance with wrap: from its last cell back to cell 1 -/
theorem ctr_wrap {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v j c : Nat) :
    Rch (cyc2 (F ::: Lc) v j g c c Rc) (pcC (F ::: Lc) v j g c 1 Rc) := by
  obtain ⟨g', hg'⟩ := hg.head
  unfold cyc2 pcC; rw [show c + 1 - c = 1 by omega, show c + 1 - 1 = c by omega]
  unfold cyR; rw [hg']
  simp only [app_cons]
  gR; gL
  sLn (c + 2)
  gR; gR; gR
  rw [← app_cons, ← hg']
  simp only [ones_succ, ones_zero]; fin

theorem ctr_adv {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v j c i : Nat) (hi : i ≤ c) :
    Rch (cyc2 (F ::: Lc) v j g c i Rc) (pcC (F ::: Lc) v j g c (nx c i) Rc) := by
  unfold nx
  split
  · exact ctr_nowrap _ Rc g v j c i (by assumption)
  · have e : c = i := by omega
    subst e
    exact ctr_wrap hg Lc Rc v j c

/-- from the counter (parser `PC`) to the cycled hole, one advance, back to the counter -/
theorem pc_part {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v j c a : Nat)
    (hj : 1 ≤ j) (hjv : j < v) (ha : 1 ≤ a) (hac : a ≤ c) :
    Rch (pcC Lc v j g c a Rc) (cyc2 Lc v (j + 1) g c a Rc) := by
  obtain ⟨n, hn⟩ : ∃ n, v + 1 - j = n + 2 := ⟨v - j - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, c + 1 - (a' + 1) = b + 1 := ⟨c - a' - 1, by omega⟩
  have hw : Clean (List.replicate (b + 1) T ++ (g ++ List.replicate (j' + 1) T)) :=
    Clean.rep_append _ (by rw [List.replicate_succ]; exact hg.clean (Clean.replicate _))
  have e : ones (b + 1) (cyR Rc v (j' + 1) g) =
      app (List.replicate (b + 1) T ++ (g ++ List.replicate (j' + 1) T)) (F ::: T ::: ones (n + 1) Rc) := by
    simp only [cyR, hn, app_append, app_replicate, ones_succ]
  unfold pcC; rw [hb, e]
  refine Rch.tr (PPC.find hw _ _) ?_
  gL0
  gR; gR; gL; gL
  have hw2 : Clean (List.replicate (j' + 2) T ++ (g.reverse ++ List.replicate (b + 1) T)) :=
    Clean.rep_append _ (by rw [List.replicate_succ]; exact hg.reverse.clean (Clean.replicate _))
  have e2 : (T ::: tl (F ::: app (List.replicate (b + 1) T ++ (g ++ List.replicate (j' + 1) T)).reverse
      (F ::: ones (a' + 1) Lc))) =
      app (List.replicate (j' + 2) T ++ (g.reverse ++ List.replicate (b + 1) T)) (F ::: T ::: ones a' Lc) := by
    simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, ones_succ]
  rw [e2]
  refine Rch.tr (PPN.find hw2 _ _) ?_
  show Rch ⟨PN2, ones a' Lc, T ::: _⟩ _
  gR; gR
  unfold cyc2 cyR
  rw [hb, show v + 1 - (j' + 1 + 1) = n + 1 by omega]
  simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, ones_succ]
  fin

/-- the last advance of a round: the cycled hole wraps; back to the counter hole (state `g1`) -/
theorem gcd_last {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v c a : Nat)
    (hv : 1 ≤ v) (ha : 1 ≤ a) (hac : a ≤ c) :
    Rch (pcC (F ::: Lc) v v g c a (F ::: Rc))
      ⟨g1, ones a (F ::: Lc), F ::: ones (c + 1 - a) (cyR (F ::: Rc) v 1 g)⟩ := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, c + 1 - (a' + 1) = b + 1 := ⟨c - a' - 1, by omega⟩
  have hw : Clean (List.replicate (b + 1) T ++ (g ++ List.replicate v T)) :=
    Clean.rep_append _ (by
      obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
      rw [List.replicate_succ]; exact hg.clean (Clean.replicate _))
  have e : ones (b + 1) (cyR (F ::: Rc) v v g) =
      app (List.replicate (b + 1) T ++ (g ++ List.replicate v T)) (F ::: T ::: F ::: Rc) := by
    simp only [cyR, show v + 1 - v = 1 by omega, app_append, app_replicate, ones_succ, ones_zero]
  unfold pcC; rw [hb, e]
  refine Rch.tr (PPC.find hw _ _) ?_
  gL0
  gR; gR; gL
  obtain ⟨g', hg'⟩ := hg.rev_head
  have e2 : (T ::: T ::: app (List.replicate (b + 1) T ++ (g ++ List.replicate v T)).reverse
      (F ::: ones (a' + 1) (F ::: Lc))) =
      ones (v + 2) (F ::: app g' (ones (b + 1) (F ::: ones (a' + 1) (F ::: Lc)))) := by
    simp only [List.reverse_append, List.reverse_replicate, app_append, app_replicate, hg', app_cons,
      ones_succ, List.append_assoc]
  show Rch (cfgL cy5 (T ::: T ::: app (List.replicate (b + 1) T ++ (g ++ List.replicate v T)).reverse
      (F ::: ones (a' + 1) (F ::: Lc))) _) _
  rw [e2]
  sLn (v + 2)
  gR; gR; gL
  show Rch (cfgL PK1 (T ::: app (F :: g') (ones (b + 1) (F ::: ones (a' + 1) (F ::: Lc)))) _) _
  rw [← hg']
  have hw2 : Clean (T :: (g.reverse ++ List.replicate (b + 1) T)) :=
    Clean.one (by rw [List.replicate_succ]; exact hg.reverse.clean (Clean.replicate b))
  have e3 : (T ::: app g.reverse (ones (b + 1) (F ::: ones (a' + 1) (F ::: Lc)))) =
      app (T :: (g.reverse ++ List.replicate (b + 1) T)) (F ::: T ::: ones a' (F ::: Lc)) := by
    simp only [app_cons, app_append, app_replicate, ones_succ]
  rw [e3]
  refine Rch.tr (PPK.find hw2 _ _) ?_
  show Rch ⟨PK2, ones a' (F ::: Lc), T ::: _⟩ _
  gR
  have e4 : cyR (F ::: Rc) v 1 g = app g (T ::: F ::: ones v (F ::: Rc)) := by
    simp only [cyR, show v + 1 - 1 = v by omega, ones_succ, ones_zero]
  rw [e4]
  simp only [List.reverse_cons, List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    List.append_assoc, List.singleton_append, app_append, app_replicate, app_cons, app_nil, ones_succ]
  fin

/-- on the counter hole at `i`, the cycled hole on cell 1 -/
def gAt (q : St) (Lc Rc : Strm) (v : Nat) (g : List Bool) (c i : Nat) : Cfg St :=
  ⟨q, ones i (F ::: Lc), F ::: ones (c + 1 - i) (cyR (F ::: Rc) v 1 g)⟩

theorem round_loop {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v c : Nat) (hv : 1 ≤ v) :
    ∀ n j i, v - j = n → 1 ≤ j → j ≤ v → 1 ≤ i → i ≤ c →
    Rch (cyc2 (F ::: Lc) v j g c i (F ::: Rc)) (gAt g1 Lc Rc v g c (nxs c i (n + 1))) := by
  intro n
  induction n with
  | zero =>
    intro j i hn hj hjv hi hic
    have e : v = j := by omega
    subst e
    have ⟨r1, r2⟩ := nx_range (c := c) hi hic
    refine Rch.tr (ctr_adv hg Lc _ v v c i hic) ?_
    exact gcd_last hg Lc Rc v c _ hv r1 r2
  | succ n ih =>
    intro j i hn hj hjv hi hic
    have ⟨r1, r2⟩ := nx_range (c := c) hi hic
    refine Rch.tr (ctr_adv hg Lc _ v j c i hic) ?_
    refine Rch.tr (pc_part hg _ _ v j c _ hj (by omega) r1 r2) ?_
    exact ih (j + 1) (nx c i) (by omega) (by omega) (by omega) r1 r2

/-- one round: the counter hole moves from `i` to `nxs c i v` -/
theorem round {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v c i : Nat) (hv : 1 ≤ v)
    (hi : 1 ≤ i) (hic : i ≤ c) :
    Rch (cyc2 (F ::: Lc) v 1 g c i (F ::: Rc)) (gAt g1 Lc Rc v g c (nxs c i v)) := by
  have := round_loop hg Lc Rc v c hv (v - 1) 1 i rfl (Nat.le_refl _) hv hi hic
  rwa [show v - 1 + 1 = v by omega] at this

theorem start_step (Lc Rc : Strm) (v : Nat) (g : List Bool) (c i : Nat) (hic : i ≤ c) :
    Rch (gAt ca1 Lc Rc v g c i) (cyc2 (F ::: Lc) v 1 g c i (F ::: Rc)) := by
  unfold gAt cyc2; gR; fin

/-- the counter hole on a position `≥ 3`: another round -/
theorem check_other (Lc Rc : Strm) (v : Nat) (g : List Bool) (c i : Nat) (h3 : 3 ≤ i) (hic : i ≤ c) :
    Rch (gAt g1 Lc Rc v g c i) (cyc2 (F ::: Lc) v 1 g c i (F ::: Rc)) := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 3 := ⟨i - 3, by omega⟩
  unfold gAt cyc2
  rw [show ones (i' + 3) (F ::: Lc) = T ::: T ::: T ::: ones i' (F ::: Lc) from rfl]
  gL0; gL; gL; gR; gR; gR; gR; fin

/-- the counter hole on position 1: `gcd > 1` -/
theorem check1 (Lc Rc : Strm) (v : Nat) (g : List Bool) (c : Nat) :
    Rch (gAt g1 Lc Rc v g c 1) ⟨H1, F ::: Lc, T ::: F ::: ones c (cyR (F ::: Rc) v 1 g)⟩ := by
  unfold gAt
  rw [show c + 1 - 1 = c by omega]
  gL0; gL
  show Rch ⟨g3, Lc, F ::: T ::: F ::: ones c (cyR (F ::: Rc) v 1 g)⟩ _
  gR; fin

/-- the counter hole on position 2: `gcd = 1` -/
theorem check2 (Lc Rc : Strm) (v : Nat) (g : List Bool) (c : Nat) (hc : 2 ≤ c) :
    Rch (gAt g1 Lc Rc v g c 2) ⟨E1, F ::: Lc, T ::: T ::: F ::: ones (c - 1) (cyR (F ::: Rc) v 1 g)⟩ := by
  unfold gAt
  rw [show c + 1 - 2 = c - 1 by omega]
  gL0; gL; gL
  show Rch ⟨g4, Lc, F ::: T ::: T ::: F ::: ones (c - 1) (cyR (F ::: Rc) v 1 g)⟩ _
  gR; fin

theorem exists_least (P : Nat → Prop) (h : ∃ j, 1 ≤ j ∧ P j) :
    ∃ j, 1 ≤ j ∧ P j ∧ ∀ i, 1 ≤ i → i < j → ¬ P i := by
  obtain ⟨j, hj, hp⟩ := h
  suffices H : ∀ n j, j ≤ n → 1 ≤ j → P j → ∃ j, 1 ≤ j ∧ P j ∧ ∀ i, 1 ≤ i → i < j → ¬ P i from
    H j j (Nat.le_refl _) hj hp
  intro n
  induction n with
  | zero => intro j h1 h2; omega
  | succ n ih =>
    intro j h1 h2 hp
    by_cases hex : ∃ i, 1 ≤ i ∧ i < j ∧ P i
    · obtain ⟨i, hi1, hi2, hpi⟩ := hex
      exact ih i (by omega) hi1 hpi
    · exact ⟨j, h2, hp, fun i hi1 hi2 hpi => hex ⟨i, hi1, hi2, hpi⟩⟩

/-- **`GCD(D, X)`**: from both holes on position 1, the head on the counter hole in `ca1`:
`gcd(v, c) = 1` ends in `E1` (counter hole on position 2), `gcd > 1` in `H1` (on 1), the
cycled hole back on cell 1. -/
theorem gcd_run {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v c : Nat) (hv : 1 ≤ v) (hc : 2 ≤ c) :
    (Nat.gcd v c = 1 →
      Rch (gAt ca1 Lc Rc v g c 1) ⟨E1, F ::: Lc, T ::: T ::: F ::: ones (c - 1) (cyR (F ::: Rc) v 1 g)⟩) ∧
    (Nat.gcd v c ≠ 1 →
      Rch (gAt ca1 Lc Rc v g c 1) ⟨H1, F ::: Lc, T ::: F ::: ones c (cyR (F ::: Rc) v 1 g)⟩) := by
  have hc1 : 1 ≤ c := by omega
  let pos := fun j => (j * v) % c + 1
  have hpos : ∀ j, 1 ≤ pos j ∧ pos j ≤ c := fun j =>
    ⟨by simp [pos], by have := Nat.mod_lt (j * v) (show 0 < c by omega); simp only [pos]; omega⟩
  have key : ∀ j, 1 ≤ j → (∀ i, 1 ≤ i → i < j → ¬ hitC v c i ∧ ¬ hitN v c i) →
      Rch (gAt ca1 Lc Rc v g c 1) (gAt g1 Lc Rc v g c (pos j)) := by
    intro j hj
    induction j with
    | zero => omega
    | succ j ih =>
      intro hno
      rcases Nat.eq_zero_or_pos j with h0 | hpos0
      · subst h0
        refine Rch.tr (start_step Lc Rc v g c 1 hc1) ?_
        have := round hg Lc Rc v c 1 hv (Nat.le_refl _) hc1
        have e := nxs_mod c hc1 v 0
        rw [Nat.zero_mod, Nat.zero_add, Nat.zero_add] at e
        rw [e] at this
        simpa [pos] using this
      · refine Rch.tr (ih hpos0 (fun i h1 h2 => hno i h1 (by omega))) ?_
        have ⟨hA, hB⟩ := hno j hpos0 (Nat.lt_succ_self j)
        have h3 : 3 ≤ pos j := by
          simp only [hitC, hitN, Nat.mod_eq_of_lt (show 1 < c by omega)] at hA hB
          simp only [pos]; omega
        refine Rch.tr (check_other Lc Rc v g c (pos j) h3 (hpos j).2) ?_
        have := round hg Lc Rc v c (pos j) hv (hpos j).1 (hpos j).2
        rw [show pos j = (j * v) % c + 1 from rfl, nxs_mod c hc1 v (j * v)] at this
        show Rch (cyc2 (F ::: Lc) v 1 g c ((j * v) % c + 1) (F ::: Rc))
          (gAt g1 Lc Rc v g c (((j + 1) * v) % c + 1))
        rw [Nat.succ_mul]; exact this
  obtain ⟨j, hj, hp, hfirst⟩ := exists_least (fun j => hitC v c j ∨ hitN v c j)
    ⟨c, hc1, Or.inr (hitN_r v c)⟩
  have hf : ∀ i, 1 ≤ i → i < j → ¬ hitC v c i ∧ ¬ hitN v c i :=
    fun i h1 h2 => by have := hfirst i h1 h2; exact ⟨fun h => this (Or.inl h), fun h => this (Or.inr h)⟩
  have hk := key j hj hf
  have hfh := first_hit (k := v) (r := c) hc1 hj hf
  constructor
  · intro hg1
    rcases hp with hC | hN
    · have e : pos j = 2 := by
        simp only [hitC, Nat.mod_eq_of_lt (show 1 < c by omega)] at hC; simp only [pos]; omega
      rw [e] at hk; exact Rch.tr hk (check2 Lc Rc v g c hc)
    · by_cases hC : hitC v c j
      · have e : pos j = 2 := by
          simp only [hitC, Nat.mod_eq_of_lt (show 1 < c by omega)] at hC; simp only [pos]; omega
        rw [e] at hk; exact Rch.tr hk (check2 Lc Rc v g c hc)
      · exact absurd hg1 (hfh.2 hN hC)
  · intro hg1
    rcases hp with hC | hN
    · exact absurd (hfh.1 hC) hg1
    · have e : pos j = 1 := by simp only [hitN] at hN; simp only [pos]; omega
      rw [e] at hk; exact Rch.tr hk (check1 Lc Rc v g c)

end TM.ABC
