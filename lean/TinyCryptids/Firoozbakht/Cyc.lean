import TinyCryptids.Firoozbakht.Blocks
import TinyCryptids.Firoozbakht.Tac

/-!
# The divisibility cycle `CYC(counter, cycled)`

The counter block (value `c`, left) and the cycled block (value `v`, right), with a gap `g`
between them.  The cycled hole goes round once; before each of its `v` advances the counter
hole advances once.  Then the counter hole is checked (and filled): it is back at cell 1
iff `c ∣ v`; the head ends right of the counter in state `PM1` or `kn3`.
-/

namespace TM.Firoozbakht
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

theorem Gap.rev_head {g : List Bool} (h : Gap g) : ∃ g', g.reverse = false :: g' := by
  rcases h with rfl | ⟨P, _, rfl⟩
  · exact ⟨[false], rfl⟩
  · exact ⟨false :: (P.reverse ++ [false, false]), by simp⟩

theorem Gap.head {g : List Bool} (h : Gap g) : ∃ g', g = false :: g' := by
  rcases h with rfl | ⟨P, _, rfl⟩
  · exact ⟨[false], rfl⟩
  · exact ⟨_, rfl⟩

theorem Gap.last {g : List Bool} (h : Gap g) : ∃ g', g = g' ++ [false] := by
  rcases h with rfl | ⟨P, _, rfl⟩
  · exact ⟨[false], rfl⟩
  · exact ⟨false :: false :: (P ++ [false]), by simp⟩

theorem PPC : ParserR delta PC1 PC2 := ⟨rfl, rfl, rfl⟩
theorem PPN : ParserL delta PN1 PN2 := ⟨rfl, rfl, rfl⟩
theorem PPK : ParserL delta PK1 PK2 := ⟨rfl, rfl, rfl⟩

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

/-- the last step: the cycled hole wraps; the counter hole (at `a`) is checked and filled -/
theorem pc_last {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v c a : Nat)
    (hv : 1 ≤ v) (ha : 1 ≤ a) (hac : a ≤ c) :
    Rch (pcC (F ::: Lc) v v g c a (F ::: Rc))
      ⟨if a = 1 then PM1 else kn3, ones (c + 2) (F ::: Lc), cyR (F ::: Rc) v 1 g⟩ := by
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
    Clean.one (by rw [List.replicate_succ]; exact hg.reverse.clean (Clean.replicate _))
  have e3 : (T ::: app g.reverse (ones (b + 1) (F ::: ones (a' + 1) (F ::: Lc)))) =
      app (T :: (g.reverse ++ List.replicate (b + 1) T)) (F ::: T ::: ones a' (F ::: Lc)) := by
    simp only [app_cons, app_append, app_replicate, ones_succ]
  rw [e3]
  refine Rch.tr (PPK.find hw2 _ _) ?_
  show Rch ⟨PK2, ones a' (F ::: Lc), T ::: _⟩ _
  gR; gL; gL
  have e4 : cyR (F ::: Rc) v 1 g = app g (T ::: F ::: ones v (F ::: Rc)) := by
    simp only [cyR, show v + 1 - 1 = v by omega, ones_succ, ones_zero]
  rw [e4]
  cases a' with
  | zero =>
    rw [if_pos rfl]
    obtain rfl : c = b + 1 := by omega
    simp only [ones_zero]
    gR
    have e5 : (T ::: T ::: app (T :: (g.reverse ++ List.replicate (b + 1) T)).reverse (F ::: ones v (F ::: Rc))) =
        ones (b + 3) (app g (T ::: F ::: ones v (F ::: Rc))) := by
      simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, ones_succ]
    show Rch ⟨PM1, F ::: Lc, T ::: T ::: app (T :: (g.reverse ++ List.replicate (b + 1) T)).reverse
      (F ::: ones v (F ::: Rc))⟩ _
    rw [e5]
    sRn (b + 3); fin
  | succ a'' =>
    rw [if_neg (by omega)]
    rw [ones_succ]
    gR
    have e5 : (T ::: T ::: app (T :: (g.reverse ++ List.replicate (b + 1) T)).reverse (F ::: ones v (F ::: Rc))) =
        ones (b + 3) (app g (T ::: F ::: ones v (F ::: Rc))) := by
      simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, ones_succ]
    show Rch ⟨kn3, T ::: ones a'' (F ::: Lc), T ::: T ::: app (T :: (g.reverse ++ List.replicate (b + 1) T)).reverse
      (F ::: ones v (F ::: Rc))⟩ _
    rw [e5]
    sRn (b + 3)
    rw [← ones_succ, ones_add, show b + 3 + (a'' + 1) = c + 2 by omega]; fin

theorem cyc_loop {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v c : Nat) (hv : 1 ≤ v) (hc : 1 ≤ c) :
    ∀ n j i, v - j = n → 1 ≤ j → j ≤ v → 1 ≤ i → i ≤ c →
    Rch (cyc2 (F ::: Lc) v j g c i (F ::: Rc))
      ⟨if nxs c i (n + 1) = 1 then PM1 else kn3, ones (c + 2) (F ::: Lc), cyR (F ::: Rc) v 1 g⟩ := by
  intro n
  induction n with
  | zero =>
    intro j i hn hj hjv hi hic
    have e : v = j := by omega
    subst e
    have ⟨r1, r2⟩ := nx_range (c := c) hi hic
    refine Rch.tr (ctr_adv hg Lc _ v v c i hic) ?_
    exact pc_last hg Lc Rc v c _ hv r1 r2
  | succ n ih =>
    intro j i hn hj hjv hi hic
    have ⟨r1, r2⟩ := nx_range (c := c) hi hic
    refine Rch.tr (ctr_adv hg Lc _ v j c i hic) ?_
    refine Rch.tr (pc_part hg _ _ v j c _ hj (by omega) r1 r2) ?_
    exact ih (j + 1) (nx c i) (by omega) (by omega) (by omega) r1 r2

/-- the whole cycle, both holes starting at cell 1 -/
theorem cyc_run {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v c : Nat) (hv : 1 ≤ v) (hc : 1 ≤ c) :
    Rch (cyc2 (F ::: Lc) v 1 g c 1 (F ::: Rc))
      ⟨if c ∣ v then PM1 else kn3, ones (c + 2) (F ::: Lc), cyR (F ::: Rc) v 1 g⟩ := by
  have := cyc_loop hg Lc Rc v c hv hc (v - 1) 1 1 rfl (Nat.le_refl _) hv (Nat.le_refl _) hc
  rw [show v - 1 + 1 = v by omega] at this
  by_cases h : c ∣ v
  · rw [if_pos ((nxs_dvd c v hc).2 h)] at this; rw [if_pos h]; exact this
  · rw [if_neg (fun e => h ((nxs_dvd c v hc).1 e))] at this; rw [if_neg h]; exact this

end TM.Firoozbakht
