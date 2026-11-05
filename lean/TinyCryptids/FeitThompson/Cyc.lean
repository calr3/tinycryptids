import TinyCryptids.FeitThompson.Blocks
import TinyCryptids.FeitThompson.Tac

/-!
# The divisibility cycle `CYC(counter, cycled)`

The cycled block (value `v`, left) and the counter block (value `c`, right), with a gap `g`
between them.  The cycled hole goes round once; before each of its `v` advances the counter
hole advances once.  Then the counter hole is checked (and filled): it is back at cell 1
iff `c ∣ v`; the head ends right of the counter in state `kd3` or `kn3`.
-/

namespace TM.FeitThompson
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

theorem PPC : ParserL delta PC1 PC2 := ⟨rfl, rfl, rfl⟩
theorem PPN : ParserR delta PN1 PN2 := ⟨rfl, rfl, rfl⟩
theorem PPK : ParserR delta PK1 PK2 := ⟨rfl, rfl, rfl⟩

/-- the tape left of the counter: the gap, then the cycled block with its hole at `j` -/
def cyL (Lc : Strm) (v j : Nat) (g : List Bool) : Strm :=
  app g.reverse (ones (v + 1 - j) (false ::: ones j Lc))

/-- the counter hole at cell `i` was just filled; head on cell `i + 1` -/
def cyc2 (Lc : Strm) (v j : Nat) (g : List Bool) (c i : Nat) (Rc : Strm) : Cfg St :=
  ⟨ca2, ones (i + 1) (cyL Lc v j g), ones (c + 1 - i) Rc⟩

/-- from the counter (parser `PC`) to the cycled hole, one advance, back to the counter -/
theorem pc_part {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v j c a b : Nat)
    (hj : 1 ≤ j) (hjv : j < v) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : b = c + 1 - a) :
    Rch (cfgL PC1 (ones a (cyL Lc v j g)) (false ::: ones b Rc)) (cyc2 Lc v (j + 1) g c a Rc) := by
  obtain ⟨n, hn⟩ : ∃ n, v + 1 - j = n + 2 := ⟨v - j - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hw : Clean (List.replicate (a' + 1) true ++ (g.reverse ++ List.replicate (n + 2) true)) :=
    Clean.rep_append _ (by rw [List.replicate_succ]; exact hg.reverse.clean (Clean.replicate _))
  have e : ones (a' + 1) (cyL Lc v (j' + 1) g) =
      app (List.replicate (a' + 1) true ++ (g.reverse ++ List.replicate (n + 2) true))
        (false ::: true ::: ones j' Lc) := by
    simp only [cyL, hn, app_append, app_replicate, ones_succ]
  rw [e]
  refine Rch.tr (PPC.find hw _ _) ?_
  gR
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_reverse, app_append,
    app_replicate]
  gR; gR; gL; gR
  show Rch ⟨PN1, false ::: true ::: true ::: ones j' Lc,
    ones (n + 1) (app g (ones (a' + 1) (false ::: ones (b' + 1) Rc)))⟩ _
  have hw2 : Clean (List.replicate (n + 1) true ++ (g ++ List.replicate (a' + 1) true)) :=
    Clean.rep_append _ (by rw [List.replicate_succ]; exact hg.clean (Clean.replicate _))
  have e2 : ones (n + 1) (app g (ones (a' + 1) (false ::: ones (b' + 1) Rc))) =
      app (List.replicate (n + 1) true ++ (g ++ List.replicate (a' + 1) true))
        (false ::: true ::: ones b' Rc) := by
    simp only [app_append, app_replicate, ones_succ]
  rw [e2]
  refine Rch.tr (PPN.find hw2 _ _) ?_
  gL; gR
  unfold cyc2 cyL
  rw [show v + 1 - (j' + 1 + 1) = n + 1 by omega, show c + 1 - (a' + 1) = b' + 1 by omega]
  simp only [List.reverse_append, List.reverse_replicate, app_append, app_replicate, ones_succ]
  fin

/-- counter advance without wrap -/
theorem ctr_nowrap (Lc Rc : Strm) (g : List Bool) (v j c i : Nat) (hi : i < c) :
    Rch (cyc2 Lc v j g c i Rc) (cfgL PC1 (ones (i + 1) (cyL Lc v j g)) (false ::: ones (c - i) Rc)) := by
  obtain ⟨k, hk⟩ : ∃ k, c + 1 - i = k + 2 := ⟨c - 1 - i, by omega⟩
  unfold cyc2; rw [hk, show c - i = k + 1 by omega]
  gR; gL; gL; fin

/-- counter advance with wrap: from its last cell back to cell 1 -/
theorem ctr_wrap {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v j c : Nat) :
    Rch (cyc2 Lc v j g c c (false ::: Rc)) (cfgL PC1 (ones 1 (cyL Lc v j g)) (false ::: ones c (false ::: Rc))) := by
  obtain ⟨g', hg'⟩ := hg.rev_head
  unfold cyc2; rw [show c + 1 - c = 1 by omega]
  gR; gL
  sLn (c + 2)
  unfold cyL; rw [hg']
  simp only [app_cons]
  gR; gR
  rw [ones_succ]
  gL; fin

/-- the last step: the cycled hole wraps; the counter hole (at `a`) is checked and filled -/
theorem pc_last {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v c a b : Nat)
    (hv : 1 ≤ v) (ha : 1 ≤ a) (hac : a ≤ c) (hab : b = c + 1 - a) :
    Rch (cfgL PC1 (ones a (cyL (false ::: Lc) v v g)) (false ::: ones b Rc))
      ⟨if a = 1 then kd3 else kn3, ones (c + 2) (cyL (false ::: Lc) v 1 g), Rc⟩ := by
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hw : Clean (List.replicate (a' + 1) true ++ (g.reverse ++ [true])) :=
    Clean.rep_append _ (hg.reverse.clean Clean.nil)
  have e : ones (a' + 1) (cyL (false ::: Lc) (v' + 1) (v' + 1) g) =
      app (List.replicate (a' + 1) true ++ (g.reverse ++ [true]))
        (false ::: true ::: ones v' (false ::: Lc)) := by
    simp only [cyL, Nat.add_sub_cancel_left, show v' + 1 + 1 - (v' + 1) = 1 by omega, app_append,
      app_replicate, ones_succ, app_cons, app_nil, ones_zero]
  rw [e]
  refine Rch.tr (PPC.find hw _ _) ?_
  obtain ⟨g', hg'⟩ := hg.head
  gR
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_reverse, app_append,
    app_replicate, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    app_cons, app_nil]
  rw [hg']
  simp only [app_cons]
  gR; gR; gL
  sLn (v' + 1 + 2)
  gR; gR; gR
  show Rch ⟨PK1, false ::: true ::: false ::: Lc,
    ones (v' + 1) (app (false :: g') (ones (a' + 1) (false ::: ones (b' + 1) Rc)))⟩ _
  rw [← hg']
  have hw2 : Clean (List.replicate (v' + 1) true ++ (g ++ List.replicate (a' + 1) true)) :=
    Clean.rep_append _ (by rw [List.replicate_succ]; exact hg.clean (Clean.replicate _))
  have e2 : ones (v' + 1) (app g (ones (a' + 1) (false ::: ones (b' + 1) Rc))) =
      app (List.replicate (v' + 1) true ++ (g ++ List.replicate (a' + 1) true))
        (false ::: true ::: ones b' Rc) := by
    simp only [app_append, app_replicate, ones_succ]
  rw [e2]
  refine Rch.tr (PPK.find hw2 _ _) ?_
  gL; gL
  simp only [List.reverse_append, List.reverse_replicate, app_append, app_replicate]
  obtain ⟨g'', hg''⟩ := hg.rev_head
  have ec : cyL (false ::: Lc) (v' + 1) 1 g =
      app g.reverse (ones (v' + 1) (false ::: true ::: false ::: Lc)) := by
    simp only [cyL, show v' + 1 + 1 - 1 = v' + 1 by omega, ones_succ, ones_zero]
  rw [ec]
  cases a' with
  | zero =>
    rw [if_pos rfl]
    obtain rfl : c = b' + 1 := by omega
    rw [hg'']; simp only [app_cons, ones_succ, ones_zero]
    gL; gR
    sRn (b' + 3); fin
  | succ a'' =>
    rw [if_neg (by omega)]
    obtain rfl : c = b' + a'' + 2 := by omega
    rw [ones_succ]
    gL; gR
    sRn (b' + 3)
    show Rch ⟨kn3, ones (b' + 3) (ones (a'' + 1)
      (app g.reverse (ones (v' + 1) (false ::: true ::: false ::: Lc)))), Rc⟩ _
    rw [ones_add, show b' + 3 + (a'' + 1) = b' + a'' + 2 + 2 by omega]; fin

theorem ctr_adv {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v j c i : Nat) (hi : i ≤ c) :
    Rch (cyc2 Lc v j g c i (false ::: Rc))
      (cfgL PC1 (ones (nx c i) (cyL Lc v j g)) (false ::: ones (c + 1 - nx c i) (false ::: Rc))) := by
  unfold nx
  split
  · rw [show c + 1 - (i + 1) = c - i by omega]; exact ctr_nowrap Lc _ g v j c i (by assumption)
  · have e : c = i := by omega
    subst e
    rw [show c + 1 - 1 = c by omega]; exact ctr_wrap hg Lc Rc v j c

theorem cyc_loop {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v c : Nat) (hv : 1 ≤ v) (hc : 1 ≤ c) :
    ∀ n j i, v - j = n → 1 ≤ j → j ≤ v → 1 ≤ i → i ≤ c →
    Rch (cyc2 (false ::: Lc) v j g c i (false ::: Rc))
      ⟨if nxs c i (n + 1) = 1 then kd3 else kn3, ones (c + 2) (cyL (false ::: Lc) v 1 g), false ::: Rc⟩ := by
  intro n
  induction n with
  | zero =>
    intro j i hn hj hjv hi hic
    have e : v = j := by omega
    subst e
    have ⟨r1, r2⟩ := nx_range (c := c) hi hic
    refine Rch.tr (ctr_adv hg _ Rc v v c i hic) ?_
    exact pc_last hg Lc _ v c _ _ hj r1 r2 rfl
  | succ n ih =>
    intro j i hn hj hjv hi hic
    have ⟨r1, r2⟩ := nx_range (c := c) hi hic
    refine Rch.tr (ctr_adv hg _ Rc v j c i hic) ?_
    refine Rch.tr (pc_part hg _ _ v j c _ _ hj (by omega) r1 (by omega) rfl) ?_
    exact ih (j + 1) (nx c i) (by omega) (by omega) (by omega) r1 r2

/-- the whole cycle, both holes starting at cell 1 -/
theorem cyc_run {g : List Bool} (hg : Gap g) (Lc Rc : Strm) (v c : Nat) (hv : 1 ≤ v) (hc : 1 ≤ c) :
    Rch (cyc2 (false ::: Lc) v 1 g c 1 (false ::: Rc))
      ⟨if c ∣ v then kd3 else kn3, ones (c + 2) (cyL (false ::: Lc) v 1 g), false ::: Rc⟩ := by
  have := cyc_loop hg Lc Rc v c hv hc (v - 1) 1 1 rfl (Nat.le_refl _) hv (Nat.le_refl _) hc
  rw [show v - 1 + 1 = v by omega] at this
  by_cases h : c ∣ v
  · rw [if_pos ((nxs_dvd c v hc).2 h)] at this; rw [if_pos h]; exact this
  · rw [if_neg (fun e => h ((nxs_dvd c v hc).1 e))] at this; rw [if_neg h]; exact this

end TM.FeitThompson
