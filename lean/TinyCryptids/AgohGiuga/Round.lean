import TinyCryptids.AgohGiuga.Consume

/-!
# One base: the check, the flag, the shift; the end of a round

Tape: `N 00 I 00 J 00 K 00 S 00 R`.  `N` holds `n` (hole at cell 1 at rest), `I` holds the base
`i` (hole at cell 1), `J` (`j` cells) and `K` (`k` cells: 2, or 1 once the flag is set) have no
hole, `S = skq p (n + 1 - p)` (hole at cell `p`), `R = 101`.
-/

namespace TM.AgohGiuga
open St

local notation "F" => false
local notation "T" => true

/-- the gap between I and S -/
def gJK (j k : Nat) : List Bool :=
  [F, F] ++ List.replicate j true ++ [F, F] ++ List.replicate k true ++ [F, F]

theorem gJK_gap {j k : Nat} (hj : 1 ≤ j) (hk : 1 ≤ k) : Gap (gJK j k) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine Or.inr ⟨List.replicate (j' + 1) true ++ F :: F :: List.replicate (k' + 1) true,
    Blk.cons j' (Blk.one k'), ?_⟩
  simp [gJK]

/-- the round start of a base: the Horner run, exponent hole at cell 1 -/
def IC (n i j k p : Nat) : Cfg St := eAtC (F ::: blank) n 1 [F, F] i (gJK j k) p (n + 1 - p) 1

/-- left of S's separator, read leftwards from K's last cell -/
def Lw (n i j k : Nat) : Strm :=
  ones k (F ::: F ::: ones j (F ::: F ::: ones i (F ::: T ::: F ::: F ::: ones n (F ::: T ::: F ::: blank))))

/-- right of S: `00 101`, blank -/
def Rr : Strm := F ::: F ::: T ::: F ::: T ::: blank

/-- `t1` on I's last cell -/
def tc (n i j k p : Nat) : Cfg St :=
  cfgL t1 (ones i (F ::: T ::: F ::: F ::: ones n (F ::: T ::: F ::: blank)))
    (F ::: F ::: ones j (F ::: F ::: ones k (F ::: F ::: app (skq p (n + 1 - p)) Rr)))

/-- the Horner run and `B += R - 1` -/
theorem run_cons (n i j k p : Nat) (hn : 2 ≤ n) (hi : 1 ≤ i) (hj : 1 ≤ j) (hk : 1 ≤ k) (hp : 1 ≤ p)
    (hpn : p ≤ n) :
    Rch (IC n i j k p) (CL (F ::: Lw n i j k) (nxs n p (i ^ (n - 1) - 1))
      (n + 1 - nxs n p (i ^ (n - 1) - 1)) 1) := by
  have hg := gJK_gap hj hk
  have h1 := horner hg Gap.sep blank n 1 i p (n + 1 - p) (Nat.le_refl 1) (by omega) hi hp (by omega)
  have hr : 1 ≤ i ^ (n - 1) := Nat.pos_pow_of_pos _ hi
  refine Rch.tr h1 ?_
  refine Rch.tr (cons_entry hg n i p (n + 1 - p) (i ^ (n - 1)) blank hi hp (by omega) hr) ?_
  have e : app (gJK j k).reverse (ones i (F ::: T ::: F ::: F ::: ones n (F ::: T ::: F ::: blank))) =
      F ::: F ::: Lw n i j k := by
    simp only [gJK, Lw, List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
      List.nil_append, List.singleton_append, List.cons_append, List.append_assoc, app_append,
      app_replicate, app_cons, app_nil]
  rw [e]
  have := cons_loop (F ::: Lw n i j k) (i ^ (n - 1)) p (n + 1 - p) hr hp (by omega)
  rw [show p + (n + 1 - p) - 1 = n by omega, show p + (n + 1 - p) = n + 1 by omega] at this
  exact this

/-- after `R = 101`: S's hole at cell 1 (`B = 0`): to I's last cell -/
theorem check_zero (n i j k : Nat) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    Rch (cfgL k1 (F ::: F ::: Lw n i j k) (T ::: F ::: ones n Rr)) (tc n i j k 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold Lw tc
  gL; gL; gL
  sLn k'
  gL; gL
  sLn j
  gL; gL
  simp only [skq, List.replicate, List.singleton_append, app_cons, app_replicate, ones_succ, ones_zero,
    Nat.add_sub_cancel, ones_cons_true]
  fin

/-- after `R = 101`: S's hole at cell `p ≥ 2` (`B ≠ 0`): set the flag (`J 00 K := J1 00 1`), to
I's last cell -/
theorem check_flag (n i j k p : Nat) (hp : 2 ≤ p) (hpn : p ≤ n) (hk : k = 1 ∧ 2 ≤ j ∨ k = 2 ∧ 1 ≤ j) :
    Rch (cfgL k1 (ones (p - 1) (F ::: F ::: Lw n i j k)) (T ::: F ::: ones (n + 1 - p) Rr))
      (tc n i (j + k - 1) 1 p) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  rw [show p' + 2 - 1 = p' + 1 by omega]
  unfold Lw tc
  rcases hk with ⟨rfl, hj⟩ | ⟨rfl, hj⟩
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
    gL
    sLn p'
    gL; gL; gL; gL; gL; gL
    sLn (j' + 1)
    gL; gL
    rw [show j' + 2 + 1 - 1 = (j' + 1) + 1 by omega]
    simp only [skq, app_append, app_cons, app_replicate, ones_succ, ones_zero, ones_cons_true]
    fin
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    gL
    sLn p'
    gL; gL; gL; gL; gL; gL
    sLn (j' + 1)
    gL; gL
    rw [show j' + 1 + 2 - 1 = (j' + 1) + 1 by omega]
    simp only [skq, app_append, app_cons, app_replicate, ones_succ, ones_zero, ones_cons_true]
    fin

theorem PHG' : ParserL delta HG1 HG2 := ⟨rfl, rfl, rfl⟩
theorem PHH' : ParserL delta HH1 HH2 := ⟨rfl, rfl, rfl⟩

/-- `i -= 1`: I's last cell joins the separator, whose last cell becomes J's cell 0; then to the
exponent hole: the next base -/
theorem shift (n i j k p : Nat) (hn : 1 ≤ n) (hi : 3 ≤ i) :
    Rch (tc n i j k p) (IC n (i - 1) (j + 1) k p) := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 3 := ⟨i - 3, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [show i' + 3 - 1 = i' + 2 by omega]
  unfold tc IC eAtC
  gL; gL; gR; gR; gR; gR; gL
  show Rch (cfgL HG1 (F ::: F ::: ones (i' + 2)
    (F ::: T ::: F ::: F ::: ones (n' + 1) (F ::: T ::: F ::: blank))) _) _
  rw [show F ::: F ::: ones (i' + 2) (F ::: T ::: F ::: F ::: ones (n' + 1) (F ::: T ::: F ::: blank)) =
    app (F :: F :: List.replicate (i' + 2) true)
      (F ::: T ::: F ::: F ::: ones (n' + 1) (F ::: T ::: F ::: blank)) by
      simp only [app_cons, app_replicate]]
  refine Rch.tr (PHG'.find (by rw [List.replicate_succ]; exact Clean.sep (Clean.replicate _)) _ _) ?_
  gL
  rw [show F ::: F ::: ones (n' + 1) (F ::: T ::: F ::: blank) =
    app (F :: F :: List.replicate (n' + 1) true) (F ::: T ::: F ::: blank) by
      simp only [app_cons, app_replicate]]
  refine Rch.tr (PHH'.find (by rw [List.replicate_succ]; exact Clean.sep (Clean.replicate _)) _ _) ?_
  gR
  simp only [bH1, rgt, gJK, skq, sep, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.singleton_append, List.cons_append, List.append_assoc, app_append,
    app_replicate, app_cons, app_nil, ones_succ, ones_zero, ones_cons_true, Nat.add_sub_cancel, Rr,
    cons_blank]
  fin

theorem PPZ : ParserR delta PZ1 PZ2 := ⟨rfl, rfl, rfl⟩

/-- left of S's separator at the end of a round: K, `00`, J and the filled I/J region, `00`, N -/
def Lw2 (n j k : Nat) : Strm := ones k (F ::: F ::: ones (j + 6) (F ::: F ::: ones n (F ::: T ::: F ::: blank)))

/-- the round ends (`i = 2`): I's hole and the I/J separator are filled; a parser finds S's hole -/
theorem round_pz (n j k p : Nat) (hk : 1 ≤ k) (hp : 1 ≤ p) (hpn : p ≤ n) :
    Rch (tc n 2 j k p) ⟨z1, ones p (F ::: F ::: Lw2 n j k), F ::: ones (n + 1 - p) Rr⟩ := by
  obtain ⟨q, hq⟩ : ∃ q, n + 1 - p = q + 1 := ⟨n - p, by omega⟩
  unfold tc
  rw [hq]
  gL; gL; gR; gR; gR; gR; gR
  rw [show ones j (F ::: F ::: ones k (F ::: F ::: app (skq p (q + 1)) Rr)) =
    app (List.replicate j true ++ (F :: F :: List.replicate k true ++ (F :: F :: List.replicate p true)))
      (F ::: T ::: ones q Rr) by
    simp only [skq, app_append, app_cons, app_replicate, ones_succ, List.cons_append]]
  have hw : Clean (List.replicate j true ++ (F :: F :: List.replicate k true ++ (F :: F :: List.replicate p true))) := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    refine Clean.rep_append j ?_
    rw [List.replicate_succ, List.cons_append, List.cons_append, List.cons_append]
    exact Clean.sep (Clean.rep_append k' (by
      rw [List.replicate_succ]; exact Clean.sep (Clean.replicate p')))
  refine Rch.tr (PPZ.find hw _ _) ?_
  gL
  simp only [Lw2, List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.singleton_append, List.cons_append, List.append_assoc, app_append,
    app_replicate, app_cons, app_nil, ones_succ, ones_zero, ones_cons_true, tl_cons]
  fin

/-- `B = 0` and the flag set (`K = 1`): HALT -/
theorem round_halt (n j : Nat) :
    HaltAt ⟨z1, ones 1 (F ::: F ::: Lw2 n j 1), F ::: ones n Rr⟩ := by
  unfold Lw2 HaltAt
  apply Exists.intro; apply Exists.intro
  gL; gL; gL; gL; gL; gR
  fin

/-- `B = 0`, the flag not set: to S's cell 1 -/
theorem round_a (n j : Nat) :
    Rch ⟨z1, ones 1 (F ::: F ::: Lw2 n j 2), F ::: ones n Rr⟩
      ⟨h1, T ::: F ::: F ::: Lw2 n j 2, F ::: ones n Rr⟩ := by
  unfold Lw2
  gL; gL; gL; gL; gL; gR; gR; gR; gR; gR
  fin

/-- `B ≠ 0`: fill S's hole, to S's cell 1 -/
theorem round_b (n j k p : Nat) (hp : 2 ≤ p) (hpn : p ≤ n) :
    Rch ⟨z1, ones p (F ::: F ::: Lw2 n j k), F ::: ones (n + 1 - p) Rr⟩
      ⟨h1, T ::: F ::: F ::: Lw2 n j k, T ::: ones n Rr⟩ := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  gL; gL; gR; gR; gL
  show Rch (cfgL x1 (ones (p' + 2) (F ::: F ::: Lw2 n j k)) (T ::: ones (n + 1 - (p' + 2)) Rr)) _
  sLn (p' + 2)
  gR; gR
  rw [show ones (p' + 1) (T ::: ones (n + 1 - (p' + 2)) Rr) = T ::: ones n Rr by
    rw [← ones_succ', ones_add, ← ones_succ, show p' + 1 + 1 + (n + 1 - (p' + 2)) = n + 1 by omega]]
  fin

/-- the reset for `n + 1`, from S's cell 1 going left (S's hole filled): S grows on its left
with its hole at the new cell 1, `K := 11`, `J := 1`, `I := n` (with N's last two cells),
N grows by three cells on its left with its hole at the new cell 1 -/
theorem round_reset (n j k : Nat) (b : Bool) (hn : 3 ≤ n) (hk : k = 1 ∧ j + 1 = n ∨ k = 2 ∧ j + 2 = n) :
    Rch ⟨h1, T ::: F ::: F ::: Lw2 n j k, b ::: ones n Rr⟩ (IC (n + 1) n 1 2 1) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
  have hc : ∀ X : Strm, ones (j + 6) X = ones 4 (ones (j + 2) X) ∧ ones (j + 6) X = ones 5 (ones (j + 1) X) :=
    fun X => ⟨by rw [ones_add, show 4 + (j + 2) = j + 6 by omega],
      by rw [ones_add, show 5 + (j + 1) = j + 6 by omega]⟩
  have hN : ones (n' + 3) (F ::: T ::: F ::: blank) = T ::: T ::: ones (n' + 1) (F ::: T ::: F ::: blank) := rfl
  unfold Lw2 IC eAtC
  have hb : ∀ X Y : Strm, Rch ⟨h1, X, b ::: Y⟩ ⟨h2, tl X, X 0 ::: T ::: Y⟩ := fun X Y => by
    cases b <;> exact sL (by rfl)
  rcases hk with ⟨rfl, hj⟩ | ⟨rfl, hj⟩
  · rw [(hc _).2, show j + 1 = n' + 3 by omega]
    refine Rch.tr (hb _ _) ?_
    gL; gL; gL; gL; gL; gL; gL; gL; gL; gL; gL
    show Rch (cfgL g1 (ones (n' + 3) (F ::: F ::: ones (n' + 3) (F ::: T ::: F ::: blank))) _) _
    sLn (n' + 3)
    rw [hN]
    gL; gL; gL; gL
    sLn (n' + 1)
    gL; gL; gL; gL; gR
    simp only [bH1, rgt, gJK, skq, sep, Rr, app_append, app_replicate, app_cons, app_nil, ones_succ,
      ones_zero, ones_cons_true, Nat.add_sub_cancel, cons_blank, List.cons_append, List.nil_append,
      List.singleton_append, List.append_assoc, List.replicate]
    fin
  · rw [(hc _).1, show j + 2 = n' + 3 by omega]
    refine Rch.tr (hb _ _) ?_
    gL; gL; gL; gL; gL; gL; gL; gL; gL; gL; gL
    show Rch (cfgL g1 (ones (n' + 3) (F ::: F ::: ones (n' + 3) (F ::: T ::: F ::: blank))) _) _
    sLn (n' + 3)
    rw [hN]
    gL; gL; gL; gL
    sLn (n' + 1)
    gL; gL; gL; gL; gR
    simp only [bH1, rgt, gJK, skq, sep, Rr, app_append, app_replicate, app_cons, app_nil, ones_succ,
      ones_zero, ones_cons_true, Nat.add_sub_cancel, cons_blank, List.cons_append, List.nil_append,
      List.singleton_append, List.append_assoc, List.replicate]
    fin

end TM.AgohGiuga
