import TinyCryptids.LehmerTau.End

/-!
# One value of `n`

`Sn n` is the start of `n` (R phase, `i = 1`, `d = 1`, P = 0). The R phase adds to P, for each
`i < n`, `Σ_{d ∣ i} Σ_{e ∣ n−i} kB kC d⁵ e⁵`; the L phase builds `M = Σ_{d ∣ n} (kC d⁵ + kA d¹¹)`;
the machine halts iff `M = P`, else it reaches `Sn (n + 1)`.
-/

namespace TM.LehmerTau
open St

local notation "F" => false

/-- the start of `n` -/
def Sn (kA kB kC n : Nat) : Cfg St := DV (LS 0 (.pl 1 :: .pl 13 :: KR kA kB kC)) (BD (n - 1)) 1 0

/-- what the pair `(i, n − i)` adds to P -/
def gI (K n i : Nat) : Nat := dsum (fun d => dsum (fun e => d ^ 5 * e ^ 5 * K) (n - i) (n - i)) i i

/-- P after `i` values -/
def rP (K n : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => rP K n i + gI K n (i + 1)

/-- M -/
def mM (kA kC n : Nat) : Nat := dsum (fun d => kC * d ^ 5 + kA * d ^ 11) n n

theorem okKR (kA kB kC : Nat) (hB : 1 ≤ kB) (hC : 1 ≤ kC) : ∀ b ∈ KR kA kB kC, b.ok := by
  intro b hb; simp [KR] at hb; rcases hb with rfl | rfl | rfl <;> simp [KB.ok] <;> omega

/-- one `i` of the R phase: the d-loop, then D unshifted -/
theorem r_one (kA kB kC : Nat) (hB : 1 ≤ kB) (hC : 1 ≤ kC) (a i j : Nat) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    Rch (DV (LS a (.pl 1 :: .pl 13 :: KR kA kB kC)) (BD j) 1 (i - 1))
      ⟨UK1, F ::: F ::: LS (a + gI (kC * kB) (i + j) i) (.pl (i + 1) :: .dg 1 1 :: .pl 1 :: .pl 13 :: KR kA kB kC), BD j⟩ := by
  have hk := okKR kA kB kC hB hC
  have hp : pK (KR kA kB kC) = kC * kB := by simp [KR, pK]
  have l := dloop' (fun a => LS a (.pl 1 :: .pl 13 :: KR kA kB kC)) (BD j)
    (fun d => dsum (fun e => d ^ 5 * e ^ 5 * pK (KR kA kB kC)) j j) i hi
    (fun a' x hx _ _ => dact_R _ hk rfl a' x (i - x) j hx hj) a
  refine Rch.tr l (Rch.tr (ud_uk _ _ i hi _) ?_)
  unfold gI; rw [hp, show i + j - i = j by omega]; fin

/-- the R phase up to `i` -/
theorem r_iter (kA kB kC : Nat) (hB : 1 ≤ kB) (hC : 1 ≤ kC) (n : Nat) :
    ∀ i, 1 ≤ i → i ≤ n - 1 →
      Rch (Sn kA kB kC n) (DV (LS (rP (kC * kB) n (i - 1)) (.pl 1 :: .pl 13 :: KR kA kB kC)) (BD (n - i)) 1 (i - 1)) := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hi
    rcases Nat.eq_zero_or_pos i with rfl | h
    · unfold Sn; simp only [rP]; fin
    · refine Rch.tr (ih h (by omega)) ?_
      have s1 := r_one kA kB kC hB hC (rP (kC * kB) n (i - 1)) i (n - i) h (by omega)
      rw [show i + (n - i) = n by omega] at s1
      refine Rch.tr s1 ?_
      have s2 := ri_next (KR kA kB kC) (rP (kC * kB) n (i - 1) + gI (kC * kB) n i) i (n - i) (by omega)
      rw [show n - i - 1 = n - (i + 1) by omega] at s2
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel, rP] at s2 ⊢
      exact s2

/-- the R phase: the start of the L phase, P = `rP (n − 1)` -/
theorem r_all (kA kB kC : Nat) (hB : 1 ≤ kB) (hC : 1 ≤ kC) (n : Nat) (hn : 2 ≤ n) :
    Rch (Sn kA kB kC n) (DV (LS 0 (.pl 1 :: .pl 13 :: KL1 kA kB kC (rP (kC * kB) n (n - 1)))) BL 1 (n - 1)) := by
  refine Rch.tr (r_iter kA kB kC hB hC n (n - 1) (by omega) (Nat.le_refl _)) ?_
  have s1 := r_one kA kB kC hB hC (rP (kC * kB) n (n - 1 - 1)) (n - 1) (n - (n - 1)) (by omega) (by omega)
  rw [show n - 1 + (n - (n - 1)) = n by omega, show n - (n - 1) = 1 by omega] at s1
  rw [show n - (n - 1) = 1 by omega]
  refine Rch.tr s1 ?_
  refine Rch.tr (ri_last kA kB kC hB hC _ (n - 1)) ?_
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega, rP]; fin

/-- **One `n`**: halt iff `M = P`, else the start of `n + 1` -/
theorem nstep (kA kB kC : Nat) (hA : 1 ≤ kA) (hB : 1 ≤ kB) (hC : 1 ≤ kC) (n : Nat) (hn : 2 ≤ n) :
    (mM kA kC n = rP (kC * kB) n (n - 1) → HaltAt (Sn kA kB kC n)) ∧
    (mM kA kC n ≠ rP (kC * kB) n (n - 1) → Rch (Sn kA kB kC n) (Sn kA kB kC (n + 1))) := by
  have s1 := r_all kA kB kC hB hC n hn
  have l := dloop' (fun m => LS m (.pl 1 :: .pl 13 :: KL1 kA kB kC (rP (kC * kB) n (n - 1)))) BL
    (fun d => kC * d ^ 5 + kA * d ^ 11) n (by omega)
    (fun a' x hx _ _ => dact_L kA kB kC _ hA hC a' x (n - x) hx) 0
  have s2 := Rch.tr s1 (Rch.tr l (ud_uk _ _ n (by omega) _))
  rw [Nat.zero_add] at s2
  have e := endn kA kB kC (rP (kC * kB) n (n - 1)) (mM kA kC n) n hA hC (by omega)
  unfold Sn
  rw [Nat.add_sub_cancel]
  exact ⟨fun h => HaltAt.back s2 (e.1 h), fun h => Rch.tr s2 (e.2 h)⟩

end TM.LehmerTau
