import TinyCryptids.LehmerTau.Copy

/-!
# The divisor loop

`dloop`: if the action at every divisor `x` of `N` takes `DV` (with the accumulator `a`
somewhere in the tape `Xs a`) to the resume configuration `RS3` with `a + g x`, the frame
engine goes through all divisors and ends in `F2` with `a + Σ_{x ∣ N} g x`.
-/

namespace TM.LehmerTau
open St

local notation "F" => false

/-- resume, the head one cell further right than in `RS` (on X's cell 2 + 1) -/
def RS3 (X B : Strm) (x r : Nat) : Cfg St :=
  ⟨rsm, true ::: F ::: ones 1 (F ::: F ::: X), ones (x - 1) (F ::: F ::: RB r B)⟩

theorem rs_rs3 (X B : Strm) (x r : Nat) (hx : 1 ≤ x) : Rch (RS X B x r) (RS3 X B x r) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  unfold RS RS3; gR; fin

theorem resume3_zero (X B : Strm) (x : Nat) (hx : 1 ≤ x) : Rch (RS3 X B x 0) (F2 X B x) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  unfold RS3 F2 RB
  rw [show y + 1 - 1 = y by omega]
  sRn y; gR; gR; gR; gR
  rw [show ones y (true ::: F ::: ones 1 (F ::: F ::: X)) = ones (y + 1) (F ::: true ::: F ::: F ::: X) by
    rw [ones_succ' y]; rfl]
  gL; fin

theorem resume3_more (X B : Strm) (x r : Nat) (hx : 1 ≤ x) (hr : 1 ≤ r) : Rch (RS3 X B x r) (SH X B x r) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  unfold RS3 SH RB
  rw [show y + 1 - 1 = y by omega]
  sRn y; gR; gR; gR; gR; gL
  show Rch (cfgL PSx1 (ones 2 (F ::: F ::: ones y (true ::: F ::: ones 1 (F ::: F ::: X)))) _) _
  rw [← ones_succ']
  refine Rch.tr (PPSx.find2 2 y _ _) ?_
  gR; gR; fin

/-- the sum of `g d` over the divisors `d ≤ k` of `N` -/
def dsum (g : Nat → Nat) (N : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => dsum g N k + if N % (k + 1) = 0 then g (k + 1) else 0

theorem dsum_mono (g : Nat → Nat) (N : Nat) {a b : Nat} (h : a ≤ b) : dsum g N a ≤ dsum g N b := by
  induction b with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (by simp only [dsum]; omega)

/-- no divisors strictly between `x` and `y` -/
theorem dsum_gap (g : Nat → Nat) (N x : Nat) :
    ∀ y, x < y → (∀ z, x < z → z < y → N % z ≠ 0) → dsum g N (y - 1) = dsum g N x := by
  intro y
  induction y with
  | zero => intro h; omega
  | succ y ih =>
    intro hxy hz
    rcases Nat.eq_or_lt_of_le (show x ≤ y by omega) with rfl | h
    · rfl
    · rw [show y + 1 - 1 = y by omega]
      obtain ⟨w, rfl⟩ : ∃ w, y = w + 1 := ⟨y - 1, by omega⟩
      simp only [dsum, if_neg (hz (w + 1) h (by omega))]
      have := ih (by omega) (fun z h1 h2 => hz z h1 (by omega))
      rw [show w + 1 - 1 = w by omega] at this; omega

theorem dsum_div (g : Nat → Nat) (N x : Nat) (hx : 1 ≤ x) (hd : N % x = 0) :
    dsum g N x = dsum g N (x - 1) + g x := by
  obtain ⟨w, rfl⟩ : ∃ w, x = w + 1 := ⟨x - 1, by omega⟩
  simp [dsum, hd]

/-- **The divisor loop** -/
theorem dloop (Xs : Nat → Strm) (B : Strm) (g : Nat → Nat) (N : Nat)
    (act : ∀ a x, 1 ≤ x → x ≤ N → N % x = 0 →
      Rch (DV (Xs a) B x (N - x)) (RS3 (Xs (a + g x)) B x (N - x))) :
    ∀ k a x, N - x = k → 1 ≤ x → x ≤ N → N % x = 0 →
      Rch (DV (Xs a) B x (N - x)) (F2 (Xs (a + dsum g N N - dsum g N (x - 1))) B N) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro a x hk hx hxN hd
  have s1 := act a x hx hxN hd
  have e1 := dsum_div g N x hx hd
  have m1 := dsum_mono g N hxN
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · obtain rfl : x = N := by omega
    refine Rch.tr s1 ?_
    rw [Nat.sub_self]
    have := resume3_zero (Xs (a + g x)) B x hx
    rw [show a + dsum g x x - dsum g x (x - 1) = a + g x by omega]; exact this
  · refine Rch.tr s1 (Rch.tr (resume3_more _ B x (N - x) hx (by omega)) ?_)
    obtain ⟨y, h1, h2, h3, h4, h5⟩ := next_div (Xs (a + g x)) B (N - x) x hx (by omega)
    rw [show x + (N - x) = N by omega] at h2 h3 h4 h5
    refine Rch.tr h5 ?_
    have := ih (N - y) (by omega) (a + g x) y rfl (by omega) h2 h3
    have e2 := dsum_gap g N x y h1 h4
    have m2 := dsum_mono g N h2
    rw [show a + g x + dsum g N N - dsum g N (y - 1) = a + dsum g N N - dsum g N (x - 1) by omega] at this
    exact this

theorem dloop' (Xs : Nat → Strm) (B : Strm) (g : Nat → Nat) (N : Nat) (hN : 1 ≤ N)
    (act : ∀ a x, 1 ≤ x → x ≤ N → N % x = 0 →
      Rch (DV (Xs a) B x (N - x)) (RS3 (Xs (a + g x)) B x (N - x))) (a : Nat) :
    Rch (DV (Xs a) B 1 (N - 1)) (F2 (Xs (a + dsum g N N)) B N) := by
  have := dloop Xs B g N act (N - 1) a 1 rfl (Nat.le_refl _) hN (Nat.mod_one N)
  simpa [dsum] using this

/-- the loop from a resume (the action at `x` done, `g x` added) -/
theorem dloopR (Xs : Nat → Strm) (B : Strm) (g : Nat → Nat) (N : Nat)
    (act : ∀ a x, 1 ≤ x → x ≤ N → N % x = 0 →
      Rch (DV (Xs a) B x (N - x)) (RS3 (Xs (a + g x)) B x (N - x))) :
    ∀ k a x, N - x = k → 1 ≤ x → x ≤ N →
      Rch (RS3 (Xs a) B x (N - x)) (F2 (Xs (a + dsum g N N - dsum g N x)) B N) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro a x hk hx hxN
  have m1 := dsum_mono g N hxN
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · obtain rfl : x = N := by omega
    rw [Nat.sub_self, show a + dsum g x x - dsum g x x = a by omega]
    exact resume3_zero _ B x hx
  · refine Rch.tr (resume3_more _ B x (N - x) hx (by omega)) ?_
    obtain ⟨y, h1, h2, h3, h4, h5⟩ := next_div (Xs a) B (N - x) x hx (by omega)
    rw [show x + (N - x) = N by omega] at h2 h3 h4 h5
    refine Rch.tr h5 (Rch.tr (act a y (by omega) h2 h3) ?_)
    have := ih (N - y) (by omega) (a + g y) y rfl (by omega) h2
    have e1 := dsum_div g N y (by omega) h3
    have e2 := dsum_gap g N x y h1 h4
    have m2 := dsum_mono g N h2
    rw [show a + g y + dsum g N N - dsum g N y = a + dsum g N N - dsum g N x by omega] at this
    exact this

end TM.LehmerTau
