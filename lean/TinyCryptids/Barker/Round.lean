import TinyCryptids.Barker.Pass
import TinyCryptids.Barker.Fail

/-!
# One round: a pass, the rewind, the check

`Start D k c`: `c` starts the pass for shift `k` on the positions `D = 0 :: a` (the dummy, then
the candidate `a`).
-/

namespace TM.Barker
open St

local notation "F" => false
local notation "T" => true

def Start (D : List Bool) (k : Nat) (c : Cfg St) : Prop :=
  ∃ A x B y, A ++ x :: B ++ [y] = D ∧ B.length + 1 = k ∧ c = P A x B y [] 0

theorem reach1_of {a b : Cfg St} (h : Rch a b) (hq : a.q ≠ b.q) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero =>
    simp only [Sys.run] at hn
    exact absurd (congrArg Cfg.q (Option.some.inj hn)) hq
  | succ n => exact ⟨n, hn⟩

/-- the pass for shift `k = a.length`: the machine halts -/
theorem round_halt (a : List Bool) (c : Cfg St) (hc : Start (F :: a) a.length c) : HaltAt c := by
  obtain ⟨A, x, B, y, hD, hk, rfl⟩ := hc
  obtain ⟨x0, B0, y0, C0, h1, h2, h3⟩ := pass_n A.length A rfl x B y [] 0
  have hC : C0 = [] := by
    have l1 := congrArg List.length h1; have l2 := congrArg List.length hD
    simp at l1 l2; apply List.eq_nil_of_length_eq_zero; omega
  subst hC
  exact HaltAt.back (Rch.tr h3 (pass_end _ _ _ _ _)) (rw_halt _ _ _ _ _)

theorem round (a : List Bool) (k : Nat) (c : Cfg St) (hc : Start (F :: a) k c) (hk : k < a.length) :
    (Int.natAbs (psum a k) ≤ 1 → ∃ c', Start (F :: a) (k + 1) c' ∧ Rch1 c c') ∧
    (2 ≤ Int.natAbs (psum a k) → ∃ c', Start (F :: inc a) 1 c' ∧ Rch1 c c') := by
  obtain ⟨A, x, B, y, hD, hkB, rfl⟩ := hc
  obtain ⟨x0, B0, y0, C0, h1, h2, h3⟩ := pass_n A.length A rfl x B y [] 0
  have hS : (A ++ x :: B ++ [y]).tail = a := by
    simpa using congrArg List.tail hD
  rw [hS, hkB, Int.zero_add] at h3
  have hD' : x0 :: B0 ++ y0 :: C0 = F :: a := by rw [h1, ← hD]
  obtain ⟨C', z, hCz⟩ := nonempty_snoc C0 (by
    intro h; subst h; have l1 := congrArg List.length hD'; simp at l1; omega)
  subst hCz
  obtain ⟨A', x', M, e1, e2, e3⟩ := rewind C' [] x0 B0 y0 z (psum a k)
  have hK : Rch1 (P A x B y [] 0) (Kc A' x' M z (psum a k)) :=
    reach1_of (Rch.tr h3 (Rch.tr (pass_end _ _ _ _ _) e3)) (by simp [P, Kc, cfgL])
  have hD2 : A' ++ x' :: M ++ [z] = F :: a := by
    rw [← hD', show A' ++ x' :: M ++ [z] = (A' ++ x' :: M) ++ [z] by simp, e1]; simp
  have hM : M.length + 1 = k + 1 := by
    have l1 := congrArg List.length hD2; have l2 := congrArg List.length hD'
    simp at l1 l2 e2; omega
  refine ⟨fun hp => ⟨_, ⟨A', x', M, z, hD2, hM, rfl⟩, Reach1.trans_reach delta hK (check_pass _ _ _ _ _ hp)⟩,
    fun hf => ?_⟩
  -- the next candidate
  obtain ⟨r, hr⟩ : ∃ r, A' ++ x' :: M = F :: r := by
    cases A' with
    | nil => simp at hD2; exact ⟨M, by rw [hD2.1]; rfl⟩
    | cons a0 A'' => simp at hD2; exact ⟨A'' ++ x' :: M, by rw [hD2.1]; rfl⟩
  have ha : r ++ [z] = a := by
    have := hD2; rw [show A' ++ x' :: M ++ [z] = (A' ++ x' :: M) ++ [z] by simp, hr] at this
    simpa using this
  obtain ⟨G, g, z', i1, i2⟩ := inc_run r z
  refine ⟨_, ⟨G, g, [], z', by rw [ha] at i1; simpa using i1, rfl, rfl⟩, ?_⟩
  refine Reach1.trans_reach delta hK (Rch.tr (check_fail _ _ _ _ _ hf) (Rch.tr (fail_scan _ _ _ _) ?_))
  rw [hr]; exact i2

end TM.Barker
