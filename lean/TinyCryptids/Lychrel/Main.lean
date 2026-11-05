import TinyCryptids.Lychrel.Cmp
import TinyCryptids.Defs

/-!
# Main theorem: the design halts iff reverse-and-add from 196 reaches a palindrome
-/

namespace TM.Lychrel

open TinyCryptids
open St

local notation "F" => false

/-! ## digit reversal -/

theorem rv0 (acc : Nat) : revAux 0 acc = acc := by rw [revAux]; simp

theorem rv_pos {n : Nat} (h : n ≠ 0) (acc : Nat) :
    revAux n acc = revAux (n / 10) (acc * 10 + n % 10) := by
  rw [revAux]; simp [h]

theorem rev10_eq (x : Nat) : revAux (x / 10) (x % 10) = rev10 x := by
  unfold rev10
  by_cases hx : x = 0
  · subst hx; rfl
  · rw [rv_pos hx, Nat.zero_mul, Nat.zero_add]

/-! ## the reversal loop -/

/-- between two iterations: T has `t + 3` cells, A has `a + 1`, p = 0 -/
def IT (x g t a : Nat) : Cfg St := PL x g 0 (t + 3) (a + 1) 0

/-- one iteration with t > 0: A := 10 A + t % 10, T := t / 10 -/
theorem iter_one (x g t a : Nat) (hg : 2 ≤ g) (ht : 1 ≤ t) :
    Rch (IT x g t a) (IT x (g + 3 + t + 3 + 2 + a) (t / 10) (a * 10 + t % 10)) := by
  have h1 := pl_next x g (t + 3) (a + 1) hg (by omega) (by omega)
  rw [show t + 3 - 3 = t by omega, show a + 1 - 1 = a by omega] at h1
  have h2 := divide (cxg x g) (CX_gap x (g + 1)) t 2 a (Nat.le_refl _)
  have h3 := wd_erase x (g + 3) t (t % 10) 2 a (t / 10 + 3) (by omega)
    (by have := Nat.mod_lt t (show 10 > 0 by decide); omega) (Nat.le_refl _) (by omega)
  have h4 := multiply x (g + 3 + t + 3 + 2) a (t / 10 + 3) (t % 10) (by omega) (by omega)
    (by have := Nat.mod_lt t (show 10 > 0 by decide); omega)
  unfold IT
  rw [show a * 10 + t % 10 + 1 = 1 + t % 10 + 10 * a by omega]
  exact Rch.tr h1 (Rch.tr h2 (Rch.tr h3 h4))

theorem rev_loop (x : Nat) :
    ∀ t g a, 2 ≤ g → ∃ g', 2 ≤ g' ∧ Rch (IT x g t a) (IT x g' 0 (revAux t a)) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro g a hg
    by_cases ht : t = 0
    · subst ht; rw [rv0]; exact ⟨g, hg, Reach.refl delta _⟩
    · obtain ⟨g', hg', h⟩ := ih (t / 10) (Nat.div_lt_self (by omega) (by decide))
        (g + 3 + t + 3 + 2 + a) (a * 10 + t % 10) (by omega)
      rw [rv_pos ht]
      exact ⟨g', hg', Rch.tr (iter_one x g t a hg (by omega)) h⟩

/-! ## the compare -/

theorem k_walk (x G a : Nat) (hG : 1 ≤ G) :
    ∀ k, k ≤ x → k ≤ a → Rch (K (x + 1) 1 G a) (K (x + 1 - k) (1 + 2 * k) G (a - k)) := by
  intro k
  induction k with
  | zero => intro _ _; exact Reach.refl delta _
  | succ k ih =>
    intro hx ha
    refine Rch.tr (ih (by omega) (by omega)) ?_
    have := k_step (x - k - 1) (1 + 2 * k) G (a - k - 1) (by omega) hG
    rw [show x - k - 1 + 2 = x + 1 - k by omega, show a - k - 1 + 1 = a - k by omega,
      show x - k - 1 + 1 = x + 1 - (k + 1) by omega, show 1 + 2 * k + 2 = 1 + 2 * (k + 1) by omega,
      show a - k - 1 = a - (k + 1) by omega] at this
    exact this

theorem n_walk (G m : Nat) (hG : 1 ≤ G) :
    ∀ i n, 1 ≤ n → Rch (N n G (m + i)) (N (n + i) G m) := by
  intro i
  induction i with
  | zero => intro n _; exact Reach.refl delta _
  | succ i ih =>
    intro n hn
    have := n_step n G (m + i) hn hG
    refine Rch.tr this ?_
    rw [show n + (i + 1) = n + 1 + i by omega]
    exact ih (n + 1) (by omega)

theorem compare (x a G : Nat) (hG : 1 ≤ G) :
    (a = x → HaltAt (K (x + 1) 1 G a)) ∧
    (a ≠ x → Rch (K (x + 1) 1 G a) (DV [] (x + a) 1 9 G 0 none)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    have := k_walk a G a hG a (Nat.le_refl _) (Nat.le_refl _)
    rw [Nat.sub_self, show a + 1 - a = 1 by omega] at this
    exact HaltAt.back this (k_halt _ G (by omega) hG)
  · rcases Nat.lt_or_gt_of_ne h with hl | hl
    · have h1 := k_walk x G a hG a (by omega) (Nat.le_refl _)
      rw [Nat.sub_self, show x + 1 - a = (x - a - 1) + 2 by omega] at h1
      have h2 := k_end (x - a - 1) (1 + 2 * a) G (by omega) hG
      rw [show x - a - 1 + (1 + 2 * a) = x + a by omega] at h2
      exact Rch.tr h1 h2
    · have h1 := k_walk x G a hG x (Nat.le_refl _) (by omega)
      rw [show x + 1 - x = 1 by omega, show a - x = (a - x - 1) + 1 by omega] at h1
      have h2 := k_one (1 + 2 * x) G (a - x - 1) (by omega) hG
      have h3 := n_walk G 0 hG (a - x - 1) (1 + 2 * x + 3) (by omega)
      rw [Nat.zero_add, show 1 + 2 * x + 3 + (a - x - 1) = (x + a) + 3 by omega] at h3
      exact Rch.tr h1 (Rch.tr h2 (Rch.tr h3 (n_end (x + a) G hG)))

/-! ## one round -/

/-- the start of a round for x: T is X with its hole at cell 1, A = 0, p = 9 -/
def RD (x G : Nat) : Cfg St := DV [] x 1 9 G 0 none

/-- a round up to the compare -/
theorem to_cmp (x G : Nat) (hG : 2 ≤ G) :
    ∃ g, 2 ≤ g ∧ Rch (RD x G) (WD [] x (x % 10) G 0 (some (x / 10 + 3))) ∧
      Rch (WD [] x (x % 10) G 0 (some (x / 10 + 3))) (K (x + 1) 1 (g + 8) (rev10 x)) := by
  have hm := Nat.mod_lt x (show 10 > 0 by decide)
  have h2 := wd_keep x (x % 10) G 0 (x / 10 + 3) (by omega) hG (by omega)
  have h3 := multiply x G 0 (x / 10 + 3) (x % 10) hG (by omega) (by omega)
  obtain ⟨g, hg, h4⟩ := rev_loop x (x / 10) G (x % 10) hG
  have h5 := pl_zero x g (rev10 x + 1) hg (by omega)
  rw [rev10_eq] at h4
  rw [Nat.add_sub_cancel] at h5
  refine ⟨g, hg, divide [] CX_nil x G 0 hG, Rch.tr h2 (Rch.tr ?_ (Rch.tr h4 h5))⟩
  unfold IT
  rw [show 1 + x % 10 + 10 * 0 = x % 10 + 1 by omega, Nat.add_zero] at h3
  exact h3

theorem round_halt (x G : Nat) (hG : 2 ≤ G) (h : rev10 x = x) : HaltAt (RD x G) := by
  obtain ⟨g, _, h1, h2⟩ := to_cmp x G hG
  exact HaltAt.back (Rch.tr h1 h2) ((compare x (rev10 x) (g + 8) (by omega)).1 h)

/-- a run between two different configurations takes at least one step -/
theorem reach1_of_ne {a b : Cfg St} (h : Rch a b) (hne : a ≠ b) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem round_next (x G : Nat) (hG : 2 ≤ G) (h : rev10 x ≠ x) :
    ∃ G', 2 ≤ G' ∧ Rch1 (RD x G) (RD (x + rev10 x) G') := by
  obtain ⟨g, _, h1, h2⟩ := to_cmp x G hG
  refine ⟨g + 8, by omega, Reach1.trans_reach delta (reach1_of_ne h1 ?_)
    (Rch.tr h2 ((compare x (rev10 x) (g + 8) (by omega)).2 h))⟩
  intro e
  have := congrArg Cfg.q e
  cases this

/-! ## the seed and the search -/

/-- a right step, also on the blank part of the tape -/
macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))

/-- the step of the search -/
def Fs (x : Nat) : Nat := x + rev10 x

theorem seed_reach : ∃ G, 2 ≤ G ∧ Rch start (RD 196 G) := by
  have h0 : Rch start (cfgL hBP (ones 0 (F ::: F ::: ones 8 (F ::: F ::: ones (1 + 1) (zeros 2 (ones (1 + 3)
      (F ::: F ::: ones (10 - 9) (F ::: ones (9 + 1) blank))))))) (true ::: blank)) := by
    unfold start
    gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
    gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
    refine blankR ?_; gL
    fin
  have h1 := hb_back 1 2 1 8 0 9 (Nat.le_refl _) (by decide) (by decide)
  have h2 := multiply 1 2 1 8 9 (Nat.le_refl _) (by decide) (by decide)
  obtain ⟨g, hg, h3⟩ := rev_loop 1 5 3 19 (by decide)
  have e : revAux 5 19 = 195 := by rw [rv_pos (by decide), show 5 / 10 = 0 by decide, rv0]
  rw [e] at h3
  have h4 := pl_zero 1 g 196 hg (by decide)
  have h5 := (compare 1 195 (g + 8) (by omega)).2 (by decide)
  refine ⟨g + 8, by omega, Rch.tr h0 (Rch.tr h1 (Rch.tr h2 (Rch.tr h3 (Rch.tr h4 h5))))⟩

/-- before round `k`, if the rounds before it found no palindrome -/
theorem reach_k : ∀ k, (∀ j, j < k → rev10 (iterate Fs j 196) ≠ iterate Fs j 196) →
    ∃ G, 2 ≤ G ∧ Rch start (RD (iterate Fs k 196) G)
  | 0, _ => seed_reach
  | k + 1, h => by
    obtain ⟨G, hG, r⟩ := reach_k k (fun j hj => h j (by omega))
    obtain ⟨G', hG', r'⟩ := round_next _ G hG (h k (by omega))
    exact ⟨G', hG', Rch.tr r r'.reach⟩

/-- If some `iterate Fs k 196` is a palindrome, the machine reaches its halting state. -/
theorem haltAt_of (h : ∃ k, rev10 (iterate (fun x => x + rev10 x) k 196) =
    iterate (fun x => x + rev10 x) k 196) : HaltAt start := by
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hj : ∃ j, j < k ∧ rev10 (iterate Fs j 196) = iterate Fs j 196
    · obtain ⟨j, hjk, hj⟩ := hj
      exact ih j hjk hj
    · obtain ⟨G, hG, r⟩ := reach_k k (fun j hjk e => hj ⟨j, hjk, e⟩)
      exact HaltAt.back r (round_halt _ G hG hk)

/-- **Main theorem.** Started on a blank tape, the design halts if and only if
reverse-and-add from 196 reaches a palindrome. -/
theorem halts_iff : Halts delta start ↔
    ∃ k, rev10 (iterate (fun x => x + rev10 x) k 196) = iterate (fun x => x + rev10 x) k 196 := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hn
    have hall : ∀ k, rev10 (iterate Fs k 196) ≠ iterate Fs k 196 := fun k e => hn ⟨k, e⟩
    obtain ⟨G, hG, r⟩ := reach_k 0 (fun j hj => absurd hj (Nat.not_lt_zero _))
    refine not_halts_of_progress delta (fun c => ∃ k G, 2 ≤ G ∧ c = RD (iterate Fs k 196) G) ?_
      _ ⟨0, G, hG, rfl⟩ (Sys.Halts.of_reach r hH)
    rintro c ⟨k, G, hG, rfl⟩
    obtain ⟨G', hG', r'⟩ := round_next _ G hG (hall k)
    exact ⟨_, ⟨k + 1, G', hG', rfl⟩, r'⟩
  · intro h; exact (haltAt_of h).halts

end TM.Lychrel
