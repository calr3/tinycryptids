import TinyCryptids.Defs

/-!
# Arithmetic for Andrica's conjecture

* `IsT m t`: `t` is the least number with `4m ≤ t²`; then `4m ≤ g² ↔ t ≤ g` (`isT_le_iff`).
* `Hinv m t x`: the phase block H (`t + 1` cells, its hole at cell `x`) for the number `m`; it
  gives `IsT m t` (`hinv_isT`) and is kept by the machine's step (`hinv_next`).
* `lpb m`, the largest prime below `m`, and `Bad m`: `m` is composite and
  `4 · lpb m ≤ (m - lpb m)²`; some `m ≥ 3` is bad iff Andrica's conjecture fails (`bad_iff`).
-/

namespace TM.Andrica

open TinyCryptids

/-- `t` is the least number with `4m ≤ t²` -/
def IsT (m t : Nat) : Prop := 4 * m ≤ t * t ∧ (t - 1) * (t - 1) < 4 * m

theorem isT_le_iff {p a : Nat} (h : IsT p a) (g : Nat) : 4 * p ≤ g * g ↔ a ≤ g := by
  constructor
  · intro hg
    apply Classical.byContradiction; intro hlt
    have h' : g ≤ a - 1 := by omega
    have := Nat.mul_le_mul h' h'
    have := h.2; omega
  · intro hle; exact Nat.le_trans h.1 (Nat.mul_le_mul hle hle)

theorem isT_mono {p m a b : Nat} (hp : IsT p a) (hm : IsT m b) (hpm : p ≤ m) : a ≤ b := by
  apply Classical.byContradiction; intro hlt
  have h' : b ≤ a - 1 := by omega
  have := Nat.mul_le_mul h' h'
  have := hp.2; have := hm.1; omega

theorem sq_succ (u : Nat) : (u + 1) * (u + 1) = u * u + 2 * u + 1 := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega

/-! ## the phase block -/

/-- H for `m`: `t + 1` cells, the hole at cell `x = 2j - 1` where `m` is the `j`-th number with
`IsT m t` -/
def Hinv (m t x : Nat) : Prop :=
  2 ≤ t ∧ x % 2 = 1 ∧ x + 1 ≤ t ∧ 4 * m + (t + 1) % 2 = (t - 1) * (t - 1) + 2 * (x + 1)

theorem hinv_isT {m t x : Nat} (h : Hinv m t x) : IsT m t := by
  obtain ⟨h2, hx, hxt, he⟩ := h
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  rw [show u + 1 - 1 = u by omega] at he
  unfold IsT
  rw [show u + 1 - 1 = u by omega]
  constructor
  · rw [sq_succ]; omega
  · omega

/-- the next number: the hole two cells on, or (it would leave H) H grows by one cell -/
def tn (t x : Nat) : Nat := if x + 3 ≤ t then t else t + 1
def xn (t x : Nat) : Nat := if x + 3 ≤ t then x + 2 else 1

theorem hinv_next {m t x : Nat} (h : Hinv m t x) : Hinv (m + 1) (tn t x) (xn t x) := by
  obtain ⟨h2, hx, hxt, he⟩ := h
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  rw [show u + 1 - 1 = u by omega] at he
  unfold tn xn
  by_cases hw : x + 3 ≤ u + 1
  · rw [if_pos hw, if_pos hw]
    refine ⟨h2, by omega, by omega, ?_⟩
    rw [show u + 1 - 1 = u by omega]; omega
  · rw [if_neg hw, if_neg hw]
    refine ⟨by omega, rfl, by omega, ?_⟩
    rw [show u + 1 + 1 - 1 = u + 1 by omega, sq_succ]; omega

theorem tn_ge (t x : Nat) : t ≤ tn t x ∧ tn t x ≤ t + 1 := by
  unfold tn; split <;> omega

/-! ## primes -/

/-- The largest prime `< m` (0 if none). -/
def lpb : Nat → Nat
  | 0 => 0
  | m + 1 => if Prime m then m else lpb m

theorem prime_two : Prime 2 := ⟨by decide, fun d hd h2 => by omega⟩

theorem lpb_spec : ∀ m, 3 ≤ m → Prime (lpb m) ∧ lpb m < m ∧ ∀ r, lpb m < r → r < m → ¬ Prime r
  | 0, h | 1, h | 2, h => absurd h (by decide)
  | m + 1, h => by
    by_cases hp : Prime m
    · rw [lpb, if_pos hp]; exact ⟨hp, by omega, fun r h1 h2 => by omega⟩
    · rw [lpb, if_neg hp]
      by_cases h3 : 3 ≤ m
      · obtain ⟨h1, h2, h4⟩ := lpb_spec m h3
        refine ⟨h1, by omega, fun r hr1 hr2 => ?_⟩
        rcases Nat.lt_or_ge r m with hl | hl
        · exact h4 r hr1 hl
        · rwa [show r = m by omega]
      · have : m = 2 := by omega
        subst this; exact absurd prime_two hp

theorem lpb_eq {p q : Nat} (hp : Prime p) (hpq : p < q) (hgap : ∀ r, p < r → r < q → ¬ Prime r) :
    lpb q = p := by
  have h3 : 3 ≤ q := by have := hp.two_le; omega
  obtain ⟨h1, h2, h4⟩ := lpb_spec q h3
  rcases Nat.lt_trichotomy (lpb q) p with hl | he | hg
  · exact absurd hp (h4 p hl hpq)
  · exact he
  · exact absurd h1 (hgap _ hg h2)

theorem fact_pos : ∀ n, 1 ≤ fact n
  | 0 => by decide
  | n + 1 => by
    have := fact_pos n
    show 1 ≤ fact n * (n + 1)
    have := Nat.mul_le_mul this (show 1 ≤ n + 1 by omega)
    omega

theorem dvd_fact {q : Nat} (hq : 1 ≤ q) : ∀ k, q ≤ k → q ∣ fact k
  | 0, h => by omega
  | k + 1, h => by
    show q ∣ fact k * (k + 1)
    rcases Nat.lt_or_ge q (k + 1) with h' | h'
    · exact Nat.dvd_trans (dvd_fact hq k (by omega)) (Nat.dvd_mul_right _ _)
    · obtain rfl : q = k + 1 := by omega
      exact Nat.dvd_mul_left _ _

theorem exists_prime_dvd : ∀ d, 2 ≤ d → ∃ p, Prime p ∧ p ∣ d := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro hd
    by_cases hp : Prime d
    · exact ⟨d, hp, Nat.dvd_refl d⟩
    · have : ∃ e, e < d ∧ 2 ≤ e ∧ d % e = 0 := by
        apply Classical.byContradiction; intro hne
        exact hp ⟨hd, fun e h1 h2 h3 => hne ⟨e, h1, h2, h3⟩⟩
      obtain ⟨e, h1, h2, h3⟩ := this
      obtain ⟨p, hp, hpe⟩ := ih e h1 h2
      exact ⟨p, hp, Nat.dvd_trans hpe (Nat.dvd_of_mod_eq_zero h3)⟩

/-- there is a prime above every `n` (a prime factor of `n! + 1`) -/
theorem exists_prime_gt (n : Nat) : ∃ q, n < q ∧ Prime q := by
  obtain ⟨q, hq, hd⟩ := exists_prime_dvd (fact n + 1) (by have := fact_pos n; omega)
  refine ⟨q, ?_, hq⟩
  apply Classical.byContradiction; intro hle
  have h1 := dvd_fact (show 1 ≤ q by have := hq.two_le; omega) n (by omega)
  have := (Nat.dvd_add_iff_right h1).2 hd
  have := Nat.le_of_dvd (by omega) this
  have := hq.two_le; omega

/-- the prime after `p`, when `(p, m]` has no prime: it is above `m` -/
theorem next_prime {p m : Nat} (hgap : ∀ r, p < r → r ≤ m → ¬ Prime r) :
    ∀ Q, Prime Q → m < Q → ∃ q, Prime q ∧ m < q ∧ ∀ r, p < r → r < q → ¬ Prime r := by
  intro Q
  induction Q using Nat.strongRecOn with
  | _ Q ih =>
    intro hQ hmQ
    by_cases h : ∃ r, p < r ∧ r < Q ∧ Prime r
    · obtain ⟨r, h1, h2, h3⟩ := h
      have : m < r := by
        apply Classical.byContradiction; intro hle
        exact hgap r h1 (by omega) h3
      exact ih r h2 h3 this
    · exact ⟨Q, hQ, hmQ, fun r h1 h2 h3 => h ⟨r, h1, h2, h3⟩⟩

/-! ## the statement -/

/-- `m` is composite and `4p ≤ (m - p)²` for the last prime `p` below it -/
def Bad (m : Nat) : Prop := ¬ Prime m ∧ 4 * lpb m ≤ (m - lpb m) * (m - lpb m)

theorem bad_iff : (∃ m, 3 ≤ m ∧ Bad m) ↔
    ∃ p q, Prime p ∧ Prime q ∧ p < q ∧ (∀ r, p < r → r < q → ¬ Prime r) ∧ 4 * p ≤ (q - p - 1) ^ 2 := by
  constructor
  · rintro ⟨m, hm, hnp, hb⟩
    obtain ⟨hp, hlt, hgap⟩ := lpb_spec m hm
    have hgap' : ∀ r, lpb m < r → r ≤ m → ¬ Prime r := fun r h1 h2 => by
      rcases Nat.lt_or_ge r m with h | h
      · exact hgap r h1 h
      · rwa [show r = m by omega]
    obtain ⟨Q, hmQ, hQ⟩ := exists_prime_gt m
    obtain ⟨q, hq, hmq, hpq⟩ := next_prime hgap' Q hQ hmQ
    refine ⟨lpb m, q, hp, hq, by omega, hpq, ?_⟩
    have hle : m - lpb m ≤ q - lpb m - 1 := by omega
    rw [Nat.pow_two]; exact Nat.le_trans hb (Nat.mul_le_mul hle hle)
  · rintro ⟨p, q, hp, hq, hpq, hgap, hle⟩
    rw [Nat.pow_two] at hle
    have h2 := hp.two_le
    have hg : 1 ≤ q - p - 1 := by
      apply Classical.byContradiction; intro h0
      rw [show q - p - 1 = 0 by omega] at hle; omega
    have hl : lpb (q - 1) = p := lpb_eq hp (by omega) (fun r h1 h2 => hgap r h1 (by omega))
    refine ⟨q - 1, by omega, hgap (q - 1) (by omega) (by omega), ?_⟩
    rw [hl, show q - 1 - p = q - p - 1 by omega]; exact hle

end TM.Andrica
