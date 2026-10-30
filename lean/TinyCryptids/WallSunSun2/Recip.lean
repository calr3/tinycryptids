import TinyCryptids.WallSunSun2.Gauss

/-!
# `q ∣ F (wssIndex q)` for every prime `q`

`S n = Σ C(n, 2j+1) 5^j` and `T n = Σ C(n, 2j) 5^j` satisfy `2 S n = 2^n F n` and
`2 T n + 2^n F n = 2^(n+1) F (n+1)` (`ST_fib`; `(1 + √5)^n = T n + S n √5`). For an odd prime
`q = 2h + 1`, `S q ≡ 5^h` and `T q ≡ 1 (mod q)` (all other binomial coefficients are
multiples of `q`), so with Fermat `F q ≡ 5^h` and `2 + 2 F q ≡ 4 F (q + 1)`. Gauss's lemma gives
`5^h ≡ ±1` by `q mod 5`: `+1` makes `q ∣ F (q - 1)`, `-1` makes `q ∣ F (q + 1)`.
-/

set_option linter.unusedSectionVars false

namespace TM.WallSunSun2
open TinyCryptids

def S (n : Nat) : Nat := ssum (fun j => choose n (2 * j + 1) * 5 ^ j) (n + 1)
def T (n : Nat) : Nat := ssum (fun j => choose n (2 * j) * 5 ^ j) (n + 1)

theorem choose_zero (n : Nat) : choose n 0 = 1 := by cases n <;> rfl

theorem S_succ (n : Nat) : S (n + 1) = S n + T n := by
  unfold S T
  rw [ssum_ext (n + 1 + 1) (g := fun j => choose n (2 * j) * 5 ^ j + choose n (2 * j + 1) * 5 ^ j)
    (fun j _ => by show (choose n (2 * j) + choose n (2 * j + 1)) * 5 ^ j = _; rw [Nat.add_mul]), ssum_add]
  show ssum _ (n + 1) + choose n (2 * (n + 1)) * 5 ^ (n + 1) +
    (ssum _ (n + 1) + choose n (2 * (n + 1) + 1) * 5 ^ (n + 1)) = _
  rw [choose_lt n (2 * (n + 1)) (by omega), choose_lt n (2 * (n + 1) + 1) (by omega)]
  omega

theorem T_succ (n : Nat) : T (n + 1) = T n + 5 * S n := by
  unfold S T
  rw [ssum_shift, ssum_shift (fun j => choose n (2 * j) * 5 ^ j)]
  simp only [Nat.mul_zero, choose_zero, Nat.pow_zero, Nat.mul_one]
  rw [ssum_ext (n + 1) (g := fun j => choose n (2 * j + 1) * 5 ^ j * 5 + choose n (2 * (j + 1)) * 5 ^ (j + 1))
    (fun j _ => by
      show (choose n (2 * j + 1) + choose n (2 * j + 1 + 1)) * 5 ^ (j + 1) =
        choose n (2 * j + 1) * 5 ^ j * 5 + choose n (2 * j + 1 + 1) * 5 ^ (j + 1)
      rw [Nat.add_mul, Nat.pow_succ, Nat.mul_assoc]), ssum_add, ssum_mul]
  show 1 + (ssum _ (n + 1) * 5 + (ssum (fun j => choose n (2 * (j + 1)) * 5 ^ (j + 1)) n +
    choose n (2 * (n + 1)) * 5 ^ (n + 1))) = _
  rw [choose_lt n (2 * (n + 1)) (by omega), Nat.zero_mul, Nat.add_zero]
  omega

theorem ST_fib : ∀ n, 2 * S n = 2 ^ n * fib n ∧ 2 * T n + 2 ^ n * fib n = 2 ^ (n + 1) * fib (n + 1)
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := ST_fib n
    rw [S_succ, T_succ]
    have e : 2 ^ (n + 1 + 1) * fib (n + 1 + 1) = 4 * (2 ^ n * fib n) + 2 * (2 ^ (n + 1) * fib (n + 1)) := by
      rw [fib_add_two, Nat.pow_succ, Nat.pow_succ]
      generalize 2 ^ n = A; generalize fib n = B; generalize fib (n + 1) = C
      ring_n
    rw [e]; omega

/-- `ssum f n ≡ f h (mod d)` when every other term is a multiple of `d` -/
theorem ssum_single {d h : Nat} {f : Nat → Nat} : ∀ n, h < n → (∀ j, j < n → j ≠ h → d ∣ f j) →
    ∃ c, ssum f n = f h + d * c
  | 0, hn, _ => absurd hn (by omega)
  | n + 1, hn, hf => by
    show ∃ c, ssum f n + f n = f h + d * c
    by_cases e : n = h
    · subst e
      obtain ⟨c, hc⟩ := dvd_ssum (f := f) (d := d) n (fun j hj => hf j (by omega) (by omega))
      exact ⟨c, by rw [hc]; omega⟩
    · obtain ⟨c, hc⟩ := ssum_single n (by omega) (fun j hj hjh => hf j (by omega) hjh)
      obtain ⟨c', hc'⟩ := hf n (by omega) e
      exact ⟨c + c', by rw [hc, hc', Nat.mul_add]; omega⟩

theorem neg_one_pow : ∀ n : Nat, (-1 : Int) ^ n = if n % 2 = 0 then 1 else -1
  | 0 => rfl
  | n + 1 => by
    rw [Int.pow_succ, neg_one_pow n]
    by_cases e : n % 2 = 0
    · rw [if_pos e, if_neg (by omega)]; rfl
    · rw [if_neg e, if_pos (by omega)]; rfl

section
variable {q h : Nat} (hq : Prime q) (hqh : q = 2 * h + 1)
include hq hqh

theorem S_mod : ∃ c, S q = 5 ^ h + q * c := by
  have := ssum_single (h := h) (d := q) (f := fun j => choose q (2 * j + 1) * 5 ^ j) (q + 1) (by omega)
    (fun j _ hjh => by
      rcases Nat.lt_or_ge j h with l | l
      · exact Nat.dvd_trans (prime_dvd_choose hq (by omega) (by omega)) (Nat.dvd_mul_right _ _)
      · show q ∣ choose q (2 * j + 1) * 5 ^ j
        rw [choose_lt q (2 * j + 1) (by omega), Nat.zero_mul]; exact Nat.dvd_zero _)
  obtain ⟨c, hc⟩ := this
  refine ⟨c, ?_⟩
  unfold S; rw [hc]
  show choose q (2 * h + 1) * 5 ^ h + q * c = _
  rw [← hqh, choose_self, Nat.one_mul]

theorem T_mod : ∃ c, T q = 1 + q * c := by
  have := ssum_single (h := 0) (d := q) (f := fun j => choose q (2 * j) * 5 ^ j) (q + 1) (by omega)
    (fun j _ hj0 => by
      rcases Nat.lt_or_ge (2 * j) q with l | l
      · exact Nat.dvd_trans (prime_dvd_choose hq (by omega) l) (Nat.dvd_mul_right _ _)
      · show q ∣ choose q (2 * j) * 5 ^ j
        rw [choose_lt q (2 * j) (by omega), Nat.zero_mul]; exact Nat.dvd_zero _)
  obtain ⟨c, hc⟩ := this
  exact ⟨c, by unfold T; rw [hc]; simp [choose_zero]⟩

theorem cancel_two {x : Int} (hx : (q : Int) ∣ 2 * x) : (q : Int) ∣ x := by
  rcases int_prime_dvd_mul hq hx with h2 | h2
  · rw [show (2 : Int) = ((2 : Nat) : Int) from rfl] at h2
    have := Nat.le_of_dvd (by decide) (Int.ofNat_dvd.mp h2)
    have := hq.1
    omega
  · exact h2

/-- the main congruences, for `q ≠ 5` -/
theorem odd_prime_dvd (h5 : q ≠ 5) :
    (q % 5 = 1 ∨ q % 5 = 4 → q ∣ fib (q - 1)) ∧ (¬ (q % 5 = 1 ∨ q % 5 = 4) → q ∣ fib (q + 1)) := by
  have h1 : 1 ≤ h := by have := hq.1; omega
  obtain ⟨cS, hS⟩ := S_mod hq hqh
  obtain ⟨cT, hT⟩ := T_mod hq hqh
  obtain ⟨e1, e2⟩ := ST_fib q
  have hf : 2 ^ (q - 1) % q = 1 := fermat hq (by decide) (by have := hq.1; omega)
  obtain ⟨cF, hF⟩ : ∃ c, 2 ^ (q - 1) = 1 + q * c := ⟨2 ^ (q - 1) / q, by
    have := Nat.mod_add_div (2 ^ (q - 1)) q; omega⟩
  have p1 : 2 ^ q = 2 * 2 ^ (q - 1) := by
    rw [show q = (q - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]; simp
  have p2 : 2 ^ (q + 1) = 2 * (2 * 2 ^ (q - 1)) := by
    rw [Nat.pow_succ, p1]; omega
  have g := gauss hq h5 hqh
  have par := mu_parity hq h5 hqh
  have ef : fib (q + 1) = fib (q - 1) + fib q := by
    rw [show q + 1 = (q - 1) + 2 by omega, fib_add_two, show q - 1 + 1 = q by omega]
  rw [hS, p1, hF] at e1
  rw [hT, p2, hF, p1, hF] at e2
  rw [neg_one_pow] at g
  -- in the integers
  have i1 : (q : Int) ∣ (5 : Int) ^ h - fib q := by
    refine cancel_two hq hqh ⟨2 * (cF * fib q) - 2 * cS, ?_⟩
    have := congrArg (fun x : Nat => (x : Int)) e1
    simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow, Int.natCast_one] at this
    rw [show ((5 : Nat) : Int) = 5 from rfl, show ((2 : Nat) : Int) = 2 from rfl] at this
    generalize (5 : Int) ^ h = X at this ⊢
    generalize (fib q : Int) = F at this ⊢
    generalize (q : Int) = Q at this ⊢
    generalize (cF : Int) = A at this ⊢; generalize (cS : Int) = B at this ⊢
    ring_z'
  have i2 : (q : Int) ∣ 2 + 2 * fib q - 2 * (2 * fib (q + 1)) := by
    refine ⟨2 * (2 * (cF * fib (q + 1))) - 2 * cT - 2 * (cF * fib q), ?_⟩
    have := congrArg (fun x : Nat => (x : Int)) e2
    simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_pow, Int.natCast_one] at this
    rw [show ((2 : Nat) : Int) = 2 from rfl] at this
    generalize (fib q : Int) = F at this ⊢
    generalize (fib (q + 1) : Int) = G at this ⊢
    generalize (q : Int) = Q at this ⊢
    generalize (cF : Int) = A at this ⊢; generalize (cT : Int) = B at this ⊢
    ring_z'
  have i3 : (q : Int) ∣ (fib (q + 1) : Int) - fib (q - 1) - fib q := ⟨0, by rw [ef]; simp; omega⟩
  constructor
  · intro hr
    rw [if_pos (par.2 hr)] at g
    have a := Int.dvd_sub i1 g        -- 1 - F q
    have b := Int.dvd_add i2 (Int.dvd_add a a)   -- 4 - 4 F(q+1)
    have c : (q : Int) ∣ 2 * (2 * (1 - fib (q + 1))) := by
      have e : 2 + 2 * (fib q : Int) - 2 * (2 * fib (q + 1)) + ((5 : Int) ^ h - fib q - ((5 : Int) ^ h - 1) +
          ((5 : Int) ^ h - fib q - ((5 : Int) ^ h - 1))) = 2 * (2 * (1 - fib (q + 1))) := by omega
      rw [← e]; exact b
    have d := cancel_two hq hqh (cancel_two hq hqh c)
    have : (q : Int) ∣ fib (q - 1) := by
      have := Int.dvd_add (Int.dvd_add d i3) a
      have e : 1 - (fib (q + 1) : Int) + (fib (q + 1) - fib (q - 1) - fib q) +
          ((5 : Int) ^ h - fib q - ((5 : Int) ^ h - 1)) = 2 * (1 - fib q) - fib (q - 1) := by omega
      rw [e] at this
      have := Int.dvd_sub (Int.dvd_trans a (Int.dvd_mul_left 2 _)) this
      have e2 : 2 * ((5 : Int) ^ h - fib q - ((5 : Int) ^ h - 1)) - (2 * (1 - fib q) - fib (q - 1)) =
          fib (q - 1) := by omega
      rwa [e2] at this
    exact Int.ofNat_dvd.mp this
  · intro hr
    have : ¬ (mu q h h % 2 = 0) := fun e => hr (par.1 e)
    rw [if_neg this] at g
    have a := Int.dvd_sub i1 g        -- -1 - F q
    have b := Int.dvd_add i2 (Int.dvd_add a a)
    have e : 2 + 2 * (fib q : Int) - 2 * (2 * fib (q + 1)) + ((5 : Int) ^ h - fib q - ((5 : Int) ^ h - -1) +
        ((5 : Int) ^ h - fib q - ((5 : Int) ^ h - -1))) = 2 * (2 * -(fib (q + 1) : Int)) := by omega
    rw [e] at b
    have := Int.dvd_neg.mp (cancel_two hq hqh (cancel_two hq hqh b))
    exact Int.ofNat_dvd.mp this

end

/-- **`q ∣ F (q - (q/5))`** for every prime `q` -/
theorem prime_dvd_fib_wss {q : Nat} (hq : Prime q) : q ∣ fib (wssIndex q) := by
  by_cases h2 : q = 2
  · subst h2; decide
  by_cases h5 : q = 5
  · subst h5; decide
  have hodd : q % 2 = 1 := by
    have := hq.2 2 (by have := hq.1; omega) (by decide); omega
  have h50 : q % 5 ≠ 0 := fun e => by
    rcases Nat.lt_or_ge 5 q with l | l
    · exact hq.2 5 l (by decide) e
    · have := hq.1; omega
  have hqh : q = 2 * (q / 2) + 1 := by omega
  have m := odd_prime_dvd hq hqh h5
  unfold wssIndex
  rw [if_neg h50]
  split
  · exact m.1 (by assumption)
  · exact m.2 (by assumption)

end TM.WallSunSun2
