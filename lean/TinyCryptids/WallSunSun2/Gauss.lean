import TinyCryptids.WallSunSun2.Fib

/-!
# Gauss's lemma for 5

For an odd prime `q = 2h + 1 ≠ 5`: `5 ^ h ≡ (-1) ^ μ (mod q)`, with `μ` the number of
`k ∈ [1, h]` such that `5k mod q > h` (`gauss`), and `μ` is even iff `q ≡ ±1 (mod 5)`
(`mu_parity`). The products are `prodF` over `[1, n]`; `perm_prod` is the product of an
injective self-map of `[1, n]`.
-/

set_option linter.unusedSectionVars false

namespace TM.WallSunSun2
open TinyCryptids

/-- `f 1 * … * f n` -/
def prodF (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => prodF f n * f (n + 1)

theorem prodF_ext {f g : Nat → Nat} : ∀ n, (∀ k, 1 ≤ k → k ≤ n → f k = g k) → prodF f n = prodF g n
  | 0, _ => rfl
  | n + 1, h => by
    show prodF f n * f (n + 1) = prodF g n * g (n + 1)
    rw [prodF_ext n (fun k h1 h2 => h k h1 (by omega)), h (n + 1) (by omega) (by omega)]

/-- one factor replaced -/
theorem prodF_update (f : Nat → Nat) (k0 v : Nat) : ∀ n, 1 ≤ k0 → k0 ≤ n →
    prodF (fun k => if k = k0 then v else f k) n * f k0 = prodF f n * v
  | 0, h1, h2 => by omega
  | n + 1, h1, h2 => by
    show prodF (fun k => if k = k0 then v else f k) n * (if n + 1 = k0 then v else f (n + 1)) * f k0 =
      prodF f n * f (n + 1) * v
    by_cases hk : n + 1 = k0
    · subst hk
      rw [if_pos rfl, prodF_ext (g := f) n (fun k _ h => by rw [if_neg (by omega)])]
      rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm v]
    · rw [if_neg hk, Nat.mul_assoc, Nat.mul_comm (f (n + 1)), ← Nat.mul_assoc,
        prodF_update f k0 v n h1 (by omega), Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm v]

/-- an injective map from `[1, m]` to `[1, n]`: `m ≤ n`, and for `m = n` the product is `n!` -/
theorem perm_prod : ∀ n m (f : Nat → Nat), (∀ k, 1 ≤ k → k ≤ m → 1 ≤ f k ∧ f k ≤ n) →
    (∀ i j, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m → f i = f j → i = j) →
    m ≤ n ∧ (m = n → prodF f m = fact n)
  | 0, m, f, hr, _ => by
    have : m = 0 := by
      rcases m with _ | m
      · rfl
      · have := hr 1 (by omega) (by omega); omega
    subst this; exact ⟨by omega, fun _ => rfl⟩
  | n + 1, m, f, hr, hi => by
    by_cases hk : ∃ k0, 1 ≤ k0 ∧ k0 ≤ m ∧ f k0 = n + 1
    · obtain ⟨k0, h1, h2, h3⟩ := hk
      let g := fun k => if k = k0 then f m else f k
      have hm : f m ≠ n + 1 ∨ m = k0 := by
        by_cases e : m = k0
        · exact Or.inr e
        · left; intro h; exact e (hi m k0 (by omega) (by omega) h1 h2 (by rw [h, h3]))
      have ih := perm_prod n (m - 1) g (fun k hk1 hk2 => by
          show 1 ≤ (if k = k0 then f m else f k) ∧ (if k = k0 then f m else f k) ≤ n
          by_cases e : k = k0
          · rw [if_pos e]
            have := hr m (by omega) (by omega)
            rcases hm with hm | hm
            · omega
            · omega
          · rw [if_neg e]
            have := hr k hk1 (by omega)
            have : f k ≠ n + 1 := fun h => e (hi k k0 hk1 (by omega) h1 h2 (by rw [h, h3]))
            omega)
        (fun i j hi1 hi2 hj1 hj2 hij => by
          simp only [g] at hij
          by_cases ei : i = k0 <;> by_cases ej : j = k0
          · omega
          · rw [if_pos ei, if_neg ej] at hij
            exact absurd (hi m j (by omega) (by omega) hj1 (by omega) hij) (by omega)
          · rw [if_neg ei, if_pos ej] at hij
            exact absurd (hi i m hi1 (by omega) (by omega) (by omega) hij) (by omega)
          · rw [if_neg ei, if_neg ej] at hij
            exact hi i j hi1 (by omega) hj1 (by omega) hij)
      refine ⟨by omega, fun e => ?_⟩
      subst e
      have hp := ih.2 (by omega)
      rw [show n + 1 - 1 = n by omega] at hp
      show prodF f n * f (n + 1) = fact n * (n + 1)
      by_cases e : k0 = n + 1
      · subst e
        have : prodF f n = prodF g n := prodF_ext n (fun k _ hk => by
          show f k = (if k = n + 1 then f (n + 1) else f k); rw [if_neg (by omega)])
        rw [this, hp, h3]
      · have u := prodF_update f k0 (f (n + 1)) n h1 (by omega)
        rw [h3] at u
        have : prodF g n = prodF (fun k => if k = k0 then f (n + 1) else f k) n := rfl
        rw [← hp, this, u]
    · have ih := perm_prod n m f (fun k hk1 hk2 => by
          have := hr k hk1 hk2
          have : f k ≠ n + 1 := fun h => hk ⟨k, hk1, hk2, h⟩
          omega) hi
      exact ⟨by omega, fun e => by omega⟩

theorem prodF_five : ∀ n, prodF (fun k => 5 * k) n = 5 ^ n * fact n
  | 0 => rfl
  | n + 1 => by
    show prodF (fun k => 5 * k) n * (5 * (n + 1)) = 5 ^ (n + 1) * (fact n * (n + 1))
    rw [prodF_five n, Nat.pow_succ]
    generalize 5 ^ n = A; generalize fact n = B
    ring_n

theorem prime_not_dvd_fact {q : Nat} (hq : Prime q) : ∀ n, n < q → ¬ q ∣ fact n
  | 0, _, h => by have h' : q ∣ 1 := h; have := Nat.le_of_dvd (by decide) h'; have := hq.1; omega
  | n + 1, hn, h => by
    rcases prime_dvd_mul hq h with h | h
    · exact prime_not_dvd_fact hq n (by omega) h
    · have := Nat.le_of_dvd (by omega) h; omega

/-! ## integers -/

theorem int_prime_dvd_mul {q : Nat} (hq : Prime q) {a b : Int} (h : (q : Int) ∣ a * b) :
    (q : Int) ∣ a ∨ (q : Int) ∣ b := by
  rw [Int.ofNat_dvd_left, Int.natAbs_mul] at h
  rcases prime_dvd_mul hq h with h | h
  · exact Or.inl (Int.ofNat_dvd_left.mpr h)
  · exact Or.inr (Int.ofNat_dvd_left.mpr h)

theorem int_small {q : Nat} {x : Int} (h : (q : Int) ∣ x) (hx : x.natAbs < q) : x = 0 := by
  rw [Int.ofNat_dvd_left] at h
  rcases Nat.eq_zero_or_pos x.natAbs with h0 | h0
  · exact Int.natAbs_eq_zero.mp h0
  · have := Nat.le_of_dvd h0 h; omega

theorem dvd_mul_cong {q : Int} {a a' b b' : Int} (ha : q ∣ a - a') (hb : q ∣ b - b') :
    q ∣ a * b - a' * b' := by
  have e : a * b - a' * b' = a * (b - b') + b' * (a - a') := by ring_z
  rw [e]; exact Int.dvd_add (Int.dvd_trans hb (Int.dvd_mul_left _ _)) (Int.dvd_trans ha (Int.dvd_mul_left _ _))

theorem five_prime : Prime 5 := by decide

/-- `q` prime, not 5: `q ∤ 5 x` unless `q ∣ x` -/
theorem dvd_of_dvd_five {q : Nat} (hq : Prime q) (h5 : q ≠ 5) {x : Int} (h : (q : Int) ∣ 5 * x) :
    (q : Int) ∣ x := by
  rcases int_prime_dvd_mul hq h with h | h
  · have h' : q ∣ 5 := Int.ofNat_dvd.mp h
    rcases ((prime_iff_dvd 5).1 five_prime).2 q h' with e | e
    · have := hq.1; omega
    · exact absurd e h5
  · exact h

/-! ## Gauss's lemma -/

section
variable (q h : Nat)

/-- `5k mod q` -/
def s5 (k : Nat) : Nat := 5 * k % q
/-- folded into `[1, h]` -/
def r5 (k : Nat) : Nat := if s5 q k ≤ h then s5 q k else q - s5 q k
/-- the number of `k ∈ [1, n]` with `5k mod q > h` -/
def mu : Nat → Nat
  | 0 => 0
  | n + 1 => mu n + if h < s5 q (n + 1) then 1 else 0

end

section
variable {q h : Nat} (hq : Prime q) (h5 : q ≠ 5) (hqh : q = 2 * h + 1)
include hq h5 hqh

theorem s5_pos {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ h) : 1 ≤ s5 q k := by
  unfold s5
  refine Nat.pos_of_ne_zero fun e => ?_
  have hd : ((q : Nat) : Int) ∣ 5 * (k : Int) := by
    have := Nat.dvd_of_mod_eq_zero e
    exact Int.ofNat_dvd.mpr (by simpa using this)
  have := dvd_of_dvd_five hq h5 hd
  have := Nat.le_of_dvd (by omega) (Int.ofNat_dvd.mp this)
  omega

theorem r5_range {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ h) : 1 ≤ r5 q h k ∧ r5 q h k ≤ h := by
  have hp := s5_pos hq h5 hqh h1 h2
  have hl : s5 q k < q := Nat.mod_lt _ (by omega)
  unfold r5; split <;> omega

/-- `5k ≡ ± r5 k (mod q)`, the sign `-` iff `5k mod q > h` -/
theorem r5_cong (k : Nat) :
    (q : Int) ∣ 5 * (k : Int) - (if h < s5 q k then -(r5 q h k : Int) else (r5 q h k : Int)) := by
  have e := Nat.div_add_mod (5 * k) q
  have hl : s5 q k < q := Nat.mod_lt _ (by omega)
  unfold r5
  unfold s5 at hl ⊢
  generalize 5 * k / q = c at e
  generalize 5 * k % q = s at e hl ⊢
  by_cases hs : h < s
  · rw [if_pos hs, if_neg (by omega)]
    refine ⟨c + 1, ?_⟩
    have : ((5 * k : Nat) : Int) = (q : Int) * c + s := by rw [← e]; simp
    have e2 : ((q - s : Nat) : Int) = (q : Int) - s := by omega
    simp only [Int.natCast_mul] at this
    rw [e2, Int.mul_add, Int.mul_one]; omega
  · rw [if_neg hs, if_pos (by omega)]
    refine ⟨c, ?_⟩
    have : ((5 * k : Nat) : Int) = (q : Int) * c + s := by rw [← e]; simp
    simp only [Int.natCast_mul] at this
    omega

theorem r5_inj (i j : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ h) (hj1 : 1 ≤ j) (hj2 : j ≤ h)
    (e : r5 q h i = r5 q h j) : i = j := by
  have ci := r5_cong hq h5 hqh i
  have cj := r5_cong hq h5 hqh j
  rw [e] at ci
  generalize (r5 q h j : Int) = R at ci cj
  by_cases a : h < s5 q i <;> by_cases b : h < s5 q j
  · rw [if_pos a] at ci; rw [if_pos b] at cj
    have := Int.dvd_sub ci cj
    have : (q : Int) ∣ 5 * ((i : Int) - j) := by
      rw [show 5 * ((i : Int) - j) = 5 * (i : Int) - -R - (5 * (j : Int) - -R) by omega]; exact this
    have := int_small (dvd_of_dvd_five hq h5 this) (by omega)
    omega
  · rw [if_pos a] at ci; rw [if_neg b] at cj
    have := Int.dvd_add ci cj
    have : (q : Int) ∣ 5 * ((i : Int) + j) := by
      rw [show 5 * ((i : Int) + j) = 5 * (i : Int) - -R + (5 * (j : Int) - R) by omega]; exact this
    have := int_small (dvd_of_dvd_five hq h5 this) (by omega)
    omega
  · rw [if_neg a] at ci; rw [if_pos b] at cj
    have := Int.dvd_add ci cj
    have : (q : Int) ∣ 5 * ((i : Int) + j) := by
      rw [show 5 * ((i : Int) + j) = 5 * (i : Int) - R + (5 * (j : Int) - -R) by omega]; exact this
    have := int_small (dvd_of_dvd_five hq h5 this) (by omega)
    omega
  · rw [if_neg a] at ci; rw [if_neg b] at cj
    have := Int.dvd_sub ci cj
    have : (q : Int) ∣ 5 * ((i : Int) - j) := by
      rw [show 5 * ((i : Int) - j) = 5 * (i : Int) - R - (5 * (j : Int) - R) by omega]; exact this
    have := int_small (dvd_of_dvd_five hq h5 this) (by omega)
    omega

theorem prod_cong : ∀ n, (q : Int) ∣ (prodF (fun k => 5 * k) n : Int) - (-1) ^ mu q h n * (prodF (r5 q h) n : Int)
  | 0 => by simp [prodF, mu]; try exact Int.dvd_zero _
  | n + 1 => by
    have ih := prod_cong n
    have c := r5_cong hq h5 hqh (n + 1)
    have := dvd_mul_cong ih c
    show (q : Int) ∣ ((prodF (fun k => 5 * k) n * (5 * (n + 1)) : Nat) : Int) -
      (-1) ^ (mu q h n + if h < s5 q (n + 1) then 1 else 0) * ((prodF (r5 q h) n * r5 q h (n + 1) : Nat) : Int)
    simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one] at this ⊢
    rw [show ((5 : Nat) : Int) = (5 : Int) from rfl]
    by_cases a : h < s5 q (n + 1)
    · rw [if_pos a] at this ⊢
      rw [Int.pow_succ]
      generalize ((-1 : Int) ^ mu q h n) = E at this ⊢
      generalize (prodF (fun k => 5 * k) n : Int) = P at this ⊢
      generalize (prodF (r5 q h) n : Int) = Q at this ⊢
      generalize (r5 q h (n + 1) : Int) = r at this ⊢
      rw [show P * (5 * ((n : Int) + 1)) - E * (-1) * (Q * r) = P * (5 * ((n : Int) + 1)) - E * Q * -r by ring_z]
      exact this
    · rw [if_neg a] at this ⊢
      rw [Nat.add_zero]
      generalize ((-1 : Int) ^ mu q h n) = E at this ⊢
      generalize (prodF (fun k => 5 * k) n : Int) = P at this ⊢
      generalize (prodF (r5 q h) n : Int) = Q at this ⊢
      generalize (r5 q h (n + 1) : Int) = r at this ⊢
      rw [show P * (5 * ((n : Int) + 1)) - E * (Q * r) = P * (5 * ((n : Int) + 1)) - E * Q * r by
        rw [Int.mul_assoc]]
      exact this

/-- **Gauss's lemma** for 5 -/
theorem gauss : (q : Int) ∣ (5 : Int) ^ h - (-1) ^ mu q h h := by
  have c := prod_cong hq h5 hqh h
  rw [prodF_five, (perm_prod h h (r5 q h) (fun k h1 h2 => r5_range hq h5 hqh h1 h2)
    (fun i j a b c d e => r5_inj hq h5 hqh i j a b c d e)).2 rfl] at c
  have e : ((5 ^ h * fact h : Nat) : Int) - (-1) ^ mu q h h * (fact h : Int) =
      (fact h : Int) * ((5 : Int) ^ h - (-1) ^ mu q h h) := by
    simp only [Int.natCast_mul, Int.natCast_pow]
    generalize ((-1 : Int) ^ mu q h h) = E; generalize (fact h : Int) = F
    generalize ((5 : Nat) : Int) ^ h = X
    ring_z
  rw [e] at c
  rcases int_prime_dvd_mul hq c with c | c
  · exact absurd (Int.ofNat_dvd.mp c) (prime_not_dvd_fact hq h (by omega))
  · exact c

/-- `5k mod q > h` as a linear condition, for `k ∈ [1, h]` -/
theorem s5_big (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ h) :
    h < s5 q k ↔ (h < 5 * k ∧ 5 * k < q) ∨ (q + h < 5 * k ∧ 5 * k < 2 * q) := by
  unfold s5
  have hq2 := hq.1
  by_cases a : 5 * k < q
  · rw [Nat.mod_eq_of_lt a]; omega
  · by_cases b : 5 * k < 2 * q
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem mu_formula : ∀ n, n ≤ h → mu q h n =
    (min n ((q - 1) / 5) - min n (h / 5)) + (min n ((2 * q - 1) / 5) - min n ((q + h) / 5))
  | 0, _ => by simp [mu]
  | n + 1, hn => by
    have ih := mu_formula n (by omega)
    have b := s5_big hq h5 hqh (n + 1) (by omega) hn
    show mu q h n + (if h < s5 q (n + 1) then 1 else 0) = _
    rw [ih]
    by_cases a : h < s5 q (n + 1)
    · rw [if_pos a]; have := b.1 a; omega
    · rw [if_neg a]; have : ¬ _ := fun x => a (b.2 x); omega

theorem mu_parity : (mu q h h % 2 = 0 ↔ q % 5 = 1 ∨ q % 5 = 4) := by
  rw [mu_formula hq h5 hqh h (Nat.le_refl h), Nat.min_eq_right (by omega : (q - 1) / 5 ≤ h),
    Nat.min_eq_right (by omega : h / 5 ≤ h), Nat.min_eq_right (by omega : (2 * q - 1) / 5 ≤ h),
    Nat.min_eq_right (by omega : (q + h) / 5 ≤ h)]
  have : q % 5 ≠ 0 := fun e => by
    rcases Nat.lt_or_ge 5 q with l | l
    · exact hq.2 5 l (by decide) e
    · have := hq.1; exact h5 (by omega)
  have : h % 5 = 0 ∨ h % 5 = 1 ∨ h % 5 = 2 ∨ h % 5 = 3 ∨ h % 5 = 4 := by omega
  rcases this with e | e | e | e | e <;> omega

end

end TM.WallSunSun2
