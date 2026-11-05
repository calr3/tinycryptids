import TinyCryptids.Defs

/-!
# The statement at list level

`D m` is the last diagonal of the triangle on the primes below `m`; appending a prime
`p` gives `ext (D m) p`, whose last entry is the first entry of the new bottom row.
`fail_iff`: the conjecture fails iff some prime `m ≥ 3` gives `lst (ext (D m) m) ≠ 1`.
-/

namespace TM.Gilbreath
open TinyCryptids

def ad (a b : Nat) : Nat := if a ≤ b then b - a else a - b

theorem ad_comm (a b : Nat) : ad a b = ad b a := by unfold ad; split <;> split <;> omega
theorem ad_eq (a b : Nat) : ad a b = (a - b) + (b - a) := by unfold ad; split <;> omega
theorem ad_le {a b M : Nat} (ha : a ≤ M) (hb : b ≤ M) : ad a b ≤ M := by unfold ad; split <;> omega

def nth : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: t, j + 1 => nth t j

def lst : List Nat → Nat
  | [] => 0
  | [a] => a
  | _ :: b :: t => lst (b :: t)

theorem lst_eq_nth : ∀ L : List Nat, lst L = nth L (L.length - 1)
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    rw [lst, lst_eq_nth (b :: t)]
    simp only [List.length_cons, Nat.add_sub_cancel]
    rfl

theorem lst_snoc : ∀ (l : List Nat) (b : Nat), lst (l ++ [b]) = b
  | [], _ => rfl
  | [_], _ => rfl
  | a :: c :: t, b => by
    show lst (a :: c :: (t ++ [b])) = b
    rw [lst]; exact lst_snoc (c :: t) b

/-- New last diagonal after appending `p`. -/
def ext : List Nat → Nat → List Nat
  | [], p => [p]
  | e :: E, p => p :: ext E (ad p e)

theorem length_ext : ∀ (E : List Nat) (p : Nat), (ext E p).length = E.length + 1
  | [], _ => rfl
  | _ :: E, _ => by simp [ext, length_ext E]

theorem nth_ext_zero (E : List Nat) (p : Nat) : nth (ext E p) 0 = p := by cases E <;> rfl

theorem nth_ext_succ : ∀ (E : List Nat) (p j : Nat), j < E.length →
    nth (ext E p) (j + 1) = ad (nth (ext E p) j) (nth E j)
  | [], _, _, h => absurd h (by simp)
  | e :: E, p, 0, _ => by simp [ext, nth, nth_ext_zero]
  | e :: E, p, j + 1, h => by
    show nth (ext E (ad p e)) (j + 1) = ad (nth (ext E (ad p e)) j) (nth E j)
    exact nth_ext_succ E _ j (by simp at h; omega)

theorem lst_ext_cons (e : Nat) (E : List Nat) (q : Nat) :
    lst (ext (e :: E) q) = lst (ext E (ad q e)) := by
  show lst (q :: ext E (ad q e)) = _
  cases E <;> rfl

theorem ext_le {M : Nat} : ∀ (E : List Nat) (p : Nat), (∀ x ∈ E, x ≤ M) → p ≤ M →
    ∀ x ∈ ext E p, x ≤ M
  | [], p, _, hp, x, hx => by simp [ext] at hx; omega
  | e :: E, p, hE, hp, x, hx => by
    simp only [ext, List.mem_cons] at hx
    rcases hx with hx | hx
    · omega
    · exact ext_le E _ (fun y hy => hE y (by simp [hy]))
        (ad_le hp (hE e (by simp))) x hx

theorem length_absDiffs : ∀ l : List Nat, (absDiffs l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    simp only [absDiffs, List.length_cons, length_absDiffs (b :: l)]
    omega

theorem absDiffs_snoc : ∀ (l : List Nat) (b : Nat), l ≠ [] →
    absDiffs (l ++ [b]) = absDiffs l ++ [ad (lst l) b]
  | [], _, h => absurd rfl h
  | [a], b, _ => rfl
  | a :: c :: t, b, _ => by
    show ad a c :: absDiffs (c :: t ++ [b]) = ad a c :: absDiffs (c :: t) ++ [ad (lst (c :: t)) b]
    rw [absDiffs_snoc (c :: t) b (by simp)]; rfl

theorem length_row (l : List Nat) : ∀ j, (gilbreathRow l j).length = l.length - j
  | 0 => rfl
  | j + 1 => by
    simp only [gilbreathRow, length_absDiffs, length_row l j]
    omega

/-- Appending `p` appends the new diagonal entry to each row. -/
theorem row_snoc (l D : List Nat) (p : Nat) (hD : D.length = l.length)
    (hd : ∀ j, j < l.length → nth D j = lst (gilbreathRow l j)) :
    ∀ j, j ≤ l.length → gilbreathRow (l ++ [p]) j = gilbreathRow l j ++ [nth (ext D p) j]
  | 0, _ => by simp [gilbreathRow, nth_ext_zero]
  | j + 1, h => by
    have ne : gilbreathRow l j ≠ [] := by
      intro e; have := length_row l j; rw [e] at this; simp at this; omega
    simp only [gilbreathRow]
    rw [row_snoc l D p hD hd j (by omega), absDiffs_snoc _ _ ne, ← hd j (by omega),
      nth_ext_succ D p j (by omega), ad_comm]

/-- The last diagonal of the triangle on the primes below `m`. -/
def D : Nat → List Nat
  | 0 => []
  | m + 1 => if Prime m then ext (D m) m else D m

theorem primesBelow_succ (m : Nat) :
    primesBelow (m + 1) = if Prime m then primesBelow m ++ [m] else primesBelow m := by
  unfold primesBelow
  rw [List.range_succ, List.filter_append]
  by_cases h : Prime m <;> simp [h]

theorem D_spec : ∀ m, (D m).length = (primesBelow m).length ∧
    ∀ j, j < (primesBelow m).length → nth (D m) j = lst (gilbreathRow (primesBelow m) j)
  | 0 => ⟨rfl, fun j h => by simp [primesBelow] at h⟩
  | m + 1 => by
    obtain ⟨h1, h2⟩ := D_spec m
    rw [D, primesBelow_succ]
    by_cases hp : Prime m
    · simp only [hp, if_true]
      refine ⟨by simp [length_ext, h1], fun j hj => ?_⟩
      simp only [List.length_append, List.length_cons, List.length_nil] at hj
      rw [row_snoc _ _ m h1 h2 j (by omega), lst_snoc]
    · simp only [hp, if_false]; exact ⟨h1, h2⟩

/-- When `m` is prime, the first entry of the new bottom row is `lst (ext (D m) m)`. -/
theorem head_new {m : Nat} (hp : Prime m) :
    (gilbreathRow (primesBelow (m + 1)) (primesBelow m).length).head? =
      some (lst (ext (D m) m)) := by
  obtain ⟨h1, h2⟩ := D_spec m
  rw [primesBelow_succ, if_pos hp, row_snoc _ _ m h1 h2 _ (Nat.le_refl _)]
  have : gilbreathRow (primesBelow m) (primesBelow m).length = [] := by
    apply List.eq_nil_of_length_eq_zero; rw [length_row]; omega
  rw [this, lst_eq_nth, length_ext, h1]; rfl

theorem head_old {m k : Nat} (hp : Prime m) (hk : k < (primesBelow m).length) :
    (gilbreathRow (primesBelow (m + 1)) k).head? = (gilbreathRow (primesBelow m) k).head? := by
  obtain ⟨h1, h2⟩ := D_spec m
  rw [primesBelow_succ, if_pos hp, row_snoc _ _ m h1 h2 _ (by omega)]
  have : gilbreathRow (primesBelow m) k ≠ [] := by
    intro e; have := length_row (primesBelow m) k; rw [e] at this; simp at this; omega
  obtain ⟨a, t, e⟩ := List.exists_cons_of_ne_nil this
  rw [e]; rfl

theorem reach : ∀ N k, k < (primesBelow N).length → ∃ m, Prime m ∧ (primesBelow m).length = k ∧
    (gilbreathRow (primesBelow N) k).head? = (gilbreathRow (primesBelow (m + 1)) k).head?
  | 0, k, h => by simp [primesBelow] at h
  | N + 1, k, h => by
    by_cases hp : Prime N
    · have hl : (primesBelow (N + 1)).length = (primesBelow N).length + 1 := by
        rw [primesBelow_succ, if_pos hp]; simp
      rcases Nat.lt_or_ge k (primesBelow N).length with hk | hk
      · obtain ⟨m, hm, hmk, he⟩ := reach N k hk
        exact ⟨m, hm, hmk, by rw [head_old hp hk, he]⟩
      · exact ⟨N, hp, by omega, by rw [show k = (primesBelow N).length by omega]⟩
    · rw [primesBelow_succ, if_neg hp] at h ⊢
      exact reach N k h

theorem prime_two : Prime 2 := ⟨by decide, fun d hd h2 => by omega⟩

theorem len_pos_iff (m : Nat) : 1 ≤ (primesBelow m).length ↔ 3 ≤ m := by
  constructor
  · intro h
    obtain ⟨a, t, e⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos h)
    have : a ∈ primesBelow m := by rw [e]; simp
    simp only [primesBelow, List.mem_filter, List.mem_range, decide_eq_true_eq] at this
    have := this.2.two_le; omega
  · intro h
    have : 2 ∈ primesBelow m := by
      simp only [primesBelow, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by omega, prime_two⟩
    exact List.length_pos_of_mem this

/-- The conjecture fails iff some prime `m ≥ 3` gives a new bottom entry `≠ 1`. -/
theorem fail_iff : (∃ N k, 1 ≤ k ∧ k < (primesBelow N).length ∧
      (gilbreathRow (primesBelow N) k).head? ≠ some 1) ↔
    ∃ m, 3 ≤ m ∧ Prime m ∧ lst (ext (D m) m) ≠ 1 := by
  constructor
  · rintro ⟨N, k, hk1, hk, hh⟩
    obtain ⟨m, hm, hmk, he⟩ := reach N k hk
    refine ⟨m, (len_pos_iff m).1 (by omega), hm, fun e => hh ?_⟩
    rw [he, ← hmk, head_new hm, e]
  · rintro ⟨m, h3, hm, hne⟩
    refine ⟨m + 1, (primesBelow m).length, (len_pos_iff m).2 h3, ?_, ?_⟩
    · rw [primesBelow_succ, if_pos hm]; simp
    · rw [head_new hm]; intro e; exact hne (Option.some.inj e)

theorem add_mod_self_left' (d x : Nat) : (d + x) % d = x % d := by
  rw [Nat.add_comm]; exact Nat.add_mod_right x d

/-- `(x + 1) % d` from `x % d` -/
theorem mod_succ (x d : Nat) :
    (x % d + 1 < d → (x + 1) % d = x % d + 1) ∧ (x % d + 1 = d → (x + 1) % d = 0) := by
  have e := Nat.div_add_mod x d
  constructor
  · intro h
    have : x + 1 = d * (x / d) + (x % d + 1) := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt h]
  · intro h
    have : x + 1 = d * (x / d + 1) := by rw [Nat.mul_add]; omega
    rw [this, Nat.mul_mod_right]

end TM.Gilbreath
