import TinyCryptids.Defs

/-!
# The odometer, on lists of bits

(A copy of `../WallSunSun/Spec.lean`, in its own namespace.)

The odometer of the machine is a string of bits without two adjacent 1s (a *Zeckendorf*
string). Here it is a `List Bool`, **least significant bit first** (the head is the bit next to
B's right end, where the machine starts each increment). `inc` is the machine's increment
step by step: clear holes (1-bits) until a cell `c` that may be set (`cand`), set it.
`val k l` is the Zeckendorf value of `l` with weights `fib (k + 2), fib (k + 3), …`.
Then `inc` adds 1 to `val 0` until the largest string, `val 0 l = fib (n + 2) - 1`.
-/

namespace TM.Zeckendorf
open TinyCryptids

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

theorem fib_add_two (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

theorem fib_pos : ∀ n, 1 ≤ n → 1 ≤ fib n
  | 0, h => absurd h (by decide)
  | 1, _ => by decide
  | n + 2, _ => by rw [fib_add_two]; have := fib_pos (n + 1) (by omega); omega

theorem fib_mono_succ (n : Nat) : fib n ≤ fib (n + 1) := by
  cases n with
  | zero => decide
  | succ n => rw [fib_add_two]; omega

/-- no two adjacent 1s -/
def Valid : List Bool → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => ¬ (a = true ∧ b = true) ∧ Valid (b :: l)

theorem Valid.tail {b : Bool} {l : List Bool} (h : Valid (b :: l)) : Valid l := by
  cases l with
  | nil => trivial
  | cons c l => exact h.2

/-- the Zeckendorf value, weights from `fib (k + 2)` -/
def val (k : Nat) : List Bool → Nat
  | [] => 0
  | b :: l => (if b then fib (k + 2) else 0) + val (k + 1) l

/-- the candidate (the head, a 0-bit) is set if the bit after it is 0; else that bit is
cleared and the bit after it is the next candidate -/
def cand : List Bool → Option (List Bool)
  | [] => none
  | true :: _ => none
  | [false] => some [true]
  | false :: false :: l => some (true :: false :: l)
  | false :: true :: l => (cand l).map (fun x => false :: false :: x)

/-- the increment: clear 1-bits, then from the first 0-bit on, as `cand` -/
def inc : List Bool → Option (List Bool)
  | [] => none
  | false :: l => cand (false :: l)
  | true :: l => (inc l).map (false :: ·)

theorem cand_spec : ∀ (l l' : List Bool) (k : Nat), cand l = some l' →
    l'.length = l.length ∧ val k l' = val k l + fib (k + 2) ∧ (Valid l → Valid l')
  | [], _, _, h => by simp [cand] at h
  | true :: _, _, _, h => by simp [cand] at h
  | [false], l', k, h => by
    simp [cand] at h; subst h; simp [val, Valid]
  | false :: false :: l, l', k, h => by
    simp [cand] at h; subst h
    refine ⟨rfl, by simp [val]; omega, fun hv => ⟨by simp, hv.2⟩⟩
  | false :: true :: l, l', k, h => by
    simp only [cand, Option.map_eq_some'] at h
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨h1, h2, h3⟩ := cand_spec l x (k + 2) hx
    refine ⟨by simp [h1], ?_, fun hv => ?_⟩
    · have e := fib_add_two (k + 2)
      simp only [val, Bool.false_eq_true, ↓reduceIte] at h2 ⊢
      simp only [Nat.add_assoc, Nat.reduceAdd] at e h2 ⊢
      omega
    · have hl := (Valid.tail (Valid.tail hv))
      cases x with
      | nil => exact ⟨by simp, trivial⟩
      | cons c x => exact ⟨by simp, ⟨by simp, h3 hl⟩⟩

theorem cand_none : ∀ (l : List Bool) (k : Nat), cand l = none → Valid l →
    (∀ b, l.head? = some b → b = false) → val k l + fib (k + 2) = fib (l.length + k + 2)
  | [], k, _, _, _ => by simp [val]
  | true :: _, _, _, _, hh => absurd (hh true rfl) (by decide)
  | [false], _, h, _, _ => by simp [cand] at h
  | false :: false :: l, _, h, _, _ => by simp [cand] at h
  | false :: true :: l, k, h, hv, _ => by
    simp only [cand, Option.map_eq_none'] at h
    have hv2 := hv.2
    have ih := cand_none l (k + 2) h (Valid.tail hv2) (fun b hb => by
      cases l with
      | nil => simp at hb
      | cons c l =>
        simp at hb; subst hb
        cases c with
        | false => rfl
        | true => exact absurd ⟨rfl, rfl⟩ hv2.1)
    have e := fib_add_two (k + 2)
    simp only [val, Bool.false_eq_true, ↓reduceIte, List.length_cons] at ih ⊢
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_left_comm _ k] at e ih ⊢
    omega

theorem inc_spec : ∀ (l l' : List Bool), inc l = some l' → Valid l →
    l'.length = l.length ∧ val 0 l' = val 0 l + 1 ∧ Valid l'
  | [], _, h, _ => by simp [inc] at h
  | false :: l, l', h, hv => by
    obtain ⟨h1, h2, h3⟩ := cand_spec (false :: l) l' 0 h
    exact ⟨h1, by rw [h2]; rfl, h3 hv⟩
  | true :: l, l', h, hv => by
    simp only [inc, Option.map_eq_some'] at h
    obtain ⟨x, hx, rfl⟩ := h
    cases l with
    | nil => simp [inc] at hx
    | cons c l =>
      cases c with
      | true => exact absurd ⟨rfl, rfl⟩ hv.1
      | false =>
        obtain ⟨h1, h2, h3⟩ := cand_spec (false :: l) x 1 hx
        refine ⟨by simp [h1], ?_, ?_⟩
        · simp only [val, Bool.false_eq_true, ↓reduceIte, Nat.add_assoc, Nat.reduceAdd, Nat.zero_add] at h2 ⊢
          simp only [show fib 2 = 1 from rfl, show fib 3 = 2 from rfl] at h2 ⊢
          omega
        · cases x with
          | nil => trivial
          | cons d x => exact ⟨by simp, h3 hv.2⟩

theorem inc_none (l : List Bool) (h : inc l = none) (hv : Valid l) :
    val 0 l + 1 = fib (l.length + 2) := by
  match l, h, hv with
  | [], _, _ => rfl
  | false :: l, h, hv =>
    have := cand_none (false :: l) 0 h hv (fun b hb => by simp at hb; exact hb.symm.symm ▸ rfl)
    exact this
  | true :: l, h, hv =>
    simp only [inc, Option.map_eq_none'] at h
    match l, h, hv with
    | [], _, _ => rfl
    | true :: _, _, hv => exact absurd ⟨rfl, rfl⟩ hv.1
    | false :: l, h, hv =>
      have := cand_none (false :: l) 1 h hv.2 (fun b hb => by simp at hb; exact hb.symm.symm ▸ rfl)
      have e := fib_add_two (l.length + 2)
      simp only [val, Bool.false_eq_true, ↓reduceIte, List.length_cons] at this ⊢
      simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_left_comm _ 1, Nat.add_left_comm _ 2] at e this ⊢
      simp only [show fib 2 = 1 from rfl, show fib 3 = 2 from rfl] at this ⊢
      omega

/-- the value of a valid string is below `fib (n + 2)` -/
theorem val_lt : ∀ (l : List Bool) (k : Nat), Valid l → val k l + fib (k + 1) ≤ fib (l.length + k + 2)
  | [], k, _ => by simp [val]; exact fib_mono_succ (k + 1)
  | [b], k, _ => by
    have e := fib_add_two (k + 1)
    have := fib_mono_succ (k + 1)
    cases b <;> simp only [val, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil,
      Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_comm 1 k] at e this ⊢ <;> omega
  | false :: b :: l, k, hv => by
    have ih := val_lt (b :: l) (k + 1) hv.2
    have := fib_mono_succ (k + 1)
    rw [show (false :: b :: l).length + k + 2 = (b :: l).length + (k + 1) + 2 by simp; omega]
    simp only [val, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at ih ⊢
    omega
  | true :: true :: _, _, hv => absurd ⟨rfl, rfl⟩ hv.1
  | true :: false :: l, k, hv => by
    have ih := val_lt l (k + 2) (Valid.tail hv.2)
    have e := fib_add_two (k + 1)
    rw [show (true :: false :: l).length + k + 2 = l.length + (k + 2) + 2 by simp; omega]
    simp only [val, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at ih ⊢
    rw [show k + 1 + 1 = k + 2 by omega]
    rw [show k + 2 + 1 = k + 1 + 2 by omega, e, show k + 1 + 1 = k + 2 by omega] at ih
    omega

theorem val_replicate (n k : Nat) : val k (List.replicate n false) = 0 := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, val, ih]

theorem val_msb (n : Nat) : ∀ k, val k (List.replicate n false ++ [true]) = fib (n + k + 2) := by
  induction n with
  | zero => intro k; simp [val]
  | succ n ih =>
    intro k
    have := ih (k + 1)
    rw [show n + 1 + k + 2 = n + (k + 1) + 2 by omega, ← this]
    simp [List.replicate_succ, val]

theorem valid_replicate (n : Nat) : Valid (List.replicate n false) := by
  induction n with
  | zero => trivial
  | succ n ih => cases n with
    | zero => trivial
    | succ n => exact ⟨by simp, ih⟩

theorem valid_msb : ∀ n, Valid (List.replicate n false ++ [true])
  | 0 => trivial
  | 1 => ⟨by simp, trivial⟩
  | n + 2 => ⟨by simp, valid_msb (n + 1)⟩

end TM.Zeckendorf
