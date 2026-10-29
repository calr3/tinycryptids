import TinyCryptids.PA.Sem
import TinyCryptids.PA.Pair

/-!
# Running DAG nodes on registers

Lemmas for the shapes that TMBuilder produces: sequences, `while` loops (decrement a register,
run a body, start again), zeroing loops, tests (`if_decnz`, `if_not_decnz`, labels left by
`break`) and `if_eq`'s lockstep loop.  `Nodes.lean` (generated) applies them to every node.
-/

namespace TM.PA

namespace R

@[simp] theorem get_0 (s : R) : s.get 0 = s.pl := rfl
@[simp] theorem get_1 (s : R) : s.get 1 = s.np := rfl
@[simp] theorem get_2 (s : R) : s.get 2 = s.top := rfl
@[simp] theorem get_3 (s : R) : s.get 3 = s.ws := rfl
@[simp] theorem get_4 (s : R) : s.get 4 = s.ac := rfl
@[simp] theorem get_5 (s : R) : s.get 5 = s.p1 := rfl
@[simp] theorem get_6 (s : R) : s.get 6 = s.p2 := rfl
@[simp] theorem get_7 (s : R) : s.get 7 = s.p3 := rfl
@[simp] theorem get_8 (s : R) : s.get 8 = s.s1 := rfl
@[simp] theorem get_9 (s : R) : s.get 9 = s.s2 := rfl

@[simp] theorem set_0 (s : R) (v : Nat) : s.set 0 v = { s with pl := v } := rfl
@[simp] theorem set_1 (s : R) (v : Nat) : s.set 1 v = { s with np := v } := rfl
@[simp] theorem set_2 (s : R) (v : Nat) : s.set 2 v = { s with top := v } := rfl
@[simp] theorem set_3 (s : R) (v : Nat) : s.set 3 v = { s with ws := v } := rfl
@[simp] theorem set_4 (s : R) (v : Nat) : s.set 4 v = { s with ac := v } := rfl
@[simp] theorem set_5 (s : R) (v : Nat) : s.set 5 v = { s with p1 := v } := rfl
@[simp] theorem set_6 (s : R) (v : Nat) : s.set 6 v = { s with p2 := v } := rfl
@[simp] theorem set_7 (s : R) (v : Nat) : s.set 7 v = { s with p3 := v } := rfl
@[simp] theorem set_8 (s : R) (v : Nat) : s.set 8 v = { s with s1 := v } := rfl
@[simp] theorem set_9 (s : R) (v : Nat) : s.set 9 v = { s with s2 := v } := rfl

@[simp] theorem inc_0 (s : R) : s.inc 0 = { s with pl := s.pl + 1 } := rfl
@[simp] theorem inc_1 (s : R) : s.inc 1 = { s with np := s.np + 1 } := rfl
@[simp] theorem inc_2 (s : R) : s.inc 2 = { s with top := s.top + 1 } := rfl
@[simp] theorem inc_3 (s : R) : s.inc 3 = { s with ws := s.ws + 1 } := rfl
@[simp] theorem inc_4 (s : R) : s.inc 4 = { s with ac := s.ac + 1 } := rfl
@[simp] theorem inc_5 (s : R) : s.inc 5 = { s with p1 := s.p1 + 1 } := rfl
@[simp] theorem inc_6 (s : R) : s.inc 6 = { s with p2 := s.p2 + 1 } := rfl
@[simp] theorem inc_7 (s : R) : s.inc 7 = { s with p3 := s.p3 + 1 } := rfl
@[simp] theorem inc_8 (s : R) : s.inc 8 = { s with s1 := s.s1 + 1 } := rfl
@[simp] theorem inc_9 (s : R) : s.inc 9 = { s with s2 := s.s2 + 1 } := rfl
@[simp] theorem dec_0 (s : R) : s.dec 0 = { s with pl := s.pl - 1 } := rfl
@[simp] theorem dec_1 (s : R) : s.dec 1 = { s with np := s.np - 1 } := rfl
@[simp] theorem dec_2 (s : R) : s.dec 2 = { s with top := s.top - 1 } := rfl
@[simp] theorem dec_3 (s : R) : s.dec 3 = { s with ws := s.ws - 1 } := rfl
@[simp] theorem dec_4 (s : R) : s.dec 4 = { s with ac := s.ac - 1 } := rfl
@[simp] theorem dec_5 (s : R) : s.dec 5 = { s with p1 := s.p1 - 1 } := rfl
@[simp] theorem dec_6 (s : R) : s.dec 6 = { s with p2 := s.p2 - 1 } := rfl
@[simp] theorem dec_7 (s : R) : s.dec 7 = { s with p3 := s.p3 - 1 } := rfl
@[simp] theorem dec_8 (s : R) : s.dec 8 = { s with s1 := s.s1 - 1 } := rfl
@[simp] theorem dec_9 (s : R) : s.dec 9 = { s with s2 := s.s2 - 1 } := rfl

theorem get_set (s : R) (r : Fin 10) (v : Nat) : (s.set r v).get r = v := by
  match r with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩
  | ⟨9, _⟩ => rfl

theorem set_get (s : R) (r : Fin 10) : s.set r (s.get r) = s := by
  match r with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩
  | ⟨9, _⟩ => rfl

theorem set_set (s : R) (r : Fin 10) (v w : Nat) : (s.set r v).set r w = s.set r w := by
  match r with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩
  | ⟨9, _⟩ => rfl

theorem set_eq_of_get {s : R} {r : Fin 10} {v : Nat} (h : s.get r = v) : s.set r v = s := by
  subst h; exact set_get s r

theorem get_set_ne (s : R) {a b : Fin 10} (h : a ≠ b) (v : Nat) : (s.set a v).get b = s.get b := by
  rcases a with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | a, ha⟩ <;>
  rcases b with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | b, hb⟩ <;>
  first | rfl | exact absurd rfl h | omega

theorem set_comm (s : R) {a b : Fin 10} (h : a ≠ b) (v w : Nat) :
    (s.set a v).set b w = (s.set b w).set a v := by
  rcases a with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | a, ha⟩ <;>
  rcases b with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | b, hb⟩ <;>
  first | rfl | exact absurd rfl h | omega

end R

variable {dag : Nat → Option (Ch × Ch)}

/-! ## sequences -/

theorem ex_seq {i : Nat} {c d : Ch} {s t u : R} (hi : dag i = some (c, d))
    (hc : Ex dag c s (.brk 0) t) (hd : Ex dag d t (.brk 0) u) : Ex dag (.node i) s (.brk 0) u :=
  Ex.cdr hi hc hd (by decide)

/-- a car that is done, then `break 1` -/
theorem ex_seqB1 {i : Nat} {c : Ch} {s t : R} (hi : dag i = some (c, .brk 1))
    (hc : Ex dag c s (.brk 0) t) : Ex dag (.node i) s (.brk 1) t :=
  Ex.cdr hi hc (Ex.brk 1 t) (by decide)

/-- the breaker node `(_break.0, X)` runs `X` -/
theorem ex_breaker {i : Nat} {d : Ch} {s t : R} {o : Res} (hi : dag i = some (.brk 0, d))
    (hd : Ex dag d s o t) (ho : adj1 o ≠ .cnt 0) : Ex dag (.node i) s (adj1 o) t :=
  Ex.cdr hi (Ex.brk 0 s) hd ho

/-! ## loops -/

theorem ex_zero {i : Nat} {r : Fin 10} (hi : dag i = some (.dec r, .cnt 1)) :
    ∀ s, Ex dag (.node i) s (.brk 0) (s.set r 0) := by
  intro s
  generalize hn : s.get r = n
  induction n generalizing s with
  | zero =>
    have := Ex.car (o := .brk 1) hi (Ex.decz r s hn) (by decide) (by decide)
    rw [R.set_eq_of_get hn]; exact this
  | succ n ih =>
    refine Ex.restart hi (Ex.decp r s (by omega)) (Ex.cnt 1 _) ?_
    have := ih (s.dec r) (by simp [R.dec, R.get_set, hn])
    simpa [R.dec, R.set_set] using this

/-- `n` rounds of a loop on register `r` with body `g`: decrement `r`, then `g` -/
def loopN (r : Fin 10) (g : R → R) : Nat → R → R
  | 0, s => s
  | n + 1, s => loopN r g n (g (s.dec r))

/-- `while r ≠ 0 (r -= 1; B)`, for a body `B` that keeps the count going down while `P` holds -/
theorem ex_while {i j : Nat} {r : Fin 10} {B : Ch} (hi : dag i = some (.dec r, .node j))
    (hj : dag j = some (B, .cnt 2)) (g : R → R) (hB : ∀ s, Ex dag B s (.brk 0) (g s))
    (P : R → Prop) (hP : ∀ s, P s → 0 < s.get r → P (g (s.dec r)) ∧ (g (s.dec r)).get r = s.get r - 1) :
    ∀ s, P s → Ex dag (.node i) s (.brk 0) (loopN r g (s.get r) s) := by
  intro s hs
  generalize hn : s.get r = n
  induction n generalizing s with
  | zero => exact Ex.car (o := .brk 1) hi (Ex.decz r s hn) (by decide) (by decide)
  | succ n ih =>
    obtain ⟨h1, h2⟩ := hP s hs (by omega)
    refine Ex.restart hi (Ex.decp r s (by omega)) (Ex.cdr (o := .cnt 2) hj (hB _) (Ex.cnt 2 _) (by decide)) ?_
    exact ih _ h1 (by rw [h2, hn]; rfl)

/-- a while loop whose body keeps its register (`P` = true) -/
theorem ex_while' {i j : Nat} {r : Fin 10} {B : Ch} (hi : dag i = some (.dec r, .node j))
    (hj : dag j = some (B, .cnt 2)) (g : R → R) (hB : ∀ s, Ex dag B s (.brk 0) (g s))
    (hg : ∀ s, (g s).get r = s.get r) :
    ∀ s, Ex dag (.node i) s (.brk 0) (loopN r g (s.get r) s) := fun s =>
  ex_while hi hj g hB (fun _ => True)
    (fun s _ hs => ⟨trivial, by rw [hg]; simp [R.dec, R.get_set]⟩) s trivial

/-- the result of a halting test: `halt` or done -/
def hres (b : Bool) : Res := if b then .halt else .brk 0

/-- a done car, then a cdr that halts or is done -/
theorem ex_seqH {i : Nat} {c d : Ch} (hi : dag i = some (c, d)) (fc fd : R → R) (hd' : R → Bool)
    (hc : ∀ s, Ex dag c s (.brk 0) (fc s)) (hd : ∀ s, Ex dag d s (hres (hd' s)) (fd s)) :
    ∀ s, Ex dag (.node i) s (hres (hd' (fc s))) (fd (fc s)) := by
  intro s
  have := Ex.cdr hi (hc s) (hd (fc s)) (by unfold hres; split <;> decide)
  have e : adj1 (hres (hd' (fc s))) = hres (hd' (fc s)) := by unfold hres; split <;> rfl
  rwa [e] at this

/-! ## tests -/

/-- `if_decnz r X`: `(decnz r, X)` with `X` ending in `brk k` -/
theorem ex_if {i : Nat} {r : Fin 10} {d : Ch} {k : Nat} (hi : dag i = some (.dec r, d))
    (f : R → R) (hd : ∀ s, Ex dag d s (.brk k) (f s)) :
    ∀ s, Ex dag (.node i) s (if s.get r = 0 then .brk 0 else .brk k)
      (if s.get r = 0 then s else f (s.dec r)) := by
  intro s
  by_cases h : s.get r = 0
  · simp only [h, if_true]
    exact Ex.car (o := .brk 1) hi (Ex.decz r s h) (by decide) (by decide)
  · simp only [h, if_false]
    exact Ex.cdr (o := .brk k) hi (Ex.decp r s (by omega)) (hd _) (by simp [adj1])

/-- a test `C` (done when `p`, else `brk 1`), then `D` when it was done -/
theorem ex_test {i : Nat} {c d : Ch} (hi : dag i = some (c, d)) (p : R → Prop) [DecidablePred p]
    (fc fd : R → R) (hc : ∀ s, Ex dag c s (if p s then .brk 0 else .brk 1) (fc s))
    (hd : ∀ s, Ex dag d s (.brk 0) (fd s)) :
    ∀ s, Ex dag (.node i) s (.brk 0) (if p s then fd (fc s) else fc s) := by
  intro s
  have := hc s
  by_cases h : p s
  · simp only [h, if_true] at this ⊢
    exact ex_seq hi this (hd _)
  · simp only [h, if_false] at this ⊢
    exact Ex.car (o := .brk 1) hi this (by decide) (by decide)

/-- the halt test: `C` done (then halt) or `brk 1` -/
theorem ex_haltTest {i : Nat} {c : Ch} (hi : dag i = some (c, .halt)) (p : R → Prop) [DecidablePred p]
    (fc : R → R) (hc : ∀ s, Ex dag c s (if p s then .brk 0 else .brk 1) (fc s)) :
    ∀ s, Ex dag (.node i) s (hres (decide (p s))) (fc s) := by
  intro s
  have := hc s
  by_cases h : p s
  · simp only [h, if_true, hres, decide_true] at this ⊢
    exact Ex.cdr (o := .halt) hi this (Ex.halt _) (by decide)
  · simp only [h, if_false, hres, decide_false] at this ⊢
    exact Ex.car (o := .brk 1) hi this (by decide) (by decide)

/-- `(decnz r, X)` with `X` halting or done: done when `r = 0` -/
theorem ex_ifHalt {i : Nat} {r : Fin 10} {d : Ch} (hi : dag i = some (.dec r, d)) (h : R → Bool)
    (f : R → R) (hd : ∀ s, Ex dag d s (hres (h s)) (f s)) :
    ∀ s, Ex dag (.node i) s (hres (s.get r != 0 && h (s.dec r)))
      (if s.get r = 0 then s else f (s.dec r)) := by
  intro s
  by_cases h0 : s.get r = 0
  · simp only [h0, if_true, bne_self_eq_false, Bool.false_and, hres]
    exact Ex.car (o := .brk 1) hi (Ex.decz r s h0) (by decide) (by decide)
  · have hb : (s.get r != 0) = true := by simpa using h0
    simp only [h0, if_false, hb, Bool.true_and]
    have := Ex.cdr hi (Ex.decp r s (by omega)) (hd (s.dec r)) (by unfold hres; split <;> decide)
    have e : adj1 (hres (h (s.dec r))) = hres (h (s.dec r)) := by unfold hres; split <;> rfl
    rwa [e] at this

/-! ## `if_eq`'s loop: decrement two registers together -/

/-- `L = (decnz a, (M, Z))` with `M = (decnz b, continue 2)` and `Z` zeroing `a` then `break 1`:
`brk 0` with `a = 0` and `b` reduced by `a` when `a ≤ b`, else `brk 1` with both zero -/
theorem ex_lockstep {i j m z : Nat} {a b : Fin 10} (hab : a ≠ b)
    (hi : dag i = some (.dec a, .node j)) (hj : dag j = some (.node m, .node z))
    (hm : dag m = some (.dec b, .cnt 2)) (hz : ∀ s, Ex dag (.node z) s (.brk 1) (s.set a 0)) :
    ∀ s, Ex dag (.node i) s (if s.get a ≤ s.get b then .brk 0 else .brk 1)
      (if s.get a ≤ s.get b then (s.set a 0).set b (s.get b - s.get a) else (s.set a 0).set b 0) := by
  intro s
  generalize hn : s.get a = n
  induction n generalizing s with
  | zero =>
    simp only [Nat.zero_le, if_true, Nat.sub_zero]
    have := Ex.car (o := .brk 1) hi (Ex.decz a s hn) (by decide) (by decide)
    rw [R.set_eq_of_get hn, R.set_get]; exact this
  | succ n ih =>
    have ha : 0 < s.get a := by omega
    by_cases hb : s.get b = 0
    · -- `b` runs out first
      have hm' : Ex dag (.node m) (s.dec a) (.brk 0) (s.dec a) := by
        have : (s.dec a).get b = 0 := by simp [R.dec, R.get_set_ne _ hab, hb]
        exact Ex.car (o := .brk 1) hm (Ex.decz b _ this) (by decide) (by decide)
      have hj' := Ex.cdr (o := .brk 1) hj hm' (hz _) (by decide)
      have := Ex.cdr (o := .brk 1) hi (Ex.decp a s ha) hj' (by decide)
      have e : ¬ n + 1 ≤ s.get b := by omega
      simp only [e, if_false]
      simp only [R.dec, R.set_set] at this
      rw [R.set_eq_of_get (by rw [R.get_set_ne _ hab, hb])]
      exact this
    · -- both go down
      have hm' : Ex dag (.node m) (s.dec a) (.cnt 1) ((s.dec a).dec b) :=
        Ex.cdr (o := .cnt 2) hm (Ex.decp b _ (by simp [R.dec, R.get_set_ne _ hab]; omega)) (Ex.cnt 2 _) (by decide)
      have hj' := Ex.car (o := .cnt 1) hj hm' (by decide) (by decide)
      have hget : ((s.dec a).dec b).get a = n := by
        simp [R.dec, R.get_set_ne _ (Ne.symm hab), R.get_set, R.get_set_ne _ hab]; omega
      refine Ex.restart hi (Ex.decp a s ha) hj' ?_
      have := ih ((s.dec a).dec b) hget
      have hb' : ((s.dec a).dec b).get b = s.get b - 1 := by
        simp [R.dec, R.get_set, R.get_set_ne _ hab]
      rw [hb'] at this
      have e2 : ∀ v, (((s.dec a).dec b).set a 0).set b v = (s.set a 0).set b v := by
        intro v
        simp only [R.dec]
        rw [R.set_comm _ hab, R.set_set, R.set_comm _ (Ne.symm hab), R.set_set]
      by_cases hc : n + 1 ≤ s.get b
      · have hc' : n ≤ s.get b - 1 := by omega
        simp only [hc, hc', if_true] at this ⊢
        rw [e2, show s.get b - 1 - n = s.get b - (n + 1) by omega] at this
        exact this
      · have hc' : ¬ n ≤ s.get b - 1 := by omega
        simp only [hc, hc', if_false] at this ⊢
        rw [e2] at this; exact this

/-! ## closed forms of the moving loops -/

theorem loopN_inc (r t : Fin 10) (h : r ≠ t) (n : Nat) (s : R) (hn : n ≤ s.get r) :
    loopN r (fun s => s.inc t) n s = (s.set r (s.get r - n)).set t (s.get t + n) := by
  induction n generalizing s with
  | zero => simp [loopN, R.set_get]
  | succ n ih =>
    rw [loopN, ih _ (by simp [R.inc, R.dec, R.get_set_ne _ h, R.get_set_ne _ (Ne.symm h), R.get_set]; omega)]
    simp only [R.inc, R.dec, R.get_set_ne _ h, R.get_set, R.get_set_ne _ (Ne.symm h)]
    rw [R.set_comm _ (Ne.symm h), show s.get r - 1 - n = s.get r - (n + 1) by omega,
      show s.get t + 1 + n = s.get t + (n + 1) by omega, R.set_set, R.set_set]

theorem loopN_inc2 (r t u : Fin 10) (h1 : r ≠ t) (h2 : r ≠ u) (h3 : t ≠ u) (n : Nat) (s : R)
    (hn : n ≤ s.get r) :
    loopN r (fun s => (s.inc t).inc u) n s =
      ((s.set r (s.get r - n)).set t (s.get t + n)).set u (s.get u + n) := by
  induction n generalizing s with
  | zero => simp [loopN, R.set_get]
  | succ n ih =>
    rw [loopN, ih _ (by simp [R.inc, R.dec, R.get_set_ne _ h1, R.get_set_ne _ h2, R.get_set_ne _ (Ne.symm h1), R.get_set_ne _ (Ne.symm h2), R.get_set_ne _ h3, R.get_set_ne _ (Ne.symm h3), R.get_set]; omega)]
    simp only [R.inc, R.dec, R.get_set_ne _ h1, R.get_set_ne _ h2, R.get_set_ne _ h3, R.get_set,
      R.get_set_ne _ (Ne.symm h1), R.get_set_ne _ (Ne.symm h2), R.get_set_ne _ (Ne.symm h3)]
    rw [show s.get r - 1 - n = s.get r - (n + 1) by omega,
      show s.get t + 1 + n = s.get t + (n + 1) by omega,
      show s.get u + 1 + n = s.get u + (n + 1) by omega]
    -- ((((s.set r x).set t y).set u z).set r X).set t Y).set u Z  ⟶  ((s.set r X).set t Y).set u Z
    rw [R.set_comm _ (Ne.symm h2), R.set_comm _ (Ne.symm h3), R.set_set, R.set_comm _ (Ne.symm h1),
      R.set_set, R.set_set]

end TM.PA
