import TinyCryptids.Goldbach.Test

/-!
# Pairs, stages and the main theorem

`Pc p Q`: the P test's entry (`e1` on P's first cell), tape `P s Q` with P = `1^p` and
`QOK Q` (Q's first three cells are 1s; a stale `b` may lie further on).  For even `n = p + q`
the pairs run `p = n - 2, n - 3, …`: `pair_step` either moves to the next stage `(n, 2)` (both
prime) or to `(p - 1, q + 1)`; at `p = 1` the machine halts (`e2` reads `s`).
-/

namespace TMK.Goldbach

open TM (Dir)
open TinyCryptids

def Pc (p : Nat) (Q : List Nat) : Cfg St :=
  ⟨.e1, blank, lst (List.replicate p 1 ++ 5 :: Q) blank⟩

def QOK (Q : List Nat) : Prop := ∃ w, Q = 1 :: 1 :: w ∧ WOK w

theorem sRb {q q' : St} {L : Strm} {w : Nat} (h : delta q 0 = some (w, Dir.R, q')) :
    Rch ⟨q, L, blank⟩ ⟨q', w ∷ L, blank⟩ := by
  have := sR (L := L) (R := blank) h; rwa [cons_blank] at this

theorem sLb {q q' : St} {L : Strm} {w : Nat} (h : delta q 0 = some (w, Dir.L, q')) :
    Rch ⟨q, L, blank⟩ (CL q' L (w ∷ blank)) := by
  have := sL (L := L) (R := blank) h; rwa [cons_blank] at this

theorem map_one (l : List Nat) : (l.map fun _ => 1).reverse = List.replicate l.length 1 := by
  rw [List.map_const', List.reverse_replicate]

/-- the shift: `s` onto P's last cell, back to P's first cell -/
theorem shift (p : Nat) (X : Strm) :
    Rch (CL .sh (lst (List.replicate (p + 1) 1) (0 ∷ blank)) (1 ∷ X))
      ⟨.e1, blank, lst (List.replicate p 1) (5 ∷ 1 ∷ X)⟩ := by
  simp only [List.replicate_succ, lst_cons, CL_cons]
  gL; rLn p; gR
  simp only [tl_blank, cons_blank]; fin

/-- the P test starts: the boundary on P's third cell -/
theorem p_entry (p : Nat) (Q : List Nat) :
    Reach1 delta (Pc (p + 2) Q) (T 0 5 blank (lst Q blank) 2 (List.replicate p 1)) := by
  simp only [Pc, lst_append]
  refine Sys.Reach1.trans_reach (stepR1 (R := lst (List.replicate (p + 2) 1) (lst (5 :: Q) blank)) rfl) ?_
  gR
  simp only [T, lst_cons, cons_blank]
  fin

/-- `p = 1`: the counterexample; `e2` reads the separator -/
theorem p_halt (Q : List Nat) : ∃ c, Rch (Pc 1 Q) c ∧ c.q = .e2 ∧ c.R 0 = 5 :=
  ⟨_, sR (by rfl), rfl, rfl⟩

/-- P is prime: the Q test starts -/
theorem q_entry (p : Nat) (w : List Nat) :
    Rch (T 0 5 blank (lst (1 :: 1 :: w) blank) p [])
      (T 5 0 (lst (List.replicate p 1) (0 ∷ blank)) blank 2 w) := by
  simp only [T, lst_nil, lst_cons]
  gR; gR; gR
  simp only [List.replicate, lst_cons, cons_blank]
  fin

/-- Q is prime too: the next stage `(p + q, 2)` -/
theorem grow (p q : Nat) :
    Rch (T 5 0 (lst (List.replicate p 1) (0 ∷ blank)) blank (q + 1) []) (Pc (p + q + 1) [1, 1]) := by
  simp only [T, lst_nil]
  gR
  refine Rch.tr (sLb (by rfl)) ?_
  simp only [CL_cons]
  gL
  simp only [List.replicate_succ, lst_cons, CL_cons]
  gL; rLn q
  simp only [CL_cons]
  gL; rLn p; gR
  simp only [Pc, lst_append, lst_rep_add, List.replicate_succ, lst_cons, cons_blank, lst_nil]
  rw [lst_rep_comm]; simp only [tl_blank, cons_blank]; fin

/-- P is composite: erase its `b`, go to the separator and shift -/
theorem p_comp (m k : Nat) (Q : List Nat) :
    Rch (Cx 0 5 blank (lst Q blank) m k) (Pc (m + k) (1 :: Q)) := by
  simp only [Cx]
  gR
  have := walkR (q := .kr) (fun _ => 1) (List.replicate m 1 ++ 4 :: List.replicate k 1)
    (0 ∷ blank) (5 ∷ lst Q blank) (fun a h => by
      simp only [List.mem_append, List.mem_cons, List.mem_replicate] at h
      rcases h with ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ <;> rfl)
  refine Rch.tr this ?_
  rw [map_one]
  gL
  simp only [List.length_append, List.length_replicate, List.length_cons]
  refine Rch.tr (shift (m + k) _) ?_
  simp only [Pc, lst_append, lst_cons]; fin

/-- Q is composite: shift at once (Q keeps its `b`) -/
theorem q_comp (p m k : Nat) :
    Rch (Cx 5 0 (lst (List.replicate (p + 1) 1) (0 ∷ blank)) blank m k)
      (Pc p (1 :: (List.replicate m 1 ++ 4 :: List.replicate k 1))) := by
  simp only [Cx]
  gL
  refine Rch.tr (shift p _) ?_
  simp only [Pc, lst_append, lst_cons, cons_blank]; fin

/-- one pair `(p, q)`, `p ≥ 2` -/
theorem pair_step (p : Nat) (Q : List Nat) (hQ : QOK Q) (hp : 2 ≤ p) :
    (Prime p ∧ Prime Q.length → Reach1 delta (Pc p Q) (Pc (p + Q.length) [1, 1])) ∧
    (¬ (Prime p ∧ Prime Q.length) → ∃ Q', QOK Q' ∧ Q'.length = Q.length + 1 ∧
      Reach1 delta (Pc p Q) (Pc (p - 1) Q')) := by
  obtain ⟨p, rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  obtain ⟨w, rfl, hw⟩ := hQ
  have e := p_entry p (1 :: 1 :: w)
  have tp := test (l := 0) (rr := 5) (Lc := blank) (Rc := lst (1 :: 1 :: w) blank) rfl rfl p 2
    (List.replicate p 1) (by simp) (Nat.le_refl _) (WOK_rep p) (fun e h1 h2 => by omega)
  rw [Nat.add_comm 2 p] at tp
  have tq := test (l := 5) (rr := 0) (Lc := lst (List.replicate (p + 2) 1) (0 ∷ blank)) (Rc := blank)
    rfl rfl w.length 2 w rfl (Nat.le_refl _) hw (fun e h1 h2 => by omega)
  simp only [List.length_cons]
  rw [show w.length + 1 + 1 = 2 + w.length by omega]
  refine ⟨fun ⟨hpp, hqp⟩ => ?_, fun hno => ?_⟩
  · refine Sys.Reach1.trans_reach e (Rch.tr (tp.1 hpp) (Rch.tr (q_entry (p + 2) w)
      (Rch.tr (tq.1 hqp) ?_)))
    have := grow (p + 2) (1 + w.length)
    rwa [show 1 + w.length + 1 = 2 + w.length by omega,
      show p + 2 + (1 + w.length) + 1 = p + 2 + (2 + w.length) by omega] at this
  · by_cases hpp : Prime (p + 2)
    · have hqp : ¬ Prime (2 + w.length) := fun h => hno ⟨hpp, h⟩
      obtain ⟨m, k, hm, hmk, hr⟩ := tq.2 hqp
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
      refine ⟨_, ⟨1 :: (List.replicate m 1 ++ 4 :: List.replicate k 1), rfl,
        Or.inr ⟨_, rfl, fun a h => ?_⟩⟩, ?_, Sys.Reach1.trans_reach e (Rch.tr (tp.1 hpp)
          (Rch.tr (q_entry (p + 2) w) (Rch.tr hr (by exact q_comp (p + 1) (m + 2) k))))⟩
      · simp only [List.mem_append, List.mem_cons, List.mem_replicate] at h; omega
      · simp; omega
    · obtain ⟨m, k, hm, hmk, hr⟩ := tp.2 hpp
      refine ⟨1 :: 1 :: 1 :: w, ⟨1 :: w, rfl, Or.inr ⟨w, rfl, ?_⟩⟩, by simp; omega, ?_⟩
      · rcases hw with rfl | ⟨v, rfl, hv⟩
        · intro a h; simp at h
        · intro a h; rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl rfl
          · exact hv a h
      · have := Sys.Reach1.trans_reach e (Rch.tr hr (p_comp m k (1 :: 1 :: w)))
        rwa [show m + k = p + 2 - 1 by omega] at this

/-! ## The boot, by computation on finite tapes (as `PAK/Boot.lean`) -/

structure LCfg where
  q : St
  L : List Nat
  R : List Nat
  deriving DecidableEq

def LCfg.toCfg (c : LCfg) : Cfg St := ⟨c.q, lst c.L blank, lst c.R blank⟩

def lstep (c : LCfg) : Option LCfg :=
  match delta c.q (c.R.headD 0) with
  | none => none
  | some (w, .R, q') => some ⟨q', w :: c.L, c.R.tail⟩
  | some (w, .L, q') => some ⟨q', c.L.tail, c.L.headD 0 :: w :: c.R.tail⟩

def lrun : Nat → LCfg → Option LCfg
  | 0, c => some c
  | n + 1, c => match lstep c with
    | none => none
    | some c' => lrun n c'

theorem lst_head (l : List Nat) : lst l blank 0 = l.headD 0 := by
  cases l <;> rfl

theorem lst_tail (l : List Nat) : tl (lst l blank) = lst l.tail blank := by
  cases l <;> rfl

theorem lstep_ok {c c' : LCfg} (h : lstep c = some c') : step delta c.toCfg = some c'.toCfg := by
  unfold lstep at h
  unfold step LCfg.toCfg
  simp only [lst_head]
  revert h
  cases delta c.q (c.R.headD 0) with
  | none => intro h; cases h
  | some t =>
    obtain ⟨w, d, q'⟩ := t
    cases d with
    | R => intro h; cases h; simp [lst_tail]
    | L => intro h; cases h; simp [lst_tail, lst_head]

theorem lrun_ok : ∀ (n : Nat) (c c' : LCfg), lrun n c = some c' → Rch c.toCfg c'.toCfg := by
  intro n
  induction n with
  | zero => intro c c' h; cases h; exact Reach.refl _ _
  | succ n ih =>
    intro c c' h
    unfold lrun at h
    cases hs : lstep c with
    | none => rw [hs] at h; cases h
    | some c1 =>
      rw [hs] at h
      exact Reach.trans _ (reach_step _ (lstep_ok hs)) (ih c1 c' h)

/-- from the blank tape to the first pair `(2, 2)` in 13 steps -/
theorem boot : Rch start (Pc 2 [1, 1]) := by
  have h := lrun_ok 13 ⟨.mark, [], []⟩ ⟨.e1, [0], [1, 1, 5, 1, 1]⟩ (by decide)
  simp only [LCfg.toCfg, lst_cons, lst_nil, cons_blank] at h
  exact h

/-! ## The main theorem -/

/-- the machine reaches its halting configuration: `e2` reading the separator -/
def HaltAt (c : Cfg St) : Prop := ∃ c', Rch c c' ∧ c'.q = .e2 ∧ c'.R 0 = 5

theorem HaltAt.back {a b : Cfg St} (h : Rch a b) (hb : HaltAt b) : HaltAt a :=
  let ⟨c, hc, h1, h2⟩ := hb; ⟨c, Rch.tr h hc, h1, h2⟩

theorem QOK_two : QOK [1, 1] := ⟨[], rfl, Or.inl rfl⟩

/-- below a counterexample `2N`, every pair is either passed or leads on to `2N` -/
theorem halt_from (N : Nat) (hN : ∀ p q, Prime p → Prime q → p + q ≠ 2 * N) :
    ∀ t p Q, QOK Q → 1 ≤ p → (p + Q.length) % 2 = 0 → p + Q.length ≤ 2 * N →
      2 * N - (p + Q.length) = t → HaltAt (Pc p Q) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t iht =>
    intro p
    induction p using Nat.strongRecOn with
    | _ p ihp =>
      intro Q hQ hp1 hev hle ht
      rcases Nat.lt_or_ge p 2 with hp | hp
      · obtain ⟨c, hc, h1, h2⟩ := p_halt Q
        rw [show p = 1 by omega]; exact ⟨c, hc, h1, h2⟩
      have st := pair_step p Q hQ hp
      by_cases hb : Prime p ∧ Prime Q.length
      · have hne : p + Q.length ≠ 2 * N := hN _ _ hb.1 hb.2
        exact HaltAt.back (st.1 hb).reach (iht (2 * N - (p + Q.length + 2)) (by omega)
          (p + Q.length) [1, 1] QOK_two (by omega) (by simp; omega) (by simp; omega) (by simp))
      · obtain ⟨Q', hQ', hl, hr⟩ := st.2 hb
        exact HaltAt.back hr.reach (ihp (p - 1) (by omega) Q' hQ' (by omega) (by omega) (by omega)
          (by omega))

/-- If Goldbach's conjecture fails, the machine reaches its halting configuration. -/
theorem haltAt_of (h : ∃ n, 2 ≤ n ∧ ∀ p q, Prime p → Prime q → p + q ≠ 2 * n) :
    ∃ c, Rch start c ∧ c.q = .e2 ∧ c.R 0 = 5 := by
  obtain ⟨N, hN2, hN⟩ := h
  exact HaltAt.back boot (halt_from N hN _ 2 [1, 1] QOK_two (by omega) rfl (by simp; omega) rfl)

/-- **Main theorem.** Started on a blank tape, the design halts if and only if some even
number `2n ≥ 4` is not the sum of two primes. -/
theorem halts_iff : Halts delta start ↔
    ∃ n, 2 ≤ n ∧ ∀ p q, Prime p → Prime q → p + q ≠ 2 * n := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    let I : Cfg St → Prop := fun c => ∃ p Q, c = Pc p Q ∧ QOK Q ∧ 1 ≤ p ∧
      (p + Q.length) % 2 = 0 ∧ 4 ≤ p + Q.length ∧
      ∀ a, p < a → a + 2 ≤ p + Q.length → ¬ (Prime a ∧ Prime (p + Q.length - a))
    have prog : ∀ c, I c → ∃ c', I c' ∧ Reach1 delta c c' := by
      rintro c ⟨p, Q, rfl, hQ, hp1, hev, h4, hbelow⟩
      have hp : 2 ≤ p := by
        apply Classical.byContradiction; intro hp
        refine hno ⟨(p + Q.length) / 2, by omega, fun a b ha hb hab => ?_⟩
        have := ha.two_le; have := hb.two_le
        exact hbelow a (by omega) (by omega) ⟨ha, by rw [show p + Q.length - a = b by omega]; exact hb⟩
      have st := pair_step p Q hQ hp
      by_cases hb : Prime p ∧ Prime Q.length
      · exact ⟨_, ⟨p + Q.length, [1, 1], rfl, QOK_two, by omega, by simp; omega, by simp; omega,
          fun a h1 h2 => by simp at h2; omega⟩, st.1 hb⟩
      · obtain ⟨Q', hQ', hl, hr⟩ := st.2 hb
        refine ⟨_, ⟨p - 1, Q', rfl, hQ', by omega, by omega, by omega, fun a h1 h2 => ?_⟩, hr⟩
        rcases Nat.lt_or_ge p a with h | h
        · rw [show p - 1 + Q'.length = p + Q.length by omega]
          exact hbelow a h (by omega)
        · rw [show a = p by omega, show p - 1 + Q'.length - p = Q.length by omega]; exact hb
    have hI : I (Pc 2 [1, 1]) := ⟨2, [1, 1], rfl, QOK_two, by omega, rfl, by simp,
      fun a h1 h2 => by simp at h2; omega⟩
    exact Sys.not_halts_of_progress I prog _ hI (Sys.Halts.of_reach boot hH)
  · intro h
    obtain ⟨c, hc, hq, hs⟩ := haltAt_of h
    obtain ⟨q, L, R⟩ := c
    simp only at hq hs
    subst hq
    exact Sys.Reach.halts hc (halt_none (by rw [hs]; rfl))

end TMK.Goldbach
