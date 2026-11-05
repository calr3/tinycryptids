import TinyCryptids.HardyLittlewood2.Rebuild

/-!
# The main theorem

Checkpoints: `CK m g c` before the trial division of the candidate `m` (gaps `g` of the
`Q`-elements below `m`, next gap `c`), `PC m g c` when `m` turned out prime. Without a
counterexample each checkpoint reaches the next (`not_halts_of_progress`); with one, the
test at the largest prime up to `x + y` halts (`complete`).
-/

namespace TM.HardyLittlewood2
open St TinyCryptids

local notation "F" => false

def CK (m : Nat) (g : List Nat) (c : Nat) : Cfg St := MW (XG g c) 3 (m - 3) 0 1
def PC (m : Nat) (g : List Nat) (c : Nat) : Cfg St := P6 (XG g c) m

theorem ones_blank_get (a i : Nat) : ones a blank i = decide (i < a) := by
  induction a generalizing i with
  | zero => simp [blank]
  | succ a ih => cases i with
    | zero => show true = _; simp
    | succ i => show ones a blank i = _; rw [ih]; simp

theorem ck_R (m : Nat) (g : List Nat) (c i : Nat) : (CK m g c).R (i + 8) = decide (i < m - 3) := by
  show ones (m - 3 + 1 - 1) blank i = _
  rw [ones_blank_get, Nat.add_sub_cancel]

/-- a run between two different configurations takes at least one step -/
theorem reach1_of_ne {a b : Cfg St} (h : Rch a b) (hne : a ≠ b) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem okE_sum : ∀ (e : Nat) (ts bs : List Nat), ts.length = bs.length → ok e ts bs →
    okE e ts bs + ssum bs = e + ssum ts
  | e, [], [], _, _ => by simp [okE, ssum]
  | _, [], _ :: _, h, _ => by simp at h
  | _, _ :: _, [], h, _ => by simp at h
  | e, t :: ts, b :: bs, h, ⟨h1, h2⟩ => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have := okE_sum (e + t - b) ts bs h h2
    simp only [okE, ssum]; omega

/-! ## one candidate -/

theorem cand {m : Nat} {g : List Nat} {c : Nat} (hi : Inv m g c) (h7 : 7 ≤ m) :
    (Q m → Rch (CK m g c) (PC m g c)) ∧ (¬ Q m → Rch1 (CK m g c) (CK (m + 2) g (c + 1))) := by
  have ho := hi.odd
  have t := test (XG g c) (m - 4) 3 (Nat.le_refl _) (fun e h1 h2 => by
    rw [show e = 2 by omega, show 3 + (m - 4) + 1 = m by omega]; omega)
  rw [show 3 + (m - 4) + 1 = m by omega, show m - 4 + 1 = m - 3 by omega] at t
  refine ⟨fun hq => t.1 ((q_iff_prime (by omega)).1 hq), fun hq => ?_⟩
  obtain ⟨d, r, hdr, hd, hr, h⟩ := t.2 (fun hp => hq ((q_iff_prime (by omega)).2 hp))
  have st := Rch.tr h (comp_rebuild _ (c + 1) d r hd hr)
  rw [show d + r - 1 = m + 2 - 3 by omega] at st
  have st' : Rch (CK m g c) (CK (m + 2) g (c + 1)) := st
  refine reach1_of_ne st' fun hc => ?_
  have := congrArg (fun c => c.R (m - 3 + 8)) hc
  simp only [ck_R] at this
  simp at this; omega

/-! ## the test at a prime -/

theorem Inv.pq_m {m : Nat} {g : List Nat} {c : Nat} (h : Inv m g c) (hq : Q m) : pq m = g.length + 2 := by
  have := h.top; have := h.ge
  rw [show m = (m - 1) + 1 by omega, pq_succ, show m - 1 + 1 = m by omega, if_pos hq]; omega

theorem test_prime {m : Nat} {g : List Nat} {c : Nat} (hi : Inv m g c) (hq : Q m) :
    (¬ bad (g ++ [c]) → Rch (PC m g c) (CK (m + 2) (g ++ [c]) 1)) ∧
    (bad (g ++ [c]) → HaltAt (PC m g c)) := by
  obtain ⟨g₀, rfl⟩ := hi.hd
  have hm5 := hi.ge
  have hc := hi.c1
  have st1 := Rch.tr (start_check g₀ c m hc (by omega)) (bot_last 0 1 g₀ 1 g₀.reverse c c (F ::: F ::: D0 m))
  have hr := run (D0 m) g₀ g₀.reverse 0 0 1 c [] [] (by simp) rfl (Nat.le_refl _) hc
    (fun x hx => hi.pos x (List.mem_cons_of_mem _ hx))
    (fun x hx => hi.pos x (List.mem_cons_of_mem _ (List.mem_reverse.1 hx)))
  have hok := ok_iff_bad g₀ c
  constructor
  · intro hb
    have hk := hok.2 hb
    have e1 := okE_sum 0 _ _ (by simp) hk
    simp only [ssum, ssum_reverse] at e1
    have r := hr.1 hk
    rw [show okE 0 (c :: g₀.reverse) (1 :: g₀) + 2 = c + 1 by omega] at r
    rw [List.nil_append, show (c :: g₀.reverse).reverse ++ [] = g₀ ++ [c] by simp] at r
    refine Rch.tr st1 (Rch.tr r (Rch.tr (end_check g₀ c m (by omega)) ?_))
    refine Rch.tr (prime_rebuild _ m hm5) ?_
    unfold CK XG
    simp only [List.cons_append, List.tail_cons, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, bks]
    rw [show m + 2 - 3 = m - 1 by omega]
    exact Reach.refl _ _
  · intro hb
    exact HaltAt.back st1 (hr.2 (fun h => hok.1 h hb))

/-! ## all candidates -/

theorem seed_reach : Rch start (PC 5 [1] 1) := by
  unfold start PC P6 XG
  simp only [List.tail_cons, List.reverse_nil, bks]
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  simp only [cons_blank]
  exact Reach.refl _ _

theorem not_bad_five : ¬ bad (1 :: [] ++ [1]) := by
  rintro ⟨i, h1, h2, h3⟩
  simp at h2
  rw [show i = 1 by omega] at h3
  exact absurd h3 (by decide)

theorem first_ck : Rch start (CK 7 [1, 1] 1) :=
  Rch.tr seed_reach ((test_prime inv_five (Or.inr ⟨rfl, by decide⟩)).1 not_bad_five)

theorem inv_seven : Inv 7 [1, 1] 1 := inv_five.prime (Or.inr ⟨rfl, by decide⟩)

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- every candidate from 7 on is reached, unless the machine halts first -/
theorem reach_all : ∀ j, HaltAt start ∨ ∃ g c, Inv (7 + 2 * j) g c ∧ Rch start (CK (7 + 2 * j) g c)
  | 0 => Or.inr ⟨[1, 1], 1, inv_seven, first_ck⟩
  | j + 1 => by
    rcases reach_all j with h | ⟨g, c, hi, hr⟩
    · exact Or.inl h
    rw [show 7 + 2 * (j + 1) = 7 + 2 * j + 2 by omega]
    by_cases hq : Q (7 + 2 * j)
    · have tp := test_prime hi hq
      have r1 := Rch.tr hr ((cand hi (by omega)).1 hq)
      by_cases hb : bad (g ++ [c])
      · exact Or.inl (HaltAt.back r1 (tp.2 hb))
      · exact Or.inr ⟨g ++ [c], 1, hi.prime hq, Rch.tr r1 (tp.1 hb)⟩
    · exact Or.inr ⟨g, c + 1, hi.comp hq, Rch.tr hr ((cand hi (by omega)).2 hq).reach⟩

/-- without a counterexample the checkpoints go on forever -/
theorem no_halt (h : ¬ ∃ x y, 2 ≤ x ∧ 2 ≤ y ∧ primeCount x + primeCount y < primeCount (x + y)) :
    ¬ Halts delta (CK 7 [1, 1] 1) := by
  refine not_halts_of_progress delta
    (fun cf => ∃ m g c, Inv m g c ∧ 7 ≤ m ∧ cf = CK m g c) ?_ _ ⟨7, [1, 1], 1, inv_seven, Nat.le_refl _, rfl⟩
  rintro cf ⟨m, g, c, hi, h7, rfl⟩
  by_cases hq : Q m
  · have hnb : ¬ bad (g ++ [c]) := fun hb => h (sound (hi.prime hq).fit hb)
    refine ⟨CK (m + 2) (g ++ [c]) 1, ⟨m + 2, g ++ [c], 1, hi.prime hq, by omega, rfl⟩, ?_⟩
    refine Reach.trans_reach1 delta ((cand hi h7).1 hq) (reach1_of_ne ((test_prime hi hq).1 hnb) ?_)
    intro he; have := congrArg Cfg.q he; simp [PC, CK, P6, MW] at this
  · exact ⟨CK (m + 2) g (c + 1), ⟨m + 2, g, c + 1, hi.comp hq, by omega, rfl⟩, (cand hi h7).2 hq⟩

/-- with a counterexample the design reaches its halting state -/
theorem haltAt_of (h : ∃ x y, 2 ≤ x ∧ 2 ≤ y ∧ primeCount x + primeCount y < primeCount (x + y)) :
    HaltAt start := by
  obtain ⟨x, y, hx, hy, hc⟩ := h
  rw [primeCount_eq x hx, primeCount_eq y hy, primeCount_eq (x + y) (by omega)] at hc
  obtain ⟨m, hmn, hq, hpm⟩ := last_q (x + y) (by omega)
  have h5 : 5 ≤ m := by
    have := pq_pos (show 1 ≤ x by omega); have := pq_pos (show 1 ≤ y by omega)
    rcases Nat.lt_or_ge m 5 with h | h
    · have : pq m ≤ 2 := by
        have := pq_mono (show m ≤ 4 by omega)
        rw [show pq 4 = 2 by decide] at this; exact this
      omega
    · exact h
  have hodd : m % 2 = 1 := by rcases hq with h | ⟨h, _⟩ <;> omega
  rcases Nat.lt_or_ge m 7 with h7 | h7
  · obtain rfl : m = 5 := by omega
    exfalso
    have hb := complete (inv_five.prime hq).fit hx hy hc
      (by rw [← hpm, inv_five.pq_m hq]; rfl) (by simp [ssum]; omega)
    exact not_bad_five hb
  · obtain ⟨j, rfl⟩ : ∃ j, m = 7 + 2 * j := ⟨(m - 7) / 2, by omega⟩
    rcases reach_all j with hh | ⟨g, c, hi, hr⟩
    · exact hh
    have hb := complete (hi.prime hq).fit hx hy hc
      (by rw [← hpm, hi.pq_m hq]; simp) (by have := hi.hm; rw [ssum_append]; simp [ssum]; omega)
    exact HaltAt.back (Rch.tr hr ((cand hi h7).1 hq)) ((test_prime hi hq).2 hb)

/-- **Main theorem.** Started on a blank tape, the design halts if and only if the second
Hardy–Littlewood conjecture fails: `π(x) + π(y) < π(x + y)` for some `x, y ≥ 2`. -/
theorem halts_iff :
    Halts delta start ↔ ∃ x y, 2 ≤ x ∧ 2 ≤ y ∧ primeCount x + primeCount y < primeCount (x + y) := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro h
    exact no_halt h (halts_det hH first_ck)
  · exact fun h => (haltAt_of h).halts

end TM.HardyLittlewood2
