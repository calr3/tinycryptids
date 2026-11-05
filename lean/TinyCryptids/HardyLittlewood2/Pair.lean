import TinyCryptids.HardyLittlewood2.Trip
import TinyCryptids.HardyLittlewood2.Spec

/-!
# The test at a prime: the cursors, one pair of blocks, all pairs

A pair: the top cursor walks its block right to left (one add per cell), moves to the next
top block; the bottom cursor walks its block (one subtraction per cell) and moves to the next
bottom block, or, when B' is used up, the test ends.
-/

namespace TM.HardyLittlewood2
open St

local notation "F" => false

/-! ## the cursors -/

theorem top_step (n : Nat) (Ub : List Nat) (b jb : Nat) (M : List Nat) (t j : Nat) (Y : Strm)
    (hj : 1 ≤ j) (hjt : j + 1 ≤ t) (h1b : 1 ≤ jb) (hb : jb ≤ b) :
    Rch (TF n Ub b jb M t (j + 1) Y) (TF (max n 1 + 1) Ub b jb M t j Y) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  unfold TF
  show Rch (cfgL Tf (F ::: true ::: true ::: ones i (LT n Ub b jb M)) (ones (t + 1 - (i + 1 + 1)) Y)) _
  gL; gL; gR; gL
  have := add_top n Ub b jb M t (i + 1) Y h1b hb (by omega)
  rw [show t + 1 - (i + 1) = (t + 1 - (i + 1 + 1)) + 1 by omega] at this
  exact this

theorem top_last (n : Nat) (Ub : List Nat) (b jb : Nat) (t' : Nat) (M : List Nat) (t : Nat) (Y : Strm) :
    Rch (TF n Ub b jb (t' :: M) t 1 Y)
      (cfgL H1s (ones t' (LT n Ub b jb M)) (F ::: ones 1 (F ::: F ::: ones (t + 2) Y))) := by
  unfold TF LT
  show Rch (cfgL Tf (F ::: true ::: F ::: F ::: true ::: true ::: ones t'
    (F ::: F ::: bks M (ones (b + 1 - jb) (F ::: ones jb (LB n Ub))))) (ones (t + 1 - 1) Y)) _
  gL; gL; gL; gL; gL; gL
  rw [show t + 1 - 1 = t by omega]
  exact Reach.refl _ _

theorem bot_step (n : Nat) (Ub : List Nat) (b j : Nat) (M : List Nat) (t jt : Nat) (Y : Strm)
    (hj : 1 ≤ j) (hjb : j + 1 ≤ b) :
    Rch (BF n Ub b (j + 1) M t jt Y)
      (cfgL H1s (ones j (LB n Ub)) (F ::: ones (b + 1 - j) (RB M t jt Y))) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  unfold BF
  show Rch (cfgL Bf (F ::: true ::: true ::: ones i (LB n Ub)) (ones (b + 1 - (i + 1 + 1)) (RB M t jt Y))) _
  gL; gL; gR; gL
  rw [show b + 1 - (i + 1) = (b + 1 - (i + 1 + 1)) + 1 by omega]
  exact Reach.refl _ _

theorem bot_last (n : Nat) (b' : Nat) (Ub : List Nat) (b : Nat) (M : List Nat) (t jt : Nat) (Y : Strm) :
    Rch (BF n (b' :: Ub) b 1 M t jt Y)
      (cfgL H1a (ones b' (LB n Ub)) (F ::: ones 1 (RB (M ++ [b]) t jt Y))) := by
  unfold BF LB
  show Rch (cfgL Bf (F ::: true ::: F ::: F ::: true ::: true ::: ones b'
    (F ::: F ::: bks Ub (F ::: F ::: ones n blank))) (ones (b + 1 - 1) (RB M t jt Y))) _
  gL; gL; gL; gL; gL; gL
  unfold RB
  rw [List.reverse_append, show b + 1 - 1 = b by omega]
  exact Reach.refl _ _

theorem bot_end (n b : Nat) (M : List Nat) (t jt : Nat) (Y : Strm) :
    Rch (BF n [] b 1 M t jt Y)
      ⟨EP1, ones (n + 1) blank, true ::: F ::: F ::: ones (b + 2) (RB M t jt Y)⟩ := by
  unfold BF LB
  show Rch (cfgL Bf (F ::: true ::: F ::: F ::: F ::: F ::: ones n blank) (ones (b + 1 - 1) (RB M t jt Y))) _
  gL; gL; gL; gL; gL
  unfold cfgL; gR
  rw [show b + 1 - 1 = b by omega]
  exact Reach.refl _ _

/-! ## the phases -/

theorem top_phase (Ub : List Nat) (b jb : Nat) (M : List Nat) (t : Nat) (Y : Strm)
    (h1b : 1 ≤ jb) (hb : jb ≤ b) :
    ∀ j n, 1 ≤ j → j ≤ t → 1 ≤ n → Rch (TF n Ub b jb M t j Y) (TF (n + j - 1) Ub b jb M t 1 Y)
  | 0, _, h, _, _ => absurd h (by decide)
  | 1, n, _, _, _ => by rw [show n + 1 - 1 = n by omega]; exact Reach.refl _ _
  | j + 2, n, _, hj, hn => by
    refine Rch.tr (top_step n Ub b jb M t (j + 1) Y (by omega) hj h1b hb) ?_
    rw [show max n 1 = n by omega, show n + (j + 2) - 1 = n + 1 + (j + 1) - 1 by omega]
    exact top_phase Ub b jb M t Y h1b hb (j + 1) (n + 1) (by omega) (by omega) (by omega)

theorem bot_phase (Ub : List Nat) (b : Nat) (M : List Nat) (t jt : Nat) (Y : Strm) :
    ∀ j n, 1 ≤ j → j ≤ b → 1 ≤ n →
      (j ≤ n → Rch (BF n Ub b j M t jt Y) (BF (n + 1 - j) Ub b 1 M t jt Y)) ∧
      (n < j → HaltAt (BF n Ub b j M t jt Y))
  | 0, _, h, _, _ => absurd h (by decide)
  | 1, n, _, _, _ => ⟨fun _ => by rw [show n + 1 - 1 = n by omega]; exact Reach.refl _ _,
      fun h => by omega⟩
  | j + 2, n, _, hj, hn => by
    have st := bot_step n Ub b (j + 1) M t jt Y (by omega) hj
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      exact ⟨fun h => by omega, fun _ => HaltAt.back st (sub_bot_halt _ _ _ _ _ _ _)⟩
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      have s2 := Rch.tr st (sub_bot k Ub b (j + 1) M t jt Y (by omega))
      have ih := bot_phase Ub b M t jt Y (j + 1) (k + 1) (by omega) (by omega) (by omega)
      refine ⟨fun h => Rch.tr s2 ?_, fun h => HaltAt.back s2 (ih.2 (by omega))⟩
      rw [show k + 2 + 1 - (j + 2) = k + 1 + 1 - (j + 1) by omega]
      exact ih.1 (by omega)

/-! ## one pair -/

/-- after the bottom cursor moved to its next block (hole at its last cell), before the
top cursor's first add -/
def PS (n : Nat) (Ub : List Nat) (b : Nat) (M : List Nat) (t : Nat) (Y : Strm) : Cfg St :=
  cfgL H1a (ones b (LB n Ub)) (F ::: ones 1 (RB M t t Y))

theorem pair (n e : Nat) (Ub : List Nat) (b t' : Nat) (M : List Nat) (t : Nat) (Y : Strm)
    (he : max n 1 = e + 1) (hb : 1 ≤ b) (ht : 1 ≤ t) (ht' : 1 ≤ t') :
    (b ≤ e + t → Rch (PS n Ub b (t' :: M) t Y)
      (BF (e + t + 1 - b) Ub b 1 M t' t' (F ::: F ::: ones (t + 2) Y))) ∧
    (e + t < b → HaltAt (PS n Ub b (t' :: M) t Y)) := by
  have s1 : Rch (PS n Ub b (t' :: M) t Y) (TF (e + 2) Ub b b (t' :: M) t t Y) := by
    have := add_bot n Ub b b (t' :: M) t t Y hb (Nat.le_refl _) (Nat.le_refl _)
    rw [show b + 1 - b = 1 by omega, he] at this
    exact this
  have s2 := Rch.tr s1 (top_phase Ub b b (t' :: M) t Y hb (Nat.le_refl _) t (e + 2) ht (Nat.le_refl _) (by omega))
  have s3 := Rch.tr s2 (top_last _ Ub b b t' M t Y)
  have s4 : Rch (PS n Ub b (t' :: M) t Y) (BF (e + t) Ub b b M t' t' (F ::: F ::: ones (t + 2) Y)) := by
    have := sub_top (e + t - 1) Ub b b M t' t' (F ::: F ::: ones (t + 2) Y) hb (Nat.le_refl _)
    rw [show e + t - 1 + 2 = e + 2 + t - 1 by omega, show t' + 1 - t' = 1 by omega,
      show e + t - 1 + 1 = e + t by omega] at this
    exact Rch.tr s3 this
  have ph := bot_phase Ub b M t' t' (F ::: F ::: ones (t + 2) Y) b (e + t) hb (Nat.le_refl _) (by omega)
  exact ⟨fun h => Rch.tr s4 (ph.1 h), fun h => HaltAt.back s4 (ph.2 h)⟩

/-! ## all pairs -/

/-- the counter after the pairs (when it never drops below 0) -/
def okE : Nat → List Nat → List Nat → Nat
  | e, t :: ts, b :: bs => okE (e + t - b) ts bs
  | e, _, _ => e

/-- Pairs `(t, b), (Ts, Ub)`. The middle is the tops to come, the parked block `A₁` (a single
cell) and the bottoms done; `Pt` the tops done, `D` the region right of them. -/
theorem run (D : Strm) : ∀ (Ub Ts : List Nat) (e n b t : Nat) (P Pt : List Nat),
    Ts.length = Ub.length → max n 1 = e + 1 → 1 ≤ b → 1 ≤ t →
    (∀ x, x ∈ Ub → 1 ≤ x) → (∀ x, x ∈ Ts → 1 ≤ x) →
    (ok e (t :: Ts) (b :: Ub) →
      Rch (PS n Ub b (Ts ++ 1 :: P) t (F ::: F ::: bks Pt D))
        ⟨EP1, ones (okE e (t :: Ts) (b :: Ub) + 2) blank, true ::: F ::: F ::: bks (P ++ b :: Ub).reverse
          (ones 1 (F ::: ones 1 (F ::: F ::: bks ((t :: Ts).reverse ++ Pt) D)))⟩) ∧
    (¬ ok e (t :: Ts) (b :: Ub) → HaltAt (PS n Ub b (Ts ++ 1 :: P) t (F ::: F ::: bks Pt D)))
  | [], [], e, n, b, t, P, Pt, _, he, hb, ht, _, _ => by
    have pr := pair n e [] b 1 P t (F ::: F ::: bks Pt D) he hb ht (Nat.le_refl _)
    simp only [ok, and_true]
    refine ⟨fun h => Rch.tr (pr.1 h) ?_, fun h => pr.2 (by omega)⟩
    refine Rch.tr (bot_end _ b P 1 1 _) ?_
    simp only [okE, List.reverse_cons, List.reverse_nil, List.nil_append, List.reverse_append,
      List.singleton_append, bks, RB]
    rw [show e + t + 1 - b + 1 = e + t - b + 2 by omega]
    exact Reach.refl _ _
  | [], _ :: _, _, _, _, _, _, _, h, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h, _, _, _, _, _ => by simp at h
  | b' :: Ub, t' :: Ts, e, n, b, t, P, Pt, hl, he, hb, ht, hU, hT => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have pr := pair n e (b' :: Ub) b t' (Ts ++ 1 :: P) t (F ::: F ::: bks Pt D) he hb ht
      (hT t' (List.mem_cons_self _ _))
    have ih := run D Ub Ts (e + t - b) (e + t + 1 - b) b' t' (P ++ [b]) (t :: Pt) hl (by omega)
      (hU b' (List.mem_cons_self _ _)) (hT t' (List.mem_cons_self _ _))
      (fun x hx => hU x (List.mem_cons_of_mem _ hx)) (fun x hx => hT x (List.mem_cons_of_mem _ hx))
    have hstep : b ≤ e + t → Rch (PS n (b' :: Ub) b (t' :: Ts ++ 1 :: P) t (F ::: F ::: bks Pt D))
        (PS (e + t + 1 - b) Ub b' (Ts ++ 1 :: (P ++ [b])) t' (F ::: F ::: bks (t :: Pt) D)) := by
      intro h
      refine Rch.tr (pr.1 h) ?_
      refine Rch.tr (bot_last _ b' Ub b _ t' t' _) ?_
      unfold PS
      rw [List.append_assoc, List.cons_append]
      exact Reach.refl _ _
    simp only [ok]
    constructor
    · rintro ⟨h1, h2⟩
      refine Rch.tr (hstep h1) ?_
      have := ih.1 h2
      simp only [okE, List.append_assoc, List.cons_append, List.nil_append, List.reverse_cons,
        List.singleton_append] at this ⊢
      exact this
    · intro h
      by_cases h1 : b ≤ e + t
      · exact HaltAt.back (hstep h1) (ih.2 (fun h2 => h ⟨h1, h2⟩))
      · exact pr.2 (by omega)

end TM.HardyLittlewood2
