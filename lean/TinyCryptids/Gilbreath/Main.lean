import TinyCryptids.Gilbreath.Update

/-!
# Main theorem: the design halts iff Gilbreath's conjecture fails

Between candidates the machine is in `RC g S e m`: the candidate `m` (trial division about to
start), the stored diagonal `S` (the last diagonal of the triangle on the primes below `m`
without its first entry) and `g = m - p`, `p` the last prime below `m`.
-/

namespace TM.Gilbreath
open St TinyCryptids

local notation "F" => false

/-- before testing `m` -/
def RC (g : Nat) (S : List Nat) (e m : Nat) : Cfg St := SHT (XS g S.reverse e) 2 (m - 2)

/-! ## the update, value by value -/

theorem upd : ∀ (t : List Nat) (v c : Nat) (os : List Nat) (e : Nat) (Y : Strm),
    (lst (ext (v :: t) c) = 1 → ∃ e', Rch (CA 0 c 1 os t.reverse v e (true ::: F ::: true ::: Y))
      ⟨c1, true ::: F ::: true ::: F ::: F ::: XS 1 ((ext (v :: t) c).reverse ++ os) e', Y⟩) ∧
    (lst (ext (v :: t) c) ≠ 1 → HaltAt (CA 0 c 1 os t.reverse v e (true ::: F ::: true ::: Y)))
  | [], v, c, os, e, Y => by
    obtain ⟨e', h⟩ := step c v os [] e (true ::: F ::: true ::: Y)
    have hl : lst (ext [v] c) = ad c v := rfl
    rw [hl]
    refine ⟨fun h1 => ⟨e' + 7, ?_⟩, fun h1 => HaltAt.back h (final_halt _ c os e' _ h1)⟩
    rw [h1] at h
    have : (ext [v] c).reverse ++ os = 1 :: c :: os := by simp [ext, h1]
    rw [this]
    exact Rch.tr h (final_ok c os e' Y)
  | w :: t, v, c, os, e, Y => by
    obtain ⟨e', h⟩ := step c v os (t.reverse ++ [w]) e (true ::: F ::: true ::: Y)
    have h2 := Rch.tr h (step_end (ad c v) c os t.reverse w e' (true ::: F ::: true ::: Y))
    have ih := upd t w (ad c v) (c :: os) (e' + 5) Y
    have hl : lst (ext (v :: w :: t) c) = lst (ext (w :: t) (ad c v)) := lst_ext_cons v (w :: t) c
    have hr : (ext (v :: w :: t) c).reverse ++ os = (ext (w :: t) (ad c v)).reverse ++ c :: os := by
      show (c :: ext (w :: t) (ad c v)).reverse ++ os = _
      simp
    rw [hl, hr]
    simp only [List.reverse_cons] at *
    refine ⟨fun h1 => ?_, fun h1 => HaltAt.back h2 (ih.2 h1)⟩
    obtain ⟨e'', h3⟩ := ih.1 h1
    exact ⟨e'', Rch.tr h2 h3⟩

/-! ## one candidate -/

theorem rc_composite (g : Nat) (S : List Nat) (e m : Nat) (hm : 2 ≤ m) (hp : ¬ Prime m) :
    Rch (RC g S e m) (RC (g + 1) S e (m + 1)) := by
  obtain ⟨d, r, hdr, hd, h⟩ := (cand (XS g S.reverse e) m hm).2 hp
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  unfold RC
  refine Rch.tr h (Rch.tr (composite g S.reverse e d' r) ?_)
  have := rebuild (XS (g + 1) S.reverse e) d' r
  rw [show m + 1 - 2 = d' + r + 1 by omega]
  exact this

theorem rc_prime (g : Nat) (v : Nat) (t : List Nat) (e m : Nat) (hm : 2 ≤ m) (hp : Prime m) :
    (lst (ext (v :: t) g) = 1 → ∃ e', Rch (RC g (v :: t) e m) (RC 1 (ext (v :: t) g) e' (m + 1))) ∧
    (lst (ext (v :: t) g) ≠ 1 → HaltAt (RC g (v :: t) e m)) := by
  have h1 := (cand (XS g (v :: t).reverse e) m hm).1 hp
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have h2 := prime_start g t.reverse v e (F ::: ones (k + 2) (F ::: F ::: ones 2 blank))
  have hst : Rch (RC g (v :: t) e (k + 2)) (CA 0 g 1 [] t.reverse v (e + 1)
      (true ::: F ::: true ::: ones (k + 1) (F ::: F ::: ones 2 blank))) := by
    unfold RC
    simp only [List.reverse_cons] at h1 ⊢
    exact Rch.tr h1 h2
  have u := upd t v g [] (e + 1) (ones (k + 1) (F ::: F ::: ones 2 blank))
  refine ⟨fun hl => ?_, fun hl => HaltAt.back hst (u.2 hl)⟩
  obtain ⟨e', h3⟩ := u.1 hl
  refine ⟨e', Rch.tr hst (Rch.tr h3 ?_)⟩
  have := rebuild (XS 1 (ext (v :: t) g).reverse e') k 0
  unfold RC
  rw [List.append_nil] at *
  rw [show k + 2 + 1 - 2 = k + 0 + 1 by omega]
  exact this

/-! ## the invariant: `RC` follows the last diagonal `D m` -/

/-- the machine before testing `m`, with `D m = p :: S` -/
def Inv (m : Nat) (c : Cfg St) : Prop :=
  ∃ p v t e, D m = p :: v :: t ∧ p < m ∧ c = RC (m - p) (v :: t) e m

/-- a run between two different configurations takes at least one step -/
theorem reach1_of_ne {a b : Cfg St} (h : Rch a b) (hne : a ≠ b) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem ones_blank_get (a i : Nat) : ones a blank i = decide (i < a) := by
  induction a generalizing i with
  | zero => simp [blank]
  | succ a ih => cases i with
    | zero => show true = _; simp
    | succ i => show ones a blank i = _; rw [ih]; simp

/-- the counterexample test at `m`: no counterexample at `m` -/
def Ok (m : Nat) : Prop := Prime m → lst (ext (D m) m) = 1

theorem inv_step (m : Nat) (hm : 4 ≤ m) (c : Cfg St) (hc : Inv m c) :
    (Ok m → ∃ c', Inv (m + 1) c' ∧ Rch1 c c') ∧ (¬ Ok m → HaltAt c) := by
  obtain ⟨p, v, t, e, hD, hpm, rfl⟩ := hc
  by_cases hp : Prime m
  · have hD' : D (m + 1) = m :: ext (v :: t) (m - p) := by
      rw [D, if_pos hp, hD]; show m :: ext (v :: t) (ad m p) = _
      rw [show ad m p = m - p by unfold ad; split <;> omega]
    have hl : lst (ext (D m) m) = lst (ext (v :: t) (m - p)) := by
      rw [hD, lst_ext_cons]; rw [show ad m p = m - p by unfold ad; split <;> omega]
    have r := rc_prime (m - p) v t e m (by omega) hp
    obtain ⟨v', t', he⟩ : ∃ v' t', ext (v :: t) (m - p) = v' :: t' := ⟨_, _, rfl⟩
    refine ⟨fun hok => ?_, fun hok => r.2 (fun h => hok (fun _ => by rw [hl]; exact h))⟩
    obtain ⟨e', h⟩ := r.1 (by rw [← hl]; exact hok hp)
    rw [he] at h hD'
    refine ⟨_, ⟨m, v', t', e', hD', by omega, by rw [show m + 1 - m = 1 by omega]⟩,
      reach1_of_ne h ?_⟩
    intro e1
    have := congrArg (fun c : Cfg St => c.R) e1
    simp only [RC, SHT] at this
    have h2 := congrFun this (m - 2 + 2)
    simp [ones_blank_get] at h2
    omega
  · have hD' : D (m + 1) = p :: v :: t := by rw [D, if_neg hp, hD]
    refine ⟨fun _ => ⟨_, ⟨p, v, t, e, hD', by omega, rfl⟩, reach1_of_ne ?_ ?_⟩,
      fun hok => absurd (fun h => absurd h hp) hok⟩
    · rw [show m + 1 - p = m - p + 1 by omega]
      exact rc_composite (m - p) (v :: t) e m (by omega) hp
    · intro e1
      have := congrArg (fun c : Cfg St => c.R) e1
      simp only [RC, SHT] at this
      have h2 := congrFun this (m - 2 + 2)
      simp [ones_blank_get] at h2
      omega

/-! ## the seed and the main theorem -/

theorem D4 : D 4 = [3, 1] := by decide

theorem seed_reach : Rch start (RC 1 [1] 0 4) := by
  unfold start
  iterate 39 (first | gR | gL | (refine blankR ?_; gR) | gL0)
  unfold RC SHT XS RL
  simp [blocks3, app_append, app_replicate]
  fin

/-- before candidate `4 + k`, if no earlier candidate was a counterexample -/
theorem reach_k : ∀ k, (∀ j, j < k → Ok (4 + j)) → ∃ c, Inv (4 + k) c ∧ Rch start c
  | 0, _ => ⟨_, ⟨3, 1, [], 0, D4, by omega, rfl⟩, seed_reach⟩
  | k + 1, h => by
    obtain ⟨c, hc, r⟩ := reach_k k (fun j hj => h j (by omega))
    obtain ⟨c', hc', r'⟩ := (inv_step (4 + k) (by omega) c hc).1 (h k (by omega))
    exact ⟨c', hc', Rch.tr r r'.reach⟩

theorem ok_three : Ok 3 := fun _ => by decide

/-- a counterexample: the machine reaches its halting state -/
theorem haltAt_of (h : ∃ m, 3 ≤ m ∧ Prime m ∧ lst (ext (D m) m) ≠ 1) : HaltAt start := by
  obtain ⟨m, h3, hp, hne⟩ := h
  have hm : ¬ Ok m := fun hok => hne (hok hp)
  have h4 : 4 ≤ m := by
    rcases Nat.lt_or_ge m 4 with h | h
    · exact absurd (by rw [show m = 3 by omega]; exact ok_three) hm
    · exact h
  obtain ⟨k, rfl⟩ : ∃ k, m = 4 + k := ⟨m - 4, by omega⟩
  clear h3 hp hne h4
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hj : ∃ j, j < k ∧ ¬ Ok (4 + j)
    · obtain ⟨j, hjk, hj⟩ := hj
      exact ih j hjk hj
    · obtain ⟨c, hc, r⟩ := reach_k k (fun j hjk => Classical.byContradiction fun e => hj ⟨j, hjk, e⟩)
      exact HaltAt.back r ((inv_step (4 + k) (by omega) c hc).2 hm)

/-- **Main theorem.** Started on a blank tape, the design halts if and only if
Gilbreath's conjecture fails. -/
theorem halts_iff : Halts delta start ↔
    ∃ N k, 1 ≤ k ∧ k < (primesBelow N).length ∧ (gilbreathRow (primesBelow N) k).head? ≠ some 1 := by
  rw [fail_iff]
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hn
    have hall : ∀ m, 4 ≤ m → Ok m := fun m hm hp =>
      Classical.byContradiction fun e => hn ⟨m, by omega, hp, e⟩
    obtain ⟨c, hc, r⟩ := reach_k 0 (fun j hj => absurd hj (Nat.not_lt_zero _))
    refine not_halts_of_progress delta (fun c => ∃ m, 4 ≤ m ∧ Inv m c) ?_ c ⟨4, by omega, hc⟩
      (Sys.Halts.of_reach r hH)
    rintro c ⟨m, hm, hc⟩
    obtain ⟨c', hc', r'⟩ := (inv_step m hm c hc).1 (hall m hm)
    exact ⟨c', ⟨m + 1, by omega, hc'⟩, r'⟩
  · intro h; exact (haltAt_of h).halts

end TM.Gilbreath
