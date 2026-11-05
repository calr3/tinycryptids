import TinyCryptids.Singmaster.Gen

/-!
# Main theorem: the design halts iff some `N ≥ 2` occurs at least 9 times in Pascal's triangle

`Chk N`: the start of the scan for `N`, with rows `0 … N - 1` on the tape and no match yet.
-/

namespace TM.Singmaster
open St TinyCryptids

local notation "F" => false
local notation "T" => true
local notation "rep" => List.replicate

def triItems (m : Nat) : List (Nat × Nat) := (List.range m).flatMap (fun n => rowItems (prow n))

def Chk (N : Nat) : Cfg St := sc [] 0 N (itemsW (triItems N))

theorem triItems_succ (m : Nat) : triItems (m + 1) = triItems m ++ rowItems (prow m) := by
  simp [triItems, List.range_succ, List.flatMap_append]

theorem prow_pos {n v : Nat} (h : v ∈ prow n) : 1 ≤ v := by
  simp only [prow, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h; exact choose_pos n k (by omega)

theorem iok_row (vs : List Nat) (h : ∀ v ∈ vs, 1 ≤ v) : IOK (rowItems vs) := by
  cases vs with
  | nil => intro x hx; simp [rowItems] at hx
  | cons v vs =>
    intro x hx
    simp only [rowItems, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨w, hw, rfl⟩
    · exact ⟨Or.inr rfl, h v (List.mem_cons_self _ _)⟩
    · exact ⟨Or.inl rfl, h w (List.mem_cons_of_mem _ hw)⟩

theorem iok_append {is js : List (Nat × Nat)} (h1 : IOK is) (h2 : IOK js) : IOK (is ++ js) := by
  intro x hx; rw [List.mem_append] at hx
  rcases hx with hx | hx
  · exact h1 x hx
  · exact h2 x hx

theorem iok_tri : ∀ m, IOK (triItems m)
  | 0 => fun x hx => by simp [triItems] at hx
  | m + 1 => by
    rw [triItems_succ]; exact iok_append (iok_tri m) (iok_row _ (fun v hv => prow_pos hv))

theorem cntv_append (N : Nat) (is js : List (Nat × Nat)) : cntv N (is ++ js) = cntv N is + cntv N js := by
  simp [cntv, List.filter_append]

theorem cntv_row (N : Nat) (vs : List Nat) : cntv N (rowItems vs) = (vs.filter (· == N)).length := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    simp only [rowItems, cntv, List.filter_cons, List.filter_map, List.length_map]
    split <;> simp_all [Function.comp_def]

theorem cnt_tri (N : Nat) : ∀ m, cntv N (triItems m) = tcnt N m
  | 0 => by simp [cntv, triItems, tcnt, tri]
  | m + 1 => by rw [triItems_succ, cntv_append, cntv_row, cnt_tri N m, tcnt_succ]

theorem sok_of_iok {is : List (Nat × Nat)} (h : IOK is) : SOK is := fun x hx => (h x hx).1

/-- from the end of the scan for `N` (rows `0 … N - 1`) to the scan for `N + 1` -/
theorem gen_all (N c : Nat) (hN : 1 ≤ N) (hc : c ≤ 6) :
    Rch (endc (itemsW (triItems N)) c N) (Chk (N + 1)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨init, x, hrow⟩ : ∃ init x, prow M = init ++ [x] := by
    rcases List.eq_nil_or_concat (prow M) with h | ⟨init, x, h⟩
    · have := prow_length M; rw [h] at this; simp at this
    · exact ⟨init, x, by rw [h, List.concat_eq_append]⟩
  have hpos : ∀ v ∈ prow M, 1 ≤ v := fun v hv => prow_pos hv
  rw [hrow] at hpos
  have hx : 1 ≤ x := hpos x (by simp)
  have hinit : ∀ y ∈ init.reverse, 1 ≤ y := fun y hy => hpos y (by simp at hy; simp [hy])
  rw [triItems_succ, hrow]
  refine Rch.tr (gen_start _ init x c (M + 1)) ?_
  have hg := gen_row ((itemsW (triItems M)).reverse ++ (Nw (M + 1) 1).reverse ++ XL c) init.reverse x []
    [] 0 hx hinit
  simp only [List.nil_append] at hg
  refine Rch.tr hg ?_
  have he := gen_end (triItems M) (sok_of_iok (iok_tri M))
    (rowW (init.reverse.reverse ++ [x]) ++ rep 3 F ++ rowW (pas 0 (x :: init.reverse))) c (M + 1) hc
    (by omega)
  simp only [List.append_assoc] at he ⊢
  refine Rch.tr he ?_
  have hp : pas 0 (x :: init.reverse) = prow (M + 1) := by
    rw [← pascal_pas, ← pascal_prow, ← prow_reverse M, hrow]; simp
  unfold Chk
  rw [triItems_succ, triItems_succ, itemsW_append, itemsW_append, hp, hrow,
    itemsW_row _ (by simp), itemsW_row _ (by simp [prow])]
  simp [List.append_assoc]; fin

theorem iok_nil : IOK [] := fun x hx => by simp at hx

theorem cyc_ok (N : Nat) (hN : 1 ≤ N) (h : tcnt N N ≤ 6) : Rch (Chk N) (Chk (N + 1)) := by
  have hs := (scan N hN (triItems N) [] 0 (by omega) (iok_tri N) iok_nil).1 (by rw [cnt_tri]; omega)
  simp only [List.nil_append, Nat.zero_add, cnt_tri] at hs
  exact Rch.tr hs (gen_all N _ hN h)

theorem cyc_halt (N : Nat) (hN : 1 ≤ N) (h : 7 ≤ tcnt N N) : HaltAt (Chk N) := by
  have hs := (scan N hN (triItems N) [] 0 (by omega) (iok_tri N) iok_nil).2 (by rw [cnt_tri]; omega)
  simpa using hs

theorem seed_reach : Rch start (endc (itemsW (triItems 1)) 0 1) := by
  have e : start = cl seed0 [] (rep 23 F) := cl_padR seed0 [] [] 23
  rw [e]
  simp only [List.replicate_succ, List.replicate_zero]
  iterate 23 gr
  fin

/-- before the scan for `2 + k`, if no smaller `N ≥ 2` had 7 matches -/
theorem reach_k : ∀ k, (∀ j, j < k → tcnt (2 + j) (2 + j) ≤ 6) → Rch start (Chk (2 + k))
  | 0, _ => Rch.tr seed_reach (gen_all 1 0 (by omega) (by omega))
  | k + 1, h => by
    refine Rch.tr (reach_k k (fun j hj => h j (by omega))) ?_
    rw [show 2 + (k + 1) = 2 + k + 1 by omega]
    exact cyc_ok (2 + k) (by omega) (h k (by omega))

theorem haltAt_of_cnt (h : ∃ N, 2 ≤ N ∧ 7 ≤ tcnt N N) : HaltAt start := by
  obtain ⟨N, h2, h7⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, N = 2 + k := ⟨N - 2, by omega⟩
  clear h2
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hj : ∃ j, j < k ∧ 7 ≤ tcnt (2 + j) (2 + j)
    · obtain ⟨j, hjk, hj⟩ := hj
      exact ih j hjk hj
    · have hr := reach_k k (fun j hj' => Nat.le_of_not_lt (fun h => hj ⟨j, hj', by omega⟩))
      exact HaltAt.back hr (cyc_halt (2 + k) (by omega) h7)

theorem chk_ne (N : Nat) : Chk N ≠ Chk (N + 1) := by
  intro e
  have hL := congrArg Cfg.L e
  have := congrFun hL (N + 2)
  simp only [Chk, sc, cl, Nw, XL, Cw, List.reverse_nil, List.nil_append, List.reverse_append,
    List.reverse_cons, List.reverse_replicate, List.append_assoc, List.singleton_append,
    List.cons_append] at this
  have k1 : ∀ (n : Nat) (l : List Bool) (s : Strm) (i : Nat), app (rep n T ++ l) s (n + i) = app l s i := by
    intro n l s i
    induction n with
    | zero => simp
    | succ n ih => rw [show n + 1 + i = (n + i) + 1 by omega]; exact ih
  have e2 : rep (N + 1) T ++ F :: (rep (7 - 0) T ++ F :: rep (0 + 1) T) =
      rep N T ++ T :: F :: (rep (7 - 0) T ++ F :: rep (0 + 1) T) := by simp [List.replicate_succ]
  rw [e2] at this
  have h1 : app (rep N T ++ F :: (rep (7 - 0) T ++ F :: rep (0 + 1) T)) blank (N + 0) =
      app (rep N T ++ T :: F :: (rep (7 - 0) T ++ F :: rep (0 + 1) T)) blank (N + 0) := this
  rw [k1, k1] at h1
  exact absurd h1 (by decide)

theorem not_halts_of (h : ∀ N, 2 ≤ N → tcnt N N ≤ 6) : ¬ Halts delta start := by
  intro hh
  have hc := Sys.Halts.of_reach (reach_k 0 (fun j hj => by omega)) hh
  refine not_halts_of_progress (δ := delta) (fun c => ∃ N, 2 ≤ N ∧ c = Chk N) ?_ _ ⟨2, Nat.le_refl _, rfl⟩ hc
  rintro c ⟨N, hN, rfl⟩
  obtain ⟨n, hn⟩ := cyc_ok N (by omega) (h N hN)
  refine ⟨Chk (N + 1), ⟨N + 1, by omega, rfl⟩, ?_⟩
  cases n with
  | zero => exact absurd (by simpa [run, Sys.run] using hn) (chk_ne N)
  | succ n => exact ⟨n, hn⟩

/-- **The design halts iff some `N ≥ 2` occurs at least 9 times in Pascal's triangle.** -/
theorem halts_iff : Halts delta start ↔
    ∃ N, 2 ≤ N ∧ ∃ l : List (Nat × Nat), l.Nodup ∧ 9 ≤ l.length ∧ ∀ x ∈ l, choose x.1 x.2 = N := by
  constructor
  · intro hh
    refine Classical.byContradiction (fun hn => ?_)
    refine not_halts_of (fun N hN => Nat.le_of_not_lt (fun h7 => ?_)) hh
    exact hn ⟨N, hN, (occ_iff N 7 hN (by omega)).2 (by omega)⟩
  · rintro ⟨N, hN, hl⟩
    exact (haltAt_of_cnt ⟨N, hN, (occ_iff N 7 hN (by omega)).1 hl⟩).halts

theorem haltAt_of (h : ∃ N, 2 ≤ N ∧ ∃ l : List (Nat × Nat), l.Nodup ∧ 9 ≤ l.length ∧
    ∀ x ∈ l, choose x.1 x.2 = N) : HaltAt start := by
  obtain ⟨N, hN, hl⟩ := h
  exact haltAt_of_cnt ⟨N, hN, (occ_iff N 7 hN (by omega)).1 hl⟩

end TM.Singmaster
