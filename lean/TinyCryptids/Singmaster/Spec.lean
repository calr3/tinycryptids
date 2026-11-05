import TinyCryptids.Singmaster.Choose

/-!
# Singmaster's bound 8: the arithmetic

Rows of Pascal's triangle as lists (`prow`), the step from one row to the next as the machine
does it (`pascal`, on the reversed row), and the count of the entries equal to `N` in rows
`0 … m - 1` (`tcnt`).  The machine counts in rows `0 … N - 1` only: row `N` holds `N` exactly
twice (`k = 1` and `k = N - 1`, for `N ≥ 3`), so "`N` occurs at least `T + 2` times" is
"`T ≤ tcnt N N`" (`occ_iff`).
-/

namespace TM.Singmaster
open TinyCryptids

/-- Row `n` of Pascal's triangle. -/
def prow (n : Nat) : List Nat := (List.range (n + 1)).map (choose n)

/-- The next row: `y₀, y₀ + y₁, …, y_{m-1} + y_m, y_m`. -/
def pascal (ys : List Nat) : List Nat := List.zipWith (· + ·) (ys ++ [0]) (0 :: ys)

theorem pascal_prow (n : Nat) : pascal (prow n) = prow (n + 1) := by
  have h1 : prow n ++ [0] = (List.range (n + 2)).map (choose n) := by
    rw [List.range_succ, List.map_append]; simp [prow, choose_eq_zero n (n + 1) (by omega)]
  have h2 : 0 :: prow n = (List.range (n + 2)).map (fun k => match k with
      | 0 => 0 | k + 1 => choose n k) := by
    rw [List.range_succ_eq_map]; simp [prow, Function.comp_def]
  rw [pascal, h1, h2, List.zipWith_map_left, List.zipWith_map_right, List.zipWith_same, prow]
  refine List.map_congr_left (fun k _ => ?_)
  cases k with
  | zero => simp
  | succ k => simp [choose_succ_succ, Nat.add_comm]

theorem pascal_reverse (ys : List Nat) : (pascal ys).reverse = pascal ys.reverse := by
  rw [pascal, List.reverse_zipWith (by simp), pascal, List.zipWith_comm]
  simp [Nat.add_comm]

theorem prow_reverse : ∀ n, (prow n).reverse = prow n
  | 0 => rfl
  | n + 1 => by rw [← pascal_prow, pascal_reverse, prow_reverse n]

theorem prow_length (n : Nat) : (prow n).length = n + 1 := by simp [prow]

/-! ## Counting -/

/-- The positions `(n, k)`, `k ≤ n < m`, row by row. -/
def tri (m : Nat) : List (Nat × Nat) := (List.range m).flatMap (fun n => (List.range (n + 1)).map (n, ·))

/-- Entries equal to `N` in rows `0 … m - 1`. -/
def tcnt (N m : Nat) : Nat := ((tri m).filter (fun x => choose x.1 x.2 == N)).length

theorem tcnt_succ (N m : Nat) :
    tcnt N (m + 1) = tcnt N m + ((prow m).filter (· == N)).length := by
  unfold tcnt tri
  rw [List.range_succ, List.flatMap_append, List.filter_append, List.length_append]
  congr 1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_map,
    List.length_map, prow]
  rfl

theorem tri_nodup : ∀ m, (tri m).Nodup := by
  intro m
  induction m with
  | zero => exact List.Pairwise.nil
  | succ m ih =>
    unfold tri at *
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine List.pairwise_append.mpr ⟨ih, ?_, ?_⟩
    · refine List.pairwise_map.mpr ((List.nodup_range _).imp ?_)
      intro a b hab heq; simp at heq; omega
    · intro x hx y hy hxy
      rw [List.mem_flatMap] at hx
      obtain ⟨d, hd, hx⟩ := hx
      simp only [List.mem_map, List.mem_range] at hx hy hd
      obtain ⟨k, _, rfl⟩ := hx
      obtain ⟨k', _, rfl⟩ := hy
      simp at hxy; omega

theorem mem_tri {m n k : Nat} : (n, k) ∈ tri m ↔ k ≤ n ∧ n < m := by
  simp only [tri, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨n, h2, k, by omega, rfl, rfl⟩

theorem length_le_of_sub {α : Type} [DecidableEq α] :
    ∀ (l m : List α), l.Nodup → (∀ x ∈ l, x ∈ m) → l.length ≤ m.length := by
  intro l
  induction l with
  | nil => intros; simp
  | cons a l ih =>
    intro m hl hsub
    have ha : a ∈ m := hsub a (List.mem_cons_self a l)
    rw [List.nodup_cons] at hl
    have := ih (m.erase a) hl.2 (fun x hx => by
      rw [List.mem_erase_of_ne (fun e => hl.1 (by rw [← e]; exact hx))]
      exact hsub x (List.mem_cons_of_mem a hx))
    rw [List.length_erase_of_mem ha] at this
    have hpos : 0 < m.length := List.length_pos.mpr (fun e => by simp [e] at ha)
    simp only [List.length_cons]; omega

theorem len_split {α : Type} (p : α → Bool) :
    ∀ l : List α, l.length = (l.filter p).length + (l.filter (fun x => !p x)).length
  | [] => rfl
  | a :: l => by
    have := len_split p l
    cases h : p a <;> simp [List.filter_cons, h] <;> omega

theorem choose_pred : ∀ m, choose (m + 1) m = m + 1
  | 0 => rfl
  | m + 1 => by rw [choose_succ_succ, choose_pred m, choose_self]

/-- In row `N`, only `k = 1` and `k = N - 1` hold `N`. -/
theorem row_self {N k : Nat} (hN : 2 ≤ N) (h : choose N k = N) : k = 1 ∨ k = N - 1 := by
  have hk : k ≤ N := (choose_range h hN).1
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · simp at h; omega
    · exact Or.inl rfl
  rcases Nat.lt_or_ge k (N - 1) with h3 | h3
  · exfalso
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [choose_succ_succ] at h
    have a := le_choose m j (by omega) (by omega)
    have b := le_choose m (j + 1) (by omega) (by omega)
    omega
  · rcases (show k = N - 1 ∨ k = N by omega) with e | rfl
    · exact Or.inr e
    · rw [choose_self] at h; omega

theorem length_le_two {l : List (Nat × Nat)} (hl : l.Nodup) {N : Nat}
    (h : ∀ x ∈ l, x = (N, 1) ∨ x = (N, N - 1)) : l.length ≤ 2 :=
  length_le_of_sub l [(N, 1), (N, N - 1)] hl (fun x hx => by
    rcases h x hx with e | e <;> simp [e])

/-- **`N ≥ 2` occurs at least `T + 2` times iff it occurs `T` times in rows `0 … N - 1`.** -/
theorem occ_iff (N T : Nat) (hN : 2 ≤ N) (hT1 : 1 ≤ T) :
    (∃ l : List (Nat × Nat), l.Nodup ∧ T + 2 ≤ l.length ∧ ∀ x ∈ l, choose x.1 x.2 = N) ↔
      T ≤ tcnt N N := by
  constructor
  · rintro ⟨l, hl, hlen, hall⟩
    -- split `l` into positions in rows below `N` and in row `N`
    have hlow := length_le_of_sub (l.filter (fun x => decide (x.1 < N)))
      ((tri N).filter (fun x => choose x.1 x.2 == N)) (hl.filter _) (fun x hx => by
        rw [List.mem_filter] at hx ⊢
        obtain ⟨n, k⟩ := x
        have hc := hall _ hx.1
        have := (choose_range hc hN).1
        exact ⟨mem_tri.2 ⟨this, by simpa using hx.2⟩, by simpa using hc⟩)
    have hhigh : (l.filter (fun x => !decide (x.1 < N))).length ≤ 2 := by
      refine length_le_two (hl.filter _) (N := N) (fun x hx => ?_)
      rw [List.mem_filter] at hx
      obtain ⟨n, k⟩ := x
      have hc := hall _ hx.1
      have hn : n = N := by have := (choose_range hc hN).2; simp at hx; omega
      subst hn
      rcases row_self hN hc with rfl | rfl <;> simp
    have hsplit := len_split (fun x => decide (x.1 < N)) l
    unfold tcnt; omega
  · intro hT
    by_cases h2 : N = 2
    · subst h2
      have : tcnt 2 2 = 0 := by decide
      exfalso; omega
    have hsub := (tri_nodup N).filter (fun x => choose x.1 x.2 == N)
    refine ⟨(N, 1) :: (N, N - 1) :: (tri N).filter (fun x => choose x.1 x.2 == N), ?_, ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, hsub⟩⟩
      · simp only [List.mem_cons, Prod.mk.injEq, List.mem_filter, not_or]
        exact ⟨by omega, fun h => by have := (mem_tri.1 h.1).2; omega⟩
      · simp only [List.mem_filter, not_and]
        exact fun h => by have := (mem_tri.1 h).2; omega
    · simp only [List.length_cons]; unfold tcnt at hT; omega
    · intro x hx
      simp only [List.mem_cons, List.mem_filter] at hx
      rcases hx with rfl | rfl | ⟨_, hx⟩
      · exact choose_one N
      · obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
        simpa using choose_pred m
      · simpa using hx

end TM.Singmaster
