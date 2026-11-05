import TinyCryptids.LehmerTau.LStart

/-!
# The L phase: the action at a divisor `d` of `n`

D is copied five times and the run (K691 active) adds `691 d⁵` to M; then K65 and K691 are
flipped, D is copied eleven times and the run (K65 active) adds `65 d¹¹`; the flips are undone
and the walk on D resumes.
-/

namespace TM.LehmerTau
open St

local notation "F" => false

/-- the left part in the L phase -/
def KLx (s691 : KB) (kB : Nat) (s65 : KB) (p : Nat) : List KB := [s691, .pl (kB + 2), s65, .pl (p + 1)]

/-- D divides `n`: to X (copies of D) -/
theorem dd_L (K : List KB) (m d rd : Nat) (hd : 1 ≤ d) :
    Rch (DV (LS m (.pl 1 :: .pl 13 :: K)) BL d rd)
      (cfgL X50 (ones 13 (F ::: F ::: LS m K)) (F ::: F ::: true ::: F ::: F ::: true ::: F ::: ones d
        (app (bw [rd + 2, 4, 1, 2]) blank))) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  unfold DV BL RB
  rw [LS_pl]
  gL; gL; gL; gR; gR; gR; gR; gR; gR; gR
  sRn d'; gR; gR; sRn (rd + 2); gR; gR; gR; gR; gR; gL
  sLn 3; gL; gL; sLn (rd + 2); gL; gL; sLn d'; gL; gL; gL; gL; gL; gL; gL; gL
  simp only [bw, app_append, app_rep, app_cons, List.cons_append, List.nil_append, app_nil, ones_cons_true]
  fin

/-- `12 − h` copies of D (cursor at cell 1), then `AL1` -/
theorem copies_D (LL : Strm) (d : Nat) (hd : 1 ≤ d) (NS : List Nat) (hNS : NOk NS) (h : Nat) (hh : 1 ≤ h)
    (hh2 : h ≤ 11) :
    Rch ⟨FS1, F ::: ones h (F ::: F ::: LL), ones (12 - h) (F ::: F ::: true ::: F ::: F ::: true ::: F ::: ones d
        (app (bw NS) blank))⟩
      (cfgL AL1 (F ::: ones 13 (F ::: F ::: LL)) (F ::: true ::: F ::: F ::: ones (d + 2)
        (app (bw (NS ++ List.replicate (12 - h) (d + 2))) blank))) := by
  have c := xloop LL [1] (by intro x hx; simp at hx; omega) d hd (11 - h) NS hNS h hh (by omega)
  have e : XC LL [1] d NS h = ⟨FS1, F ::: ones h (F ::: F ::: LL), ones (12 - h) (F ::: F ::: true ::: F ::: F :::
      true ::: F ::: ones d (app (bw NS) blank))⟩ := by
    simp [XC, bw, app_append, app_rep, rep]
  rw [e] at c
  refine Rch.tr c ?_
  unfold XE
  simp only [bw, List.reverse_cons, List.reverse_nil, List.nil_append, app_append, app_rep, List.singleton_append,
    List.cons_append, app_cons, app_nil, rep_rev]
  gL; gL; fin

/-- a run of the L phase (`c` copies of D) and the erase: `PD2` on Re' -/
theorem run_L (K : List KB) (hK : ∀ b ∈ K, b.ok) (hr : rsK K = K) (m d rd c : Nat) (hd : 1 ≤ d) (hc : 1 ≤ c) :
    Rch (cfgL AL1 (F ::: ones 13 (F ::: F ::: LS m K)) (F ::: true ::: F ::: F ::: ones (d + 2)
        (app (bw ([rd + 2, 4, 1, 2] ++ List.replicate c (d + 2))) blank)))
      (cfgL PD2 (app (lpR ([.pl 1, .pl 4, .pl (rd + 2), .pl (d + 2), .pl 1, .pl 13] ++ K) ++
          rep (m + d ^ c * pK K + 1)) blank) (F ::: F ::: true ::: true ::: blank)) := by
  have hk : ∀ b ∈ ([.pl 1, .pl 4, .pl (rd + 2), .pl (d + 2), .pl 1, .pl 13] ++ K : List KB), b.ok := by
    intro b hb; rcases List.mem_append.1 hb with h | h
    · simp at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [KB.ok]
    · exact hK b h
  have := runpost m _ (List.replicate c (d, 0)) hk (vok_rep d c hd) (by simp; omega)
    (by simp [zv, List.map_replicate]) (by simp [rsK, hr])
    F (rep 13 ++ F :: F :: (lpR K ++ rep (m + 1)))
    (F :: true :: F :: F :: rep (d + 2) ++ bw ([rd + 2, 4, 1, 2] ++ List.replicate c (d + 2)))
    (by simp) ?_
  · have e1 : app (rep 13 ++ F :: F :: (lpR K ++ rep (m + 1))) blank = ones 13 (F ::: F ::: LS m K) := by
      simp [LS, app_append, app_rep]
    have e2 : pV (List.replicate c (d, 0)) * pK ([.pl 1, .pl 4, .pl (rd + 2), .pl (d + 2), .pl 1, .pl 13] ++ K) =
        d ^ c * pK K := by
      rw [pV_rep]; simp [pK]
    rw [e1, e2] at this
    simp only [app_cons, app_append, app_rep] at this ⊢
    exact this
  · rw [TW_K, List.reverse_replicate, vp_rep]
    simp [LK, lpR_append, lpR, KB.w, List.reverse_append, rep_rev, bw_append, bw, List.append_assoc, rep]

theorem FFL : FarL delta FL1 FL2 FL3 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem LS_pl' (a n : Nat) (K : List KB) : ones n (F ::: F ::: LS a K) = LS a (.pl n :: K) := (LS_pl a n K).symm

/-- after a run of the L phase: D's hole back, `FL1` on D's cell 0 -/
theorem post_L0 (K : List KB) (m d rd : Nat) :
    Rch (cfgL PD2 (app (lpR ([.pl 1, .pl 4, .pl (rd + 2), .pl (d + 2), .pl 1, .pl 13] ++ K) ++ rep (m + 1)) blank)
        (F ::: F ::: true ::: true ::: blank))
      (cfgL FL1 (LS m (.pl 1 :: .pl 1 :: .pl 13 :: K)) (F ::: ones d (app (bw [rd + 2, 4, 1, 2]) blank))) := by
  rw [LS_eq]
  simp only [List.cons_append, List.nil_append]
  rw [LS_pl, LS_pl, LS_pl, LS_pl]
  gL; gL; gL; sLn 4; gL; gL; sLn (rd + 2); gL; gL
  rw [LS_pl]
  sLn (d + 2); gR; gR; gL
  show Rch (cfgL FL1 (true ::: F ::: F ::: ones 1 (F ::: F ::: LS m (KB.pl 13 :: K))) _) _
  simp only [LS_pl, bw, app_cons, app_append, app_rep, app_nil]
  fin

theorem ok_KLx (kA kB kC p : Nat) (hA : 1 ≤ kA) (hC : 1 ≤ kC) (on65 : Bool) :
    ∀ b ∈ (.pl 1 :: .pl 1 :: .pl 13 ::
      KLx (if on65 then .pl (kC + 2) else .dg kC 1) kB (if on65 then .dg kA 1 else .pl (kA + 2)) p : List KB), b.ok := by
  intro b hb; cases on65 <;> simp [KLx] at hb <;> rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [KB.ok] <;> omega

/-- the end of the L1 run: K65 on, K691 off, X's cursor at cell 1 (eleven copies) -/
theorem flip_1 (kA kB kC p m d : Nat) (hA : 1 ≤ kA) (hC : 1 ≤ kC) (NS : List Nat) :
    Rch (cfgL FL1 (LS m (.pl 1 :: .pl 1 :: .pl 13 :: KLx (.dg kC 1) kB (.pl (kA + 2)) p))
        (F ::: ones d (app (bw NS) blank)))
      ⟨FS1, F ::: ones 1 (F ::: F ::: LS m (KLx (.pl (kC + 2)) kB (.dg kA 1) p)), ones 11 (F ::: F ::: true ::: F ::: F :::
        true ::: F ::: ones d (app (bw NS) blank))⟩ := by
  refine Rch.tr (farL_LS FFL m _ (ok_KLx kA kB kC p hA hC false) _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, KLx, lpR, KB.w, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_assoc, List.singleton_append, List.cons_append, app_append, app_cons, rep, app_replicate,
    List.reverse_replicate, List.reverse_reverse, Nat.add_sub_cancel]
  gR0; gR; gR; sRn (m + 1); gR; gR; sRn (p + 1); gR; gR
  gR; gR; sRn kA; gR; gR; sRn (kB + 2); gR; gR; gR; gR; sRn kC; gR; gR; gR; gR
  have e : LS m [] = ones (m + 1) blank := by simp [LS, lpR, app_rep]
  simp only [LS_pl, LS_dg1, e, tl_blank, cons_blank, ones_cons_true]
  fin

/-- the end of the L2 run: K65 off, K691 on, resume the walk on D -/
theorem flip_2 (kA kB kC p m d rd : Nat) (hA : 1 ≤ kA) (hC : 1 ≤ kC) (hd : 1 ≤ d) :
    Rch (cfgL FL1 (LS m (.pl 1 :: .pl 1 :: .pl 13 :: KLx (.pl (kC + 2)) kB (.dg kA 1) p))
        (F ::: ones d (app (bw [rd + 2, 4, 1, 2]) blank)))
      (RS3 (LS m (.pl 1 :: .pl 13 :: KLx (.dg kC 1) kB (.pl (kA + 2)) p)) BL d rd) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  refine Rch.tr (farL_LS FFL m _ (ok_KLx kA kB kC p hA hC true) _) ?_
  simp only [↓reduceIte, KLx, lpR, KB.w, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_assoc, List.singleton_append, List.cons_append, app_append, app_cons, rep, app_replicate,
    List.reverse_replicate, List.reverse_reverse, Nat.add_sub_cancel]
  gR0; gR; gR; sRn (m + 1); gR; gR; sRn (p + 1); gR; gR
  gR; gR; sRn kA; gR; gR; sRn (kB + 2); gR; gR; gR; gR; sRn kC; gR; gR; sRn 13; gR; gR; sRn 1; gR; gR; gR; gR; gR
  have e : LS m [] = ones (m + 1) blank := by simp [LS, lpR, app_rep]
  unfold RS3 BL RB
  simp only [LS_pl, LS_dg1, e, tl_blank, cons_blank, ones_cons_true, bw, app_cons, app_append, app_rep, app_nil,
    Nat.add_sub_cancel, List.cons_append, List.nil_append]
  fin

/-- **The action at a divisor `d` of `n`** (L phase): M gains `kC d⁵ + kA d¹¹` -/
theorem dact_L (kA kB kC p : Nat) (hA : 1 ≤ kA) (hC : 1 ≤ kC) (m d rd : Nat) (hd : 1 ≤ d) :
    Rch (DV (LS m (.pl 1 :: .pl 13 :: KLx (.dg kC 1) kB (.pl (kA + 2)) p)) BL d rd)
      (RS3 (LS (m + (kC * d ^ 5 + kA * d ^ 11)) (.pl 1 :: .pl 13 :: KLx (.dg kC 1) kB (.pl (kA + 2)) p)) BL d rd) := by
  have hNS : NOk [rd + 2, 4, 1, 2] := by intro x hx; simp at hx; omega
  have ok1 : ∀ b ∈ KLx (.dg kC 1) kB (.pl (kA + 2)) p, b.ok := by
    intro b hb; simp [KLx] at hb; rcases hb with rfl | rfl | rfl | rfl <;> simp [KB.ok] <;> omega
  have ok2 : ∀ b ∈ KLx (.pl (kC + 2)) kB (.dg kA 1) p, b.ok := by
    intro b hb; simp [KLx] at hb; rcases hb with rfl | rfl | rfl | rfl <;> simp [KB.ok] <;> omega
  have r1 : rsK (KLx (.dg kC 1) kB (.pl (kA + 2)) p) = KLx (.dg kC 1) kB (.pl (kA + 2)) p := rfl
  have r2 : rsK (KLx (.pl (kC + 2)) kB (.dg kA 1) p) = KLx (.pl (kC + 2)) kB (.dg kA 1) p := rfl
  have p1 : pK (KLx (.dg kC 1) kB (.pl (kA + 2)) p) = kC := by simp [KLx, pK]
  have p2 : pK (KLx (.pl (kC + 2)) kB (.dg kA 1) p) = kA := by simp [KLx, pK]
  refine Rch.tr (dd_L _ m d rd hd) (Rch.tr (x50 _ _) ?_)
  refine Rch.tr (copies_D _ d hd _ hNS 7 (by omega) (by omega)) ?_
  rw [show (12 - 7 : Nat) = 5 from rfl]
  refine Rch.tr (run_L _ ok1 r1 m d rd 5 hd (by omega)) ?_
  rw [p1]
  refine Rch.tr (post_L0 _ (m + d ^ 5 * kC) d rd) ?_
  have f1 := flip_1 kA kB kC p (m + d ^ 5 * kC) d hA hC [rd + 2, 4, 1, 2]
  refine Rch.tr f1 ?_
  refine Rch.tr (copies_D (LS (m + d ^ 5 * kC) (KLx (.pl (kC + 2)) kB (.dg kA 1) p)) d hd _ hNS 1 (by omega) (by omega)) ?_
  rw [show (12 - 1 : Nat) = 11 from rfl]
  refine Rch.tr (run_L _ ok2 r2 (m + d ^ 5 * kC) d rd 11 hd (by omega)) ?_
  rw [p2]
  refine Rch.tr (post_L0 _ (m + d ^ 5 * kC + d ^ 11 * kA) d rd) ?_
  refine Rch.tr (flip_2 kA kB kC p (m + d ^ 5 * kC + d ^ 11 * kA) d rd hA hC hd) ?_
  rw [show m + d ^ 5 * kC + d ^ 11 * kA = m + (kC * d ^ 5 + kA * d ^ 11) by
    rw [Nat.mul_comm (d ^ 5), Nat.mul_comm (d ^ 11)]; omega]
  fin

end TM.LehmerTau
