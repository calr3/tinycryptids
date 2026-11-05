import TinyCryptids.LehmerTau.Post

/-!
# The R phase: the action at a divisor `e` of `j`

Tape (left to right): `KL` (the constants and P, given leftward from K691), X (13 cells), Z,
D (`d + 2` cells), Rd, E (`e + 2` cells, its hole at cell 1), Re, S0. The action copies E five
times and D five times, runs (P gains `d⁵ e⁵ · pK KL`), erases the copies and comes back to
resume the walk on E.
-/

namespace TM.LehmerTau
open St

local notation "F" => false

/-- the tape left of a separator, read leftward: the blocks `K` (nearest first), then the
accumulator (`a + 1` cells) -/
def LS (a : Nat) (K : List KB) : Strm := app (lpR K ++ rep (a + 1)) blank

theorem LS_pl (a n : Nat) (K : List KB) : LS a (.pl n :: K) = ones n (F ::: F ::: LS a K) := by
  simp [LS, lpR, KB.w, app_append, rep_rev, app_rep]

theorem LS_dg1 (a f : Nat) (K : List KB) : LS a (.dg f 1 :: K) = ones f (F ::: true ::: F ::: F ::: LS a K) := by
  simp [LS, lpR, KB.w, app_append, rep_rev, app_rep, List.reverse_append, rep, app_replicate]

theorem lpR_append (l m : List KB) : lpR (l ++ m) = lpR l ++ lpR m := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [lpR, ih, List.append_assoc]

theorem bw_cons (n : Nat) (l : List Nat) (s : Strm) : app (bw (n :: l)) s = F ::: F ::: ones n (app (bw l) s) := by
  simp [bw, app_append, app_rep]

theorem ones_add2 (n : Nat) (s : Strm) : ones (n + 2) s = ones n (true ::: true ::: s) := by
  rw [ones_succ', ones_succ']

theorem bw_nil (s : Strm) : app (bw []) s = s := rfl

/-- D's hole (if any) is filled on the way to X; `VG1` on Z -/
theorem ve_fill (a d rd : Nat) (K : List KB) (Dh : KB) (hD : Dh = .pl (d + 2) ∨ Dh = .dg d 1) (R : Strm) :
    Rch (cfgL VF1 (LS a (Dh :: .pl 1 :: K)) R)
      (cfgL VG1 (LS a (.pl 1 :: K)) (F ::: F ::: ones (d + 2) R)) := by
  rcases hD with rfl | rfl
  · rw [LS_pl]
    sLn (d + 2); gL; gL; fin
  · rw [LS_dg1, LS_pl]
    sLn d; gL; gR; gL; gL; gL; gL
    rw [show ones (d + 2) R = true ::: true ::: ones d R from rfl]
    fin

/-- X's cursor at cell 7 (five copies): from `X50` on X's last cell -/
theorem x50 (LL R : Strm) : Rch (cfgL X50 (ones 13 (F ::: F ::: LL)) R) ⟨FS1, F ::: ones 7 (F ::: F ::: LL), ones 5 R⟩ := by
  gL; gL; gL; gL; gL; gR; fin

/-- the start of the action: `X50` on X's last cell -/
theorem ve_start (a d rd e re : Nat) (K : List KB) (Dh : KB) (hD : Dh = .pl (d + 2) ∨ Dh = .dg d 1) (B : Strm) :
    Rch (DV (LS a (.pl (rd + 2) :: Dh :: .pl 1 :: .pl 13 :: K)) B e re)
      (cfgL X50 (ones 13 (F ::: F ::: LS a K)) (F ::: F ::: true ::: F ::: F ::: ones (d + 2)
        (F ::: F ::: ones (rd + 2) (F ::: F ::: true ::: F ::: ones e (F ::: F ::: RB re B))))) := by
  unfold DV
  rw [LS_pl]
  gL; gL; gL; gL
  sLn rd; gL; gL
  refine Rch.tr (ve_fill a d rd _ Dh hD _) ?_
  rw [LS_pl, LS_pl]
  gL; gL; gL
  rw [ones_add2 rd]; fin

/-- E copied: D gets its cursor; `X50` again -/
theorem ed_d (LL : Strm) (d rd e : Nat) (ns : List Nat) :
    Rch (XE LL [1, d + 2, rd + 2] e ns)
      (cfgL X50 (ones 13 (F ::: F ::: LL)) (F ::: F ::: true ::: F ::: F ::: true ::: F ::: ones d
        (app (bw ((rd + 2) :: (e + 2) :: ns)) blank))) := by
  unfold XE
  simp only [bw, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, rep_rev, app_append,
    app_rep, List.singleton_append, List.cons_append, app_cons, List.append_assoc, app_nil]
  gL; gL; sLn rd; gL; gL
  sLn (d + 2); gR; gR; gL; gL; gL; gL; gL; gL; gL
  simp only [bw, app_append, app_rep, app_cons, List.cons_append, List.nil_append, rep_succ, ones_succ, app_nil,
    ones_cons_true]
  fin

/-- the copies of E, then of D: `AL1` (the run starts) -/
theorem copies_R (LL : Strm) (d rd e re : Nat) (hd : 1 ≤ d) (he : 1 ≤ e) :
    Rch ⟨FS1, F ::: ones 7 (F ::: F ::: LL), ones 5 (F ::: F ::: true ::: F ::: F ::: ones (d + 2)
        (F ::: F ::: ones (rd + 2) (F ::: F ::: true ::: F ::: ones e (F ::: F ::: RB re (ones 2 blank)))))⟩
      (cfgL AL1 (F ::: ones 13 (F ::: F ::: LL)) (F ::: true ::: F ::: F ::: ones (d + 2)
        (app (bw ([rd + 2, e + 2, re + 2, 2] ++ List.replicate 5 (e + 2) ++ List.replicate 5 (d + 2))) blank))) := by
  have h1 : NOk [1, d + 2, rd + 2] := by intro x hx; simp at hx; omega
  have h2 : NOk [re + 2, 2] := by intro x hx; simp at hx; omega
  have c1 := xloop LL [1, d + 2, rd + 2] h1 e he 4 [re + 2, 2] h2 7 (by omega) rfl
  have e1 : XC LL [1, d + 2, rd + 2] e [re + 2, 2] 7 = ⟨FS1, F ::: ones 7 (F ::: F ::: LL), ones 5 (F ::: F ::: true :::
      F ::: F ::: ones (d + 2) (F ::: F ::: ones (rd + 2) (F ::: F ::: true ::: F ::: ones e (F ::: F ::: RB re (ones 2 blank)))))⟩ := by
    simp [XC, bw, app_append, app_rep, rep]
    simp [app_replicate]; rfl
  rw [e1] at c1
  refine Rch.tr c1 (Rch.tr (ed_d LL d rd e _) (Rch.tr (x50 LL _) ?_))
  have h3 : NOk ((rd + 2) :: (e + 2) :: ([re + 2, 2] ++ List.replicate (12 - 7) (e + 2))) := by
    intro x hx; simp at hx; omega
  have c2 := xloop LL [1] (by intro x hx; simp at hx; omega) d hd 4 _ h3 7 (by omega) rfl
  have e2 : XC LL [1] d ((rd + 2) :: (e + 2) :: ([re + 2, 2] ++ List.replicate (12 - 7) (e + 2))) 7 =
      ⟨FS1, F ::: ones 7 (F ::: F ::: LL), ones 5 (F ::: F ::: true ::: F ::: F ::: true ::: F ::: ones d
        (app (bw ((rd + 2) :: (e + 2) :: ([re + 2, 2] ++ List.replicate (12 - 7) (e + 2)))) blank))⟩ := by
    simp [XC, bw, app_append, app_rep, rep]
  rw [e2] at c2
  refine Rch.tr c2 ?_
  unfold XE
  simp only [bw, List.reverse_cons, List.reverse_nil, List.nil_append, app_append, app_rep, List.singleton_append,
    List.cons_append, app_cons, app_nil, rep_rev]
  gL; gL
  fin

theorem vp_append (l m : List (Nat × Nat)) : vp (l ++ m) = vp l ++ vp m := by
  induction l with
  | nil => rfl
  | cons x l ih => obtain ⟨f, p⟩ := x; simp [vp, ih, List.append_assoc]

theorem vp_rep (f : Nat) : ∀ k, vp (List.replicate k (f, 0)) = bw (List.replicate k (f + 2))
  | 0 => rfl
  | k + 1 => by
    simp only [List.replicate_succ, vp, bw, vwi, if_pos, ite_true, vp_rep f k, List.append_assoc]
    rw [show f + 2 = (f + 1) + 1 from rfl, rep_succ']; simp only [List.append_assoc]
    rw [show rep (f + 1 + 1) = rep f ++ [true, true] from rep_add f 2]; simp

theorem vok_rep (f k : Nat) (hf : 1 ≤ f) : ∀ x ∈ List.replicate k (f, 0), VOk x := by
  intro x hx; rw [List.eq_of_mem_replicate hx]; exact ⟨hf, by simp; omega⟩

theorem zv_rep (f k : Nat) : zv (List.replicate k (f, 0)) = List.replicate k (f, 0) := by
  simp [zv, List.map_replicate]

theorem pV_append (l m : List (Nat × Nat)) : pV (l ++ m) = pV l * pV m := by
  induction l with
  | nil => simp [pV]
  | cons x l ih => obtain ⟨f, p⟩ := x; simp [pV, ih, Nat.mul_assoc]

theorem pV_rep (f : Nat) : ∀ k, pV (List.replicate k (f, 0)) = f ^ k
  | 0 => rfl
  | k + 1 => by simp [List.replicate_succ, pV, pV_rep f k, Nat.pow_succ, Nat.mul_comm]

/-- the run of the R phase and the erase: `PD2` left of S0 -/
theorem run_R (KL : List KB) (hKL : ∀ b ∈ KL, b.ok) (hr : rsK KL = KL) (a d rd e re : Nat) (hd : 1 ≤ d) (he : 1 ≤ e) :
    Rch (cfgL AL1 (F ::: ones 13 (F ::: F ::: LS a KL)) (F ::: true ::: F ::: F ::: ones (d + 2)
        (app (bw ([rd + 2, e + 2, re + 2, 2] ++ List.replicate 5 (e + 2) ++ List.replicate 5 (d + 2))) blank)))
      (cfgL PD2 (app (lpR ([.pl (re + 2), .pl (e + 2), .pl (rd + 2), .pl (d + 2), .pl 1, .pl 13] ++ KL) ++
          rep (a + d ^ 5 * e ^ 5 * pK KL + 1)) blank) (F ::: F ::: true ::: true ::: blank)) := by
  have hk : ∀ b ∈ ([.pl (re + 2), .pl (e + 2), .pl (rd + 2), .pl (d + 2), .pl 1, .pl 13] ++ KL : List KB), b.ok := by
    intro b hb; rcases List.mem_append.1 hb with h | h
    · simp at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [KB.ok]
    · exact hKL b h
  have hv : ∀ x ∈ List.replicate 5 (d, 0) ++ List.replicate 5 (e, 0), VOk x :=
    vok_app (vok_rep d 5 hd) (vok_rep e 5 he)
  have := runpost a _ (List.replicate 5 (d, 0) ++ List.replicate 5 (e, 0)) hk hv (by simp)
    (by simp [zv, List.map_replicate]) (by simp [rsK, hr])
    F (rep 13 ++ F :: F :: (lpR KL ++ rep (a + 1)))
    (F :: true :: F :: F :: rep (d + 2) ++ bw ([rd + 2, e + 2, re + 2, 2] ++ List.replicate 5 (e + 2) ++ List.replicate 5 (d + 2)))
    (by simp) ?_
  · have e1 : app (rep 13 ++ F :: F :: (lpR KL ++ rep (a + 1))) blank = ones 13 (F ::: F ::: LS a KL) := by
      simp [LS, app_append, app_rep]
    have e2 : pV (List.replicate 5 (d, 0) ++ List.replicate 5 (e, 0)) *
        pK ([.pl (re + 2), .pl (e + 2), .pl (rd + 2), .pl (d + 2), .pl 1, .pl 13] ++ KL) = d ^ 5 * e ^ 5 * pK KL := by
      rw [pV_append, pV_rep, pV_rep]; simp [pK]
    rw [e1, e2] at this
    simp only [app_cons, app_append, app_rep] at this ⊢
    exact this
  · have hrev : (List.replicate 5 (d, 0) ++ List.replicate 5 (e, 0) : List (Nat × Nat)).reverse =
        List.replicate 5 (e, 0) ++ List.replicate 5 (d, 0) := by simp
    rw [TW_K, hrev, vp_append, vp_rep, vp_rep]
    simp [LK, lpR_append, lpR, KB.w, List.reverse_append, rep_rev, bw_append, bw, List.append_assoc, rep]

theorem LS_eq (a : Nat) (K : List KB) : app (lpR K ++ rep (a + 1)) blank = LS a K := rfl

/-- after the erase: E's hole back, resume the walk on E -/
theorem post_R (K : List KB) (a d rd e re : Nat) :
    Rch (cfgL PD2 (app (lpR ([.pl (re + 2), .pl (e + 2), .pl (rd + 2), .pl (d + 2), .pl 1, .pl 13] ++ K) ++
          rep (a + 1)) blank) (F ::: F ::: true ::: true ::: blank))
      (RS (LS a (.pl (rd + 2) :: .pl (d + 2) :: .pl 1 :: .pl 13 :: K)) (ones 2 blank) e re) := by
  rw [LS_eq]
  simp only [List.cons_append, List.nil_append]
  rw [LS_pl, LS_pl]
  unfold RS RB
  gL; gL; sLn re; gL; gL; sLn (e + 2); gR; gR; gR
  rw [ones_add2 re]; fin

/-- **The action at a divisor `e` of `j`** (R phase): P gains `d⁵ e⁵ · pK KL` -/
theorem eact (KL : List KB) (hKL : ∀ b ∈ KL, b.ok) (hr : rsK KL = KL) (a d rd e re : Nat) (hd : 1 ≤ d) (he : 1 ≤ e)
    (Dh : KB) (hD : Dh = .pl (d + 2) ∨ Dh = .dg d 1) :
    Rch (DV (LS a (.pl (rd + 2) :: Dh :: .pl 1 :: .pl 13 :: KL)) (ones 2 blank) e re)
      (RS3 (LS (a + d ^ 5 * e ^ 5 * pK KL) (.pl (rd + 2) :: .pl (d + 2) :: .pl 1 :: .pl 13 :: KL)) (ones 2 blank) e re) := by
  refine Rch.tr (ve_start a d rd e re KL Dh hD _) (Rch.tr (x50 _ _) ?_)
  refine Rch.tr (copies_R _ d rd e re hd he) (Rch.tr (run_R KL hKL hr a d rd e re hd he) ?_)
  exact Rch.tr (post_R KL _ d rd e re) (rs_rs3 _ _ e re he)

end TM.LehmerTau
