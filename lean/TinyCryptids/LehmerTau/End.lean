import TinyCryptids.LehmerTau.LAct

/-!
# The end of `n`

After the L phase: E' and Re' become E at rest and Re = 0, then Rd's cells move to Re one by
one (`TL` loop) until Rd = 0; then M and P are compared at the far left (halt iff equal);
M is erased, P reset to 0, K252 switched on, and the walk starts on `n + 1`.
-/

namespace TM.LehmerTau
open St

local notation "F" => false

/-- the TL loop: Rd has `r + 2` cells, Re `q + 2` -/
def TLc (M : Nat) (K : List KB) (r q : Nat) : Cfg St :=
  cfgL TL1 (LS M (.pl (r + 2) :: K)) (F ::: F ::: ones 3 (F ::: F ::: ones (q + 2) (F ::: F ::: ones 2 blank)))

theorem en_tl (M n : Nat) (K : List KB) (hn : 1 ≤ n) :
    Rch ⟨UK1, F ::: F ::: LS M (.pl (n + 1) :: K), BL⟩ (TLc M K (n - 1) 0) := by
  unfold BL TLc
  gR; gR; gR; gR; gR; gL; gL; gL
  sLn 3; gL; gL
  rw [show n - 1 + 2 = n + 1 by omega]; fin

theorem tl_step (M : Nat) (K : List KB) (r q : Nat) : Rch (TLc M K (r + 1) q) (TLc M K r (q + 1)) := by
  unfold TLc
  rw [LS_pl, LS_pl]
  gL; gL; gR; gR; gR; gR; gR; gR; gR; gR; gR; gL; gL; gL
  sLn 3; gL; gL; fin

theorem tl_loop (M : Nat) (K : List KB) : ∀ r q, Rch (TLc M K r q) (TLc M K 0 (q + r))
  | 0, q => by simp only [Nat.add_zero]; fin
  | r + 1, q => by
    refine Rch.tr (tl_step M K r q) ?_
    rw [show q + (r + 1) = q + 1 + r by omega]; exact tl_loop M K r (q + 1)

theorem tl_end (M : Nat) (K : List KB) (q : Nat) :
    Rch (TLc M K 0 q) (cfgL CMa1 (F ::: LS M K) (F ::: ones 2 (F ::: F ::: ones 3 (F ::: F ::: ones (q + 2)
      (F ::: F ::: ones 2 blank))))) := by
  unfold TLc
  rw [LS_pl]
  gL; gL; gL; fin

/-! ## the compare -/

/-- `CM1` on M's first cell: M has `a + 1` cells, then `g + 2` zeros, P (`b + 1` cells) -/
def CMc (a b g : Nat) (Rt : Strm) : Cfg St := ⟨CM1, blank, ones (a + 1) (zeros (g + 2) (ones (b + 1) (F ::: F ::: Rt)))⟩

/-- the compare is over (`M ≠ P`): P is one cell, `CK1` on K65's cell 0 -/
def CKc (Rt : Strm) : Cfg St := ⟨CK1, F ::: F ::: true ::: blank, Rt⟩

theorem zeros_blank' (n : Nat) (s : Strm) (h : s = blank) : zeros n s = blank := by rw [h, zeros_blank]

theorem ca_loop (Rt : Strm) : ∀ c, Rch ⟨CA3, blank, ones (c + 2) (F ::: F ::: Rt)⟩ (CKc Rt)
  | 0 => by
    unfold CKc
    gR; gR; gL; gR; gR; gR
    simp only [cons_blank]; fin
  | c + 1 => by
    gR; gR; gL
    rw [cons_blank]; exact ca_loop Rt c

theorem cmp (Rt : Strm) : ∀ a b g, (a = b → HaltAt (CMc a b g Rt)) ∧ (a ≠ b → Rch (CMc a b g Rt) (CKc Rt)) := by
  intro a
  induction a with
  | zero =>
    intro b g
    unfold CMc
    have s1 : Rch ⟨CM1, blank, ones (0 + 1) (zeros (g + 2) (ones (b + 1) (F ::: F ::: Rt)))⟩
        ⟨CP1, blank, ones (b + 1) (F ::: F ::: Rt)⟩ := by
      gR; gL0; gR; zRn (g + 2)
      show Rch ⟨CP1, zeros (g + 2) (F ::: blank), _⟩ _
      rw [cons_blank, zeros_blank]; fin
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      refine ⟨F ::: true ::: blank, F ::: Rt, Rch.tr s1 ?_⟩
      gR; gR; fin
    · refine ⟨fun h => by omega, fun _ => Rch.tr s1 ?_⟩
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
      gR; gL
      show Rch ⟨CA3, blank, ones (c + 2) (F ::: F ::: Rt)⟩ _
      exact ca_loop Rt c
  | succ a ih =>
    intro b g
    have pre : Rch (CMc (a + 1) b g Rt)
        ⟨CM6, true ::: zeros (g + 1) (F ::: ones (a + 1) (F ::: blank)), ones b (F ::: F ::: Rt)⟩ := by
      unfold CMc
      gR; gL0; gR; sRn (a + 1); gR; zRn (g + 1); gR
      fin
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · refine ⟨fun h => by omega, fun _ => Rch.tr pre ?_⟩
      unfold CKc
      gL; gL; zLn (g + 1); gL; gL
      eLn a
      gR; zRn a; gR; gR; zRn (g + 1); gR; gR; gR
      show Rch ⟨CK1, F ::: F ::: true ::: zeros (g + 1) (F ::: F ::: zeros a (F ::: blank)), Rt⟩ _
      simp only [cons_blank, zeros_blank]; fin
    · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
      have st : Rch (CMc (a + 1) (c + 1) g Rt) (CMc a c (g + 1) Rt) := by
        refine Rch.tr pre ?_
        unfold CMc
        gL; gL; zLn (g + 1); gL; gL; sLn a; gR
        show Rch ⟨CM1, F ::: blank, ones a (true ::: F ::: zeros (g + 1) (F ::: true ::: ones c (F ::: F ::: Rt)))⟩ _
        rw [cons_blank, ← zeros_succ' (g + 1), ← ones_succ' a]; fin
      have := ih c (g + 1)
      exact ⟨fun h => HaltAt.back st (this.1 (by omega)), fun h => Rch.tr st (this.2 (by omega))⟩

theorem FCM : FarL delta CMa1 CMa2 CMa3 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- to the far left, the compare starts -/
theorem cm_start (kA kB kC p M : Nat) (hA : 1 ≤ kA) (hC : 1 ≤ kC) (R0 : Strm) :
    Rch (cfgL CMa1 (F ::: LS M (.dg 1 1 :: .pl 1 :: .pl 13 :: KLx (.dg kC 1) kB (.pl (kA + 2)) p)) R0)
      (CMc M p 0 (ones (kA + 2) (F ::: F ::: ones (kB + 2) (F ::: F ::: true ::: F ::: ones kC (F ::: F ::: ones 13
        (F ::: F ::: ones 1 (F ::: F ::: true ::: F ::: ones 1 (F ::: R0)))))))) := by
  have hk : ∀ b ∈ (.dg 1 1 :: .pl 1 :: .pl 13 :: KLx (.dg kC 1) kB (.pl (kA + 2)) p : List KB), b.ok := by
    intro b hb; simp [KLx] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [KB.ok] <;> omega
  have hc : Clean12 (F :: (lpR (.dg 1 1 :: .pl 1 :: .pl 13 :: KLx (.dg kC 1) kB (.pl (kA + 2)) p) ++ rep (M + 1))) := by
    have := c12_LS M _ hk
    obtain ⟨w, hw⟩ : ∃ w, lpR (.dg 1 1 :: .pl 1 :: .pl 13 :: KLx (.dg kC 1) kB (.pl (kA + 2)) p) ++ rep (M + 1) =
      true :: w := ⟨_, rfl⟩
    rw [hw] at this ⊢; cases this with | one h => exact Clean12.z1 h
  have := FCM.go hc R0
  unfold LS
  refine Rch.tr this ?_
  simp only [KLx, lpR, KB.w, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_assoc, List.singleton_append, List.cons_append, app_append, app_cons, rep, app_replicate,
    List.reverse_replicate, List.reverse_reverse, Nat.add_sub_cancel]
  unfold CMc
  gR0; gR; gR
  show Rch ⟨CM1, F ::: F ::: F ::: blank, _⟩ _
  simp only [cons_blank]; fin

/-- after the compare: K252 on, the walk on `n + 1` starts (`i = 1`, `d = 1`) -/
theorem ck_next (kA kB kC n : Nat) (hC : 1 ≤ kC) (hn : 1 ≤ n) :
    Rch (CKc (ones (kA + 2) (F ::: F ::: ones (kB + 2) (F ::: F ::: true ::: F ::: ones kC (F ::: F ::: ones 13
        (F ::: F ::: ones 1 (F ::: F ::: true ::: F ::: ones 1 (F ::: F ::: ones 2 (F ::: F ::: ones 3 (F ::: F :::
        ones (n - 1 + 2) (F ::: F ::: ones 2 blank)))))))))))
      (DV (LS 0 (.pl 1 :: .pl 13 :: KR kA kB kC)) (BD n) 1 0) := by
  obtain ⟨c, rfl⟩ : ∃ c, kC = c + 1 := ⟨kC - 1, by omega⟩
  unfold CKc
  sRn (kA + 2); gR; gR; gR; gR
  refine Rch.tr (PH2a.find2 kB 0 _ _) ?_
  gR; sRn c; gR; gR; sRn 13; gR; gR; gR; gR; gR; gR; gR; gL; gL; gL
  unfold DV BD RB KR
  rw [show n - 1 + 2 = n + 1 by omega]
  simp only [LS_pl, LS_dg1, LS, lpR, KB.w, List.nil_append, app_append, app_rep, rep, app_replicate,
    List.reverse_replicate, List.reverse_cons, List.reverse_nil, List.singleton_append, List.cons_append, app_cons,
    app_nil, List.reverse_append, ones_cons_true, Nat.add_sub_cancel]
  fin

/-- **The end of `n`**: halt iff `M = P`, else the start of `n + 1` -/
theorem endn (kA kB kC p M n : Nat) (hA : 1 ≤ kA) (hC : 1 ≤ kC) (hn : 1 ≤ n) :
    (M = p → HaltAt ⟨UK1, F ::: F ::: LS M (.pl (n + 1) :: .dg 1 1 :: .pl 1 :: .pl 13 ::
      KLx (.dg kC 1) kB (.pl (kA + 2)) p), BL⟩) ∧
    (M ≠ p → Rch ⟨UK1, F ::: F ::: LS M (.pl (n + 1) :: .dg 1 1 :: .pl 1 :: .pl 13 ::
      KLx (.dg kC 1) kB (.pl (kA + 2)) p), BL⟩ (DV (LS 0 (.pl 1 :: .pl 13 :: KR kA kB kC)) (BD n) 1 0)) := by
  let K : List KB := .dg 1 1 :: .pl 1 :: .pl 13 :: KLx (.dg kC 1) kB (.pl (kA + 2)) p
  have s1 := Rch.tr (en_tl M n K hn) (Rch.tr (tl_loop M K (n - 1) 0) (tl_end M K _))
  rw [Nat.zero_add] at s1
  have s2 := Rch.tr s1 (cm_start kA kB kC p M hA hC _)
  exact ⟨fun h => HaltAt.back s2 ((cmp _ M p 0).1 h),
    fun h => Rch.tr s2 (Rch.tr ((cmp _ M p 0).2 h) (ck_next kA kB kC n hC hn))⟩

end TM.LehmerTau
