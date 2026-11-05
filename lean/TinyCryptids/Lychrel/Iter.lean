import TinyCryptids.Lychrel.Mul

/-!
# One iteration of the reversal loop: T := T / 10, A := 10 A + T % 10
-/

namespace TM.Lychrel
open St

local notation "F" => false

/-- end of the walk when T is X: keep it, make P (first cell), back to D -/
theorem wd_keep (t p h a q : Nat) (hp : p ≤ 9) (hh : 2 ≤ h) (hq : 1 ≤ q) :
    Rch (WD [] t p h a (some q)) (PL t h a q 1 p) := by
  obtain ⟨n, hn⟩ : ∃ n, 10 - p = n + 1 := ⟨9 - p, by omega⟩
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  unfold WD Qp
  simp only [List.reverse_nil, app_nil]
  rw [hn]
  sLn (t + 3); gL; gL; gR; gR; gR; gR; sRn (t + 2); gR
  have := dep4 t 0 h' a q 0 p (by omega) hq hp
  rw [show 0 + 1 + h' = h' + 1 by omega] at this
  unfold LX at this
  rw [hn, ones_zero, cons_blank, cons_blank] at this
  rw [ones_tr (t + 2)]
  exact this

/-- end of the walk when T is not X (a gap of at least 3 left of T): erase T -/
theorem wd_erase (x g t p h a q : Nat) (hg : 3 ≤ g) (hp : p ≤ 9) (hh : 2 ≤ h) (hq : 1 ≤ q) :
    Rch (WD (List.replicate (x + 3) true ++ List.replicate g false) t p h a (some q))
      (PL x (g + t + 3 + h) a q 1 p) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 3 := ⟨g - 3, by omega⟩
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  unfold WD Qp
  rw [show (List.replicate (x + 3) true ++ List.replicate (g' + 3) false).reverse =
    List.replicate (g' + 3) false ++ List.replicate (x + 3) true by simp [List.reverse_append, List.reverse_replicate],
    app_append, app_zeros, app_replicate]
  sLn (t + 3); gL; gL; gR; gR; gR; eRn (t + 3); gR
  have := dep4 x (t + 3 + (g' + 3)) h' a q 0 p (by omega) hq hp
  rw [show t + 3 + (g' + 3) + 1 + h' = g' + 3 + t + 3 + (h' + 1) by omega] at this
  rw [ones_zero, cons_blank, cons_blank] at this
  unfold LX at this
  show Rch ⟨rP4, F ::: zeros (t + 3) (F ::: F ::: F ::: zeros g' _), _⟩ _
  rw [zeros_fa, zeros_fa, zeros_fa, zeros_add, ← zeros_cons_false, zeros_fa,
    show t + 3 + 1 + 1 + 1 + g' + 1 = t + 3 + (g' + 3) + 1 by omega]
  exact this

theorem CX_nil : CX [] where
  r n c := by
    have := GC.append (GC.replicate (n + 1)) (GC.zl 0 (GC.replicate c))
    simpa [List.replicate_succ] using this
  l n c := by
    have := GC.append (GC.replicate (c + 1)) (GC.zl 0 (GC.replicate n))
    simpa [List.replicate_succ] using this

theorem CX_gap (x g : Nat) : CX (List.replicate (x + 3) true ++ List.replicate (g + 2) false) where
  r n c := by
    have := GC.append (GC.replicate (n + 1)) (GC.zl 0 (GC.append (GC.replicate (x + 2))
      (GC.zl g (GC.replicate c))))
    simpa [List.replicate_succ] using this
  l n c := by
    have := GC.append (GC.replicate (c + 1)) (GC.zl g (GC.append (GC.replicate (x + 2))
      (GC.zl 0 (GC.replicate n))))
    rw [List.reverse_append, List.reverse_replicate, List.reverse_replicate]
    simpa [List.replicate_succ] using this

/-- the cells left of the new T at the start of the next iteration -/
abbrev cxg (x g : Nat) : List Bool := List.replicate (x + 3) true ++ List.replicate (g + 3) false

/-- end of an iteration with t' = q - 3 > 0: A's last cell is erased, Q and P are the
new T and A, T's hole at cell 1 -/
theorem pl_next (x g q r : Nat) (hg : 2 ≤ g) (hq : 4 ≤ q) (hr : 1 ≤ r) :
    Rch (PL x g 0 q r 0) (DV (cxg x g) (q - 3) 1 9 2 (r - 1) none) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 2 := ⟨g - 2, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 4 := ⟨q - 4, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  unfold PL RtP
  rw [show 10 - 0 = 10 by rfl]
  refine Rch.tr (bstep_wrap _) ?_
  gR; gR; gR; gR; sRn (x + 2); gR; zRn (g' + 1); gR; gL; gR; gR; gR; gR; gR; gR; gL; gL; gL
  show Rch (cfgL hFP (true ::: F ::: F ::: F ::: zeros (g' + 1) (F ::: ones (x + 2)
    (true ::: F ::: F ::: true ::: F ::: ones 10 blank))) _) _
  have e2 : (true ::: F ::: F ::: F ::: zeros (g' + 1) (F ::: ones (x + 2)
      (true ::: F ::: F ::: true ::: F ::: ones 10 blank))) =
      app (List.replicate (0 + 1) true ++ ((cxg x (g' + 2)).reverse ++ F :: F :: List.replicate (0 + 1) true))
        (F ::: ones 10 blank) := by
    simp [cxg, app_append, app_replicate, app_zeros, List.reverse_replicate, zeros_fa, ones_tr]; rfl
  rw [e2]
  refine Rch.tr (FF.cross ((CX_gap x (g' + 3)).l 0 0) _ _) ?_
  gL; gR
  unfold DV TAQ Qp cxg
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_replicate, List.reverse_cons,
    List.reverse_nil, List.nil_append, app_append, app_replicate, List.append_assoc, List.cons_append,
    List.singleton_append]
  rw [show q' + 4 - 3 + 2 - 1 = q' + 2 by omega, show r' + 1 - 1 + 1 = r' + 1 by omega, app_zeros,
    show g' + 2 + 3 = g' + 3 + 2 by omega]
  show Rch ⟨fA, ones 10 blank, F ::: ones 1 (F ::: F ::: app (List.replicate (x + 3) true ++
    (List.replicate (g' + 3 + 2) F ++ List.replicate 1 true))
      (F ::: true ::: true ::: ones q' (F ::: F ::: ones (r' + 1) blank)))⟩ _
  rw [app_append, app_append, app_replicate, app_zeros, app_replicate]
  fin

end TM.Lychrel
