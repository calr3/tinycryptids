import TinyCryptids.PAK.Tape

/-!
# Register operations on the register file

From a node's transition into a chain state to the return on the node's cell (`a`, with `Lc`
left of it): an inc or a successful decnz (`retok`) and a failed decnz (`retfail`), on a present
register or on the one after the last (created).  `op_inc`, `op_dec` state them for the
registers `R`, with nine or ten registers present (`LV`).
-/

namespace TMK.PA

open TM (Dir)
open TM.PA (R)

theorem U_ys (g : Nat) (l : List Nat) : ∀ y ∈ (regs l ++ [9]).reverse ++ List.replicate g 1, U y := by
  intro y hy
  simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hy
  rcases hy with (h | h) | h
  · exact U_regs l y h
  · right; exact h
  · exact U_rep g y h

theorem inc_list (a : Nat) (Lc : Strm) (g : Nat) (l : List Nat) (p : Nat) (hp : p < l.length)
    (hN : p + 1 ≤ NR) :
    Reach delta ⟨.cinc (p + 1), a ∷ Lc, lst (List.replicate g 1 ++ regs l) blank⟩
      ⟨.retok, Lc, a ∷ lst (List.replicate g 1 ++ regs (upd l p (l.getD p 0 + 1))) blank⟩ := by
  have h1 := chain_gap true (p + 1) (by omega) hN g (a ∷ Lc) (lst (regs l) blank)
  have h2 := chain_regs true l p hp hN (lst (List.replicate g 1) (a ∷ Lc))
  have h3 := shift_ret a Lc (List.replicate (l.getD p 0) 1 ++ regs (l.drop (p + 1)))
    ((regs (l.take p) ++ [9]).reverse ++ List.replicate g 1) 1 (Or.inl rfl)
    (fun x hx => by
      rcases List.mem_append.mp hx with h | h
      · exact U_rep _ x h
      · exact U_regs _ x h)
    (U_ys g _)
  rw [show lst (List.replicate g 1 ++ regs l) blank = lst (List.replicate g 1) (lst (regs l) blank) from lst_append _ _ _]
  rw [← lst_append] at h2
  have e : ((regs (l.take p) ++ [9]).reverse ++ List.replicate g 1).reverse ++
      1 :: (List.replicate (l.getD p 0) 1 ++ regs (l.drop (p + 1))) =
      List.replicate g 1 ++ regs (upd l p (l.getD p 0 + 1)) := by
    simp [regs_upd, List.replicate_succ]
  rw [e] at h3
  exact Reach.trans _ h1 (Reach.trans _ h2 h3)

theorem inc_new (a : Nat) (Lc : Strm) (g : Nat) (l : List Nat) (hN : l.length + 1 ≤ NR) :
    Reach delta ⟨.cinc (l.length + 1), a ∷ Lc, lst (List.replicate g 1 ++ regs l) blank⟩
      ⟨.retok, Lc, a ∷ lst (List.replicate g 1 ++ regs (l ++ [1])) blank⟩ := by
  have h1 := chain_gap true (l.length + 1) (by omega) hN g (a ∷ Lc) (lst (regs l) blank)
  have h2 := chain_new true l hN (lst (List.replicate g 1) (a ∷ Lc))
  have h3 := shift_ret a Lc [] ((regs l ++ [9]).reverse ++ List.replicate g 1) 1 (Or.inl rfl)
    (fun x hx => by simp at hx) (U_ys g _)
  rw [show lst (List.replicate g 1 ++ regs l) blank = lst (List.replicate g 1) (lst (regs l) blank) from lst_append _ _ _]
  rw [← lst_append] at h2
  have e : ((regs l ++ [9]).reverse ++ List.replicate g 1).reverse ++ [1] =
      List.replicate g 1 ++ regs (l ++ [1]) := by
    simp [regs_append, regs]
  rw [e] at h3
  exact Reach.trans _ h1 (Reach.trans _ h2 h3)

theorem dec_pos (a : Nat) (Lc : Strm) (g : Nat) (l : List Nat) (p : Nat) (hp : p < l.length)
    (hN : p + 1 ≤ NR) (hv : 0 < l.getD p 0) :
    Reach delta ⟨.cdec (p + 1), a ∷ Lc, lst (List.replicate g 1 ++ regs l) blank⟩
      ⟨.retok, Lc, a ∷ lst (List.replicate g 1 ++ regs (upd l p (l.getD p 0 - 1))) blank⟩ := by
  have h1 := chain_gap false (p + 1) (by omega) hN g (a ∷ Lc) (lst (regs l) blank)
  have h2 := chain_regs false l p hp hN (lst (List.replicate g 1) (a ∷ Lc))
  rw [show lst (List.replicate g 1 ++ regs l) blank = lst (List.replicate g 1) (lst (regs l) blank) from lst_append _ _ _]
  rw [← lst_append] at h2
  obtain ⟨v, hv'⟩ : ∃ v, l.getD p 0 = v + 1 := ⟨l.getD p 0 - 1, by omega⟩
  rw [hv'] at h2 ⊢
  have h3 : Reach delta ⟨.dstart, lst ((regs (l.take p) ++ [9]).reverse ++ List.replicate g 1) (a ∷ Lc),
      lst (List.replicate (v + 1) 1 ++ regs (l.drop (p + 1))) blank⟩
      ⟨.dscan, 1 ∷ lst ((regs (l.take p) ++ [9]).reverse ++ List.replicate g 1) (a ∷ Lc),
        lst (List.replicate v 1 ++ regs (l.drop (p + 1))) blank⟩ := by
    have := stepR (δ := delta) (q := .dstart) (q' := .dscan) (w := 1)
      (L := lst ((regs (l.take p) ++ [9]).reverse ++ List.replicate g 1) (a ∷ Lc))
      (R := lst (List.replicate (v + 1) 1 ++ regs (l.drop (p + 1))) blank) rfl
    simpa [List.replicate_succ] using this
  have h4 := dscan_ret a Lc (List.replicate v 1 ++ regs (l.drop (p + 1)))
    ((regs (l.take p) ++ [9]).reverse ++ List.replicate g 1)
    (fun x hx => by
      rcases List.mem_append.mp hx with h | h
      · exact U_rep _ x h
      · exact U_regs _ x h)
    (U_ys g _)
  have e : ((regs (l.take p) ++ [9]).reverse ++ List.replicate g 1).reverse ++
      (List.replicate v 1 ++ regs (l.drop (p + 1))) =
      List.replicate g 1 ++ regs (upd l p (v + 1 - 1)) := by
    simp [regs_upd]
  rw [e] at h4
  exact Reach.trans _ h1 (Reach.trans _ h2 (Reach.trans _ h3 h4))

theorem dec_zero (a : Nat) (Lc : Strm) (g : Nat) (l : List Nat) (p : Nat) (hp : p < l.length)
    (hN : p + 1 ≤ NR) (hv : l.getD p 0 = 0) :
    Reach delta ⟨.cdec (p + 1), a ∷ Lc, lst (List.replicate g 1 ++ regs l) blank⟩
      ⟨.retfail, Lc, a ∷ lst (List.replicate g 1 ++ regs l) blank⟩ := by
  have h1 := chain_gap false (p + 1) (by omega) hN g (a ∷ Lc) (lst (regs l) blank)
  have h2 := chain_regs false l p hp hN (lst (List.replicate g 1) (a ∷ Lc))
  rw [show lst (List.replicate g 1 ++ regs l) blank = lst (List.replicate g 1) (lst (regs l) blank) from lst_append _ _ _]
  rw [← lst_append] at h2
  rw [hv] at h2
  -- dstart reads the next separator or the blank
  have hR : (lst (regs (l.drop (p + 1))) blank 0 = 9 ∨ lst (regs (l.drop (p + 1))) blank 0 = 0) := by
    cases l.drop (p + 1) with
    | nil => right; rfl
    | cons v l' => left; rfl
  have hst : delta .dstart (lst (regs (l.drop (p + 1))) blank 0) =
      some (lst (regs (l.drop (p + 1))) blank 0, .L, .retfail) := by
    rcases hR with h | h <;> rw [h] <;> rfl
  have h3 := stepL (δ := delta) (L := lst ((regs (l.take p) ++ [9]).reverse ++ List.replicate g 1) (a ∷ Lc))
    (R := lst (regs (l.drop (p + 1))) blank) hst
  rw [cons_head_tl] at h3
  simp only [List.replicate_zero, List.nil_append] at h2
  refine Reach.trans _ h1 (Reach.trans _ h2 (Reach.trans _ h3 ?_))
  have hrev : (regs (l.take p) ++ [9]).reverse = 9 :: (regs (l.take p)).reverse := by simp
  rw [hrev]
  simp only [List.cons_append, lst_cons, cons_zero, tl_cons]
  have h4 := ret_back (q := .retfail) (Or.inr rfl) a Lc ((regs (l.take p)).reverse ++ List.replicate g 1)
    (fun y hy => by
      rcases List.mem_append.mp hy with h | h
      · exact U_regs _ y (List.mem_reverse.mp h)
      · exact U_rep g y h)
    (9 ∷ lst (regs (l.drop (p + 1))) blank) (Or.inr rfl)
  have e : lst ((regs (l.take p)).reverse ++ List.replicate g 1).reverse (9 ∷ lst (regs (l.drop (p + 1))) blank) =
      lst (List.replicate g 1) (lst (regs l) blank) := by
    rw [regs_split l p hp, hv]
    simp [lst_append]
  rw [e] at h4
  simpa [lst_append] using h4

theorem dec_new (a : Nat) (Lc : Strm) (g : Nat) (l : List Nat) (hN : l.length + 1 ≤ NR) :
    Reach delta ⟨.cdec (l.length + 1), a ∷ Lc, lst (List.replicate g 1 ++ regs l) blank⟩
      ⟨.retfail, Lc, a ∷ lst (List.replicate g 1 ++ regs (l ++ [0])) blank⟩ := by
  have h1 := chain_gap false (l.length + 1) (by omega) hN g (a ∷ Lc) (lst (regs l) blank)
  have h2 := chain_new false l hN (lst (List.replicate g 1) (a ∷ Lc))
  rw [show lst (List.replicate g 1 ++ regs l) blank = lst (List.replicate g 1) (lst (regs l) blank) from lst_append _ _ _]
  rw [← lst_append] at h2
  have h3 := stepL (δ := delta) (q := .dstart) (q' := .retfail) (w := 0)
    (L := lst ((regs l ++ [9]).reverse ++ List.replicate g 1) (a ∷ Lc)) (R := blank) rfl
  refine Reach.trans _ h1 (Reach.trans _ h2 (Reach.trans _ h3 ?_))
  have hrev : (regs l ++ [9]).reverse = 9 :: (regs l).reverse := by simp
  rw [hrev]
  simp only [List.cons_append, lst_cons, cons_zero, tl_cons, tl_blank]
  have h4 := ret_back (q := .retfail) (Or.inr rfl) a Lc ((regs l).reverse ++ List.replicate g 1)
    (fun y hy => by
      rcases List.mem_append.mp hy with h | h
      · exact U_regs _ y (List.mem_reverse.mp h)
      · exact U_rep g y h)
    (9 ∷ 0 ∷ blank) (Or.inr rfl)
  have e : lst ((regs l).reverse ++ List.replicate g 1).reverse (9 ∷ 0 ∷ blank) =
      lst (List.replicate g 1 ++ regs (l ++ [0])) blank := by
    simp [lst_append, regs_append, regs, cons_blank]
  rw [e] at h4
  exact h4

/-! ## the registers `R` in the register file -/

/-- the registers in the order of first use (`mpos`) -/
def mlist (s : R) : List Nat := [s.pl, s.np, s.s1, s.s2, s.ac, s.p1, s.p3, s.ws, s.top, s.p2]

/-- the register file with the first `n` registers present -/
def rfile (s : R) (n : Nat) : List Nat := regs ((mlist s).take n)

/-- nine registers (all but `param2`, which is then zero) or ten -/
def LV (s : R) (n : Nat) : Prop := (n = 9 ∧ s.p2 = 0) ∨ n = 10

theorem LV_10 (s : R) : LV s 10 := Or.inr rfl

theorem mpos_lt (r : Fin 10) : mpos r < 10 := by
  revert r; decide

theorem mpos_lt9 (r : Fin 10) (h : r ≠ 6) : mpos r < 9 := by
  revert r; decide

theorem mpos6 : mpos 6 = 9 := rfl

theorem rfile10 (s : R) : rfile s 10 = regs (mlist s) := rfl

theorem mlist_upd (s : R) (r : Fin 10) (x : Nat) :
    upd (mlist s) (mpos r) x = mlist (s.set r x) := by
  rcases r with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r, hr⟩ <;> first | omega | rfl

theorem mlist_get (s : R) (r : Fin 10) : (mlist s).getD (mpos r) 0 = s.get r := by
  rcases r with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r, hr⟩ <;> first | omega | rfl

theorem mlist9_upd (s : R) (r : Fin 10) (h : r ≠ 6) (x : Nat) :
    upd ((mlist s).take 9) (mpos r) x = (mlist (s.set r x)).take 9 := by
  rcases r with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r, hr⟩ <;> first | omega | rfl | exact (h (Fin.ext rfl)).elim

theorem mlist9_get (s : R) (r : Fin 10) (h : r ≠ 6) : ((mlist s).take 9).getD (mpos r) 0 = s.get r := by
  rcases r with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r, hr⟩ <;> first | omega | rfl | exact (h (Fin.ext rfl)).elim

theorem len_mlist (s : R) : (mlist s).length = 10 := rfl
theorem len_mlist9 (s : R) : ((mlist s).take 9).length = 9 := rfl

theorem set_p2 (s : R) (r : Fin 10) (h : r ≠ 6) (x : Nat) : (s.set r x).p2 = s.p2 := by
  rcases r with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r, hr⟩ <;> first | omega | rfl | exact (h (Fin.ext rfl)).elim

theorem op_inc (r : Fin 10) (s : R) (n : Nat) (hn : LV s n) (a : Nat) (Lc : Strm) (g : Nat) :
    ∃ n', LV (s.inc r) n' ∧ Reach delta ⟨.cinc (mpos r + 1), a ∷ Lc, lst (List.replicate g 1 ++ rfile s n) blank⟩
      ⟨.retok, Lc, a ∷ lst (List.replicate g 1 ++ rfile (s.inc r) n') blank⟩ := by
  rcases hn with ⟨rfl, hp2⟩ | rfl
  · by_cases h6 : r = 6
    · subst h6
      refine ⟨10, Or.inr rfl, ?_⟩
      have := inc_new a Lc g ((mlist s).take 9) (by rw [len_mlist9]; decide)
      rw [len_mlist9] at this
      have e : (mlist s).take 9 ++ [1] = mlist (s.inc 6) := by
        simp only [mlist, TM.PA.R.inc_6, hp2]; rfl
      rw [e] at this
      exact this
    · refine ⟨9, Or.inl ⟨rfl, by simp only [TM.PA.R.inc]; rw [set_p2 s r h6]; exact hp2⟩, ?_⟩
      have := inc_list a Lc g ((mlist s).take 9) (mpos r) (by rw [len_mlist9]; exact mpos_lt9 r h6)
        (by have := mpos_lt9 r h6; simp only [NR]; omega)
      rw [mlist9_get s r h6, mlist9_upd s r h6] at this
      exact this
  · refine ⟨10, Or.inr rfl, ?_⟩
    have := inc_list a Lc g (mlist s) (mpos r) (by rw [len_mlist]; exact mpos_lt r)
      (by have := mpos_lt r; simp only [NR]; omega)
    rw [mlist_get, mlist_upd] at this
    exact this

theorem op_dec (r : Fin 10) (s : R) (n : Nat) (hn : LV s n) (a : Nat) (Lc : Strm) (g : Nat) :
    (0 < s.get r → ∃ n', LV (s.dec r) n' ∧
      Reach delta ⟨.cdec (mpos r + 1), a ∷ Lc, lst (List.replicate g 1 ++ rfile s n) blank⟩
        ⟨.retok, Lc, a ∷ lst (List.replicate g 1 ++ rfile (s.dec r) n') blank⟩) ∧
    (s.get r = 0 → ∃ n', LV s n' ∧
      Reach delta ⟨.cdec (mpos r + 1), a ∷ Lc, lst (List.replicate g 1 ++ rfile s n) blank⟩
        ⟨.retfail, Lc, a ∷ lst (List.replicate g 1 ++ rfile s n') blank⟩) := by
  rcases hn with ⟨rfl, hp2⟩ | rfl
  · by_cases h6 : r = 6
    · subst h6
      constructor
      · intro h; simp [TM.PA.R.get, hp2] at h
      · intro _
        refine ⟨10, Or.inr rfl, ?_⟩
        have := dec_new a Lc g ((mlist s).take 9) (by rw [len_mlist9]; decide)
        rw [len_mlist9] at this
        have e : (mlist s).take 9 ++ [0] = mlist s := by simp only [mlist, hp2]; rfl
        rw [e] at this
        exact this
    · have hp : mpos r < ((mlist s).take 9).length := by rw [len_mlist9]; exact mpos_lt9 r h6
      have hN : mpos r + 1 ≤ NR := by have := mpos_lt9 r h6; simp only [NR]; omega
      constructor
      · intro h
        refine ⟨9, Or.inl ⟨rfl, by simp only [TM.PA.R.dec]; rw [set_p2 s r h6]; exact hp2⟩, ?_⟩
        have := dec_pos a Lc g ((mlist s).take 9) (mpos r) hp hN (by rw [mlist9_get s r h6]; exact h)
        rw [mlist9_get s r h6, mlist9_upd s r h6] at this
        exact this
      · intro h
        exact ⟨9, Or.inl ⟨rfl, hp2⟩, dec_zero a Lc g _ _ hp hN (by rw [mlist9_get s r h6]; exact h)⟩
  · have hp : mpos r < (mlist s).length := by rw [len_mlist]; exact mpos_lt r
    have hN : mpos r + 1 ≤ NR := by have := mpos_lt r; simp only [NR]; omega
    constructor
    · intro h
      refine ⟨10, Or.inr rfl, ?_⟩
      have := dec_pos a Lc g (mlist s) (mpos r) hp hN (by rw [mlist_get]; exact h)
      rw [mlist_get, mlist_upd] at this
      exact this
    · intro h
      exact ⟨10, Or.inr rfl, dec_zero a Lc g (mlist s) (mpos r) hp hN (by rw [mlist_get]; exact h)⟩

end TMK.PA
