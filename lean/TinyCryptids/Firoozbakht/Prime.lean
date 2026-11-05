import TinyCryptids.Firoozbakht.Horner
import TinyCryptids.Firoozbakht.CopyC
import TinyCryptids.Firoozbakht.Compare

/-!
# The prime path

`m = q` is prime, the list is `pre ++ [p]` (`p` the previous prime), `N` holds `e`:
the marker goes back to `p`; `M` is copied to `M'`; `H_B` pushes `B = p ^ (e - 1)`; `N` grows
and its hole moves to cell 3; `H_A` pushes `A = q ^ (e - 2)`; then `B` and `A` are compared.
-/

namespace TM.Firoozbakht
open St TinyCryptids

local notation "F" => false
local notation "T" => true

/-- a walk to the first run of three blanks -/
structure Walk (w1 w2 w3 : St) : Prop where
  a1 : delta w1 true = some (true, Dir.R, w1)
  a0 : delta w1 false = some (false, Dir.R, w2)
  b1 : delta w2 true = some (true, Dir.R, w1)
  b0 : delta w2 false = some (false, Dir.R, w3)
  c1 : delta w3 true = some (true, Dir.R, w1)

theorem Walk.cross {w1 w2 w3 : St} (W : Walk w1 w2 w3) {u : List Bool} (hu : Clean12 u) (L X : Strm) :
    Rch ⟨w1, L, app u X⟩ ⟨w1, app u.reverse L, X⟩ := by
  induction hu generalizing L with
  | nil => fin
  | @one l _ ih =>
    refine Rch.tr (sR W.a1) ?_
    simpa [app_append] using ih (T ::: L)
  | @z1 l _ ih =>
    refine Rch.tr (sR W.a0) ?_
    refine Rch.tr (sR W.b1) ?_
    simpa [app_append] using ih (T ::: F ::: L)
  | @z2 l _ ih =>
    refine Rch.tr (sR W.a0) ?_
    refine Rch.tr (sR W.b0) ?_
    refine Rch.tr (sR W.c1) ?_
    simpa [app_append] using ih (T ::: F ::: F ::: L)

theorem Walk.go {w1 w2 w3 : St} (W : Walk w1 w2 w3) {u : List Bool} (hu : Clean12 u) (L X : Strm) :
    Rch ⟨w1, L, app u (F ::: F ::: F ::: X)⟩ ⟨w3, F ::: F ::: app u.reverse L, F ::: X⟩ := by
  refine Rch.tr (W.cross hu L _) ?_
  refine Rch.tr (sR W.a0) ?_
  exact sR W.b0

theorem WPW : Walk pw1 pw2 pw3 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem WCW : Walk cw1 cw2 cw3 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem clean_seps : ∀ qs, Clean (seps qs)
  | [] => Clean.nil
  | q :: qs => by
    show Clean (F :: F :: (List.replicate (q + 1 + 1) T ++ seps qs))
    rw [List.replicate_succ]
    exact Clean.sep (Clean.rep_append _ (clean_seps qs))

theorem c12_skp (y : Nat) (hy : 1 ≤ y) {l : List Bool} (hl : Clean12 l) :
    Clean12 ([F, F] ++ skp y ++ l) := by
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  show Clean12 (F :: F :: T :: F :: T :: (List.replicate y' T ++ l))
  exact Clean12.z2 (Clean12.z1 ((Clean12.of_clean (Clean.replicate y')).append hl))

/-- push `R = 101` on the third blank -/
theorem push (L : Strm) : Rch ⟨pw3, L, F ::: blank⟩ (cfgL HE1 (F ::: T ::: L) (T ::: blank)) := by
  gR
  refine blankR ?_
  gR
  refine blankR ?_
  gL0; fin

/-- RETREAT: from a block (head on one of its cells left of any hole) to the previous block,
whose cell 1 becomes the marker -/
theorem retreat (a q : Nat) (X R : Strm) :
    Rch (cfgL rt1 (ones a (F ::: F ::: ones (q + 2) (F ::: X))) R)
      ⟨cw1, F ::: T ::: F ::: X, ones q (F ::: F ::: ones a R)⟩ := by
  sLn a
  gL; gL
  sLn (q + 2)
  gR; gR; gR
  fin

/-- the prime checkpoint: the marker on `p` (the last list block), head on its cell 2 -/
def PR (e m : Nat) (pre : List Nat) (p : Nat) : Cfg St :=
  ⟨cw1, F ::: T ::: lft e pre, app (List.replicate p T ++ [F, F] ++ skp m) blank⟩

/-- after the cycle: the counter does not divide `m` and it is the last list block: `m` is
prime -/
theorem trial_prime (e m : Nat) (pre : List Nat) (p : Nat) (hm : 1 ≤ m) :
    Rch ⟨kn3, ones (p + 2) (lft e pre), cyR (F ::: blank) m 1 (seps [] ++ [F, F])⟩ (PR e m pre p) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨X, hX⟩ := lft_head e pre
  simp only [cyR, seps, List.nil_append, app_cons, app_nil, Nat.add_sub_cancel]
  gR; gR; gR; gL
  rw [hX]
  refine Rch.tr (retreat 1 p _ _) ?_
  unfold PR
  rw [hX]
  simp only [skp, List.append_assoc, List.cons_append, List.nil_append, app_append, app_replicate,
    app_cons, app_nil, ones_succ, ones_zero, cons_blank]
  fin

theorem clean12_pm (p m : Nat) (hm : 1 ≤ m) : Clean12 (List.replicate p T ++ [F, F] ++ skp m) := by
  rw [List.append_assoc]
  exact Clean12.append (Clean12.of_clean (Clean.replicate p)) (by simpa using c12_skp m hm Clean12.nil)

/-- `M` is copied onto `M'`; `M` joins the list; head on cell 2 of `M'` -/
theorem prime_copy (e m : Nat) (pre : List Nat) (p : Nat) (hm : 1 ≤ m) :
    Rch (PR e m pre p)
      ⟨pw1, F ::: T ::: F ::: F ::: ones (m + 2) (F ::: F ::: ones p (F ::: T ::: lft e pre)), ones m blank⟩ := by
  unfold PR
  rw [show app (List.replicate p T ++ [F, F] ++ skp m) blank =
    app (List.replicate p T ++ [F, F] ++ skp m) (F ::: F ::: F ::: blank) by simp only [cons_blank]]
  refine Rch.tr (WCW.go (clean12_pm p m hm) _ _) ?_
  gR
  refine blankR ?_
  gL; gL; gL
  have e1 : app (List.replicate p T ++ [F, F] ++ skp m).reverse (F ::: T ::: lft e pre) =
      ones (m + 1 - 1) (F ::: ones 1 (F ::: F ::: ones p (F ::: T ::: lft e pre))) := by
    simp only [skp, List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
      List.nil_append, List.append_assoc, List.cons_append, List.singleton_append, app_append,
      app_replicate, app_cons, app_nil, Nat.add_sub_cancel, ones_succ, ones_zero]
  show Rch ⟨Cc1, app (List.replicate p T ++ [F, F] ++ skp m).reverse (F ::: T ::: lft e pre),
    F ::: F ::: ones 2 blank⟩ _
  rw [e1]
  refine Rch.tr (copyC_all m 2 _ 1 (Nat.le_refl _) hm) ?_
  unfold cpyDoneC sep
  rw [show 2 + (m + 1 - 1) = m + 2 by omega]
  sRn (m + 1)
  gR; gR; gR; gR
  rw [ones_succ' (m + 1)]; fin


/-- a Horner run: walk to the right end, push `R = 1`, find the holes, `R := β ^ (e - ep)` -/
theorem hrun {gB gE : List Bool} (hgB : Gap gB) (hgE : Gap gE) (e ep β s : Nat) {u : List Bool}
    (hu : Clean12 u) (L : Strm) (hep : 1 ≤ ep) (hepe : ep ≤ e) (hβ : 1 ≤ β) (hs : 1 ≤ s)
    (hL : app u.reverse L = app (skp s).reverse (app gB.reverse (ones β (F ::: T ::: lftE (F ::: blank) e ep gE)))) :
    Rch ⟨pw1, L, app u blank⟩
      ⟨PD1, F ::: T ::: F ::: blank, ones e (app gE (app (bH1 β) (rgt gB s (β ^ (e - ep)) 0)))⟩ := by
  rw [show app u blank = app u (F ::: F ::: F ::: blank) by simp only [cons_blank]]
  refine Rch.tr (WPW.go hu _ _) ?_
  refine Rch.tr (push _) ?_
  rw [hL]
  have h1 := he_chain hgB hgE (F ::: blank) (T ::: blank) e ep β s 0 hep hepe hβ hs
  simp only [ones_zero] at h1
  refine Rch.tr h1 ?_
  have h := horner hgB hgE blank e ep β s hep hepe hβ hs
  refine Rch.tr ?_ h
  unfold eAtC rgt
  simp only [sep_blank, sep, ones_zero, ones_succ, cons_blank]
  fin

theorem lft_eq (e : Nat) (pre : List Nat) :
    lft e pre = app (seps pre ++ [F, F]).reverse (ones e (F ::: T ::: blank)) := by
  simp only [lft, skp, List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.cons_append, List.singleton_append, app_append,
    app_replicate, app_cons, app_nil]

/-- `H_B`: `B = p ^ (e - 1)` pushed right of `M'` -/
theorem run_b (e m : Nat) (pre : List Nat) (p : Nat) (he : 1 ≤ e) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    Rch ⟨pw1, F ::: T ::: F ::: F ::: ones (m + 2) (F ::: F ::: ones p (F ::: T ::: lft e pre)), ones m blank⟩
      ⟨PD1, F ::: T ::: F ::: blank, ones e (app (seps pre ++ [F, F]) (app (bH1 p)
        (rgt (seps [m] ++ [F, F]) m (p ^ (e - 1)) 0)))⟩ := by
  rw [show ones m blank = app (List.replicate m T) blank from (app_replicate m blank).symm]
  refine hrun (gap_seps [m]) (gap_seps pre) e 1 p m (Clean12.of_clean (Clean.replicate m)) _
    (Nat.le_refl _) he hp hm ?_
  rw [lft_eq]
  simp only [lftE, skp, seps, List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.cons_append, List.singleton_append, app_append,
    app_replicate, app_cons, app_nil, ones_succ, ones_zero, Nat.add_sub_cancel, cons_blank]
  done

theorem PPD : ParserR delta PD1 PD2 := ⟨rfl, rfl, rfl⟩
theorem PQA : ParserL delta QA1 QA2 := ⟨rfl, rfl, rfl⟩
theorem PQB : ParserL delta QB1 QB2 := ⟨rfl, rfl, rfl⟩

/-- after `H_B`: `p`'s marker is filled, `N` grows on its left and its hole moves to (new)
cell 3; head on cell 4, state `pw1` -/
theorem after_b (e m : Nat) (pre : List Nat) (p r : Nat) (he : 2 ≤ e) (hm : 1 ≤ m) (hp : 2 ≤ p) :
    Rch ⟨PD1, F ::: T ::: F ::: blank, ones e (app (seps pre ++ [F, F]) (app (bH1 p)
        (rgt (seps [m] ++ [F, F]) m r 0)))⟩
      ⟨pw1, F ::: T ::: T ::: T ::: blank, app (List.replicate (e - 1) T ++ seps (pre ++ [p, m]) ++ [F, F] ++
        skp m ++ [F, F] ++ skp r) blank⟩ := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hw : Clean (List.replicate e T ++ (seps pre ++ [F, F] ++ [T])) :=
    Clean.rep_append _ ((gap_seps pre).clean Clean.nil)
  have e1 : ones e (app (seps pre ++ [F, F]) (app (bH1 (p' + 2)) (rgt (seps [m' + 1] ++ [F, F]) (m' + 1) r 0))) =
      app (List.replicate e T ++ (seps pre ++ [F, F] ++ [T])) (F ::: T ::: T ::: ones p'
        (F ::: F ::: T ::: T ::: ones (m' + 1) (F ::: F ::: T ::: F ::: ones (m' + 1) (F ::: F ::: T ::: F ::: ones r blank)))) := by
    simp only [bH1, rgt, skp, seps, sep, List.append_assoc, List.cons_append, List.nil_append,
      app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero, cons_blank]
  rw [e1]
  refine Rch.tr (PPD.find hw _ _) ?_
  gR; gR
  sRn p'
  gR; gR; gR; gL
  show Rch (cfgL QA1 (T ::: F ::: F ::: ones p' (T ::: T ::: F ::: app (List.replicate e T ++
    (seps pre ++ [F, F] ++ [T])).reverse (F ::: T ::: F ::: blank))) _) _
  have e0 : app (List.replicate e T ++ (seps pre ++ [F, F] ++ [T])).reverse (F ::: T ::: F ::: blank) =
      T ::: app (seps pre ++ [F, F]).reverse (ones e (F ::: T ::: F ::: blank)) := by
    simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.cons_append, app_append, app_replicate, app_cons]
  rw [e0]
  have hw2 : Clean ([T, F, F] ++ List.replicate (p' + 2) T) :=
    Clean.one (Clean.sep (Clean.replicate (p' + 1)))
  have e2 : (T ::: F ::: F ::: ones p' (T ::: T ::: F ::: T ::: app (seps pre ++ [F, F]).reverse
      (ones e (F ::: T ::: F ::: blank)))) = app ([T, F, F] ++ List.replicate (p' + 2) T)
      (F ::: T ::: app (seps pre ++ [F, F]).reverse (ones e (F ::: T ::: F ::: blank))) := by
    simp only [app_append, app_replicate, app_cons, app_nil]
    rw [show p' + 2 = p' + 1 + 1 from rfl, ← ones_succ', ← ones_succ']
  rw [e2]
  refine Rch.tr (PQA.find hw2 _ _) ?_
  gR; gL
  have hw3 : Clean (T :: ((seps pre ++ [F, F]).reverse ++ List.replicate e T)) := by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    exact Clean.one (by rw [List.replicate_succ]; exact (gap_seps pre).reverse.clean (Clean.replicate e'))
  have e3 : (T ::: app (seps pre ++ [F, F]).reverse (ones e (F ::: T ::: F ::: blank))) =
      app (T :: ((seps pre ++ [F, F]).reverse ++ List.replicate e T)) (F ::: T ::: F ::: blank) := by
    simp only [app_append, app_replicate, app_cons]
  rw [e3]
  refine Rch.tr (PQB.find hw3 _ _) ?_
  gL
  show Rch ⟨n1, blank, F ::: _⟩ _
  gR; gR; gR
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil,
    List.reverse_reverse, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
    app_append, app_replicate, app_cons, app_nil, ones_succ]
  gR
  simp only [skp, seps_append, seps, List.append_assoc, List.cons_append, List.nil_append,
    app_append, app_replicate, app_cons, app_nil, ones_succ, Nat.add_sub_cancel,
    show e' + 2 - 1 = e' + 1 by omega]
  fin

/-- `H_A`: `A = m ^ (e - 2)` pushed right of `B` -/
theorem run_a (e m : Nat) (pre : List Nat) (p r : Nat) (he : 2 ≤ e) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    Rch ⟨pw1, F ::: T ::: T ::: T ::: blank, app (List.replicate (e - 1) T ++ seps (pre ++ [p, m]) ++ [F, F] ++
        skp m ++ [F, F] ++ skp r) blank⟩
      ⟨PD1, F ::: T ::: F ::: blank, ones (e + 1) (app (seps (pre ++ [p, m]) ++ [F, F]) (app (bH1 m)
        (rgt [F, F] r (m ^ (e - 2)) 0)))⟩ := by
  have hu : Clean12 (List.replicate (e - 1) T ++ seps (pre ++ [p, m]) ++ [F, F] ++ skp m ++ [F, F] ++ skp r) := by
    have := c12_skp m hm (c12_skp r hr Clean12.nil)
    simp only [List.append_assoc, List.nil_append, List.append_nil] at this ⊢
    exact Clean12.append (Clean12.of_clean (Clean.replicate _))
      (Clean12.append (Clean12.of_clean (clean_seps _)) this)
  have h := hrun (gB := [F, F]) Gap.sep (gap_seps (pre ++ [p, m])) (e + 1) 3 m r hu
    (F ::: T ::: T ::: T ::: blank) (by omega) (by omega) hm hr ?_
  · rw [show e + 1 - 3 = e - 2 by omega] at h; exact h
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
  simp only [lftE, skp, List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.cons_append, List.singleton_append, app_append,
    app_replicate, app_cons, app_nil, ones_succ, ones_zero, cons_blank,
    show e' + 2 + 1 + 1 - 3 = e' + 1 by omega, show e' + 2 - 1 = e' + 1 by omega]
  done

/-- after `H_A`: to `B`'s cell 2, state `z0` (the comparison) -/
theorem after_a (e m : Nat) (gE : List Bool) (hgE : Gap gE) (r a : Nat) (hm : 2 ≤ m) :
    Rch ⟨PD1, F ::: T ::: F ::: blank, ones (e + 1) (app gE (app (bH1 m) (rgt [F, F] r a 0)))⟩
      ⟨z0, F ::: T ::: F ::: F ::: ones m (F ::: T ::: app gE.reverse (ones (e + 1) (F ::: T ::: F ::: blank))),
        ones r (F ::: F ::: T ::: F ::: ones a blank)⟩ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have hw : Clean (List.replicate (e + 1) T ++ (gE ++ [T])) :=
    Clean.rep_append _ (hgE.clean Clean.nil)
  have e1 : ones (e + 1) (app gE (app (bH1 (m' + 2)) (rgt [F, F] r a 0))) =
      app (List.replicate (e + 1) T ++ (gE ++ [T])) (F ::: T ::: T ::: ones m'
        (F ::: F ::: T ::: F ::: ones r (F ::: F ::: T ::: F ::: ones a blank))) := by
    simp only [bH1, rgt, skp, sep, List.append_assoc, List.cons_append, List.nil_append,
      app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero, cons_blank]
  rw [e1]
  refine Rch.tr (PPD.find hw _ _) ?_
  gR; gR
  sRn m'
  gR; gR; gR; gR
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.cons_append, List.append_assoc, app_append,
    app_replicate, app_cons, app_nil, ones_succ]
  rw [← ones_succ', ← ones_succ']; fin

/-- **The prime step**: from the end of the trial pass of a prime `m` (the last list block `p`),
halt iff `p ^ (e - 1) ≤ m ^ (e - 2)`; otherwise the next candidate, with `p, m` in the list and
`N` one longer -/
theorem prime_step (e m : Nat) (pre : List Nat) (p : Nat) (he : 2 ≤ e) (hm : 2 ≤ m) (hp : 2 ≤ p) :
    (p ^ (e - 1) ≤ m ^ (e - 2) →
      HaltAt ⟨kn3, ones (p + 2) (lft e pre), cyR (F ::: blank) m 1 (seps [] ++ [F, F])⟩) ∧
    (m ^ (e - 2) < p ^ (e - 1) →
      Rch ⟨kn3, ones (p + 2) (lft e pre), cyR (F ::: blank) m 1 (seps [] ++ [F, F])⟩
        (MSE (e + 1) m (pre ++ [p, m]))) := by
  have hr : 1 ≤ p ^ (e - 1) := Nat.pos_pow_of_pos _ (by omega)
  have ha : 1 ≤ m ^ (e - 2) := Nat.pos_pow_of_pos _ (by omega)
  have h1 := Rch.tr (trial_prime e m pre p (by omega)) (prime_copy e m pre p (by omega))
  have h2 := Rch.tr h1 (run_b e m pre p (by omega) (by omega) (by omega))
  have h3 := Rch.tr h2 (after_b e m pre p (p ^ (e - 1)) he (by omega) hp)
  have h4 := Rch.tr h3 (run_a e m pre p (p ^ (e - 1)) he (by omega) hr)
  have h5 := Rch.tr h4 (after_a e m _ (gap_seps (pre ++ [p, m])) (p ^ (e - 1)) (m ^ (e - 2)) hm)
  have hc := compare (ones m (F ::: T ::: app (seps (pre ++ [p, m]) ++ [F, F]).reverse
    (ones (e + 1) (F ::: T ::: F ::: blank)))) _ _ hr ha
  refine ⟨fun h => HaltAt.back h5 (hc.1 h), fun h => Rch.tr h5 ?_⟩
  refine Rch.tr (hc.2 h) ?_
  unfold MSE
  rw [lft_eq, cons_blank]; fin

end TM.Firoozbakht
