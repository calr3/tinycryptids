import TinyCryptids.Pillai.NextBase
import TinyCryptids.Core.BeepBoop
namespace TM.Pillai
open St

/-! The compare: A (`x` cells) against R (`y` cells), erasing the last cell of A and the first
of R in turn. If R runs out first with `x - y ≥ 2`, the rest of A is erased with one beep
(`zX3` reading 1) for every cell but the first, `x - y - 2` beeps, and then the boop (`zX3`
reading 0). Otherwise there is no event. Either way the head stops right of M. -/

set_option maxHeartbeats 0 in
theorem deltaQ_sub : ∀ q b t, deltaQ q b = some t → delta q b = some t := by
  intro q b t h
  cases q <;> cases b <;> first | exact h | cases h

/-- runs of `deltaQ` joined by beeps and boops of `delta` -/
abbrev Tr := Trace delta deltaQ zX3 true zX3 false

theorem Tr.pre {x y z : Cfg St} {es : List Bool} (h : Rch x y) (t : Tr y es z) : Tr x es z := by
  have := (Trace.nil (δ := delta) (qb := zX3) (bb := true) (qo := zX3) (bo := false) h).append t deltaQ_sub
  simpa using this

theorem Tr.post {x y z : Cfg St} {es : List Bool} (t : Tr x es y) (h : Rch y z) : Tr x es z := by
  have := t.append (Trace.nil (δ := delta) (qb := zX3) (bb := true) (qo := zX3) (bo := false) h) deltaQ_sub
  simpa using this

theorem Tr.of {x y : Cfg St} (h : Rch x y) : Tr x [] y := Trace.nil h

/-- the zig-zag: `zH1` on a gap of `i + 1` zeros left and `j` zeros right of the head, A's `x`
cells on the left (then `LA`, which starts with a separator), R's `y` cells on the right (then
blank) -/
def Z (LA : Strm) (i j x y : Nat) : Cfg St :=
  cfgL zH1 (zeros (i + 1) (ones x LA)) (zeros j (ones y blank))

/-- after the clear: on the cell right of M (state `cr4`), blank to the right -/
def clrC (LM : Strm) : Cfg St := ⟨cr4, LM, blank⟩

theorem zz_step (LA : Strm) (i j x y : Nat) :
    Rch (Z LA i j (x + 2) (y + 2)) (Z LA (i + j + 2) 0 (x + 1) (y + 1)) := by
  unfold Z
  zLn (i + 1)
  gL; gR
  rw [show F ::: zeros (i + 1) (zeros j (ones (y + 2) blank)) = zeros (i + j + 2) (ones (y + 2) blank) by
    rw [zeros_add, show i + j + 2 = (i + 1 + j) + 1 by omega]; rfl]
  zRn (i + j + 2)
  gR; gL
  fin

theorem zeros_gap (i j y : Nat) (Y : Strm) :
    F ::: zeros (i + 1) (zeros j (ones y Y)) = zeros (i + j + 2) (ones y Y) := by
  rw [zeros_add, show i + j + 2 = (i + 1 + j) + 1 by omega]; rfl

/-- A runs out first (`x = 1`): erase the rest of R and go back to M -/
theorem zz_A (LM : Strm) (i j y : Nat) :
    Rch (Z (sep (true ::: LM)) i j 1 (y + 1)) (clrC (true ::: LM)) := by
  unfold Z sep clrC
  zLn (i + 1)
  gL; gR
  rw [zeros_gap]
  zRn (i + j + 2)
  gR
  eRn y
  refine blankR ?_
  gL
  show Rch (cfgL cr3 (zeros y (F ::: zeros (i + j + 2) (F ::: F ::: true ::: LM))) (F ::: blank)) _
  rw [show zeros y (F ::: zeros (i + j + 2) (F ::: F ::: true ::: LM)) =
      zeros (y + 1 + (i + j + 2) + 2) (true ::: LM) by
    rw [← zeros_succ', zeros_add, show y + 1 + (i + j + 2) + 2 = (y + 1 + (i + j + 2)) + 1 + 1 by omega,
      zeros_succ', zeros_succ']]
  zLn (y + 1 + (i + j + 2) + 2)
  gR
  simp only [zeros_cons_false, zeros_blank, cons_blank]
  fin

/-- the beep loop: `zX3` erases `n` cells moving left, beeping on each -/
theorem beeps (n : Nat) : ∀ (S R : Strm),
    Tr (cfgL zX3 (ones n S) R) (List.replicate n true) (cfgL zX3 S (zeros n R)) := by
  induction n with
  | zero => intro S R; exact Tr.of (Reach.refl deltaQ _)
  | succ n ih =>
    intro S R
    refine Trace.beep (Reach.refl deltaQ _) rfl rfl
      (show step delta (cfgL zX3 (ones (n + 1) S) R) = some (cfgL zX3 (ones n S) (F ::: R)) from rfl) ?_
    rw [zeros_succ']; exact ih S (F ::: R)

/-- R runs out first (`y = 1`): one more cell of A is erased. If A is then empty there is no
event; else the next cell is erased and each further one with a beep, then the boop -/
theorem zz_R (LM : Strm) (i j x : Nat) :
    (x = 0 → Rch (Z (sep (true ::: LM)) i j (x + 2) 1) (clrC (true ::: LM))) ∧
    (∀ x', x = x' + 1 → Tr (Z (sep (true ::: LM)) i j (x + 2) 1) (List.replicate x' true ++ [false])
      (clrC (true ::: LM))) := by
  have h0 : Rch (Z (sep (true ::: LM)) i j (x + 2) 1)
      (cfgL zX2 (ones x (F ::: F ::: true ::: LM)) (F ::: zeros (i + j + 3) blank)) := by
    unfold Z sep
    zLn (i + 1)
    gL; gR
    rw [zeros_gap]
    zRn (i + j + 2)
    gR
    refine blankR ?_
    gL
    show Rch (cfgL zX1 (zeros (i + j + 3) (true ::: ones x (F ::: F ::: true ::: LM))) (F ::: blank)) _
    zLn (i + j + 3)
    gL
    simp only [zeros_cons_false, zeros_blank, cons_blank]
    fin
  refine ⟨fun hx => ?_, fun x' hx => ?_⟩
  · subst hx
    refine Rch.tr h0 ?_
    unfold clrC
    gL; gL; gR
    simp only [zeros_cons_false, zeros_blank, cons_blank]
    fin
  · subst hx
    refine Tr.pre h0 ?_
    refine Tr.pre (show Rch _ (cfgL zX3 (ones x' (F ::: F ::: true ::: LM)) (F ::: F ::: zeros (i + j + 3) blank))
      by gL; fin) ?_
    refine (beeps x' _ _).append ?_ deltaQ_sub
    refine Trace.boop (Reach.refl deltaQ _) rfl rfl
      (show step delta (cfgL zX3 (F ::: F ::: true ::: LM) (zeros x' (F ::: F ::: zeros (i + j + 3) blank))) =
        some (cfgL cr3 (F ::: true ::: LM) (F ::: zeros x' (F ::: F ::: zeros (i + j + 3) blank))) from rfl) ?_
    refine Tr.of ?_
    unfold clrC
    gL; gR
    simp only [zeros_cons_false, zeros_blank, cons_blank]
    fin

open Classical in
/-- the events of a compare of A (`x` cells) with R (`y` cells) -/
noncomputable def zev (x y : Nat) : List Bool :=
  if y + 2 ≤ x then List.replicate (x - y - 2) true ++ [false] else []

/-- the whole compare -/
theorem zz (LM : Strm) : ∀ x y i j, 1 ≤ x → 1 ≤ y →
    Tr (Z (sep (true ::: LM)) i j x y) (zev x y) (clrC (true ::: LM)) := by
  intro x
  induction x with
  | zero => intro y i j h; omega
  | succ x ih =>
    intro y i j _ hy
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    rcases x with _ | x
    · have : zev 1 (y' + 1) = [] := by unfold zev; rw [if_neg (by omega)]
      rw [this]; exact Tr.of (zz_A LM i j y')
    rcases y' with _ | y'
    · have := zz_R LM i j x
      rcases x with _ | x'
      · have e : zev 2 1 = [] := by unfold zev; rw [if_neg (by omega)]
        rw [e]; exact Tr.of (this.1 rfl)
      · have e : zev (x' + 1 + 1 + 1) (0 + 1) = List.replicate x' true ++ [false] := by
          unfold zev; rw [if_pos (by omega)]; congr 2
        rw [e]; exact this.2 x' rfl
    have st := zz_step (sep (true ::: LM)) i j x y'
    have := ih (y' + 1) (i + j + 2) 0 (by omega) (by omega)
    have e : zev (x + 1 + 1) (y' + 1 + 1) = zev (x + 1) (y' + 1) := by
      unfold zev
      by_cases h : y' + 1 + 2 ≤ x + 1
      · rw [if_pos (by omega), if_pos h]; congr 2; omega
      · rw [if_neg (by omega), if_neg h]
    rw [e]; exact Tr.pre st this

theorem PCP : ParserR deltaQ CP1 CP2 := ⟨rfl, rfl, rfl⟩

/-- after the power of the last base: the next block is M, so to R; the zig-zag starts on the
single 0 between A and R -/
theorem compare_entry (pre : List Bool) (k β α r : Nat) (W : Strm) (hr : 1 ≤ r) :
    Rch (nbC pre k β (true :: F :: F :: rep α) r W)
      (Z (sep (true ::: F ::: F ::: ones (β + 2) (leftOf pre k 1 W))) 0 0 α r) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  unfold nbC rgt
  gR; sRn β
  simp only [sep, app_cons, app_nil, app_replicate]
  gR; gR; gR; gR; gR
  have e : ones α (F ::: ones (r' + 1) (F ::: ones 0 blank)) =
      app (rep α) (F ::: true ::: ones r' blank) := by
    simp [app_replicate, ones_succ, cons_blank]
  rw [e]
  refine Rch.tr (PCP.find (Clean.replicate α) _ _) ?_
  gL
  unfold Z
  simp [sep, List.reverse_replicate, app_replicate, zeros, ones_succ, ones_cons_true, cons_blank]
  fin

end TM.Pillai
