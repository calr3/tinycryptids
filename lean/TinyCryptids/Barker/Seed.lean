import TinyCryptids.Barker.Round
import TinyCryptids.Barker.Enum

/-!
# The seed: a 4-bit counter writes the first candidate `1 0^13`

Left of the dummy: the counter, one position `[0 b]` per bit (least significant next to the
dummy), then a sentinel `[1 1]`. The run starts at `4`; each round appends a `0` to the
candidate (by unmarking `j`: the blank position after the last is a marked `0`) and adds 1 to the
counter. When the counter overflows, the sentinel is erased and the pass for shift 1 starts.
-/

namespace TM.Barker
open St

local notation "F" => false
local notation "T" => true

theorem sRb {q q' : St} {L : Strm} {w : Bool} (h : delta q F = some (w, Dir.R, q')) :
    Rch ⟨q, L, blank⟩ ⟨q', w ::: L, blank⟩ := stepR (δ := delta) (R := blank) h

macro "gRb" : tactic => `(tactic| refine Rch.tr (sRb (by rfl)) ?_)

/-- the counter as the cells left of the dummy: bits least significant first, then the sentinel -/
def Ctr : List Bool → Strm
  | [] => blank
  | b :: bs => b ::: bs.isEmpty ::: Ctr bs

theorem Ctr_cc (b : Bool) (bs : List Bool) (h : bs ≠ []) : Ctr (b :: bs) = b ::: F ::: Ctr bs := by
  cases bs with
  | nil => exact absurd rfl h
  | cons c bs => rfl

/-- the loop: `PRp` on the marked blank position after the candidate `1 0^m` -/
def Lc (bs : List Bool) (m : Nat) : Cfg St :=
  ⟨PRp, UL (F :: T :: List.replicate m F) (Ctr bs), blank⟩

theorem init : Rch start (Lc [F, F, T, F] 0) := by
  unfold start; iterate 12 gRb
  fin

theorem ccarry (rest : List Bool) (hr : rest ≠ []) : ∀ (r : Nat) (R : Strm),
    Rch (cfgL Ca (Ctr (List.replicate r T ++ rest)) R) (cfgL Ca (Ctr rest) (zeros (2 * r) R)) := by
  intro r
  induction r with
  | zero => intro R; fin
  | succ r ih =>
    intro R
    rw [show List.replicate (r + 1) T ++ rest = T :: (List.replicate r T ++ rest) from rfl,
      Ctr_cc _ _ (by cases r <;> simp [hr])]
    gL; gL
    refine Rch.tr (ih _) ?_
    rw [show 2 * (r + 1) = 2 * r + 2 by omega, ← zeros_add]; fin

theorem incR_rep (rest : List Bool) : ∀ r, incR (List.replicate r T ++ F :: rest) =
    List.replicate r F ++ T :: rest
  | 0 => rfl
  | r + 1 => by
    show F :: incR (List.replicate r T ++ F :: rest) = _
    rw [incR_rep rest r]; rfl

theorem Ctr_rep (x : List Bool) (hx : x ≠ []) : ∀ r, Ctr (List.replicate r F ++ x) = zeros (2 * r) (Ctr x)
  | 0 => rfl
  | r + 1 => by
    rw [show List.replicate (r + 1) F ++ x = F :: (List.replicate r F ++ x) from rfl,
      Ctr_cc _ _ (by cases r <;> simp [hx])]
    rw [Ctr_rep x hx r, show 2 * (r + 1) = 2 + 2 * r by omega, ← zeros_add]; rfl

theorem scanR0' {q : St} (h : delta q F = some (F, Dir.R, q)) (n : Nat) (L R : Strm) :
    Rch ⟨q, L, zeros n R⟩ ⟨q, zeros n L, R⟩ := scanR0 h n L R

theorem pl_ca (b : Bool) (bs : List Bool) (h : bs ≠ []) (R : Strm) :
    Rch (cfgL PLa (Ctr (b :: bs)) R) (cfgL Ca (Ctr (b :: bs)) R) := by
  rw [Ctr_cc _ _ h]
  cases b
  all_goals gL; gR; fin

/-- one round: append a `0`, add 1 to the counter (no overflow) -/
theorem lc_step (r : Nat) (rest : List Bool) (hrest : r ≠ 0 ∨ rest ≠ []) (m : Nat) :
    Rch (Lc (List.replicate r T ++ F :: rest) m) (Lc (List.replicate r F ++ T :: rest) (m + 1)) := by
  unfold Lc
  refine Rch.tr (sLb (by rfl)) ?_
  refine Rch.tr (keyL (fun b => by cases b <;> rfl) (by rfl) _ _ _) ?_
  refine Rch.tr (b := cfgL Ca (Ctr (List.replicate r T ++ F :: rest))
    (app (U (F :: T :: List.replicate m F)) (T ::: blank))) ?_ ?_
  · cases r with
    | zero => exact pl_ca F rest (hrest.resolve_left (by simp)) _
    | succ r => exact pl_ca T _ (by simp) _
  refine Rch.tr (ccarry _ (by simp) r _) ?_
  show Rch (cfgL Ca (F ::: rest.isEmpty ::: Ctr rest) _) _
  gR
  refine Rch.tr (scanR0' (by rfl) _ _ _) ?_
  rw [appU_cons]
  gR; gR
  rw [show (T ::: blank : Strm) = app (U [F]) blank by simp [cons_blank], ← appU_append]
  refine Rch.tr (keyR (by rfl) (fun b => by cases b <;> rfl) _ _ _) ?_
  rw [Ctr_rep _ (by simp), rep_succ', UL_cons F]
  fin

theorem lc_over (m : Nat) :
    Rch (Lc [T, T, T, T] m) (P (F :: T :: List.replicate m F) F [] F [] 0) := by
  unfold Lc
  refine Rch.tr (sLb (by rfl)) ?_
  refine Rch.tr (keyL (fun b => by cases b <;> rfl) (by rfl) _ _ _) ?_
  refine Rch.tr (pl_ca T _ (by simp) _) ?_
  refine Rch.tr (ccarry [T] (by simp) 3 _) ?_
  show Rch (cfgL Ca (T ::: T ::: blank) _) _
  gL; gR
  refine Rch.tr (scanR0' (by rfl) (6 + 1) _ _) ?_
  rw [appU_cons]
  gR; gR
  rw [show (T ::: blank : Strm) = app (U [F]) (F ::: F ::: blank) by simp [cons_blank], ← appU_append]
  refine Rch.tr (keyR (by rfl) (fun b => by cases b <;> rfl) _ _ _) ?_
  refine Rch.tr ?_ (finish _ F F)
  rw [show F :: T :: List.replicate m F ++ [F] = F :: (T :: List.replicate m F ++ [F]) from rfl, UL_cons]
  simp only [U_cons, U_nil, app_cons, app_nil, tl_cons, cons_blank, zeros_blank]
  fin

/-- the first candidate: `1` and thirteen `0`s -/
def a0 : List Bool := T :: List.replicate 13 F

theorem seed : ∃ c, Start (F :: a0) 1 c ∧ Rch start c := by
  refine ⟨P (F :: T :: List.replicate 11 F) F [] F [] 0, ⟨_, _, _, _, rfl, rfl, rfl⟩, ?_⟩
  refine Rch.tr init ?_
  refine Rch.tr (lc_step 0 [F, T, F] (Or.inr (by simp)) 0) ?_
  refine Rch.tr (lc_step 1 [T, F] (Or.inr (by simp)) 1) ?_
  refine Rch.tr (lc_step 0 [T, T, F] (Or.inr (by simp)) 2) ?_
  refine Rch.tr (lc_step 3 [] (Or.inl (by decide)) 3) ?_
  refine Rch.tr (lc_step 0 [F, F, T] (Or.inr (by simp)) 4) ?_
  refine Rch.tr (lc_step 1 [F, T] (Or.inr (by simp)) 5) ?_
  refine Rch.tr (lc_step 0 [T, F, T] (Or.inr (by simp)) 6) ?_
  refine Rch.tr (lc_step 2 [T] (Or.inr (by simp)) 7) ?_
  refine Rch.tr (lc_step 0 [F, T, T] (Or.inr (by simp)) 8) ?_
  refine Rch.tr (lc_step 1 [T, T] (Or.inr (by simp)) 9) ?_
  refine Rch.tr (lc_step 0 [T, T, T] (Or.inr (by simp)) 10) ?_
  exact lc_over 11

end TM.Barker
