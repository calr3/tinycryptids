import TinyCryptids.AgohGiuga.Horner
import TinyCryptids.AgohGiuga.Spec

/-!
# `B += R - 1`: R's last cell is erased and S's hole advances, until `R = 101`

Tape right of the base block: the gap `gB`, `S = skq p q` (hole at cell `p`, `p + q = n + 1`),
`00`, `R = 1 0 1^r`, blank.  `CL Lx p q r`: state `r1` on R's cell 3 (`Lx` is the tape left
of S's separator cell).
-/

namespace TM.AgohGiuga
open St

local notation "F" => false
local notation "T" => true

theorem PPD : ParserR delta PD1 PD2 := ⟨rfl, rfl, rfl⟩
theorem PPE : ParserR delta PE1 PE2 := ⟨rfl, rfl, rfl⟩
theorem PPC : ParserR delta PC1 PC2 := ⟨rfl, rfl, rfl⟩
theorem PPN : ParserL1 PN1 PN2 := ⟨rfl, rfl⟩
theorem PPO : ParserL delta PO1 PO2 := ⟨rfl, rfl, rfl⟩
theorem PPK : ParserL delta PK1 PK2 := ⟨rfl, rfl, rfl⟩

def CL (Lx : Strm) (p q r : Nat) : Cfg St :=
  ⟨r1, T ::: F ::: T ::: F ::: F ::: app (skq p q).reverse (F ::: Lx), ones (r - 1) blank⟩

theorem skq_rev (p q : Nat) (X : Strm) :
    app (skq p q).reverse X = ones q (F ::: ones p X) := by
  simp only [skq, List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc,
    List.singleton_append, app_append, app_replicate, app_cons]

/-- S's hole advances: from the PO parser's landing (S's cell `p - 1`) to `PC1` -/
theorem s_adv (Lx Y : Strm) (p q : Nat) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Rch ⟨ca1, ones p (F ::: Lx), F ::: ones q (F ::: F ::: Y)⟩
      ⟨PC1, F ::: ones (nx (p + q - 1) p) (F ::: Lx),
        ones (p + q - nx (p + q - 1) p) (F ::: F ::: Y)⟩ := by
  unfold nx
  by_cases hq2 : 2 ≤ q
  · rw [if_pos (by omega)]
    obtain ⟨c, rfl⟩ : ∃ c, q = c + 2 := ⟨q - 2, by omega⟩
    rw [show p + (c + 2) - (p + 1) = c + 1 by omega]
    gR; gR; gL; gR
    fin
  · obtain rfl : q = 1 := by omega
    rw [if_neg (by omega), show p + 1 - 1 = p by omega]
    gR; gR; gL
    sLn (p + 2)
    gR; gR; gR
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [ones_succ']
    fin

theorem nx_range {c i : Nat} (h1 : 1 ≤ i) (h2 : i ≤ c) : 1 ≤ nx c i ∧ nx c i ≤ c := by
  unfold nx; split <;> omega

/-- one cell of R erased, S's hole one step on -/
theorem cons_step (Lx : Strm) (p q r : Nat) (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 2 ≤ r) :
    Rch (CL Lx p q r) (CL Lx (nx (p + q - 1) p) (p + q - nx (p + q - 1) p) (r - 1)) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  unfold CL
  rw [show r' + 2 - 1 = r' + 1 by omega]
  sRn (r' + 1)
  refine blankR ?_
  gL; gL; rw [ones_cons_true]; gR; gL
  show Rch (cfgL PN1 (T ::: ones r'
    (F ::: T ::: F ::: F ::: app (skq (p' + 1) (q' + 1)).reverse (F ::: Lx))) (F ::: F ::: blank)) _
  rw [← ones_succ, ← app_replicate]
  refine Rch.tr (PPN.find _ _ _) ?_
  gL
  rw [skq_rev, show F ::: F ::: ones (q' + 1) (F ::: ones (p' + 1) (F ::: Lx)) =
    app (F :: F :: List.replicate (q' + 1) true) (F ::: T ::: ones p' (F ::: Lx)) by
      simp only [app_cons, app_replicate, ones_succ]]
  refine Rch.tr (PPO.find (by rw [List.replicate_succ]; exact Clean.sep (Clean.replicate q')) _ _) ?_
  gR
  simp only [List.reverse_cons, List.reverse_replicate, List.reverse_nil, List.nil_append,
    List.singleton_append, List.cons_append, List.append_assoc, app_append, app_replicate, app_cons,
    app_nil, tl_cons]
  rw [← ones_succ]
  refine Rch.tr (s_adv Lx _ (p' + 1) (q' + 1) (by omega) (by omega)) ?_
  generalize hx : nx (p' + 1 + (q' + 1) - 1) (p' + 1) = x
  rw [show ones (p' + 1 + (q' + 1) - x) (F ::: F ::: T ::: F ::: ones (r' + 1) (F ::: F ::: blank)) =
    app (List.replicate (p' + 1 + (q' + 1) - x) true ++ [F, F, T]) (F ::: T ::: ones r' (F ::: F ::: blank))
    by simp only [app_append, app_replicate, app_cons, app_nil, ones_succ]]
  refine Rch.tr (PPC.find (Clean.rep_append _ (Clean.sep Clean.nil)) _ _) ?_
  gR
  simp only [cons_blank, skq_rev, List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append, app_append,
    app_replicate, app_cons, app_nil, Nat.add_sub_cancel]
  fin

theorem cons_loop (Lx : Strm) : ∀ r p q, 1 ≤ r → 1 ≤ p → 1 ≤ q →
    Rch (CL Lx p q r) (CL Lx (nxs (p + q - 1) p (r - 1)) (p + q - nxs (p + q - 1) p (r - 1)) 1)
  | 0, _, _, h, _, _ => absurd h (by omega)
  | 1, p, q, _, _, _ => by
    show Rch _ (CL Lx p (p + q - p) 1)
    rw [show p + q - p = q by omega]; fin
  | r + 2, p, q, _, hp, hq => by
    have hx := nx_range (c := p + q - 1) (i := p) hp (by omega)
    refine Rch.tr (cons_step Lx p q (r + 2) hp hq (by omega)) ?_
    have ih := cons_loop Lx (r + 1) (nx (p + q - 1) p) (p + q - nx (p + q - 1) p) (by omega) hx.1
      (by omega)
    rw [show nx (p + q - 1) p + (p + q - nx (p + q - 1) p) = p + q by omega,
      show r + 1 - 1 = r by omega] at ih
    rw [show r + 2 - 1 = r + 1 by omega]
    exact ih

/-- from the end of the Horner run (head on N's cell 2) to R's cell 3 -/
theorem cons_entry {gB : List Bool} (hg : Gap gB) (n i p q r : Nat) (Le : Strm)
    (hi : 1 ≤ i) (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) :
    Rch ⟨PD1, F ::: T ::: F ::: Le, ones n (app [F, F] (app (bH1 i) (rgt gB p q r 0)))⟩
      ⟨r1, T ::: F ::: T ::: F ::: F ::: app (skq p q).reverse (app gB.reverse
        (ones i (F ::: T ::: F ::: F ::: ones n (F ::: T ::: F ::: Le)))), ones (r - 1) blank⟩ := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [show ones n (app [F, F] (app (bH1 (i' + 1)) (rgt gB (p' + 1) (q' + 1) (r' + 1) 0))) =
    app (List.replicate n true ++ [F, F, T]) (F ::: T ::: ones i' (rgt gB (p' + 1) (q' + 1) (r' + 1) 0))
    by simp only [bH1, app_append, app_replicate, app_cons, app_nil, ones_succ]]
  refine Rch.tr (PPD.find (Clean.rep_append _ (Clean.sep Clean.nil)) _ _) ?_
  gR
  rw [show ones i' (rgt gB (p' + 1) (q' + 1) (r' + 1) 0) =
    app (List.replicate i' true ++ (gB ++ List.replicate (p' + 1) true))
      (F ::: T ::: ones q' (F ::: F ::: T ::: F ::: ones (r' + 1) (F ::: F ::: blank)))
    by simp only [rgt, skq, sep, app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero]]
  refine Rch.tr (PPE.find (Clean.rep_append _ (by
    rw [List.replicate_succ]; exact hg.clean (Clean.replicate p'))) _ _) ?_
  gR
  rw [show ones q' (F ::: F ::: T ::: F ::: ones (r' + 1) (F ::: F ::: blank)) =
    app (List.replicate q' true ++ [F, F, T]) (F ::: T ::: ones r' (F ::: F ::: blank))
    by simp only [app_append, app_replicate, app_cons, app_nil, ones_succ]]
  refine Rch.tr (PPC.find (Clean.rep_append _ (Clean.sep Clean.nil)) _ _) ?_
  gR
  simp only [cons_blank, skq_rev, bH1, List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
    app_append, app_replicate, app_cons, app_nil, Nat.add_sub_cancel, ones_succ, ones_cons_true]
  fin

/-- R = 101: to S's hole; `k1` on S's cell `p - 2` -/
theorem cons_done (Lx : Strm) (p q : Nat) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Rch (CL Lx p q 1) (cfgL k1 (ones (p - 1) (F ::: Lx))
      (T ::: F ::: ones q (F ::: F ::: T ::: F ::: T ::: blank))) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  unfold CL
  refine blankR ?_
  gL; gL; gL
  rw [skq_rev, show T ::: F ::: F ::: ones (q' + 1) (F ::: ones (p' + 1) (F ::: Lx)) =
    app (T :: F :: F :: List.replicate (q' + 1) true) (F ::: T ::: ones p' (F ::: Lx))
    by simp only [app_cons, app_replicate, ones_succ]]
  refine Rch.tr (PPK.find (Clean.one (by rw [List.replicate_succ]; exact Clean.sep (Clean.replicate q'))) _ _) ?_
  gL
  simp only [List.reverse_cons, List.reverse_replicate, List.reverse_nil, List.nil_append,
    List.singleton_append, List.cons_append, List.append_assoc, app_append, app_replicate, app_cons,
    app_nil, Nat.add_sub_cancel, cons_blank]
  fin

end TM.AgohGiuga
