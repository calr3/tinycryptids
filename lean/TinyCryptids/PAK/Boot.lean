import TinyCryptids.PAK.Machine

/-!
# The boot and the first register operations, by computation

The machine starts on a blank tape; its boot (`bA`, `bB`, `bC`) writes the gap of 12 ones and
enters `scan`; main's first operations then create the registers one by one (the file grows on
the blank after it, `chain_new`), which the simulation of `Frame.lean` does not cover (it keeps
nine or ten registers).  So the first 853 steps are run here as a computation on finite tapes
(`LCfg`, `lrun`, checked by `rfl`): they end in the second chunk of main (node 17) at its slot
5, with nine registers, all zero but `nextproof` (1).
-/

namespace TMK.PA

open TM (Dir)

/-- a configuration with finite tape sides (blank beyond them) -/
structure LCfg where
  q : St
  L : List Nat
  R : List Nat
  deriving DecidableEq

def LCfg.toCfg (c : LCfg) : Cfg St := ⟨c.q, lst c.L blank, lst c.R blank⟩

def lstep (c : LCfg) : Option LCfg :=
  match delta c.q (c.R.headD 0) with
  | none => none
  | some (w, .R, q') => some ⟨q', w :: c.L, c.R.tail⟩
  | some (w, .L, q') => some ⟨q', c.L.tail, c.L.headD 0 :: w :: c.R.tail⟩

def lrun : Nat → LCfg → Option LCfg
  | 0, c => some c
  | n + 1, c => match lstep c with
    | none => none
    | some c' => lrun n c'

theorem lst_head (l : List Nat) : lst l blank 0 = l.headD 0 := by
  cases l <;> rfl

theorem lst_tail (l : List Nat) : tl (lst l blank) = lst l.tail blank := by
  cases l <;> rfl

theorem lstep_ok {c c' : LCfg} (h : lstep c = some c') : step delta c.toCfg = some c'.toCfg := by
  unfold lstep at h
  unfold step LCfg.toCfg
  simp only [lst_head]
  revert h
  cases delta c.q (c.R.headD 0) with
  | none => intro h; cases h
  | some t =>
    obtain ⟨w, d, q'⟩ := t
    cases d with
    | R => intro h; cases h; simp [lst_tail]
    | L => intro h; cases h; simp [lst_tail, lst_head]

theorem lrun_ok : ∀ (n : Nat) (c c' : LCfg), lrun n c = some c' → Reach delta c.toCfg c'.toCfg := by
  intro n
  induction n with
  | zero => intro c c' h; cases h; exact Reach.refl _ _
  | succ n ih =>
    intro c c' h
    unfold lrun at h
    cases hs : lstep c with
    | none => rw [hs] at h; cases h
    | some c1 =>
      rw [hs] at h
      exact Reach.trans _ (reach_step _ (lstep_ok hs)) (ih c1 c' h)

/-- after 853 steps: node 17 at value 5 (main at value 1 left of it), the gap, nine registers -/
def bootEnd : LCfg :=
  ⟨.node 17, [2, 0], [6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 9, 1, 9, 9, 9, 9, 9, 9, 9, 0]⟩

set_option maxRecDepth 200000 in
theorem boot_run : lrun 853 ⟨.bA, [], []⟩ = some bootEnd := by decide

theorem boot_reach : Reach delta start bootEnd.toCfg := by
  have := lrun_ok 853 _ _ boot_run
  exact this

end TMK.PA
