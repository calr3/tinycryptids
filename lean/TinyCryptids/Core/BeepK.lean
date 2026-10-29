import TinyCryptids.Core.Multi

/-!
# Beeping machines with more than two symbols

`Beep.lean` for the machines of `Multi.lean` (symbols `Nat`, `0` the blank): the beep is one
transition, state `qb` reading `bb`, and the machine quasihalts if it takes it only finitely
often.

* `BeepsAt δ qb bb c n`: step `n + 1` of the run from `c` is the beep transition.
* `QuasiHalts δ qb bb c`: from some step on, it never is.
* `quasihalts_of_sub`: a sub-machine `δ'` of `δ` (`δ` without its beep) that never halts from
  a configuration the run reaches means that `δ` beeps only finitely often.
-/

namespace TMK

variable {Q : Type}

/-- Step `n + 1` of the run from `c` is the beep transition: after `n` steps the machine is
in state `qb` reading `bb`, and that transition exists. -/
def BeepsAt (δ : Q → Nat → Option (Nat × TM.Dir × Q)) (qb : Q) (bb : Nat) (c : Cfg Q)
    (n : Nat) : Prop :=
  ∃ c', run δ n c = some c' ∧ c'.q = qb ∧ c'.R 0 = bb ∧ δ qb bb ≠ none

/-- The machine quasihalts: it takes the beep transition only finitely often. -/
def QuasiHalts (δ : Q → Nat → Option (Nat × TM.Dir × Q)) (qb : Q) (bb : Nat) (c : Cfg Q) :
    Prop :=
  ∃ N, ∀ n, N ≤ n → ¬ BeepsAt δ qb bb c n

theorem run_some_of_not_halts {δ : Q → Nat → Option (Nat × TM.Dir × Q)} {c : Cfg Q}
    (h : ¬ Halts δ c) (n : Nat) : ∃ c', run δ n c = some c' := by
  cases hr : run δ n c with
  | none => exact absurd ⟨n, hr⟩ h
  | some c' => exact ⟨c', rfl⟩

section sub
variable {δ δ' : Q → Nat → Option (Nat × TM.Dir × Q)}
  (hsub : ∀ q b t, δ' q b = some t → δ q b = some t)
include hsub

theorem step_sub {c c' : Cfg Q} (h : step δ' c = some c') : step δ c = some c' := by
  unfold step at h ⊢
  cases ht : δ' c.q (c.R 0) with
  | none => rw [ht] at h; exact absurd h (by simp)
  | some t => rw [hsub _ _ _ ht]; rw [ht] at h; exact h

theorem run_sub : ∀ n (c c' : Cfg Q), run δ' n c = some c' → run δ n c = some c' := by
  intro n
  induction n with
  | zero => intro c c' h; exact h
  | succ n ih =>
    intro c c' h
    simp only [run, Sys.run] at h ⊢
    cases hs : step δ' c with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some c1 => rw [step_sub hsub hs]; rw [hs] at h; exact ih c1 c' h

theorem Reach.sub {a b : Cfg Q} (h : Reach δ' a b) : Reach δ a b :=
  let ⟨n, hn⟩ := h; ⟨n, run_sub hsub n a b hn⟩

theorem Reach1.sub {a b : Cfg Q} (h : Reach1 δ' a b) : Reach1 δ a b :=
  let ⟨n, hn⟩ := h; ⟨n, run_sub hsub (n + 1) a b hn⟩

end sub

/-- A machine without a defined `(qb, bb)` transition that never halts is never in state
`qb` reading `bb`. -/
theorem not_at_of_not_halts {δ' : Q → Nat → Option (Nat × TM.Dir × Q)} {qb : Q} {bb : Nat}
    (hnone : δ' qb bb = none) {c : Cfg Q} (h : ¬ Halts δ' c) {n : Nat} {c' : Cfg Q}
    (hr : run δ' n c = some c') : ¬ (c'.q = qb ∧ c'.R 0 = bb) := by
  rintro ⟨hq, hb⟩
  have hs : step δ' c' = none := by simp [step, hq, hb, hnone]
  apply h; refine ⟨n + 1, ?_⟩
  show Sys.run (step δ') (n + 1) c = none
  rw [Sys.run_add, show Sys.run (step δ') n c = some c' from hr]
  simp [Sys.run, hs]

/-- If the run from `c` reaches `c0` (at step `T`), and from `c0` the machine without its beep
transition never halts, the machine quasihalts: it never beeps after step `T`. -/
theorem quasihalts_of_sub {δ δ' : Q → Nat → Option (Nat × TM.Dir × Q)} {qb : Q} {bb : Nat}
    (hsub : ∀ q b t, δ' q b = some t → δ q b = some t) (hnone : δ' qb bb = none)
    {c c0 : Cfg Q} (hr : Reach δ c c0) (h : ¬ Halts δ' c0) : QuasiHalts δ qb bb c := by
  obtain ⟨T, hT⟩ := hr
  have hT : run δ T c = some c0 := hT
  refine ⟨T, fun n hn ⟨c', hc', hq, hb, _⟩ => ?_⟩
  obtain ⟨c'', h''⟩ := run_some_of_not_halts h (n - T)
  have h1 := run_sub hsub (n - T) c0 c'' h''
  have h2 : run δ n c = some c'' := by
    show Sys.run (step δ) n c = some c''
    rw [show n = T + (n - T) by omega, Sys.run_add, show Sys.run (step δ) T c = some c0 from hT]
    exact h1
  rw [hc'] at h2; cases h2
  exact not_at_of_not_halts hnone h h'' ⟨hq, hb⟩

end TMK
