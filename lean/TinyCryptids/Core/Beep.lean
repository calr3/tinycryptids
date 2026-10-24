import TinyCryptids.Core.Basic

/-!
# Beeping machines and quasihalting

A *beeping* Turing machine has one designated transition, the beep: state `qb` reading
`bb`. The machine *quasihalts* if it takes the beep transition only finitely often (it may
run forever). This is the halting notion of the Beeping Busy Beaver function `BBB`: a
machine whose last beep can be bounded by a simple statement. A machine that beeps once
per solution of a problem quasihalts iff the problem has finitely many solutions, a Π₂
statement such as the negation of the twin prime conjecture.

* `BeepsAt δ qb bb c n`: step `n + 1` of the run from `c` is the beep transition.
* `QuasiHalts δ qb bb c`: from some step on, it never is.
* A sub-machine `δ'` of `δ` (`δ'` defined only where `δ` is, and agreeing there) runs as
  `δ` does (`run_sub`). With `δ'` = `δ` without its beep, "`δ'` does not halt" means "`δ`
  does not beep" (`quasihalts_of_sub`).
* `quasihalts_iff_of_sim`: quasihalting carries over to a machine that simulates the
  original (a merged machine), provided the original never halts and the simulator's beep
  state plays the beep state only on the beep symbol.
-/

namespace TM

variable {Q : Type}

/-- Step `n + 1` of the run from `c` is the beep transition: after `n` steps the machine is
in state `qb` reading `bb`, and that transition exists. -/
def BeepsAt (δ : Q → Bool → Option (Bool × Dir × Q)) (qb : Q) (bb : Bool) (c : Cfg Q)
    (n : Nat) : Prop :=
  ∃ c', run δ n c = some c' ∧ c'.q = qb ∧ c'.R 0 = bb ∧ δ qb bb ≠ none

/-- The machine quasihalts: it takes the beep transition only finitely often. -/
def QuasiHalts (δ : Q → Bool → Option (Bool × Dir × Q)) (qb : Q) (bb : Bool) (c : Cfg Q) :
    Prop :=
  ∃ N, ∀ n, N ≤ n → ¬ BeepsAt δ qb bb c n

theorem not_quasiHalts {δ : Q → Bool → Option (Bool × Dir × Q)} {qb : Q} {bb : Bool}
    {c : Cfg Q} (h : ∀ N, ∃ n, N ≤ n ∧ BeepsAt δ qb bb c n) : ¬ QuasiHalts δ qb bb c :=
  fun ⟨N, hN⟩ => let ⟨n, h1, h2⟩ := h N; hN n h1 h2

theorem run_some_of_not_halts {δ : Q → Bool → Option (Bool × Dir × Q)} {c : Cfg Q}
    (h : ¬ Halts δ c) (n : Nat) : ∃ c', run δ n c = some c' := by
  cases hr : run δ n c with
  | none => exact absurd ⟨n, hr⟩ h
  | some c' => exact ⟨c', rfl⟩

/-! ## sub-machines -/

section sub
variable {δ δ' : Q → Bool → Option (Bool × Dir × Q)}
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
theorem not_at_of_not_halts {δ' : Q → Bool → Option (Bool × Dir × Q)} {qb : Q} {bb : Bool}
    (hnone : δ' qb bb = none) {c : Cfg Q} (h : ¬ Halts δ' c) {n : Nat} {c' : Cfg Q}
    (hr : run δ' n c = some c') : ¬ (c'.q = qb ∧ c'.R 0 = bb) := by
  rintro ⟨hq, hb⟩
  have hs : step δ' c' = none := by simp [step, hq, hb, hnone]
  apply h; refine ⟨n + 1, ?_⟩
  show run δ' (n + 1) c = none
  rw [run_add, hr]; simp [run, Sys.run, hs]

/-- If the run from `c` reaches `c0` (at step `T`), and from `c0` the machine without its beep
transition never halts, the machine quasihalts: it never beeps after step `T`. -/
theorem quasihalts_of_sub {δ δ' : Q → Bool → Option (Bool × Dir × Q)} {qb : Q} {bb : Bool}
    (hsub : ∀ q b t, δ' q b = some t → δ q b = some t) (hnone : δ' qb bb = none)
    {c c0 : Cfg Q} (hr : Reach δ c c0) (h : ¬ Halts δ' c0) : QuasiHalts δ qb bb c := by
  obtain ⟨T, hT⟩ := hr
  have hT : run δ T c = some c0 := hT
  refine ⟨T, fun n hn ⟨c', hc', hq, hb, _⟩ => ?_⟩
  obtain ⟨c'', h''⟩ := run_some_of_not_halts h (n - T)
  have h1 := run_sub hsub (n - T) c0 c'' h''
  have h2 : run δ n c = some c'' := by
    rw [show n = T + (n - T) by omega, run_add, hT]; exact h1
  rw [hc'] at h2; cases h2
  exact not_at_of_not_halts hnone h h'' ⟨hq, hb⟩

/-! ## transfer to a simulating machine -/

theorem not_halts_of_sim {Q' : Type} (δ : Q → Bool → Option (Bool × Dir × Q))
    (δ' : Q' → Bool → Option (Bool × Dir × Q')) (φ : Q → Q')
    (h : ∀ q b, Compat φ (δ q b) (δ' (φ q) b)) (s : Cfg Q) (hnh : ¬ Halts δ s) :
    ¬ Halts δ' (s.map φ) := by
  intro ⟨n, hn⟩
  have hn : run δ' n (s.map φ) = none := hn
  obtain ⟨c, hc⟩ := run_some_of_not_halts hnh n
  rw [sim_run δ δ' φ h n s c hc] at hn; exact Option.noConfusion hn

/-- The simulator beeps at step `n` iff the original does, if the original never halts and
every state that `φ` maps to the simulator's beep state is the beep state or has no
transition on the beep symbol. -/
theorem beepsAt_iff_of_sim {Q' : Type} (δ : Q → Bool → Option (Bool × Dir × Q))
    (δ' : Q' → Bool → Option (Bool × Dir × Q')) (φ : Q → Q')
    (h : ∀ q b, Compat φ (δ q b) (δ' (φ q) b)) (s : Cfg Q) (hnh : ¬ Halts δ s)
    (qb : Q) (bb : Bool) (hex : ∀ q, φ q = φ qb → q = qb ∨ δ q bb = none) (n : Nat) :
    BeepsAt δ' (φ qb) bb (s.map φ) n ↔ BeepsAt δ qb bb s n := by
  obtain ⟨c, hc⟩ := run_some_of_not_halts hnh n
  have hc' := sim_run δ δ' φ h n s c hc
  -- the original does not halt at `c`
  have hdef : δ c.q (c.R 0) ≠ none := by
    intro hnone; apply hnh; refine ⟨n + 1, ?_⟩
    show run δ (n + 1) s = none
    rw [run_add, hc]; simp [run, Sys.run, step, hnone]
  constructor
  · rintro ⟨c', h1, hq, hb, _⟩
    rw [hc'] at h1; cases h1
    simp only [Cfg.map] at hq hb
    rcases hex c.q hq with he | he
    · refine ⟨c, hc, he, hb, ?_⟩; rw [← he, ← hb]; exact hdef
    · exact absurd (by rw [hb]; exact he) hdef
  · rintro ⟨c', h1, hq, hb, hd⟩
    rw [hc] at h1; obtain rfl := Option.some.inj h1
    refine ⟨_, hc', by simp [Cfg.map, hq], hb, ?_⟩
    have := h qb bb
    cases ht : δ qb bb with
    | none => exact absurd ht hd
    | some t =>
      obtain ⟨w, d, q'⟩ := t
      rw [ht] at this; simp only [Compat] at this; rw [this]; simp

/-- Quasihalting carries over to a simulating machine (see `beepsAt_iff_of_sim`). -/
theorem quasihalts_iff_of_sim {Q' : Type} (δ : Q → Bool → Option (Bool × Dir × Q))
    (δ' : Q' → Bool → Option (Bool × Dir × Q')) (φ : Q → Q')
    (h : ∀ q b, Compat φ (δ q b) (δ' (φ q) b)) (s : Cfg Q) (hnh : ¬ Halts δ s)
    (qb : Q) (bb : Bool) (hex : ∀ q, φ q = φ qb → q = qb ∨ δ q bb = none) :
    QuasiHalts δ' (φ qb) bb (s.map φ) ↔ QuasiHalts δ qb bb s := by
  have e := beepsAt_iff_of_sim δ δ' φ h s hnh qb bb hex
  constructor
  · rintro ⟨N, hN⟩; exact ⟨N, fun n hn hb => hN n hn ((e n).2 hb)⟩
  · rintro ⟨N, hN⟩; exact ⟨N, fun n hn hb => hN n hn ((e n).1 hb)⟩

end TM
