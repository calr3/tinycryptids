import TinyCryptids.Core.Beep

/-!
# Beeping booping machines

Bram Cohen's *Beeping Booping Busy Beavers*: a machine that never halts, with two designated
transitions, the beep (`qb` reading `bb`) and the boop (`qo` reading `bo`).  Its output is
the sequence of beep counts between consecutive boops; the machine has a "number" when some
value of that sequence occurs infinitely often (Cohen: "find the first output value which is
later repeated an infinite number of times").  This is a Σ₃ property, one level above
quasihalting (`Core/Beep.lean`).

* `beepsBetween δ qb bb c i j`: the number of beep steps among steps `i + 1, …, j - 1`.
* `RepeatsForever δ qb bb qo bo c`: some value `v` is, infinitely often, the number of beeps
  between two consecutive boops.
* `repeatsForever_of_segments`: a run cut into segments, each of which either has no beep
  or boop or has `v` beeps followed by one boop, repeats a value forever iff infinitely many
  segments boop with the same `v`.
* `Trace`: runs of a sub-machine without the two special transitions (no events) joined by
  single beep or boop steps; `Trace.evs` gives the events of such a run.
* `repeatsForever_iff_of_sim`: the property carries over to a machine that simulates the
  original (a merged machine).
-/

namespace TM

variable {Q : Type}

/-- induction on `n ≥ m` (as Mathlib's `Nat.le_induction`) -/
@[elab_as_elim] theorem Nat.le_induction {m : Nat} {P : ∀ n, m ≤ n → Prop}
    (base : P m (Nat.le_refl m)) (succ : ∀ n hmn, P n hmn → P (n + 1) (Nat.le_succ_of_le hmn)) :
    ∀ n hmn, P n hmn := by
  intro n hmn
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  induction d with
  | zero => exact base
  | succ d ih => exact succ (m + d) (by omega) (ih (by omega))

open Classical in
/-- The number of beep steps among steps `i + 1, …, j - 1` of the run from `c`. -/
noncomputable def beepsBetween (δ : Q → Bool → Option (Bool × Dir × Q)) (qb : Q) (bb : Bool)
    (c : Cfg Q) (i j : Nat) : Nat :=
  ((List.range (j - (i + 1))).filter (fun k => decide (BeepsAt δ qb bb c (i + 1 + k)))).length

/-- Some value occurs infinitely often as the number of beeps between two consecutive boops:
for every `N` there are boop steps `N ≤ i < j` with no boop strictly between them and exactly
`v` beeps strictly between them. -/
def RepeatsForever (δ : Q → Bool → Option (Bool × Dir × Q)) (qb : Q) (bb : Bool) (qo : Q)
    (bo : Bool) (c : Cfg Q) : Prop :=
  ∃ v, ∀ N, ∃ i j, N ≤ i ∧ i < j ∧ BeepsAt δ qo bo c i ∧ BeepsAt δ qo bo c j ∧
    (∀ k, i < k → k < j → ¬ BeepsAt δ qo bo c k) ∧ beepsBetween δ qb bb c i j = v

/-! ## event lists -/

section events
variable (beep boop : Nat → Prop)

open Classical in
/-- the event at step `n`: `some true` a beep, `some false` a boop -/
noncomputable def evAt (n : Nat) : Option Bool :=
  if beep n then some true else if boop n then some false else none

/-- the events at steps `a, …, b - 1` -/
noncomputable def evs (a b : Nat) : List Bool :=
  (List.range (b - a)).filterMap (fun k => evAt beep boop (a + k))

variable {beep boop}

theorem evs_self (a : Nat) : evs beep boop a a = [] := by simp [evs]

theorem evs_succ {a b : Nat} (h : a ≤ b) :
    evs beep boop a (b + 1) = evs beep boop a b ++ (evAt beep boop b).toList := by
  unfold evs
  rw [show b + 1 - a = (b - a) + 1 by omega, List.range_succ, List.filterMap_append]
  congr 1
  simp only [List.filterMap_cons, List.filterMap_nil, show a + (b - a) = b by omega]
  cases evAt beep boop b <;> rfl

theorem evs_append {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) :
    evs beep boop a c = evs beep boop a b ++ evs beep boop b c := by
  induction c, h2 using Nat.le_induction with
  | base => rw [evs_self, List.append_nil]
  | succ c hbc ih => rw [evs_succ (by omega), evs_succ hbc, ih, List.append_assoc]

theorem evs_nil_iff {a b : Nat} :
    evs beep boop a b = [] ↔ ∀ n, a ≤ n → n < b → evAt beep boop n = none := by
  constructor
  · intro h n h1 h2
    have := evs_append (beep := beep) (boop := boop) h1 (Nat.le_of_lt h2)
    rw [evs_append (beep := beep) (boop := boop) (Nat.le_succ n) h2, evs_succ (Nat.le_refl n),
      evs_self, h] at this
    cases e : evAt beep boop n with
    | none => rfl
    | some x => rw [e] at this; simp at this
  · intro h
    rcases Nat.lt_or_ge b a with hab | hab
    · simp [evs, show b - a = 0 by omega]
    induction b, hab using Nat.le_induction with
    | base => exact evs_self a
    | succ b hab ih =>
      rw [evs_succ hab, ih (fun n h1 h2 => h n h1 (by omega)), h b hab (Nat.lt_succ_self b)]; rfl

/-- the last event of a nonempty event list, and its step -/
theorem evs_last {a b : Nat} {l : List Bool} {e : Bool} (h : evs beep boop a b = l ++ [e]) :
    ∃ o, a ≤ o ∧ o < b ∧ evAt beep boop o = some e ∧ evs beep boop a o = l ∧
      evs beep boop (o + 1) b = [] := by
  rcases Nat.lt_or_ge b a with hab | hab
  · simp [evs, show b - a = 0 by omega] at h
  induction b, hab using Nat.le_induction generalizing l with
  | base => rw [evs_self] at h; simp at h
  | succ b hab ih =>
    rw [evs_succ hab] at h
    cases hx : evAt beep boop b with
    | none =>
      rw [hx] at h; simp only [Option.toList, List.append_nil] at h
      obtain ⟨o, h1, h2, h3, h4, h5⟩ := ih h
      refine ⟨o, h1, by omega, h3, h4, ?_⟩
      rw [evs_succ (by omega), h5, hx]; rfl
    | some x =>
      rw [hx] at h; simp only [Option.toList] at h
      have := List.append_inj' h rfl
      obtain ⟨rfl, hxe⟩ := this
      cases hxe
      exact ⟨b, hab, Nat.lt_succ_self b, hx, rfl, evs_self _⟩

open Classical in
/-- the number of steps in `[a, b)` where `P` holds -/
noncomputable def cnt (P : Nat → Prop) (a b : Nat) : Nat :=
  ((List.range (b - a)).filter (fun k => decide (P (a + k)))).length

theorem cnt_self (P : Nat → Prop) (a : Nat) : cnt P a a = 0 := by simp [cnt]

open Classical in
theorem cnt_succ (P : Nat → Prop) {a b : Nat} (h : a ≤ b) :
    cnt P a (b + 1) = cnt P a b + (if P b then 1 else 0) := by
  unfold cnt
  rw [show b + 1 - a = (b - a) + 1 by omega, List.range_succ, List.filter_append,
    List.length_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil]
  rw [show a + (b - a) = b by omega]
  by_cases hp : P b <;> simp [hp]

/-- the beeps in `[a, b)` are counted by the event list -/
theorem cnt_beep (hx : ∀ n, ¬ (beep n ∧ boop n)) {a b : Nat} (h : a ≤ b) :
    cnt beep a b = (evs beep boop a b).count true := by
  induction b, h using Nat.le_induction with
  | base => rw [cnt_self, evs_self]; rfl
  | succ b hab ih =>
    rw [cnt_succ _ hab, evs_succ hab, List.count_append, ih]
    unfold evAt
    by_cases h1 : beep b
    · simp [h1]
    · by_cases h2 : boop b <;> simp [h1, h2]

theorem evAt_boop (hx : ∀ n, ¬ (beep n ∧ boop n)) {n : Nat} :
    evAt beep boop n = some false ↔ boop n := by
  unfold evAt
  by_cases h1 : beep n
  · simp only [h1, if_true]
    constructor
    · intro h; cases h
    · intro h2; exact absurd ⟨h1, h2⟩ (hx n)
  · by_cases h2 : boop n <;> simp [h1, h2]

theorem evAt_beep {n : Nat} : evAt beep boop n = some true ↔ beep n := by
  unfold evAt
  by_cases h1 : beep n
  · simp [h1]
  · by_cases h2 : boop n <;> simp [h1, h2]

end events

/-! ## segments -/

open Classical in
/-- A run cut into segments `[T k, T (k + 1))`: no event before `T 0`; a segment that is not
`good` has no event, a good one has `val k` beeps and then one boop.  Then some value repeats
forever iff infinitely many good segments have the same value. -/
theorem repeatsForever_of_segments (δ : Q → Bool → Option (Bool × Dir × Q)) (qb : Q) (bb : Bool)
    (qo : Q) (bo : Bool) (c : Cfg Q)
    (hx : ∀ n, ¬ (BeepsAt δ qb bb c n ∧ BeepsAt δ qo bo c n))
    (T : Nat → Nat) (hT : ∀ k, T k < T (k + 1)) (good : Nat → Prop) (val : Nat → Nat)
    (h0 : evs (BeepsAt δ qb bb c) (BeepsAt δ qo bo c) 0 (T 0) = [])
    (hseg : ∀ k, evs (BeepsAt δ qb bb c) (BeepsAt δ qo bo c) (T k) (T (k + 1)) =
      if good k then List.replicate (val k) true ++ [false] else []) :
    RepeatsForever δ qb bb qo bo c ↔ ∃ v, ∀ K, ∃ k, K ≤ k ∧ good k ∧ val k = v := by
  -- notation
  let bp := BeepsAt δ qb bb c
  let op := BeepsAt δ qo bo c
  have hTm : ∀ k l, k ≤ l → T k ≤ T l := by
    intro k l h
    induction l, h using Nat.le_induction with
    | base => exact Nat.le_refl _
    | succ l _ ih => exact Nat.le_trans ih (Nat.le_of_lt (hT l))
  have hTk : ∀ k, k ≤ T k := by
    intro k; induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => have := hT k; omega
  -- every step lies in a segment
  have hloc : ∀ n, T 0 ≤ n → ∃ k, T k ≤ n ∧ n < T (k + 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact ⟨0, Nat.le_refl _, hT 0⟩
    | succ n _ ih =>
      obtain ⟨k, h1, h2⟩ := ih
      rcases Nat.lt_or_ge (n + 1) (T (k + 1)) with h | h
      · exact ⟨k, by omega, h⟩
      · exact ⟨k + 1, by omega, by have := hT (k + 1); omega⟩
  -- the boop of a good segment
  have hboop : ∀ k, good k → ∃ o, T k ≤ o ∧ o < T (k + 1) ∧ op o ∧
      evs bp op (T k) o = List.replicate (val k) true ∧ evs bp op (o + 1) (T (k + 1)) = [] := by
    intro k hk
    have := hseg k; rw [if_pos hk] at this
    obtain ⟨o, h1, h2, h3, h4, h5⟩ := evs_last this
    exact ⟨o, h1, h2, (evAt_boop hx).1 h3, h4, h5⟩
  -- no event in a segment that is not good; events of a good one are before or at its boop
  have hnone : ∀ k, ¬ good k → evs bp op (T k) (T (k + 1)) = [] := by
    intro k hk; have := hseg k; rw [if_neg hk] at this; exact this
  -- a boop step is the boop of a good segment
  have hwhere : ∀ n, op n → ∃ k, good k ∧ T k ≤ n ∧ n < T (k + 1) ∧
      evs bp op (T k) n = List.replicate (val k) true ∧ evs bp op (n + 1) (T (k + 1)) = [] := by
    intro n hn
    have hn0 : T 0 ≤ n := by
      apply Classical.byContradiction; intro hlt
      have := (evs_nil_iff.1 h0) n (Nat.zero_le _) (by omega)
      rw [(evAt_boop hx).2 hn] at this; cases this
    obtain ⟨k, h1, h2⟩ := hloc n hn0
    by_cases hk : good k
    · obtain ⟨o, o1, o2, o3, o4, o5⟩ := hboop k hk
      rcases Nat.lt_trichotomy n o with hlt | heq | hgt
      · -- the event at n would be in the list of `o`'s prefix: only beeps there
        have e := evs_append (beep := bp) (boop := op) h1 (Nat.le_of_lt hlt)
        rw [o4, evs_append (beep := bp) (boop := op) (Nat.le_succ n) hlt, evs_succ (Nat.le_refl n),
          evs_self, (evAt_boop hx).2 hn] at e
        have : false ∈ List.replicate (val k) true := by rw [e]; simp
        simp at this
      · subst heq; exact ⟨k, hk, h1, h2, o4, o5⟩
      · have := (evs_nil_iff.1 o5) n (by omega) h2
        rw [(evAt_boop hx).2 hn] at this; cases this
    · have := (evs_nil_iff.1 (hnone k hk)) n h1 h2
      rw [(evAt_boop hx).2 hn] at this; cases this
  -- segments strictly between two good ones without a good one in between have no event
  have hquiet : ∀ k l, k ≤ l → (∀ m, k ≤ m → m < l → ¬ good m) → evs bp op (T k) (T l) = [] := by
    intro k l hkl hm
    induction l, hkl using Nat.le_induction with
    | base => exact evs_self _
    | succ l hkl ih =>
      rw [evs_append (hTm k l hkl) (Nat.le_of_lt (hT l)), ih (fun m h1 h2 => hm m h1 (by omega)),
        hnone l (hm l hkl (Nat.lt_succ_self l))]; rfl
  -- consecutive boops of good segments `k < l` (no good one between): `val l` beeps between
  have hgap : ∀ k l o o', k < l → (∀ m, k < m → m < l → ¬ good m) →
      T k ≤ o → o < T (k + 1) → evs bp op (o + 1) (T (k + 1)) = [] →
      T l ≤ o' → evs bp op (T l) o' = List.replicate (val l) true →
      evs bp op (o + 1) o' = List.replicate (val l) true := by
    intro k l o o' hkl hm _ o2 o3 o'1 o'4
    rw [evs_append (show o + 1 ≤ T (k + 1) by omega) (Nat.le_trans (hTm _ _ hkl) o'1),
      evs_append (hTm _ _ hkl) o'1, o3, hquiet (k + 1) l hkl (fun m h1 h2 => hm m h1 h2), o'4]; rfl
  have hcount : ∀ i j, i < j → beepsBetween δ qb bb c i j = cnt bp (i + 1) j := by
    intro i j _; rfl
  constructor
  · -- from consecutive boops to good segments
    rintro ⟨v, hv⟩
    refine ⟨v, fun K => ?_⟩
    obtain ⟨i, j, hi, hij, hbi, hbj, hnb, hc⟩ := hv (T K)
    obtain ⟨l, hl, l1, l2, l4, _⟩ := hwhere j hbj
    obtain ⟨k, _, k1, k2, _, k5⟩ := hwhere i hbi
    have hkl : k < l := by
      rcases Nat.lt_trichotomy k l with h | h | h
      · exact h
      · subst h
        have := (evs_nil_iff.1 k5) j (by omega) l2
        rw [(evAt_boop hx).2 hbj] at this; cases this
      · have := hTm (l + 1) k h; omega
    refine ⟨l, ?_, hl, ?_⟩
    · rcases Nat.lt_or_ge l K with h | h
      · have := hTm (l + 1) K h; omega
      · exact h
    · -- no good segment strictly between k and l (its boop would lie between i and j)
      have hm : ∀ m, k < m → m < l → ¬ good m := by
        intro m h1 h2 hg
        obtain ⟨o, o1, o2, o3, _, _⟩ := hboop m hg
        have := hTm (k + 1) m h1; have := hTm (m + 1) l h2
        exact hnb o (by omega) (by omega) o3
      have e := hgap k l i j hkl hm k1 k2 k5 l1 l4
      rw [← hc, hcount i j hij, cnt_beep hx (by omega), e, List.count_replicate_self]
  · -- from good segments to consecutive boops
    rintro ⟨v, hv⟩
    refine ⟨v, fun N => ?_⟩
    -- a good segment k0 with T k0 ≥ N, then a later good one l with value v
    obtain ⟨k0, hk0, hg0, _⟩ := hv N
    obtain ⟨l, hl, hgl, hvl⟩ := hv (k0 + 1)
    -- the last good segment before l
    have hex : ∃ k, k < l ∧ good k ∧ k0 ≤ k ∧ ∀ m, k < m → m < l → ¬ good m := by
      -- downward search from l - 1
      have key : ∀ d, d + k0 < l → good k0 → (∀ m, d + k0 < m → m < l → ¬ good m) →
          ∃ k, k < l ∧ good k ∧ k0 ≤ k ∧ ∀ m, k < m → m < l → ¬ good m := by
        intro d
        induction d with
        | zero => intro h1 h2 h3; exact ⟨k0, by omega, h2, Nat.le_refl _, by simpa using h3⟩
        | succ d ih =>
          intro h1 h2 h3
          by_cases hg : good (d + 1 + k0)
          · exact ⟨d + 1 + k0, h1, hg, by omega, h3⟩
          · exact ih (by omega) h2 (fun m hm1 hm2 => by
              rcases Nat.lt_or_ge (d + 1 + k0) m with h | h
              · exact h3 m h hm2
              · have : m = d + 1 + k0 := by omega
                subst this; exact hg)
      exact key (l - 1 - k0) (by omega) hg0 (fun m h1 h2 => by omega)
    obtain ⟨k, hkl, hgk, hk0k, hm⟩ := hex
    obtain ⟨o, o1, o2, o3, _, o5⟩ := hboop k hgk
    obtain ⟨o', o'1, o'2, o'3, o'4, _⟩ := hboop l hgl
    have hTk1 := hTm (k + 1) l hkl
    refine ⟨o, o', ?_, by omega, o3, o'3, ?_, ?_⟩
    · have := hTk k0; have := hTm k0 k hk0k; omega
    · intro n hn1 hn2 hbn
      obtain ⟨m, hgm, m1, m2, _, _⟩ := hwhere n hbn
      -- m is between k and l, or is k or l itself
      rcases Nat.lt_trichotomy m k with h | h | h
      · have := hTm (m + 1) k h; omega
      · subst h
        have := (evs_nil_iff.1 o5) n (by omega) m2
        rw [(evAt_boop hx).2 hbn] at this; cases this
      · rcases Nat.lt_trichotomy m l with h' | h' | h'
        · exact hm m h h' hgm
        · subst h'
          -- n < o' inside segment l: the prefix before o' has only beeps
          have e := evs_append (beep := bp) (boop := op) m1 (Nat.le_of_lt hn2)
          rw [o'4, evs_append (beep := bp) (boop := op) (Nat.le_succ n) hn2, evs_succ (Nat.le_refl n),
            evs_self, (evAt_boop hx).2 hbn] at e
          have : false ∈ List.replicate (val m) true := by rw [e]; simp
          simp at this
        · have := hTm (l + 1) m h'; omega
    · rw [hcount o o' (by omega), cnt_beep hx (by omega), hgap k l o o' hkl hm o1 o2 o5 o'1 o'4,
        List.count_replicate_self, hvl]

/-! ## traces: event-free runs joined by beep and boop steps -/

section trace
variable (δ δ0 : Q → Bool → Option (Bool × Dir × Q)) (qb : Q) (bb : Bool) (qo : Q) (bo : Bool)

/-- `Trace a es b`: from `a` to `b` by runs of `δ0` (the machine without its beep and boop)
and single beep (`true`) or boop (`false`) steps of `δ`, in the order `es`. -/
inductive Trace : Cfg Q → List Bool → Cfg Q → Prop
  | nil {a b : Cfg Q} : Reach δ0 a b → Trace a [] b
  | beep {a b c d : Cfg Q} {es : List Bool} : Reach δ0 a b → b.q = qb → b.R 0 = bb →
      step δ b = some c → Trace c es d → Trace a (true :: es) d
  | boop {a b c d : Cfg Q} {es : List Bool} : Reach δ0 a b → b.q = qo → b.R 0 = bo →
      step δ b = some c → Trace c es d → Trace a (false :: es) d

variable {δ δ0 qb bb qo bo}

theorem Trace.append {a b c : Cfg Q} {es fs : List Bool}
    (h1 : Trace δ δ0 qb bb qo bo a es b) (h2 : Trace δ δ0 qb bb qo bo b fs c)
    (hsub : ∀ q b t, δ0 q b = some t → δ q b = some t) :
    Trace δ δ0 qb bb qo bo a (es ++ fs) c := by
  induction h1 with
  | nil h =>
    cases h2 with
    | nil h' => exact Trace.nil (Reach.trans δ0 h h')
    | beep r hq hb hs t => exact Trace.beep (Reach.trans δ0 h r) hq hb hs t
    | boop r hq hb hs t => exact Trace.boop (Reach.trans δ0 h r) hq hb hs t
  | beep r hq hb hs _ ih => exact Trace.beep r hq hb hs (ih h2)
  | boop r hq hb hs _ ih => exact Trace.boop r hq hb hs (ih h2)

/-- The events of a trace, for a `δ0` that is `δ` without its beep and boop transitions:
if the run from `s` is at `a` after `n` steps, it is at `b` after `n + m` steps and the
events at steps `n, …, n + m - 1` are `es`. -/
theorem Trace.evs (hsub : ∀ q b t, δ0 q b = some t → δ q b = some t)
    (hb0 : δ0 qb bb = none) (ho0 : δ0 qo bo = none) (hne : ¬ (qo = qb ∧ bo = bb))
    {s a b : Cfg Q} {es : List Bool}
    (h : Trace δ δ0 qb bb qo bo a es b) {n : Nat} (hn : run δ n s = some a) :
    ∃ m, run δ (n + m) s = some b ∧
      TM.evs (BeepsAt δ qb bb s) (BeepsAt δ qo bo s) n (n + m) = es := by
  -- a run of δ0: no events, and the run of δ follows it
  have quiet : ∀ (a b : Cfg Q) (n : Nat), run δ n s = some a → Reach δ0 a b →
      ∃ m, run δ (n + m) s = some b ∧
        TM.evs (BeepsAt δ qb bb s) (BeepsAt δ qo bo s) n (n + m) = [] := by
    intro a b n hn ⟨m, hm⟩
    have hm : run δ0 m a = some b := hm
    refine ⟨m, ?_, ?_⟩
    · rw [run_add, hn]; exact run_sub hsub m a b hm
    · rw [evs_nil_iff]
      intro k h1 h2
      -- the configuration at step k is on the δ0 run, which continues from it
      obtain ⟨d, hd⟩ : ∃ d, run δ0 (k - n) a = some d := by
        cases e : run δ0 (k - n) a with
        | none =>
          have := run_none_mono (δ := δ0) e (m - (k - n))
          rw [show k - n + (m - (k - n)) = m by omega, hm] at this; cases this
        | some d => exact ⟨d, rfl⟩
      have hk : run δ k s = some d := by
        rw [show k = n + (k - n) by omega, run_add, hn]; exact run_sub hsub _ a d hd
      have hstep : step δ0 d ≠ none := by
        intro hs
        have := run_none_mono (δ := δ0) (show run δ0 (k - n + 1) a = none by
          rw [run_add, hd]; simp [run, Sys.run, hs]) (m - (k - n) - 1)
        rw [show k - n + 1 + (m - (k - n) - 1) = m by omega, hm] at this; cases this
      unfold evAt
      have nb : ¬ BeepsAt δ qb bb s k := by
        rintro ⟨d', h1, h2, h3, _⟩
        rw [hk] at h1; cases h1
        exact hstep (by simp [step, h2, h3, hb0])
      have no : ¬ BeepsAt δ qo bo s k := by
        rintro ⟨d', h1, h2, h3, _⟩
        rw [hk] at h1; cases h1
        exact hstep (by simp [step, h2, h3, ho0])
      simp [nb, no]
  -- one special step at `n + m1`, then the rest
  have joinev : ∀ (b c d : Cfg Q) (n m1 m2 : Nat) (e : Bool) (es : List Bool),
      run δ (n + m1) s = some b → step δ b = some c →
      TM.evs (BeepsAt δ qb bb s) (BeepsAt δ qo bo s) n (n + m1) = [] →
      evAt (BeepsAt δ qb bb s) (BeepsAt δ qo bo s) (n + m1) = some e →
      run δ (n + m1 + 1 + m2) s = some d →
      TM.evs (BeepsAt δ qb bb s) (BeepsAt δ qo bo s) (n + m1 + 1) (n + m1 + 1 + m2) = es →
      ∃ m, run δ (n + m) s = some d ∧
        TM.evs (BeepsAt δ qb bb s) (BeepsAt δ qo bo s) n (n + m) = e :: es := by
    intro b c d n m1 m2 e es _ _ e1 he _ e2
    refine ⟨m1 + 1 + m2, by rwa [← Nat.add_assoc, ← Nat.add_assoc], ?_⟩
    rw [← Nat.add_assoc, ← Nat.add_assoc, evs_append (Nat.le_add_right n m1) (by omega),
      evs_append (Nat.le_succ (n + m1)) (by omega), evs_succ (Nat.le_refl _), evs_self, e1, he, e2]
    rfl
  induction h generalizing n with
  | nil r => exact quiet _ _ n hn r
  | @beep a b c d es r hq hb hs _ ih =>
    obtain ⟨m1, h1, e1⟩ := quiet a b n hn r
    have hc : run δ (n + m1 + 1) s = some c := by rw [run_add, h1]; simp [run, Sys.run, hs]
    obtain ⟨m2, h2, e2⟩ := ih hc
    have hbeep : BeepsAt δ qb bb s (n + m1) :=
      ⟨b, h1, hq, hb, by intro e; rw [← hq, ← hb] at e; simp [step, e] at hs⟩
    exact joinev b c d n m1 m2 true es h1 hs e1 (evAt_beep.2 hbeep) h2 e2
  | @boop a b c d es r hq hb hs _ ih =>
    obtain ⟨m1, h1, e1⟩ := quiet a b n hn r
    have hc : run δ (n + m1 + 1) s = some c := by rw [run_add, h1]; simp [run, Sys.run, hs]
    obtain ⟨m2, h2, e2⟩ := ih hc
    have hboop : BeepsAt δ qo bo s (n + m1) :=
      ⟨b, h1, hq, hb, by intro e; rw [← hq, ← hb] at e; simp [step, e] at hs⟩
    have hnb : ¬ BeepsAt δ qb bb s (n + m1) := by
      rintro ⟨b', h1', hq', hb', _⟩
      rw [h1] at h1'; cases h1'
      exact hne ⟨hq.symm.trans hq', hb.symm.trans hb'⟩
    have hev : evAt (BeepsAt δ qb bb s) (BeepsAt δ qo bo s) (n + m1) = some false := by
      unfold evAt; simp [hnb, hboop]
    exact joinev b c d n m1 m2 false es h1 hs e1 hev h2 e2

end trace

/-! ## transfer to a simulating machine -/

/-- Repeating forever carries over to a machine that simulates the original (a merged
machine), if the original never halts and the simulator's beep and boop states play the
design's beep and boop states only on the beep and boop symbols. -/
theorem repeatsForever_iff_of_sim {Q' : Type} (δ : Q → Bool → Option (Bool × Dir × Q))
    (δ' : Q' → Bool → Option (Bool × Dir × Q')) (φ : Q → Q')
    (h : ∀ q b, Compat φ (δ q b) (δ' (φ q) b)) (s : Cfg Q) (hnh : ¬ Halts δ s)
    (qb : Q) (bb : Bool) (qo : Q) (bo : Bool)
    (hexb : ∀ q, φ q = φ qb → q = qb ∨ δ q bb = none)
    (hexo : ∀ q, φ q = φ qo → q = qo ∨ δ q bo = none) :
    RepeatsForever δ' (φ qb) bb (φ qo) bo (s.map φ) ↔ RepeatsForever δ qb bb qo bo s := by
  have eb := beepsAt_iff_of_sim δ δ' φ h s hnh qb bb hexb
  have eo := beepsAt_iff_of_sim δ δ' φ h s hnh qo bo hexo
  have ec : ∀ i j, beepsBetween δ' (φ qb) bb (s.map φ) i j = beepsBetween δ qb bb s i j := by
    intro i j; unfold beepsBetween; congr 1; apply List.filter_congr
    intro k _; exact decide_eq_decide.mpr (eb _)
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, fun N => ?_⟩
    obtain ⟨i, j, h1, h2, h3, h4, h5, h6⟩ := hv N
    exact ⟨i, j, h1, h2, (eo i).1 h3, (eo j).1 h4, fun k a b => fun hk => h5 k a b ((eo k).2 hk),
      by rw [← ec]; exact h6⟩
  · rintro ⟨v, hv⟩
    refine ⟨v, fun N => ?_⟩
    obtain ⟨i, j, h1, h2, h3, h4, h5, h6⟩ := hv N
    exact ⟨i, j, h1, h2, (eo i).2 h3, (eo j).2 h4, fun k a b => fun hk => h5 k a b ((eo k).1 hk),
      by rw [ec]; exact h6⟩

end TM
