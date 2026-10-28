import TinyCryptids.ABC.Blocks
import TinyCryptids.ABC.Tac
import TinyCryptids.Core.Mirror

/-!
# One round of `Z := Z * β`, as a template machine

The design has two copies of this routine: `R*` (base left of `Z`, `Z` grows to the right:
`R := R * d` and `Q := Q * R`) and `L*` (its mirror image: `P := P * c`).  The routine is
proved once, for the template machine `mdelta` below, and carried over to both copies by
`sim_run` (a state map under which every template transition is a design transition), the
second one through the mirror image of the design (`Mirror`).

Template tape, left to right: `Lb`, the base block (value `β`, hole at `j`), a gap `g` (no
hole), `Z` (value `z`, its copy cursor on cell 1), `00`, the copies `Q` (`q` cells), blank.
Each non-wrapping advance of the base hole appends a copy of `Z`'s `z` positions to `Q`;
the wrap merges `Z 00 Q` into one block (fill the separator, erase two cells).
-/

namespace TM.ABC

inductive MS
  | ba1 | ba2 | ba3 | ba4 | ba5 | ba6 | ba7 | MC1 | MC2
  | c1 | c2 | c3 | c4 | c5 | c6 | a2 | a3 | a4 | d1 | d2 | d3 | NB1 | NB2
  | MM1 | MM2 | mR | m2 | m3 | m4 | m5 | EXIT
deriving DecidableEq

open MS Dir in
def mdelta : MS → Bool → Option (Bool × Dir × MS)
  | ba1, false => some (true, R, ba2)
  | ba2, true => some (true, R, ba3)
  | ba3, false => some (false, L, ba5)
  | ba3, true => some (true, L, ba4)
  | ba4, true => some (false, R, MC1)
  | ba5, false => some (false, R, ba6)
  | ba5, true => some (true, L, ba5)
  | ba6, true => some (true, R, ba7)
  | ba7, true => some (false, R, MM1)
  | MC1, false => some (false, R, MC2)
  | MC1, true => some (true, R, MC1)
  | MC2, false => some (false, R, MC1)
  | MC2, true => some (true, R, c1)
  | c1, false => some (false, R, c2)
  | c1, true => some (true, R, c1)
  | c2, false => some (false, R, c3)
  | c3, false => some (true, L, c4)
  | c3, true => some (true, R, c3)
  | c4, false => some (false, L, c5)
  | c4, true => some (true, L, c4)
  | c5, false => some (false, L, c6)
  | c6, false => some (true, R, a2)
  | c6, true => some (true, L, c6)
  | a2, true => some (true, R, a3)
  | a3, false => some (false, L, d1)
  | a3, true => some (true, L, a4)
  | a4, true => some (false, R, c1)
  | d1, false => some (false, R, d2)
  | d1, true => some (true, L, d1)
  | d2, true => some (true, R, d3)
  | d3, true => some (false, L, NB1)
  | NB1, false => some (false, L, NB2)
  | NB1, true => some (true, L, NB1)
  | NB2, false => some (false, L, NB1)
  | NB2, true => some (true, R, ba1)
  | MM1, false => some (false, R, MM2)
  | MM1, true => some (true, R, MM1)
  | MM2, false => some (false, R, MM1)
  | MM2, true => some (true, R, mR)
  | mR, false => some (true, R, m2)
  | mR, true => some (true, R, mR)
  | m2, false => some (true, R, m3)
  | m3, false => some (false, L, m4)
  | m3, true => some (true, R, m3)
  | m4, true => some (false, L, m5)
  | m5, true => some (false, L, EXIT)
  | _, _ => none

namespace Mt

abbrev MR := Reach mdelta

theorem sR {q q' : MS} {L R : Strm} {b w : Bool} (h : mdelta q b = some (w, Dir.R, q')) :
    MR ⟨q, L, b ::: R⟩ ⟨q', w ::: L, R⟩ := stepR (δ := mdelta) (R := b ::: R) h
theorem sL {q q' : MS} {s R : Strm} {b w : Bool} (h : mdelta q b = some (w, Dir.L, q')) :
    MR (cfgL q (b ::: s) R) (cfgL q' s (w ::: R)) := stepL' (δ := mdelta) (s := b ::: s) h
theorem tr {a b c : Cfg MS} (h1 : MR a b) (h2 : MR b c) : MR a c := Reach.trans mdelta h1 h2
theorem scanR' {q : MS} (h : mdelta q true = some (true, Dir.R, q)) (n : Nat) (L R : Strm) :
    MR ⟨q, L, ones n R⟩ ⟨q, ones n L, R⟩ := scanR h n L R
theorem scanL' {q : MS} (h : mdelta q true = some (true, Dir.L, q)) (n : Nat) (s R : Strm) :
    MR (cfgL q (ones n s) R) (cfgL q s (ones n R)) := scanL h n s R
theorem blankR {q : MS} {L : Strm} {X : Cfg MS} (h : MR ⟨q, L, false ::: blank⟩ X) :
    MR ⟨q, L, blank⟩ X := by rw [← cons_blank]; exact h

macro "tR" : tactic => `(tactic| refine Mt.tr (Mt.sR (by rfl)) ?_)
macro "tL" : tactic => `(tactic| refine Mt.tr (Mt.sL (by rfl)) ?_)
macro "tL0" : tactic => `(tactic| refine Mt.tr (stepL (δ := mdelta) (by rfl)) ?_)
macro "tfin" : tactic => `(tactic| exact Reach.refl mdelta _)
macro "tsR" n:term : tactic => `(tactic| refine Mt.tr (Mt.scanR' (by rfl) $n _ _) ?_)
macro "tsL" n:term : tactic => `(tactic| refine Mt.tr (Mt.scanL' (by rfl) $n _ _) ?_)

open MS

local notation "F" => false
local notation "T" => true

def sep (s : Strm) : Strm := F ::: F ::: s

theorem PMC : ParserR mdelta MC1 MC2 := ⟨rfl, rfl, rfl⟩
theorem PMM : ParserR mdelta MM1 MM2 := ⟨rfl, rfl, rfl⟩
theorem PNB : ParserL mdelta NB1 NB2 := ⟨rfl, rfl, rfl⟩

/-! ## the copy loop -/

/-- head on the separator right of `Z` (value `r`, cursor at `c`), `q` copied cells -/
def cpyS (c r q : Nat) (Lc : Strm) : Cfg MS :=
  ⟨c1, ones (r + 1 - c) (F ::: ones c Lc), sep (ones q blank)⟩

theorem copy_one (c r q : Nat) (Lc : Strm) (hc : c < r) :
    MR (cpyS c r q Lc) (cpyS (c+1) r (q+1) Lc) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = c + 1 + k := ⟨r - c - 1, by omega⟩
  have e1 : c + 1 + k + 1 - c = k + 2 := by omega
  have e2 : c + 1 + k + 1 - (c + 1) = k + 1 := by omega
  unfold cpyS sep; rw [e1, e2, ones_succ' q]
  tR; tR; tsR q
  refine Mt.blankR ?_
  tL; tsL q; tL; tL; tsL (k + 2)
  tR; tR; tL; tR; tsR (k + 1); tfin

/-- after the last cell: cursor reset to cell 1, head on cell 0 in state `NB1` -/
def cpyDone (r q : Nat) (Lc : Strm) : Cfg MS :=
  cfgL NB1 (T ::: F ::: Lc) (F ::: ones r (sep (ones q blank)))

theorem copy_last (r q : Nat) (Lc : Strm) :
    MR (cpyS r r q (F ::: Lc)) (cpyDone r (q+1) Lc) := by
  unfold cpyS cpyDone sep
  rw [show r + 1 - r = 1 by omega, ones_succ' q]
  tR; tR; tsR q
  refine Mt.blankR ?_
  tL; tsL q; tL; tL; tL; tR; tR; tL; tsL (r + 2); tR; tR; tL; tfin

theorem copy_all (r q : Nat) (Lc : Strm) : ∀ c, 1 ≤ c → c ≤ r →
    MR (cpyS c r q (F ::: Lc)) (cpyDone r (q + (r + 1 - c)) Lc) := by
  suffices H : ∀ n c q, r - c = n → 1 ≤ c → c ≤ r →
      MR (cpyS c r q (F ::: Lc)) (cpyDone r (q + (r + 1 - c)) Lc) from
    fun c h1 h2 => H _ c q rfl h1 h2
  intro n
  induction n with
  | zero =>
    intro c q h _ h2
    have : c = r := by omega
    subst this; rw [show c + 1 - c = 1 by omega]; exact copy_last c q Lc
  | succ n ih =>
    intro c q h h1 h2
    refine Mt.tr (copy_one c r q _ (by omega)) ?_
    have := ih (c+1) (q+1) (by omega) (by omega) (by omega)
    rw [show q + 1 + (r + 1 - (c + 1)) = q + (r + 1 - c) by omega] at this
    exact this

/-- a full copy of `Z`, entered from the parser (head two cells right of the cursor) -/
theorem copy_full (r q : Nat) (Lc : Strm) (hr : 1 ≤ r) :
    MR ⟨c1, T ::: F ::: T ::: F ::: Lc, ones (r - 1) (sep (ones q blank))⟩
      (cpyDone r (q + r) Lc) := by
  tsR (r - 1)
  have := copy_all r q Lc 1 (Nat.le_refl _) hr
  rw [show q + (r + 1 - 1) = q + r by omega] at this
  unfold cpyS at this
  rw [show r + 1 - 1 = (r - 1) + 1 by omega, ones_succ'] at this
  exact this

/-! ## the base loop -/

/-- the tape right of the base block: the gap, `Z` (cursor at cell 1), the copies -/
def rgt (g : List Bool) (z q : Nat) : Strm := app g (T ::: F ::: ones z (sep (ones q blank)))

/-- at the base hole (cell `j`) -/
def bAt (Lb : Strm) (β j : Nat) (g : List Bool) (z q : Nat) : Cfg MS :=
  ⟨ba1, ones j Lb, F ::: ones (β + 1 - j) (rgt g z q)⟩

theorem to_z {g : List Bool} (hg : Gap g) (n z q : Nat) (L : Strm) (hz : 1 ≤ z) :
    MR ⟨MC1, L, ones n (rgt g z q)⟩
      ⟨c1, T ::: F ::: T ::: app g.reverse (ones n L), ones (z - 1) (sep (ones q blank))⟩ := by
  obtain ⟨z, rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
  have hw : Clean (List.replicate n true ++ (g ++ [true])) := Clean.rep_append n (hg.clean Clean.nil)
  have e : ones n (rgt g (z + 1) q) =
      app (List.replicate n true ++ (g ++ [true])) (F ::: T ::: ones z (sep (ones q blank))) := by
    simp only [rgt, app_append, app_replicate, app_cons, app_nil, ones_succ]
  rw [e]
  refine Mt.tr (PMC.find hw _ _) ?_
  tR
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.reverse_replicate, app_append, app_replicate, app_cons, app_nil, List.singleton_append,
    Nat.add_sub_cancel]
  tfin

theorem nb_back {g : List Bool} (hg : Gap g) (z q k j : Nat) (Lb Lc : Strm)
    (he : F ::: Lc = app g.reverse (ones (k + 1) (F ::: ones (j + 1) Lb))) :
    MR (cpyDone z q Lc) ⟨ba1, ones (j + 1) Lb, F ::: ones (k + 1) (rgt g z q)⟩ := by
  have hw : Clean (true :: (g.reverse ++ List.replicate (k + 1) true)) :=
    Clean.one (by rw [List.replicate_succ]; exact hg.reverse.clean (Clean.replicate k))
  have e : T ::: F ::: Lc =
      app (true :: (g.reverse ++ List.replicate (k + 1) true)) (F ::: T ::: ones j Lb) := by
    rw [he]; simp only [app_cons, app_append, app_replicate, ones_succ]
  unfold cpyDone; rw [e]
  refine Mt.tr (PNB.find hw _ _) ?_
  tR
  simp only [rgt, List.reverse_cons, List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    List.append_assoc, List.singleton_append, app_append, app_replicate, app_cons, app_nil, ones_succ]
  tfin

theorem base_adv {g : List Bool} (hg : Gap g) (Lb : Strm) (β j z q : Nat)
    (hj : 1 ≤ j) (hjb : j < β) (hz : 1 ≤ z) :
    MR (bAt Lb β j g z q) (bAt Lb β (j + 1) g z (q + z)) := by
  obtain ⟨k, hk⟩ : ∃ k, β + 1 - j = k + 2 := ⟨β - j - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  unfold bAt
  rw [hk, show β + 1 - (j' + 1 + 1) = k + 1 by omega]
  tR; tR; tL; tR
  show MR ⟨MC1, F ::: ones (j' + 2) Lb, ones (k + 1) (rgt g z q)⟩ _
  refine Mt.tr (to_z hg (k + 1) z q _ hz) ?_
  obtain ⟨g', hg'⟩ := hg.rev_head
  rw [hg', app_cons]
  refine Mt.tr (copy_full z q _ hz) ?_
  exact nb_back hg z (q + z) k (j' + 1) Lb _ (by rw [hg', app_cons])

theorem base_loop {g : List Bool} (hg : Gap g) (Lb : Strm) (β z q : Nat) (hz : 1 ≤ z) :
    ∀ j, 1 ≤ j → j ≤ β → MR (bAt Lb β j g z q) (bAt Lb β β g z (q + z * (β - j))) := by
  suffices H : ∀ n j q, β - j = n → 1 ≤ j → j ≤ β →
      MR (bAt Lb β j g z q) (bAt Lb β β g z (q + z * (β - j))) from
    fun j hj hjb => H _ j q rfl hj hjb
  intro n
  induction n with
  | zero =>
    intro j q h hj hjb
    have : β = j := by omega
    subst this; simp; tfin
  | succ n ih =>
    intro j q h hj hjb
    refine Mt.tr (base_adv hg Lb β j z q hj (by omega) hz) ?_
    have := ih (j + 1) (q + z) (by omega) (by omega) (by omega)
    rw [show q + z + z * (β - (j + 1)) = q + z * (β - j) by
      rw [show β - j = (β - (j + 1)) + 1 by omega, Nat.mul_succ]; omega] at this
    exact this

/-- the base hole wraps; to `Z`'s cursor; merge `Z 00 Q` -/
theorem base_wrap {g : List Bool} (hg : Gap g) (Lb : Strm) (β z q : Nat) (hz : 1 ≤ z) (hq : 1 ≤ q) :
    MR (bAt (F ::: Lb) β β g z q)
      (cfgL EXIT (ones (z + q) (F ::: T ::: app g.reverse (ones β (F ::: T ::: F ::: Lb)))) blank) := by
  obtain ⟨g', hg'⟩ := hg.head
  unfold bAt; rw [show β + 1 - β = 1 by omega]
  unfold rgt; rw [hg']; simp only [app_cons]
  tR; tR; tL
  tsL (β + 2)
  tR; tR; tR
  rw [← app_cons, ← hg']
  show MR ⟨MM1, F ::: T ::: F ::: Lb, ones β (app g (T ::: F ::: ones z (sep (ones q blank))))⟩ _
  have hw : Clean (List.replicate β true ++ (g ++ [true])) := Clean.rep_append β (hg.clean Clean.nil)
  obtain ⟨z', rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
  have e : ones β (app g (T ::: F ::: ones (z' + 1) (sep (ones q blank)))) =
      app (List.replicate β true ++ (g ++ [true])) (F ::: T ::: ones z' (sep (ones q blank))) := by
    simp only [app_append, app_replicate, app_cons, app_nil, ones_succ]
  rw [e]
  refine Mt.tr (PMM.find hw _ _) ?_
  tR
  tsR z'
  simp only [sep]
  tR; tR
  tsR q
  refine Mt.blankR ?_
  tL
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [ones_succ]
  tL
  cases q' with
  | zero =>
    tL
    simp only [cons_blank, ones_zero, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.reverse_replicate, app_append, app_replicate, app_cons, app_nil,
      List.singleton_append]
    rw [ones_cons_true, ← ones_succ, ← ones_succ]; tfin
  | succ q'' =>
    tL
    simp only [cons_blank, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.reverse_replicate, app_append, app_replicate, app_cons, app_nil,
      List.singleton_append]
    rw [ones_cons_true, ← ones_succ, ← ones_succ, ones_cons_true, ← ones_succ, ones_add]
    rw [show q'' + 1 + (z' + 1 + 1) = z' + 1 + (q'' + 1 + 1) by omega]; tfin

/-- **one round** `Z := Z * β` (`β ≥ 2`): from the base hole on cell 1 to `Z`'s new last cell -/
theorem mult {g : List Bool} (hg : Gap g) (Lb : Strm) (β z : Nat) (hβ : 2 ≤ β) (hz : 1 ≤ z) :
    MR (bAt (F ::: Lb) β 1 g z 0)
      (cfgL EXIT (ones (z * β) (F ::: T ::: app g.reverse (ones β (F ::: T ::: F ::: Lb)))) blank) := by
  refine Mt.tr (base_loop hg _ β z 0 hz 1 (Nat.le_refl _) (by omega)) ?_
  obtain ⟨β', rfl⟩ : ∃ β', β = β' + 1 := ⟨β - 1, by omega⟩
  have hq : 1 ≤ z * β' := Nat.le_trans (by omega : 1 ≤ 1 * 1) (Nat.mul_le_mul hz (by omega))
  have := base_wrap hg Lb (β' + 1) z (0 + z * (β' + 1 - 1)) hz (by rw [Nat.add_sub_cancel]; omega)
  rw [show z + (0 + z * (β' + 1 - 1)) = z * (β' + 1) by rw [Nat.add_sub_cancel, Nat.mul_succ]; omega] at this
  exact this

end Mt

open Mt

def phiR : MS → St
  | MS.ba1 => St.Rba1
  | MS.ba2 => St.Rba2
  | MS.ba3 => St.Rba3
  | MS.ba4 => St.Rba4
  | MS.ba5 => St.Rba5
  | MS.ba6 => St.Rba6
  | MS.ba7 => St.Rba7
  | MS.MC1 => St.RMC1
  | MS.MC2 => St.RMC2
  | MS.c1 => St.Rc1
  | MS.c2 => St.Rc2
  | MS.c3 => St.Rc3
  | MS.c4 => St.Rc4
  | MS.c5 => St.Rc5
  | MS.c6 => St.Rc6
  | MS.a2 => St.Ra2
  | MS.a3 => St.Ra3
  | MS.a4 => St.Ra4
  | MS.d1 => St.Rd1
  | MS.d2 => St.Rd2
  | MS.d3 => St.Rd3
  | MS.NB1 => St.RNB1
  | MS.NB2 => St.RNB2
  | MS.MM1 => St.RMM1
  | MS.MM2 => St.RMM2
  | MS.mR => St.RmR
  | MS.m2 => St.Rm2
  | MS.m3 => St.Rm3
  | MS.m4 => St.Rm4
  | MS.m5 => St.Rm5
  | MS.EXIT => St.ZD1

def phiL : MS → St
  | MS.ba1 => St.Lba1
  | MS.ba2 => St.Lba2
  | MS.ba3 => St.Lba3
  | MS.ba4 => St.Lba4
  | MS.ba5 => St.Lba5
  | MS.ba6 => St.Lba6
  | MS.ba7 => St.Lba7
  | MS.MC1 => St.LMC1
  | MS.MC2 => St.LMC2
  | MS.c1 => St.Lc1
  | MS.c2 => St.Lc2
  | MS.c3 => St.Lc3
  | MS.c4 => St.Lc4
  | MS.c5 => St.Lc5
  | MS.c6 => St.Lc6
  | MS.a2 => St.La2
  | MS.a3 => St.La3
  | MS.a4 => St.La4
  | MS.d1 => St.Ld1
  | MS.d2 => St.Ld2
  | MS.d3 => St.Ld3
  | MS.NB1 => St.LNB1
  | MS.NB2 => St.LNB2
  | MS.MM1 => St.LMM1
  | MS.MM2 => St.LMM2
  | MS.mR => St.LmR
  | MS.m2 => St.Lm2
  | MS.m3 => St.Lm3
  | MS.m4 => St.Lm4
  | MS.m5 => St.Lm5
  | MS.EXIT => St.LZ1

theorem compatR : ∀ q b, Compat phiR (mdelta q b) (deltaQ (phiR q) b) := by
  intro q b; cases q <;> cases b <;> first | trivial | rfl

theorem compatL : ∀ q b, Compat phiL (mdelta q b) (mirror deltaQ (phiL q) b) := by
  intro q b; cases q <;> cases b <;> first | trivial | rfl

local notation "F" => false
local notation "T" => true

/-- `R*` in the design: the base hole on cell 1 (state `Rba1`) to `Z`'s new last cell (`ZD1`) -/
theorem multR {g : List Bool} (hg : Gap g) (Lb : Strm) (β z : Nat) (hβ : 2 ≤ β) (hz : 1 ≤ z) :
    Rch ⟨St.Rba1, ones 1 (F ::: Lb), F ::: ones β (rgt g z 0)⟩
      (cfgL St.ZD1 (ones (z * β) (F ::: T ::: app g.reverse (ones β (F ::: T ::: F ::: Lb)))) blank) := by
  have := Reach.embed compatR (mult hg Lb β z hβ hz)
  unfold bAt at this; rw [Nat.add_sub_cancel] at this
  exact this

/-- `L*` in the design, the mirror image: `P := P * c` -/
theorem multL {g : List Bool} (hg : Gap g) (Lb : Strm) (β z : Nat) (hβ : 2 ≤ β) (hz : 1 ≤ z) :
    Rch (Cfg.mir ⟨St.Lba1, ones 1 (F ::: Lb), F ::: ones β (rgt g z 0)⟩)
      (Cfg.mir (cfgL St.LZ1 (ones (z * β) (F ::: T ::: app g.reverse (ones β (F ::: T ::: F ::: Lb)))) blank)) := by
  have := Reach.embed compatL (mult hg Lb β z hβ hz)
  unfold bAt at this; rw [Nat.add_sub_cancel] at this
  exact Reach.of_mir this

end TM.ABC