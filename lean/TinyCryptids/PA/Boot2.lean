import TinyCryptids.PA.Boot1
import TinyCryptids.PA.Run

/-!
# boot2: building the register file

boot1 leaves `(10)^1909 1 [1] 0 1111` in `3.prooflist.inc`: the tail looks like the middle of an
`inc` of register 0 with the -1 register `1111` ending at cell `G = 3824` and no register yet.
Finishing it creates register 0 (`firstOp`) and leaves the boot2 program counter
`pcB m = 1 0 (10)^m 1 1`: the root reads `1 0`, states `0b.boot2.0/1` skip the pairs and
`0b.boot2.2` reads the bit after `1 1` — `0`: `inc` register 0, `1`: `decnz` register 0.  The
`inc` sets that bit; the `decnz` (which appends a register, value 0) erases it and the `1 1` and
moves `1 1` two cells left.  After 1908 pairs the program counter is `1 1`, there are 1909 zero
registers, and main starts (`boot`).
-/

namespace TM.PA

open TM

/-- the boot2 program counter -/
def pcB (m : Nat) : List Bool := true :: false :: (pairs m ++ [true, true])

theorem pairs_len (m : Nat) : (pairs m).length = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [pairs, ih]; omega

theorem pcB_len (m : Nat) : (pcB m).length = 2 * m + 4 := by
  simp [pcB, pairs_len]

/-- `5.root.1` with the boot2 program counter `pcB m` and the bit `x` after it -/
def bootCfg (m : Nat) (x : Bool) (rs : List Nat) : Cfg St :=
  ⟨.root1, true ::: blank, app ((pcB m).tail ++ [x]) (RT G ((pcB m).length + 1) 1 rs)⟩

section
variable {dag : Nat → Option (Ch × Ch)}

/-- `inc` of register 0 when there is no register: it becomes 0 -/
theorem phase2IncEmpty (a : Nat) (ha : 1 ≤ a) (L : Strm) :
    Rch dag ⟨.chI 2, false ::: L, false ::: app (rcells a []) blank⟩
      (cfgL .brk0 L (false ::: false ::: app (rcells a [0]) blank)) := by
  gR
  simp only [rcells, blist_nil, List.append_nil, app_ones]
  refine Rch.tr (scanRq (chI_true _) _ _ _) ?_
  refine Rch.tr (sRb (by rfl)) ?_
  refine Rch.tr (sRb (by rfl)) ?_
  refine Rch.tr (stepL (δ := delta dag 0) (L := true ::: false ::: ones a (false ::: false ::: L))
    (R := blank) (by rfl)) ?_
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have hw : Sep1 (true :: false :: List.replicate (a' + 1) true) := by
    refine Sep1.one (Sep1.zero ?_)
    simpa using Sep1.replicate a' Sep1.nil
  have := ret0 (dag := dag) hw L (false ::: blank)
  simp only [app_cons, app_ones] at this
  refine Rch.tr this (Rch.of_eq ?_)
  simp [blist, app_append, app_ones, List.reverse_replicate, cons_blank]

/-- the boot2 walk: `5.root.1` reads `0`, the pairs, `1 1` and the bit `x`; the register operation
of `x` starts on the cell after it -/
theorem walkB (m : Nat) (x : Bool) (X : Strm) :
    Rch dag ⟨.root1, true ::: blank, app ((pcB m).tail ++ [x]) X⟩
      ⟨if x then .decL 0 else .incL 0, app (x :: (pcB m).reverse) blank, X⟩ := by
  have hp : ∀ n (L Y : Strm), Rch dag ⟨.b2s0, L, app (pairs n) Y⟩ ⟨.b2s0, app (pairs n).reverse L, Y⟩ := by
    intro n; induction n with
    | zero => intro L Y; exact Reach.refl _ _
    | succ n ih =>
      intro L Y
      show Rch dag ⟨.b2s0, L, true ::: false ::: app (pairs n) Y⟩ _
      gR; gR
      refine Rch.tr (ih _ _) (Rch.of_eq ?_)
      simp [pairs, app_append]
  simp only [pcB, List.tail_cons, List.append_assoc, List.singleton_append, List.cons_append,
    app_cons, app_append]
  gR
  refine Rch.tr (hp m _ _) ?_
  gR; gR
  cases x
  · gR; exact Rch.of_eq (by simp [pcB, app_append])
  · gR; exact Rch.of_eq (by simp [pcB, app_append])

theorem dok_tail (m : Nat) : DOK 6 (rpairs m ++ [false, true]) := by
  induction m with
  | zero => simp [DOK]
  | succ m ih => simp only [rpairs, List.cons_append, DOK]; exact Or.inr ih

theorem pcB_rev (m : Nat) : (pcB m).reverse = true :: true :: (rpairs m ++ [false, true]) := by
  simp [pcB, pairs_rev]

theorem dok_pcB (m : Nat) : DOK 6 (pcB m).reverse := by
  rw [pcB_rev]; simp only [DOK]; exact Or.inr (Or.inr (dok_tail m))

theorem dok_pcBx (m : Nat) (x : Bool) : DOK 6 (x :: (pcB m).reverse) := by
  cases x
  · show DOK 5 (pcB m).reverse
    rw [pcB_rev]; simp only [DOK]; exact Or.inr (Or.inr (dok_tail m))
  · exact Or.inr (dok_pcB m)

/-- `inc` of register 0 in boot2 -/
theorem incOpB (m v : Nat) (rest : List Nat) (hm : 2 * m + 9 ≤ G) :
    Rch dag (bootCfg m false (v :: rest)) (bootCfg m true ((v + 1) :: rest)) := by
  have hl := pcB_len m
  unfold bootCfg
  refine Rch.tr (walkB m false _) ?_
  simp only [Bool.false_eq_true, if_false]
  have hu : (pcB m ++ [false]).reverse = false :: (pcB m).reverse := by simp
  have h1 := phase1 (dag := dag) (G := G) (pcB m ++ [false]) (by rw [hu]; exact dok_pcBx m false) (.incL 0)
    rfl (v :: rest) (by simp; omega)
  rw [hu] at h1
  simp only [List.length_append, List.length_singleton] at h1
  refine Rch.tr h1 ?_
  have e1 : (pcB m ++ [false]).tail ++ [true, false] = ((pcB m).tail ++ [false]) ++ [true, false] := by
    simp [pcB]
  rw [e1, app_append]
  refine Rch.tr (walkB m false _) ?_
  simp only [Bool.false_eq_true, if_false, app_cons]
  gR
  have h2 := phase2Inc (dag := dag) [] rest v (by decide) (G - ((pcB m).length + 1) - 1) (by omega)
    (app (false :: (pcB m).reverse) blank)
  simp only [List.nil_append, List.length_nil] at h2
  refine Rch.tr h2 ?_
  have h3 := cleanup (dag := dag) (G := G) (pcB m) (dok_pcB m) (G - ((pcB m).length + 1) - 1) (by omega)
    (by omega) (by omega) ((v + 1) :: rest)
  refine Rch.tr (Rch.of_eq ?_) (Rch.tr h3 (Rch.of_eq ?_))
  · simp only [app_cons, RT]
    rw [show G + 1 - (G - ((pcB m).length + 1) - 1) - ((pcB m).length + 1) = 2 by omega]; rfl
  · rfl

end

section
variable {dag : Nat → Option (Ch × Ch)}

/-- the start of a boot2 `decnz` up to `6.break.0` on its bit -/
theorem decStartB (m v : Nat) (rest : List Nat) (hm : 2 * m + 9 ≤ G) :
    Rch dag (bootCfg m true ((v + 1) :: rest))
      (cfgL .brk0 (app (true :: (pcB m).reverse) blank)
        (false ::: false ::: app (rcells (G - ((pcB m).length + 1) - 1) (v :: (rest ++ [0]))) blank)) := by
  have hl := pcB_len m
  unfold bootCfg
  refine Rch.tr (walkB m true _) ?_
  simp only [if_true]
  have hu : (pcB m ++ [true]).reverse = true :: (pcB m).reverse := by simp
  have h1 := phase1 (dag := dag) (G := G) (pcB m ++ [true]) (by rw [hu]; exact dok_pcBx m true) (.decL 0)
    rfl ((v + 1) :: rest) (by simp; omega)
  rw [hu] at h1
  simp only [List.length_append, List.length_singleton] at h1
  refine Rch.tr h1 ?_
  have e1 : (pcB m ++ [true]).tail ++ [true, false] = ((pcB m).tail ++ [true]) ++ [true, false] := by
    simp [pcB]
  rw [e1, app_append]
  refine Rch.tr (walkB m true _) ?_
  simp only [if_true, app_cons]
  gR
  have h2 := phase2DecPos (dag := dag) [] rest v (by decide) (G - ((pcB m).length + 1) - 1) (by omega)
    (app (true :: (pcB m).reverse) blank)
  simp only [List.nil_append, List.length_nil] at h2
  exact h2

/-- `decnz` of register 0 in boot2: `1 1` moves two cells left, a register is appended -/
theorem decOpB (m v : Nat) (rest : List Nat) (hm : 2 * (m + 1) + 9 ≤ G) :
    Rch dag (bootCfg (m + 1) true ((v + 1) :: rest)) (bootCfg m false (v :: (rest ++ [0]))) := by
  have hl := pcB_len (m + 1)
  have hl' := pcB_len m
  have hp := pairs_len m
  refine Rch.tr (decStartB (m + 1) v rest hm) ?_
  rw [pcB_rev]
  show Rch dag (cfgL .brk0 (app (true :: true :: true :: false :: true :: (rpairs m ++ [false, true])) blank) _) _
  simp only [app_cons]
  gL; gL; gL
  -- now on the last pair's 0: clean up with the program counter `1 0 (10)^m 1`
  have hu : (true :: false :: (pairs m ++ [true])).reverse = true :: (rpairs m ++ [false, true]) := by
    simp [pairs_rev]
  have h3 := cleanup (dag := dag) (G := G) (true :: false :: (pairs m ++ [true])) (by rw [hu]; exact Or.inr (dok_tail m))
    (G - ((pcB (m + 1)).length + 1) - 1) (by omega) (by simp; omega) (by simp; omega) (v :: (rest ++ [0]))
  rw [hu] at h3
  refine Rch.tr (Rch.of_eq ?_) (Rch.tr h3 (Rch.of_eq ?_))
  · simp only [app_cons, RT]
    rw [show G + 1 - (G - ((pcB (m + 1)).length + 1) - 1) -
        ((true :: false :: (pairs m ++ [true])).length + 1) = 5 by simp; omega]
    rfl
  · unfold bootCfg
    have e : (true :: false :: (pairs m ++ [true])).tail ++ [true] = (pcB m).tail := by simp [pcB]
    have e2 : (true :: false :: (pairs m ++ [true])).length + 1 = (pcB m).length := by simp [pcB]
    rw [e, e2, app_append, app_cons, app_nil, ← RT_succ _ (by omega : 1 + (pcB m).length ≤ G)]

/-- the last `decnz`: the program counter is `1 1`, and main starts -/
theorem decOpB0 (v : Nat) (rest : List Nat) :
    Rch dag (bootCfg 0 true ((v + 1) :: rest)) (atNode G 0 [] false (v :: (rest ++ [0]))) := by
  refine Rch.tr (decStartB 0 v rest (by decide)) ?_
  rw [pcB_rev]
  show Rch dag (cfgL .brk0 (app [true, true, true, false, true] blank) _) _
  simp only [app_cons, app_nil]
  gL; gL; gL
  have h3 := cleanup (dag := dag) (G := G) [true] (by simp [DOK])
    (G - ((pcB 0).length + 1) - 1) (by decide) (by decide) (by decide) (v :: (rest ++ [0]))
  refine Rch.tr (Rch.of_eq ?_) (Rch.tr h3 ?_)
  · simp only [app_cons, app_nil, RT]
    rfl
  · show Rch dag ⟨.root1, true ::: blank, true ::: RT G 2 1 (v :: (rest ++ [0]))⟩ _
    gR
    rw [RT_succ _ (by decide : 1 + 2 ≤ G)]
    gR
    exact Rch.of_eq (by unfold atNode; rw [RT_succ _ (by decide : 1 + 3 ≤ G)]; rfl)

/-- 1908 pairs -/
theorem loopB : ∀ m n : Nat, 2 * m + 9 ≤ G →
    Rch dag (bootCfg m false (List.replicate (n + 1) 0)) (atNode G 0 [] false (List.replicate (n + m + 2) 0))
  | 0, n, _ => by
    refine Rch.tr (incOpB 0 0 (List.replicate n 0) (by decide)) ?_
    refine Rch.tr (decOpB0 0 (List.replicate n 0)) (Rch.of_eq ?_)
    have : 0 :: (List.replicate n 0 ++ [0]) = List.replicate (n + 0 + 2) 0 := by
      simp [List.replicate_succ, rep_cons]
    rw [this]
  | m + 1, n, hm => by
    refine Rch.tr (incOpB (m + 1) 0 (List.replicate n 0) hm) ?_
    refine Rch.tr (decOpB m 0 (List.replicate n 0) hm) ?_
    have : 0 :: (List.replicate n 0 ++ [0]) = List.replicate (n + 1 + 1) 0 := by
      simp [List.replicate_succ, rep_cons]
    rw [this]
    refine Rch.tr (loopB m (n + 1) (by omega)) (Rch.of_eq ?_)
    rw [show n + 1 + m + 2 = n + (m + 1) + 2 by omega]

theorem dok_rpairs (n : Nat) : DOK 6 (true :: rpairs n) := by
  induction n with
  | zero => simp [DOK, rpairs]
  | succ n ih =>
    simp only [rpairs, DOK]
    exact Or.inr (by simpa only [DOK] using ih)

/-- finishing boot1's last operation: register 0 is created, then boot2 starts -/
theorem firstOp :
    Rch dag ⟨.incL 0, true ::: app (rpairs 1909) blank, true ::: false ::: ones 4 blank⟩
      (bootCfg 1907 false [0]) := by
  have hp := pairs_len 1908
  gR
  have h2 := phase2IncEmpty (dag := dag) 4 (by decide) (true ::: app (rpairs 1909) blank)
  refine Rch.tr (Rch.of_eq rfl) (Rch.tr h2 ?_)
  · show Rch dag (cfgL .brk0 (true ::: false ::: true ::: app (rpairs 1908) blank) _) _
    gL
    have hu : (pairs 1908 ++ [true]).reverse = true :: rpairs 1908 := by simp [pairs_rev]
    have h3 := cleanup (dag := dag) (G := G) (pairs 1908 ++ [true]) (by rw [hu]; exact dok_rpairs 1908)
      4 (by decide) (by simp [hp]; decide) (by simp [hp]; decide) [0]
    rw [hu] at h3
    refine Rch.tr (Rch.of_eq ?_) (Rch.tr h3 (Rch.of_eq ?_))
    · simp only [app_cons, RT, List.length_append, hp, List.length_singleton]
      rfl
    · unfold bootCfg
      have h1908 : pairs 1908 = true :: false :: pairs 1907 := rfl
      have e : (pairs 1908 ++ [true]).tail ++ [true] = (pcB 1907).tail := by
        rw [h1908]; simp only [pcB, List.cons_append, List.tail_cons, List.append_assoc, List.singleton_append,
          List.nil_append]
      have e2 : (pairs 1908 ++ [true]).length + 1 = (pcB 1907).length := by
        rw [pcB_len, List.length_append, pairs_len]; rfl
      rw [e, e2, app_append, app_cons, app_nil, ← RT_succ _ (by rw [pcB_len]; decide)]

/-- the boot: from the blank tape to the start of main with 1909 zero registers -/
theorem boot : Rch dag ⟨.bA, blank, blank⟩ (atNode G 0 [] false (List.replicate 1909 0)) :=
  Rch.tr boot1 (Rch.tr firstOp (loopB 1907 0 (by decide)))

end

end TM.PA

