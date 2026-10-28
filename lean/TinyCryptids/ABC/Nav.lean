import TinyCryptids.ABC.Tac
import TinyCryptids.ABC.Blocks

/-! Parsers with their `found` step, and list facts used to apply them. -/

namespace TM.ABC
open St

local notation "F" => false
local notation "T" => true

theorem pRR {p1 p2 q : St} (P : ParserR deltaQ p1 p2) (hf : deltaQ p2 true = some (true, Dir.R, q))
    {w : List Bool} (hw : Clean w) (L R : Strm) :
    Rch ⟨p1, L, app w (F ::: T ::: R)⟩ ⟨q, T ::: F ::: app w.reverse L, R⟩ :=
  Rch.tr (P.find hw L R) (sR hf)

theorem pRL {p1 p2 q : St} (P : ParserR deltaQ p1 p2) (hf : deltaQ p2 true = some (true, Dir.L, q))
    {w : List Bool} (hw : Clean w) (L R : Strm) :
    Rch ⟨p1, L, app w (F ::: T ::: R)⟩ ⟨q, app w.reverse L, F ::: T ::: R⟩ :=
  Rch.tr (P.find hw L R) (stepL (δ := deltaQ) hf)

theorem pLR {p1 p2 q : St} (P : ParserL deltaQ p1 p2) (hf : deltaQ p2 true = some (true, Dir.R, q))
    {w : List Bool} (hw : Clean w) (s R : Strm) :
    Rch (cfgL p1 (app w (F ::: T ::: s)) R) ⟨q, T ::: s, F ::: app w.reverse R⟩ :=
  Rch.tr (P.find hw s R) (sR hf)

theorem pLL {p1 p2 q : St} (P : ParserL deltaQ p1 p2) (hf : deltaQ p2 true = some (true, Dir.L, q))
    {w : List Bool} (hw : Clean w) (s R : Strm) :
    Rch (cfgL p1 (app w (F ::: T ::: s)) R) (cfgL q s (T ::: F ::: app w.reverse R)) :=
  Rch.tr (P.find hw s R) (sL hf)

/-! ## clean lists -/

theorem Clean.rep_gap {g : List Bool} (hg : Gap g) (n : Nat) {m : List Bool} (hm : Clean m) :
    Clean (List.replicate n T ++ (g ++ T :: m)) :=
  Clean.rep_append n (hg.clean hm)

theorem Gap.join {g h : List Bool} (hg : Gap g) (hh : Gap h) (v : Nat) :
    Gap (g ++ List.replicate (v + 1) T ++ h) := by
  rcases hg with rfl | ⟨P, hP, rfl⟩ <;> rcases hh with rfl | ⟨Q, hQ, rfl⟩
  · exact Or.inr ⟨List.replicate (v + 1) T, Blk.one v, by simp⟩
  · exact Or.inr ⟨List.replicate (v + 1) T ++ F :: F :: Q, Blk.cons v hQ, by simp⟩
  · exact Or.inr ⟨P ++ F :: F :: List.replicate (v + 1) T, hP.join (Blk.one v), by simp⟩
  · exact Or.inr ⟨P ++ F :: F :: (List.replicate (v + 1) T ++ F :: F :: Q),
      hP.join (Blk.cons v hQ), by simp⟩

end TM.ABC
