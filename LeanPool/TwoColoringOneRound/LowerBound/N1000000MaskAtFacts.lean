/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Polyrith
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000StructureConstants

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000MaskAtFacts
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000MaskAtFacts

open Distributed2Coloring.LowerBound.N1000000StructureConstants

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Mask := Distributed2Coloring.LowerBound.Mask
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev DirIdx := N1000000StructureConstants.DirIdx

theorem maskAt_testBit_eq_decide_colMatch (d : DirIdx) (i j : Fin 3) :
    (maskAt d).testBit (i.1 * 3 + j.1) = decide (colMatch (maskAt d) j = some i) := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;> decide

theorem maskAt_testBit_eq_decide_rowMatch (d : DirIdx) (i j : Fin 3) :
    (maskAt d).testBit (i.1 * 3 + j.1) = decide (rowMatch (maskAt d) i = some j) := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;> decide

end N1000000MaskAtFacts

end Distributed2Coloring.LowerBound

