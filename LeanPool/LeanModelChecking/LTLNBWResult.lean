/-
Copyright (c) 2026 György Kurucz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: György Kurucz
-/
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Powerset

import LeanPool.LeanModelChecking.LTLNBWStatement
import LeanPool.LeanModelChecking.LTLNNF
import LeanPool.LeanModelChecking.NNFABW
import LeanPool.LeanModelChecking.ABWNBW

/-!
# Every LTL formula has an equivalent finite-state Büchi automaton

We assemble the translations `LTL → NNF → ABW → NBW` to conclude that for any
linear temporal logic formula there is an equivalent finite-state
nondeterministic Büchi automaton accepting the same language. Finiteness comes
from the construction: the alternating automaton's states are subformulas of
the (negation normal form of the) input formula, and the Miyano–Hayashi
breakpoint construction squares that state space to pairs of subsets.
-/

namespace LeanModelChecking

theorem for_any_LTL_formula_exists_an_equivalent_NBW :
    forAnyLTLFormulaExistsAnEquivalentNBWStatement := by
  unfold forAnyLTLFormulaExistsAnEquivalentNBWStatement
  intros _ φ
  obtain ⟨Q, qfin, A, lang_eq⟩ := exists_ABW_lang_for_LTL φ
  exists A.toNBW
  constructor
  · haveI := qfin
    exact inferInstanceAs (Finite ((Set Q) × (Set Q)))
  · rw [lang_eq, ABW.toNBW.lang_eq]

end LeanModelChecking
