/-
Copyright (c) 2026 György Kurucz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: György Kurucz
-/
import LeanPool.LeanModelChecking.LTLNBWStatement
import LeanPool.LeanModelChecking.LTLNNF
import LeanPool.LeanModelChecking.NNFABW
import LeanPool.LeanModelChecking.ABWNBW

/-!
# Every LTL formula has an equivalent Büchi automaton

We assemble the translations `LTL → NNF → ABW → NBW` to conclude that for any
linear temporal logic formula there is an equivalent nondeterministic Büchi
automaton accepting the same language.
-/

namespace LeanModelChecking

theorem for_any_LTL_formula_exists_an_equivalent_NBW :
    forAnyLTLFormulaExistsAnEquivalentNBWStatement := by
  unfold forAnyLTLFormulaExistsAnEquivalentNBWStatement
  intros _ φ
  obtain ⟨_, _, A, lang_eq⟩ := exists_ABW_lang_for_LTL φ
  exists A.toNBW
  rw [lang_eq]
  rw [ABW.toNBW.lang_eq]

end LeanModelChecking
