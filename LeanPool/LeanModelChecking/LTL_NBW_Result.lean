/-
Copyright (c) 2026 György Kurucz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: György Kurucz
-/
import LeanPool.LeanModelChecking.LTL_NBW_Statement
import LeanPool.LeanModelChecking.LTL_NNF
import LeanPool.LeanModelChecking.NNF_ABW
import LeanPool.LeanModelChecking.ABW_NBW

theorem for_any_LTL_formula_exists_an_equivalent_NBW : for_any_LTL_formula_exists_an_equivalent_NBW_statement := by
  unfold for_any_LTL_formula_exists_an_equivalent_NBW_statement
  intros _ φ
  obtain ⟨_, _, A, lang_eq⟩ := exists_ABW_lang_for_LTL φ
  exists A.toNBW
  rw [lang_eq]
  rw [ABW.toNBW.lang_eq]
