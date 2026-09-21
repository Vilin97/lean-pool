/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.OpenFiniteIndexSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalExistenceOrderIso
/-!
# Finite abelian local existence

This module states the existence half of finite abelian local class field
theory.  Both sides of the correspondence are expressed directly with
Mathlib objects: intermediate fields of `SeparableClosure K` and subgroups
of `Kˣ`.  No implementation-specific class-formation object appears in the
statement.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- Every open finite-index subgroup of `Kˣ` is the norm subgroup of a
finite abelian subextension. -/
theorem finiteAbelianLocalExistence
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∀ H : OpenFiniteIndexSubgroup K,
      ∃ E : FiniteAbelianLocalExtension K,
        E.normSubgroup = H.1 := by
  obtain ⟨e, he⟩ := finiteAbelianLocalExistence_orderIso K
  intro H
  refine ⟨e.symm (OrderDual.toDual H), ?_⟩
  have h := he (e.symm (OrderDual.toDual H))
  rw [e.apply_symm_apply] at h
  exact h.symm

end ClassFieldTheory
