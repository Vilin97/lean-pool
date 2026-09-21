/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.OpenFiniteIndexSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.MathlibInterface
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkLocalClassification
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Order.Hom.Basic
/-!
# Order classification in finite abelian local existence

This module states the classification form of local existence for a
nonarchimedean local field `K`.  Finite abelian intermediate fields of
`SeparableClosure K` are ordered by field inclusion, whereas open
finite-index subgroups of `Kˣ` are ordered contravariantly.  The statement
also records that the order isomorphism sends each extension to its actual
field-norm subgroup.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- Finite abelian local extensions correspond contravariantly to open
finite-index norm subgroups. -/
theorem finiteAbelianLocalExistence_orderIso
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
  ∃ e : FiniteAbelianLocalExtension K ≃o
        (OpenFiniteIndexSubgroup K)ᵒᵈ,
      ∀ E : FiniteAbelianLocalExtension K,
        (OrderDual.ofDual (e E)).1 = E.normSubgroup := by
  exact ⟨LocalFieldTheory.shrinkFiniteAbelianFieldNormSubgroupOrderIso K,
    LocalFieldTheory.shrinkFiniteAbelianFieldNormSubgroupOrderIso_apply K⟩

end ClassFieldTheory
