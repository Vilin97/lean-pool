/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.IsFieldNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.MathlibInterface
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
/-!
# Finite abelian local reciprocity

This module states local reciprocity for a finite abelian extension `L / K`
of a nonarchimedean local field.  The assumptions provide the finite
abelian-Galois extension together with the valuative topology on `K`.  The
conclusion supplies a surjective continuous homomorphism from `Kˣ` to the
Galois group whose kernel consists exactly of nonzero field norms from `L`.

This finite quotient statement deliberately leaves the usual uniformizer
normalization and tower functoriality to separate compatibility theorems; it
does not claim that the displayed witness is uniquely determined.
-/

noncomputable section

namespace ClassFieldTheory

/-- A finite abelian local extension has a surjective continuous Artin map
whose kernel is its field-norm subgroup. -/
theorem finiteAbelianLocalReciprocity
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ artin : Kˣ →ₜ* (L ≃ₐ[K] L),
      Function.Surjective artin ∧
      ∀ x : Kˣ, artin x = 1 ↔ IsFieldNorm K L x := by
  exact LocalCFT.finiteAbelianLocalReciprocity K L

end ClassFieldTheory
