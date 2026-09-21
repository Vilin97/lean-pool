/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormQuotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.MathlibInterface
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
/-!
# Quotient form of finite abelian local reciprocity

This module states the quotient formulation of local reciprocity for a
finite abelian extension `L / K` of a nonarchimedean local field.  Under the
finite-dimensional, abelian-Galois, valuative, and topological assumptions,
the conclusion identifies `Kˣ / N_{L/K}(Lˣ)` with the ordinary Galois group
by a continuous multiplicative equivalence.
-/

noncomputable section

namespace ClassFieldTheory

/-- The field-norm quotient is continuously multiplicatively equivalent to
the finite abelian Galois group. -/
theorem finiteAbelianLocalReciprocity_quotient
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Nonempty
      (FieldNormQuotient K L ≃ₜ* (L ≃ₐ[K] L)) := by
  exact LocalCFT.finiteAbelianLocalReciprocity_quotient K L

end ClassFieldTheory
