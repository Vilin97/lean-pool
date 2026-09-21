/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.IsSepClosed
/-!
# Finite abelian local extensions
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- A finite abelian extension of `K` inside Mathlib's chosen separable
closure.  The inherited order is field inclusion. -/
abbrev FiniteAbelianLocalExtension
    (K : Type u) [Field K] :=
  { E : IntermediateField K (SeparableClosure K) //
      FiniteDimensional K E ∧ IsAbelianGalois K E }

namespace FiniteAbelianLocalExtension

variable {K : Type u} [Field K]

/-- The packaged intermediate field is finite-dimensional over the base. -/
instance finiteDimensional (E : FiniteAbelianLocalExtension K) :
    FiniteDimensional K E.1 :=
  E.2.1

/-- The packaged intermediate field is abelian Galois over the base. -/
instance isAbelianGalois (E : FiniteAbelianLocalExtension K) :
    IsAbelianGalois K E.1 :=
  E.2.2

/-- The norm subgroup belonging to a packaged finite abelian extension. -/
def normSubgroup (E : FiniteAbelianLocalExtension K) : Subgroup Kˣ :=
  fieldNormSubgroup K E.1

end FiniteAbelianLocalExtension

end ClassFieldTheory
