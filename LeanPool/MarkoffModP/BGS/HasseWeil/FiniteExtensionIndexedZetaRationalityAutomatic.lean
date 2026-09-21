/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionIndexedZetaRationality
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannRoch
import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaEulerDegree

/-!
# Unconditional indexed zeta rationality from exact constants

This file discharges the uniform Riemann--Roch premise of the indexed zeta
composition by transporting the vendored Riemann--Roch theorem to the
exhaustive BGS divisor model.
-/

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open scoped Polynomial

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance automaticIndexedZetaConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance automaticIndexedZetaConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) automaticIndexedZetaPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance automaticIndexedZetaPolynomialTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance automaticIndexedZetaConstantPolynomialTower :
    IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Exact constants alone supply the indexed rational form of the exhaustive
closed-place zeta series. -/
theorem exists_finiteExtensionClosedPlaceZeta_indexed_rational_of_constants
    (hconstants : algebraicClosure K L =
      (⊥ : IntermediateField K L)) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧
        HasIndexedCurveZetaRationalForm
          (formalPointCountZeta
            (finiteExtensionClosedPlaceExtensionCount K L))
          (Nat.card K) (finiteExtensionDivisorDegreeIndex K L) P := by
  letI : FunctionField.IsFullConstantField K L :=
    (FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot K L).2
      hconstants
  exact exists_finiteExtensionClosedPlaceZeta_indexed_rational
    K L (FunctionField.Chart.genus K L)
      (2 * FunctionField.Chart.genus K L) hconstants
      (hasFiniteExtensionUniformEventualRiemannFormula_of_fullConstantField K L)

/-- The same automatic composition retains the truncation bound on the
indexed numerator. -/
theorem exists_finiteExtensionClosedPlaceZeta_indexed_rational_with_natDegree_lt_of_constants
    (hconstants : algebraicClosure K L =
      (⊥ : IntermediateField K L)) :
    ∃ (genus threshold : ℕ) (P : Polynomial ℂ),
      HasFiniteExtensionUniformEventualRiemannFormula
          K L genus threshold ∧
        P.coeff 0 = 1 ∧
        P.natDegree <
          threshold + 2 * finiteExtensionDivisorDegreeIndex K L ∧
        HasIndexedCurveZetaRationalForm
          (formalPointCountZeta
            (finiteExtensionClosedPlaceExtensionCount K L))
          (Nat.card K) (finiteExtensionDivisorDegreeIndex K L) P := by
  obtain ⟨genus, threshold, hRiemann⟩ :=
    exists_hasFiniteExtensionUniformEventualRiemannFormula_of_constants
      K L hconstants
  obtain ⟨P, hP0, hPdegree, hP⟩ :=
    exists_formalPointCountZeta_indexed_rational_with_natDegree_lt_of_effectiveDivisor_recurrences
      (finiteExtensionEffectiveDivisorCount K L)
      (finiteExtensionClosedPlaceExtensionCount K L)
      (Nat.card K) (finiteExtensionDivisorDegreeIndex K L)
      threshold
      (finiteExtensionDivisorDegreeIndex_pos K L)
      (finiteExtensionEffectiveDivisorCount_zero K L)
      (finiteExtensionEffectiveDivisorPointCountRecurrence K L)
      (fun n hn =>
        finiteExtensionEffectiveDivisorCount_indexed_eventual_recurrence_complex
          K L genus threshold n hconstants hRiemann hn)
  exact ⟨genus, threshold, P, hRiemann, hP0, hPdegree, hP⟩

end

end BGS.HasseWeil
