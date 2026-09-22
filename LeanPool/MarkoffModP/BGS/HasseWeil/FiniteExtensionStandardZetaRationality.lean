/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZetaNumeratorNoncancellation
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionIndexedZetaRationalityAutomatic
import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaRationalityDegree
import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaTrace

/-!
# Standard zeta rationality after proving degree index one

This file packages the exact downstream consequence of F. K. Schmidt's
degree-index theorem.  Once the exhaustive divisor-degree index is one, the
automatic indexed zeta rational form becomes the standard curve denominator
`(1 - T) (1 - qT)`.  The Riemann--Roch construction also retains a concrete
numerator-degree bound and numerator noncancellation at `T = 1`.
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

local instance standardZetaConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance standardZetaConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) standardZetaPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance standardZetaPolynomialTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance standardZetaConstantPolynomialTower :
    IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- An indexed zeta rational form with index one is exactly a standard curve
zeta rational form. -/
theorem hasCurveZetaRationalForm_of_indexed_index_one
    (Z : PowerSeries ℂ) (q : ℕ) (P : Polynomial ℂ)
    (hindexed : HasIndexedCurveZetaRationalForm Z q 1 P) :
    HasCurveZetaRationalForm Z q P := by
  simpa [HasIndexedCurveZetaRationalForm, indexedCurveZetaDenominator,
    HasCurveZetaRationalForm, curveZetaDenominator, linearPowerSeriesFactor]
    using hindexed

/-- Uniform Riemann--Roch and degree index one give a normalized standard
zeta numerator.  Its degree is bounded by the same truncation length used in
the indexed recurrence, and its value at `T = 1` is nonzero. -/
theorem exists_finiteExtensionClosedPlaceZeta_rational_with_natDegree_lt_of_uniformRiemann
    (genus threshold : ℕ)
    (hconstants : algebraicClosure K L =
      (⊥ : IntermediateField K L))
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold)
    (hindex : finiteExtensionDivisorDegreeIndex K L = 1) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧
        P.eval 1 ≠ 0 ∧
        P.natDegree < threshold + 2 ∧
        HasCurveZetaRationalForm
          (formalPointCountZeta
            (finiteExtensionClosedPlaceExtensionCount K L))
          (Nat.card K) P := by
  obtain ⟨P, hPzero, hPdegree, hPindexed⟩ :=
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
  have hPone : P.eval 1 ≠ 0 :=
    finiteExtensionClosedPlaceZeta_indexedNumerator_eval_one_ne_zero_of_uniformRiemann
      K L genus threshold hconstants hRiemann P hPindexed
  have hPdegree' : P.natDegree < threshold + 2 := by
    simpa [hindex] using hPdegree
  have hPstandard :
      HasCurveZetaRationalForm
        (formalPointCountZeta
          (finiteExtensionClosedPlaceExtensionCount K L))
        (Nat.card K) P := by
    rw [hindex] at hPindexed
    exact hasCurveZetaRationalForm_of_indexed_index_one _ _ _ hPindexed
  exact ⟨P, hPzero, hPone, hPdegree', hPstandard⟩

/-- Exact constants and degree index one give the standard curve zeta form
with numerator degree strictly below `2g + 2`, where `g` is the transported
function-field genus. -/
theorem exists_finiteExtensionClosedPlaceZeta_rational_with_genus_degree_bound
    (hconstants : algebraicClosure K L =
      (⊥ : IntermediateField K L))
    (hindex : finiteExtensionDivisorDegreeIndex K L = 1) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧
        P.eval 1 ≠ 0 ∧
        P.natDegree < 2 * FunctionField.genus K L + 2 ∧
        HasCurveZetaRationalForm
          (formalPointCountZeta
            (finiteExtensionClosedPlaceExtensionCount K L))
          (Nat.card K) P := by
  let : FunctionField.IsFullConstantField K L :=
    (FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot K L).2
      hconstants
  simpa only [FunctionField.genus_eq_genusChart K L] using
    exists_finiteExtensionClosedPlaceZeta_rational_with_natDegree_lt_of_uniformRiemann
      K L (FunctionField.Chart.genus K L)
        (2 * FunctionField.Chart.genus K L) hconstants
        (hasFiniteExtensionUniformEventualRiemannFormula_of_fullConstantField K L)
        hindex

/-- If the intrinsic genus is at most `budget`, the standard numerator has at
most `2 * budget + 1` reciprocal roots.  The same polynomial carries the
formal extension point-count trace formula. -/
theorem exists_finiteExtensionClosedPlaceZeta_trace_with_degree_budget
    (budget : ℕ)
    (hconstants : algebraicClosure K L =
      (⊥ : IntermediateField K L))
    (hindex : finiteExtensionDivisorDegreeIndex K L = 1)
    (hgenus : FunctionField.genus K L ≤ budget) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧
        P.eval 1 ≠ 0 ∧
        P.natDegree ≤ 2 * budget + 1 ∧
        HasCurveZetaRationalForm
          (formalPointCountZeta
            (finiteExtensionClosedPlaceExtensionCount K L))
          (Nat.card K) P ∧
        HasZetaNumeratorPointCountFormula
          (Nat.card K)
          (finiteExtensionClosedPlaceExtensionCount K L) P := by
  obtain ⟨P, hPzero, hPone, hPdegree, hPform⟩ :=
    exists_finiteExtensionClosedPlaceZeta_rational_with_genus_degree_bound
      K L hconstants hindex
  have hdegreeBudget : P.natDegree ≤ 2 * budget + 1 := by
    omega
  exact ⟨P, hPzero, hPone, hdegreeBudget, hPform,
    hasZetaNumeratorPointCountFormula_of_formalPointCountZeta_rational
      (Nat.card K) (finiteExtensionClosedPlaceExtensionCount K L)
        P hPzero hPform⟩

end

end BGS.HasseWeil
