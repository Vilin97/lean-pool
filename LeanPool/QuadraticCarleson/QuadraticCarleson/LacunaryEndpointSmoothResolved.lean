/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodBoundaryControl
import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertMaximalWeakResolved
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySmoothSparseClosure
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseDilation

/-!
# Lacunary endpoint with only the smooth sparse input remaining

This module combines the unconditional ordinary Hilbert maximal theorem with
the smooth Krause--Lacey adapter.  Thus the displayed theorem has exactly one
analytic input: the genuine uniform finite-radius smooth sparse estimate.
-/

open MeasureTheory
open scoped ENNReal

namespace QuadraticCarleson.LacunaryEndpointSmoothResolved

open QuadraticHilbertMaximalMeasurable
open HardyLittlewoodBoundaryControl
open PositivePrincipalValueEndpoints
open KrauseLaceySparseDilation


/-- The paper-facing lacunary principal-value endpoint, conditional only on
the genuine smooth Krause--Lacey sparse estimate.  The ordinary Hilbert
maximal input has already been discharged unconditionally. -/
theorem lacunary_principalValue_endpoint_of_smoothSparse
    {A : ℝ} (hA : HasUniformFiniteRadiusSmoothSparseBound A) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ alpha : ℝ, 0 < alpha →
        volume {x | ENNReal.ofReal alpha < lacunaryPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / alpha) * paperLog 2 (‖f x‖ / alpha) ^ 2 *
              paperLog 4 (‖f x‖ / alpha)) :=
  HilbertMaximalWeakResolved.lacunary_principalValue_endpoint
    (hasUniformL0LogSquaredFrozenBlockWeakBounds_of_smoothSparse hA)

/-- The same endpoint reduced all the way to uniform sparse domination of the
finite positive dyadic suffix maxima used in the Krause--Lacey proof. -/
theorem lacunary_principalValue_endpoint_of_positiveSuffix
    {A : ℝ} (hA : HasUniformPositiveSuffixSmoothSparseBound A) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ alpha : ℝ, 0 < alpha →
        volume {x | ENNReal.ofReal alpha < lacunaryPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / alpha) * paperLog 2 (‖f x‖ / alpha) ^ 2 *
              paperLog 4 (‖f x‖ / alpha)) :=
  lacunary_principalValue_endpoint_of_smoothSparse
    (hasUniformFiniteRadiusSmoothSparseBound_of_positiveSuffix hA)

/-- The paper-facing endpoint reduced to the exact unit-modulation analytic
input needed after the proved dilation and conjugation reductions: sparse
domination for a common positive scale offset of each rounded dyadic family. -/
theorem lacunary_principalValue_endpoint_of_unitScaleOffset
    {A : ℝ}
    (hA : HasUnitScaleOffsetSmoothSparseBound A) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ alpha : ℝ, 0 < alpha →
        volume {x | ENNReal.ofReal alpha < lacunaryPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / alpha) * paperLog 2 (‖f x‖ / alpha) ^ 2 *
              paperLog 4 (‖f x‖ / alpha)) :=
  lacunary_principalValue_endpoint_of_smoothSparse
    (hasUniformFiniteRadiusSmoothSparseBound_of_unit_scaleOffset hA)


end QuadraticCarleson.LacunaryEndpointSmoothResolved
