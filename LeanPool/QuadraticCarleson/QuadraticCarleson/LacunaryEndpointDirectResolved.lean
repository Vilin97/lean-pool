/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryFrozenBlockDirectResolved
import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertMaximalWeakResolved

/-!
# Unconditional lacunary principal-value endpoint

The direct quadratic one-node proof, finite full-odd high suffix sparse bound,
and exact frozen-block comparison discharge the last analytic input of the
paper-facing endpoint. The theorem statement is the existing principal-value
endpoint statement with its proved hypothesis supplied, not a modified bound.
-/

open MeasureTheory
open scoped ENNReal

namespace QuadraticCarleson.LacunaryEndpointDirectResolved

open PositivePrincipalValueEndpoints


/-- The sharper lacunary modular bound, including simultaneous existence of
the genuine principal values, with no outstanding analytic hypothesis. -/
theorem lacunary_principalValue_endpoint :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ α : ℝ, 0 < α →
        volume {x | ENNReal.ofReal α < lacunaryPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) :=
  HilbertMaximalWeakResolved.lacunary_principalValue_endpoint
    LacunaryFrozenBlockDirectResolved.hasUniformL0LogSquaredFrozenBlockWeakBounds


end QuadraticCarleson.LacunaryEndpointDirectResolved
