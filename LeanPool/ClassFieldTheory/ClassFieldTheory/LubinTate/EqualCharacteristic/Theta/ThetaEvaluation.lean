/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CompletedUnramifiedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaSeries
/-!
# Analytic evaluation for theta

The theta series of the completed theta-intertwining theorem has coefficients in
`(AlgebraicClosure k)[[T]]`.  This file evaluates it at a topologically
nilpotent element of the valued integer ring of the completed unramified
Laurent field.  The value is accompanied by its convergent coefficient sum,
and the formal intertwining identity is transported through this genuine
analytic evaluation map.
-/

noncomputable section

open scoped LaurentSeries PowerSeries PowerSeries.WithPiTopology Topology Valued WithZero


universe u

namespace LubinTate
namespace EqualCharacteristic

variable (k : Type u) [Field k] [Finite k]

omit [Finite k] in
noncomputable local instance equalCharacteristicThetaEvaluationCoefficientUniformSpace :
    UniformSpace (AlgebraicClosure k) := ⊥

noncomputable local instance equalCharacteristicThetaEvaluationLinearTopology :
    IsLinearTopology
      (Valued.integer (equalCharacteristicCompletedUnramifiedField k))
      (Valued.integer (equalCharacteristicCompletedUnramifiedField k)) :=
  valuedIntegerLinearTopology

noncomputable local instance equalCharacteristicThetaEvaluationCompleteSpace :
    CompleteSpace
      (Valued.integer (equalCharacteristicCompletedUnramifiedField k)) :=
  valuedIntegerCompleteSpace

noncomputable local instance equalCharacteristicThetaEvaluationUniformAddGroup :
    IsUniformAddGroup
      (Valued.integer (equalCharacteristicCompletedUnramifiedField k)) :=
  valuedIntegerIsUniformAddGroup

/-- The analytic value of the theta series at a topologically nilpotent
element of the completed-unramified integer ring. -/
noncomputable def equalCharacteristicCompletedThetaValue
    (u : k⟦X⟧ˣ)
    (a : Valued.integer (equalCharacteristicCompletedUnramifiedField k))
    (ha : PowerSeries.HasEval a) :
    Valued.integer (equalCharacteristicCompletedUnramifiedField k) :=
  equalCharacteristicCompletedIntegerEvaluation k a ha
    (equalCharacteristicThetaSeries u)

/-- The defining coefficient series for the analytic theta value converges.
This records every natural degree, including the zero coefficients away from
the additive exponents `q^j`. -/
theorem equalCharacteristicCompletedThetaValue_hasSum
    (u : k⟦X⟧ˣ)
    (a : Valued.integer (equalCharacteristicCompletedUnramifiedField k))
    (ha : PowerSeries.HasEval a) :
    HasSum
      (fun n : ℕ ↦
        equalCharacteristicPowerSeriesToCompletedInteger k
            (PowerSeries.coeff n (equalCharacteristicThetaSeries u)) *
          a ^ n)
      (equalCharacteristicCompletedThetaValue k u a ha) := by
  rw [equalCharacteristicCompletedThetaValue,
    equalCharacteristicCompletedIntegerEvaluation,
    PowerSeries.coe_eval₂Hom]
  exact PowerSeries.hasSum_eval₂
    (equalCharacteristicPowerSeriesToCompletedInteger_continuous k)
    ha (equalCharacteristicThetaSeries u)

/-- Analytic evaluation of the theta intertwining identity.  The right-hand
formal composition is evaluated explicitly as
`theta(a)^q + T * theta(a)` in the completed-unramified integer ring. -/
theorem equalCharacteristicThetaSeries_intertwines_evaluated
    (u : k⟦X⟧ˣ)
    (a : Valued.integer (equalCharacteristicCompletedUnramifiedField k))
    (ha : PowerSeries.HasEval a) :
    equalCharacteristicCompletedIntegerEvaluation k a ha
        (PowerSeries.subst
          (equalCharacteristicCompletedLubinTateSeries (k := k)
            (equalCharacteristicCompletedSourceUniformizer u))
          (equalCharacteristicThetaSeriesFrobenius u)) =
      equalCharacteristicCompletedThetaValue k u a ha ^ Nat.card k +
        equalCharacteristicCompletedIntegerUniformizer k *
          equalCharacteristicCompletedThetaValue k u a ha := by
  rw [equalCharacteristicThetaSeries_intertwines u]
  have htheta := equalCharacteristicThetaSeries_hasSubst u
  rw [equalCharacteristicCompletedLubinTateSeries,
    ← PowerSeries.smul_eq_C_mul,
    PowerSeries.subst_add htheta,
    PowerSeries.subst_pow htheta,
    PowerSeries.subst_smul htheta,
    PowerSeries.subst_X htheta,
    PowerSeries.smul_eq_C_mul]
  simp only [map_add, map_pow, map_mul,
    equalCharacteristicCompletedIntegerEvaluation_C,
    equalCharacteristicCompletedThetaValue,
    equalCharacteristicCompletedIntegerUniformizer]

end EqualCharacteristic
end LubinTate
