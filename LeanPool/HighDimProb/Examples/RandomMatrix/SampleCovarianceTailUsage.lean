/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix.ConcentrationStatements

/-!
# Sample covariance tail wrapper usage examples

This examples-only file shows the compact bounded-row sample-covariance tail
route and the lower-level exact-row centered-square bridge route. The compact
route remains the preferred reader-facing surface through
`SampleCovarianceBoundedRowTroppAssumptions`; the exact-row centered-square
examples show how bridge-layer infrastructure feeds the sample-covariance
wrappers without making those bridge bundles the default user entry point.
-/

namespace HighDimProb.Examples.RandomMatrix.SampleCovarianceTailUsage

open MeasureTheory

noncomputable section

/-- The quadratic-form specialization of the compact bounded-row route.

This example intentionally uses the same core route record as the operator-norm
example below. Users who only need the positive-side quadratic-form theorem with
fewer assumptions can still call the lower-level wrapper directly. -/
theorem sampleCovariance_quadraticForm_tail_usage
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R Rneg t : Real)
    (h : SampleCovarianceBoundedRowTroppAssumptions (P := P) A R Rneg t) :
    P (quadraticFormUpperTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
        (m := m) (n := n + 1) R t
        (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R) := by
  simpa [SampleCovarianceTailTarget.event, SampleCovarianceTailTarget.rhs] using
    sampleCovariance_tail_optimized_under_boundedRowTroppAssumptions
      (P := P) A R Rneg t SampleCovarianceTailTarget.quadraticFormUpper h

/-- Example-level exact-row centered-square-chain quadratic-form tail usage.

This demonstrates the core assumption bundle
`SampleCovarianceExactRowCenteredSquareTroppAssumptions` directly, rather than
copying its long field list into an example-local structure. This is a
bridge-layer example: the generic centered-square chain, Tropp primitive, and
analytic assumptions remain fields of that core bundle. -/
theorem sampleCovariance_exactRow_centeredSquare_quadraticForm_tail_usage
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R t : Real)
    (Rvar : Fin m -> Real)
    (h : SampleCovarianceExactRowCenteredSquareTroppAssumptions
      (P := P) A R t Rvar) :
    P (quadraticFormUpperTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
        (m := m) (n := n + 1) R t
        (rowSqNormVarianceProxyNormRHS Rvar) := by
  exact
    sampleCovariance_quadraticForm_tail_exactRowSqNorm_centeredSquareChain_troppAssumptions
      (P := P) A R t Rvar h

/-- The self-adjoint operator-norm specialization of the compact bounded-row route. -/
theorem sampleCovariance_operatorNorm_tail_usage
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R Rneg t : Real)
    (h : SampleCovarianceBoundedRowTroppAssumptions (P := P) A R Rneg t) :
    P (SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n + 1) R t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) R) +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n + 1) Rneg t
          (sampleCovarianceCenteredRankOneVarianceProxyBound (m := m) Rneg) := by
  simpa [SampleCovarianceTailTarget.event, SampleCovarianceTailTarget.rhs] using
    sampleCovariance_tail_optimized_under_boundedRowTroppAssumptions
      (P := P) A R Rneg t SampleCovarianceTailTarget.selfAdjointOperatorNorm h

/-- Example-level exact-row centered-square-chain operator-norm tail usage.

This demonstrates the two-sided core bundle
`SampleCovarianceExactRowCenteredSquareTwoSidedTroppAssumptions`. It adds no
new mathematics; it routes bridge-layer assumptions to the public wrapper. -/
theorem sampleCovariance_exactRow_centeredSquare_operatorNorm_tail_usage
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {m n : Nat}
    (A : RandomMatrix Omega m (n + 1))
    (R Rneg t : Real)
    (Rvar RvarNeg : Fin m -> Real)
    (h : SampleCovarianceExactRowCenteredSquareTwoSidedTroppAssumptions
      (P := P) A R Rneg t Rvar RvarNeg) :
    P (SelfAdjointOperatorNormTailEvent
        (centeredRandomMatrix P (sampleCovariance A)) t) <=
      sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n + 1) R t (rowSqNormVarianceProxyNormRHS Rvar) +
        sampleCovarianceQuadraticFormTailRHS
          (m := m) (n := n + 1) Rneg t
          (rowSqNormVarianceProxyNormRHS RvarNeg) := by
  exact
    sampleCovariance_opNorm_tail_pos_exactRowSqNorm_negSquare_centeredSquare_troppAssumptions
      (P := P) A R Rneg t Rvar RvarNeg h

end

end HighDimProb.Examples.RandomMatrix.SampleCovarianceTailUsage
