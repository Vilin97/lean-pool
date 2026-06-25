/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Examples.RandomMatrix.GradientCovarianceUsage

/-!
# Empirical Fisher operator-norm usage

This examples-only file packages the empirical Fisher / mini-batch gradient
covariance use case for the current self-adjoint operator-norm Matrix Bernstein
route. It reuses the gradient rank-one vocabulary from
`GradientCovarianceUsage` and keeps neural-network, SGD, independence,
boundedness, variance-proxy, and Tropp hypotheses explicit.
-/

namespace HighDimProb
namespace Examples
namespace RandomMatrix
namespace EmpiricalFisherOperatorNormUsage

open MeasureTheory
open HighDimProb.Examples.RandomMatrix.GradientCovarianceUsage

noncomputable section

/-- Mini-batch random gradient vectors, indexed by the batch coordinate. -/
abbrev miniBatchGradientFamily {Omega : Type*}
    {batch n : Nat} (G : RandomGradientTable Omega batch n) :
    Fin batch -> RandomVector Omega (n + 1) :=
  randomGradientVectorFamily G

/-- Centered rank-one empirical Fisher summands for Matrix Bernstein. -/
abbrev centeredEmpiricalFisherSummands {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {batch n : Nat}
    (G : RandomGradientTable Omega batch n) :
    Fin batch -> RandomMatrix Omega (n + 1) (n + 1) :=
  centeredGradientCovarianceSummands (P := P) G

/--
Assumptions for the empirical Fisher / gradient covariance operator-norm tail.

The gradient-facing fields document the ML input model: coordinate-level
second-moment control and a per-sample squared-norm bound. The Matrix
Bernstein fields reuse the core positive- and negative-side assumption bundles.
The gradient fields do not derive those bundles; `positiveSide` and
`negativeSide` are the actual tail-proof obligations.
-/
structure EmpiricalFisherTailAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {batch n : Nat}
    (G : RandomGradientTable Omega batch n)
    (A : Fin batch -> RandomMatrix Omega (n + 1) (n + 1))
    (R Rneg t sigmaSq sigmaSqNeg : Real) : Prop where
  fisherAdapter : IsCenteredGradientCovarianceSummandFamily (P := P) G A
  gradientCoordinateMemLpTwo :
    forall b : Fin batch, forall j : Fin (n + 1),
      MemLpRealRandomVariable P
        (fun omega => (miniBatchGradientFamily G b omega) j) 2
  gradientSqNormBound :
    forall b : Fin batch, forall omega,
      vectorSqNorm (miniBatchGradientFamily G b omega) <= R
  positiveSide :
    MatrixBernsteinPositiveSideTroppAssumptions (P := P) A R t sigmaSq
  negativeSide :
    MatrixBernsteinNegativeSideTroppAssumptions (P := P) A Rneg t sigmaSqNeg

/--
Empirical Fisher / mini-batch gradient covariance operator-norm tail usage.

The summand family `A` is tied to centered rank-one gradient covariance
contributions by `fisherAdapter`; the bound itself is supplied by the current
optimized positive-threshold self-adjoint operator-norm Matrix Bernstein
wrapper.
-/
theorem empiricalFisher_operatorNorm_tail_usage
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {batch n : Nat}
    (G : RandomGradientTable Omega batch n)
    (A : Fin batch -> RandomMatrix Omega (n + 1) (n + 1))
    (R Rneg t sigmaSq sigmaSqNeg : Real)
    (h : EmpiricalFisherTailAssumptions
      (P := P) G A R Rneg t sigmaSq sigmaSqNeg) :
    P (SelfAdjointOperatorNormTailEvent (randomMatrixSum A) t) <=
      matrixBernsteinTwoSidedOptimizedScalarTailRHS
        (n + 1) R Rneg t sigmaSq sigmaSqNeg := by
  exact
    matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_arbitrary_of_troppAssumptions
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      (sigmaSq := sigmaSq) (sigmaSqNeg := sigmaSqNeg)
      h.positiveSide h.negativeSide

end

end EmpiricalFisherOperatorNormUsage
end RandomMatrix
end Examples
end HighDimProb
