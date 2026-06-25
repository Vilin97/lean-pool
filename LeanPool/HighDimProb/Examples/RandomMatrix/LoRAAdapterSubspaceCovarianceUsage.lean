/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Examples.RandomMatrix.GradientCovarianceUsage

/-!
# LoRA adapter-subspace covariance usage

This examples-only file models a mini-batch of full gradients after restriction
to a finite adapter subspace, such as a LoRA or other trainable adapter block.
The adapter projection is represented by an example-local coordinate map rather
than a new core subspace theory. Once gradients are in adapter coordinates, the
existing rank-one gradient covariance and empirical Fisher operator-norm usage
APIs apply directly.
-/

namespace HighDimProb
namespace Examples
namespace RandomMatrix
namespace LoRAAdapterSubspaceCovarianceUsage

open MeasureTheory
open HighDimProb.Examples.RandomMatrix.GradientCovarianceUsage

noncomputable section

/-- A full model gradient in a finite ambient parameter dimension. -/
abbrev FullGradient (d : Nat) :=
  Fin (d + 1) -> Real

/-- Adapter coordinates in a finite LoRA / adapter subspace. -/
abbrev AdapterGradient (r : Nat) :=
  Fin (r + 1) -> Real

/--
Example-local adapter feature map from a full gradient to adapter coordinates.

This deliberately avoids building a full projection or LoRA parameterization
theory in core.
-/
abbrev AdapterFeature (d r : Nat) :=
  FullGradient d -> AdapterGradient r

/-- A random mini-batch of full gradients. -/
abbrev RandomFullGradientTable (Omega : Type*)
    (batch d : Nat) :=
  Omega -> Fin batch -> FullGradient d

/-- Restrict a random full-gradient mini-batch to adapter coordinates. -/
def adapterGradientTable {Omega : Type*}
    {batch d r : Nat}
    (adapterFeature : AdapterFeature d r)
    (fullGradients : RandomFullGradientTable Omega batch d) :
    RandomGradientTable Omega batch r :=
  fun omega b => adapterFeature (fullGradients omega b)

/-- The adapter-coordinate gradient family used by rank-one covariance APIs. -/
abbrev loraAdapterGradientFamily {Omega : Type*}
    {batch d r : Nat}
    (adapterFeature : AdapterFeature d r)
    (fullGradients : RandomFullGradientTable Omega batch d) :
    Fin batch -> RandomVector Omega (r + 1) :=
  randomGradientVectorFamily (adapterGradientTable adapterFeature fullGradients)

/-- One rank-one adapter-subspace covariance contribution. -/
abbrev loraAdapterRankOneCovarianceContribution {Omega : Type*}
    {batch d r : Nat}
    (adapterFeature : AdapterFeature d r)
    (fullGradients : RandomFullGradientTable Omega batch d)
    (b : Fin batch) :
    RandomMatrix Omega (r + 1) (r + 1) :=
  randomGradientCovarianceContribution
    (adapterGradientTable adapterFeature fullGradients) b

/-- Centered rank-one covariance summands in the adapter subspace. -/
abbrev centeredLoRAAdapterCovarianceSummands {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {batch d r : Nat}
    (adapterFeature : AdapterFeature d r)
    (fullGradients : RandomFullGradientTable Omega batch d) :
    Fin batch -> RandomMatrix Omega (r + 1) (r + 1) :=
  centeredGradientCovarianceSummands
    (P := P) (adapterGradientTable adapterFeature fullGradients)

/--
Usage assumptions for LoRA / adapter-subspace covariance concentration.

The first fields state the ML-facing assumptions on adapter-coordinate
gradients. The Matrix Bernstein fields reuse the CFC-free core positive- and
negative-side assumption bundles for the centered adapter covariance summands.
The adapter fields document the domain model; they do not derive those bundles,
which remain the actual tail-proof obligations.
-/
structure LoRAAdapterSubspaceCovarianceAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {batch d r : Nat}
    (adapterFeature : AdapterFeature d r)
    (fullGradients : RandomFullGradientTable Omega batch d)
    (A : Fin batch -> RandomMatrix Omega (r + 1) (r + 1))
    (R Rneg t sigmaSq sigmaSqNeg : Real) : Prop where
  adapterCoordinateMemLpTwo :
    forall b : Fin batch, forall j : Fin (r + 1),
      MemLpRealRandomVariable P
        (fun omega => (adapterGradientTable adapterFeature fullGradients omega b) j) 2
  adapterSquaredNormBound :
    forall b : Fin batch, forall omega,
      vectorSqNorm (adapterGradientTable adapterFeature fullGradients omega b) <= R
  centeredAdapterSummands :
    A = centeredLoRAAdapterCovarianceSummands
      (P := P) adapterFeature fullGradients
  positiveSide :
    MatrixBernsteinPositiveSideTroppAssumptions (P := P) A R t sigmaSq
  negativeSide :
    MatrixBernsteinNegativeSideTroppAssumptions (P := P) A Rneg t sigmaSqNeg

/--
LoRA / adapter-subspace gradient covariance operator-norm tail usage.

After the full gradients are mapped into adapter coordinates, the theorem is
the same core Matrix Bernstein route used by the empirical Fisher examples for
centered rank-one covariance summands.
-/
theorem loraAdapterSubspaceCovariance_operatorNorm_tail_usage
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {batch d r : Nat}
    (adapterFeature : AdapterFeature d r)
    (fullGradients : RandomFullGradientTable Omega batch d)
    (A : Fin batch -> RandomMatrix Omega (r + 1) (r + 1))
    (R Rneg t sigmaSq sigmaSqNeg : Real)
    (h : LoRAAdapterSubspaceCovarianceAssumptions
      (P := P) adapterFeature fullGradients A R Rneg t sigmaSq sigmaSqNeg) :
    P (SelfAdjointOperatorNormTailEvent (randomMatrixSum A) t) <=
      matrixBernsteinTwoSidedOptimizedScalarTailRHS
        (r + 1) R Rneg t sigmaSq sigmaSqNeg := by
  exact
    matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_arbitrary_of_troppAssumptions
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      (sigmaSq := sigmaSq) (sigmaSqNeg := sigmaSqNeg)
      h.positiveSide h.negativeSide

end

end LoRAAdapterSubspaceCovarianceUsage
end RandomMatrix
end Examples
end HighDimProb
