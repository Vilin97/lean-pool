/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Examples.RandomMatrix.RandomFeatureKernelUsage

/-!
# Attention-feature Gram operator-norm usage

This examples-only file connects transformer-style token feature Gram matrices
to the existing RandomMatrix Matrix Bernstein API. A sampled attention head or
feature channel gives a token-indexed vector, and its outer product is a
rank-one Gram contribution on the token dimension. We do not formalize softmax
attention or transformer training dynamics here; those assumptions remain
example-local and explicit.
-/

namespace HighDimProb
namespace Examples
namespace RandomMatrix
namespace AttentionFeatureGramOperatorNormUsage

open MeasureTheory
open HighDimProb.Examples.RandomMatrix.RandomFeatureKernelUsage

noncomputable section

/-- A token-indexed attention feature vector. -/
abbrev AttentionFeatureVector (numTokens : Nat) :=
  Fin (numTokens + 1) -> Real

/-- A finite collection of head/channel features over the same tokens. -/
abbrev AttentionFeatureTable (numHeads numTokens : Nat) :=
  Fin numHeads -> AttentionFeatureVector numTokens

/-- A random attention feature table. -/
abbrev RandomAttentionFeatureTable (Omega : Type*)
    (numHeads numTokens : Nat) :=
  Omega -> AttentionFeatureTable numHeads numTokens

/-- One rank-one token Gram contribution from an attention feature. -/
def attentionFeatureGramContribution {numHeads numTokens : Nat}
    (Phi : AttentionFeatureTable numHeads numTokens) (h : Fin numHeads) :
    Matrix (Fin (numTokens + 1)) (Fin (numTokens + 1)) Real :=
  featureKernelContribution Phi h

@[simp]
theorem attentionFeatureGramContribution_apply {numHeads numTokens : Nat}
    (Phi : AttentionFeatureTable numHeads numTokens) (h : Fin numHeads)
    (i j : Fin (numTokens + 1)) :
    attentionFeatureGramContribution Phi h i j = Phi h i * Phi h j := by
  rfl

/-- Empirical attention-feature token Gram matrix. -/
def empiricalAttentionFeatureGram {numHeads numTokens : Nat}
    (Phi : AttentionFeatureTable numHeads numTokens) :
    Matrix (Fin (numTokens + 1)) (Fin (numTokens + 1)) Real :=
  empiricalFeatureKernel Phi

@[simp]
theorem empiricalAttentionFeatureGram_apply {numHeads numTokens : Nat}
    (Phi : AttentionFeatureTable numHeads numTokens)
    (i j : Fin (numTokens + 1)) :
    empiricalAttentionFeatureGram Phi i j =
      Finset.univ.sum fun h : Fin numHeads => Phi h i * Phi h j := by
  simp [empiricalAttentionFeatureGram]

/-- Random attention feature vector for one head/channel. -/
abbrev randomAttentionFeatureVector {Omega : Type*}
    {numHeads numTokens : Nat}
    (Phi : RandomAttentionFeatureTable Omega numHeads numTokens)
    (h : Fin numHeads) :
    RandomVector Omega (numTokens + 1) :=
  randomFeatureVector Phi h

/-- Centered rank-one attention Gram summands. -/
abbrev centeredAttentionFeatureGramSummands {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {numHeads numTokens : Nat}
    (Phi : RandomAttentionFeatureTable Omega numHeads numTokens) :
    Fin numHeads -> RandomMatrix Omega (numTokens + 1) (numTokens + 1) :=
  centeredRandomFeatureKernelSummands (P := P) Phi

/-- Adapter from attention-feature vocabulary to the random-feature kernel API. -/
def IsCenteredAttentionFeatureGramSummandFamily {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {numHeads numTokens : Nat}
    (Phi : RandomAttentionFeatureTable Omega numHeads numTokens)
    (A : Fin numHeads -> RandomMatrix Omega (numTokens + 1) (numTokens + 1)) :
    Prop :=
  A = centeredAttentionFeatureGramSummands (P := P) Phi

/--
Assumptions for transformer-style attention feature Gram concentration.

The feature-level fields keep measurability, integrability, boundedness, and
softmax/Lipschitz-style controls explicit. The Matrix Bernstein fields are the
CFC-free core positive- and negative-side bundles for centered rank-one token
Gram summands. The feature fields document the domain model; they do not derive
the Matrix Bernstein bundles, which remain the actual tail-proof obligations.
-/
structure AttentionFeatureGramTailAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {numHeads numTokens : Nat}
    (Phi : RandomAttentionFeatureTable Omega numHeads numTokens)
    (A : Fin numHeads -> RandomMatrix Omega (numTokens + 1) (numTokens + 1))
    (R Rneg t sigmaSq sigmaSqNeg softmaxLip : Real) : Prop where
  attentionAdapter : IsCenteredAttentionFeatureGramSummandFamily (P := P) Phi A
  randomFeatureAdapter :
    IsCenteredRandomFeatureKernelSummandFamily (P := P) Phi A
  featureCoordinateMemLpTwo :
    forall h : Fin numHeads, forall i : Fin (numTokens + 1),
      MemLpRealRandomVariable P (fun omega => Phi omega h i) 2
  featureSquaredNormBound :
    forall h : Fin numHeads, forall omega,
      vectorSqNorm (Phi omega h) <= R
  softmaxLipschitzProxyNonneg : 0 <= softmaxLip
  softmaxFeatureBoundProxy :
    forall h : Fin numHeads, forall omega,
      vectorSqNorm (Phi omega h) <= softmaxLip
  positiveSide :
    MatrixBernsteinPositiveSideTroppAssumptions (P := P) A R t sigmaSq
  negativeSide :
    MatrixBernsteinNegativeSideTroppAssumptions (P := P) A Rneg t sigmaSqNeg

/-- Quadratic-form attention Gram tail via the existing random-feature wrapper. -/
theorem attentionFeatureGram_quadraticForm_tail_usage
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {numHeads numTokens : Nat}
    (Phi : RandomAttentionFeatureTable Omega numHeads numTokens)
    (A : Fin numHeads -> RandomMatrix Omega (numTokens + 1) (numTokens + 1))
    (R Rneg t sigmaSq sigmaSqNeg softmaxLip : Real)
    (h : AttentionFeatureGramTailAssumptions
      (P := P) Phi A R Rneg t sigmaSq sigmaSqNeg softmaxLip) :
    P (quadraticFormUpperTailEvent (randomMatrixSum A) t) <=
      matrixBernsteinOptimizedScalarTailRHS (numTokens + 1) R t sigmaSq := by
  exact
    randomFeatureKernel_quadraticForm_tail_optimized_under_primitives
      (P := P) Phi A R t sigmaSq
      { featureAdapter := h.randomFeatureAdapter
        matrixBernsteinSide := h.positiveSide }

/-- Attention-feature Gram operator-norm tail usage under explicit assumptions. -/
theorem attentionFeatureGram_operatorNorm_tail_usage
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {numHeads numTokens : Nat}
    (Phi : RandomAttentionFeatureTable Omega numHeads numTokens)
    (A : Fin numHeads -> RandomMatrix Omega (numTokens + 1) (numTokens + 1))
    (R Rneg t sigmaSq sigmaSqNeg softmaxLip : Real)
    (h : AttentionFeatureGramTailAssumptions
      (P := P) Phi A R Rneg t sigmaSq sigmaSqNeg softmaxLip) :
    P (SelfAdjointOperatorNormTailEvent (randomMatrixSum A) t) <=
      matrixBernsteinTwoSidedOptimizedScalarTailRHS
        (numTokens + 1) R Rneg t sigmaSq sigmaSqNeg := by
  exact
    matrixBernsteinOpNormTailOptimizedScalarRHSWithCoeff_arbitrary_of_troppAssumptions
      (P := P) (A := A) (R := R) (Rneg := Rneg) (t := t)
      (sigmaSq := sigmaSq) (sigmaSqNeg := sigmaSqNeg)
      h.positiveSide h.negativeSide

end

end AttentionFeatureGramOperatorNormUsage
end RandomMatrix
end Examples
end HighDimProb
