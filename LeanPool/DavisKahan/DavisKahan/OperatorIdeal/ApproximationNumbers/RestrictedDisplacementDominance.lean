/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
public import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-!
# Approximation-number dominance for restricted displacements

Pointwise approximation-number domination gives every finite Ky Fan
approximation-gauge inequality.  For a `KyFanDominantIdealFamily`, those
inequalities imply ideal membership and gauge domination.

The final structure packages this comparison for restricted displacements, so
Davis--Kahan Section 4 can consume the operator-ideal result without owning the
majorization argument.
-/

@[expose] public section

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan
namespace Section4

open ExactSinTheta

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Pointwise domination of approximation singular values implies domination
of every finite Ky Fan approximation gauge. -/
theorem kyFanApproximationGauge_le_of_approximationSingularValue_le
    {A B : E →L[𝕜] F}
    (h : ∀ n, approximationSingularValue n A ≤
      approximationSingularValue n B) (k : ℕ) :
    kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  exact Finset.sum_le_sum fun n hn => h n

/-- Correct infinite-dimensional ideal-dominance bridge for Corollary 4.1.
The stronger family contains precisely the missing monotonicity principle. -/
theorem mem_and_gauge_le_of_approximationSingularValue_le
    (N : FanDominantIdealFamily (𝕜 := 𝕜))
    {A B : E →L[𝕜] F}
    (hB : N.Mem B)
    (h : ∀ n, approximationSingularValue n A ≤
      approximationSingularValue n B) :
    N.Mem A ∧
      N.gauge A ≤
        N.gauge B := by
  apply mem_and_gauge_le_of_all_kyFanApproximationGauge_le N hB
  intro k
  exact kyFanApproximationGauge_le_of_approximationSingularValue_le h k

/-- A reusable certificate containing exactly the mathematical output of
Proposition 4.1 for a pair of rectangular operators. -/
structure RestrictedDisplacementApproximationDominance
    (A B : E →L[𝕜] F) : Prop where
  approximation_le : ∀ n,
    approximationSingularValue n A ≤ approximationSingularValue n B

/-- Corollary 4.1 follows formally from a Proposition 4.1 certificate for every
Fan-dominant ideal family. -/
theorem restrictedDisplacement_idealGauge_le
    (N : FanDominantIdealFamily (𝕜 := 𝕜))
    {A B : E →L[𝕜] F}
    (D : RestrictedDisplacementApproximationDominance A B)
    (hB : N.Mem B) :
    N.Mem A ∧
      N.gauge A ≤
        N.gauge B :=
  mem_and_gauge_le_of_approximationSingularValue_le N hB D.approximation_le

omit [CompleteSpace E] [CompleteSpace F] in
/-- The operator-norm specialization of the dominance bridge. -/
theorem restrictedDisplacement_opNorm_le
    {A B : E →L[𝕜] F}
    (D : RestrictedDisplacementApproximationDominance A B) :
    ‖A‖ ≤ ‖B‖ := by
  simpa only [approximationSingularValue_zero] using D.approximation_le 0

omit [CompleteSpace E] [CompleteSpace F] in
/-- Every fixed positive Ky Fan gauge is a direct specialization. -/
theorem restrictedDisplacement_kyFan_le
    {A B : E →L[𝕜] F}
    (D : RestrictedDisplacementApproximationDominance A B)
    (k : ℕ) :
    kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B :=
  kyFanApproximationGauge_le_of_approximationSingularValue_le
    D.approximation_le k

end Section4
end DavisKahan
end TauCeti
