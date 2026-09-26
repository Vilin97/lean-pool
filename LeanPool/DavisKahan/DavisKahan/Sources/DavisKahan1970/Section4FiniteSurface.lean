/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.RestrictedDisplacementDominance

/-!
# Finite-dimensional Section 4 source surface

The finite-dimensional Davis--Kahan direct-rotation development already proves
the valid content of Propositions 4.1--4.3 and Corollary 4.1.  This module gives
those results a compact source-facing surface and records the exact bridge
from ordinary singular values to approximation singular values.

The infinite-dimensional frontier must not be discharged merely by importing
these finite results.  Its remaining task is to prove pointwise approximation
number dominance for the restricted displacement in arbitrary Hilbert space.
-/

@[expose] public section

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan1970
namespace Section4

open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Section4

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Finite-dimensional Proposition 4.1 in its original singular-value form. -/
theorem finite_proposition4_1_singularValues
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : TauCeti.IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) (n : ℕ) :
    ((LinearMap.id - (DavisKahan.FiniteDimensional.directRotation U V hacute).toLinearMap) ∘ₗ
        TauCeti.projection U).singularValues n ≤
      ((LinearMap.id - W.toLinearMap) ∘ₗ TauCeti.projection U).singularValues n :=
  DavisKahan.FiniteDimensional.singularValues_restrictedDisplacement_le U V hacute W hmap n

/-- Finite-dimensional Proposition 4.1 rewritten with the same approximation
singular values used by the infinite-dimensional ideal framework. -/
theorem finite_proposition4_1_approximationSingularValue
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : TauCeti.IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) (n : ℕ) :
    approximationSingularValue n
        (((LinearMap.id - (DavisKahan.FiniteDimensional.directRotation U V hacute).toLinearMap) ∘ₗ
          TauCeti.projection U).toContinuousLinearMap) ≤
      approximationSingularValue n
        (((LinearMap.id - W.toLinearMap) ∘ₗ
          TauCeti.projection U).toContinuousLinearMap) := by
  rw [approximationSingularValue_eq_singularValues,
    approximationSingularValue_eq_singularValues]
  exact finite_proposition4_1_singularValues U V hacute W hmap n

/-- Package the finite Proposition 4.1 result as the certificate consumed by
`restrictedDisplacement_idealGauge_le`. -/
theorem finite_restrictedDisplacementDominance
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : TauCeti.IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    RestrictedDisplacementApproximationDominance
      (((LinearMap.id - (DavisKahan.FiniteDimensional.directRotation U V hacute).toLinearMap) ∘ₗ
        TauCeti.projection U).toContinuousLinearMap)
      (((LinearMap.id - W.toLinearMap) ∘ₗ
        TauCeti.projection U).toContinuousLinearMap) where
  approximation_le :=
    finite_proposition4_1_approximationSingularValue U V hacute W hmap

/-- Finite-dimensional Corollary 4.1 for every ordinary square
unitarily-invariant norm. -/
theorem finite_corollary4_1_uiNorm
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : TauCeti.IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    N ((LinearMap.id - (DavisKahan.FiniteDimensional.directRotation U V hacute).toLinearMap) ∘ₗ
        TauCeti.projection U) ≤
      N ((LinearMap.id - W.toLinearMap) ∘ₗ TauCeti.projection U) :=
  DavisKahan.FiniteDimensional.directRotation_minimizes_restrictedDisplacement_uiNorm
    N U V hacute W hmap

/-- Finite-dimensional Proposition 4.3: the direct rotation minimizes every
unitarily-invariant norm of the positive displacement square. -/
theorem finite_proposition4_3_uiNorm
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : TauCeti.IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    N (DavisKahan.FiniteDimensional.displacementSquare
      (DavisKahan.FiniteDimensional.directRotation U V hacute).toLinearMap) ≤
      N (DavisKahan.FiniteDimensional.displacementSquare W.toLinearMap) :=
  DavisKahan.FiniteDimensional.directRotation_minimizes_displacementSquare_uiNorm
    N U V hacute W hmap

/-- Finite-dimensional Proposition 4.2 in the compiled full-basis energy form.
This is intentionally not the stronger arbitrary-partial-family statement in
the current frontier scaffold. -/
theorem finite_proposition4_2_fullBasisEnergy
    {n : ℕ}
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : TauCeti.IsAcute U V)
    (b : OrthonormalBasis (Fin n) 𝕜 E)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    ∑ i, ‖DavisKahan.FiniteDimensional.directRotation U V hacute (b i) - b i‖ ^ 2 ≤
      ∑ i, ‖W (b i) - b i‖ ^ 2 :=
  DavisKahan.FiniteDimensional.directRotation_minimizes_sum_sq_basis_angles
    U V hacute b W hmap

end Section4
end DavisKahan1970
end TauCeti
