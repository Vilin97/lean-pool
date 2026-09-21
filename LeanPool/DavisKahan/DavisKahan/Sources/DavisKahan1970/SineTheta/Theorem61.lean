/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.Canonical
import LeanPool.DavisKahan.DavisKahan.SinTheta.Real.Canonical
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SingularValueTransport

/-!
# Literal Davis--Kahan Theorem 6.1 surface

The paper does not choose a unique codomain realization of `sin Θ₀`. It permits
any operator having the complete singular-value sequence of the cross
projection between the trial and unwanted exact subspaces. The previously
verified theorem uses one canonical rectangular realization. This file proves
the literal paper statement by transporting membership and gauge along the
complete singular-value sequence, without changing the spectral, domain,
residual, or lower-frame hypotheses.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

section Complex

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The literal complex input package for Davis--Kahan Theorem 6.1. -/
structure GeneralSinThetaRepresentativeProblem
    (N : KyFanDominantIdealFamily (𝕜 := ℂ)) where
  problem : FormBoundedGeneralSinThetaProblem (E := E) (F := F) (G := G) (H := H) N
  sinTheta₀ : SinThetaRepresentative
    (directedSinThetaOperator problem.data.X problem.exactMap
      problem.lowerFrame problem.frameLowerBound_pos)

namespace GeneralSinThetaRepresentativeProblem

/-- **Davis--Kahan 1970, Theorem 6.1, literal complex form.**

The chosen `sin Θ₀` may be any rectangular operator with the complete
singular-value sequence prescribed in the paper. -/
theorem result
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (P : GeneralSinThetaRepresentativeProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem P.sinTheta₀.operator ∧
      P.problem.gap * P.problem.frameLowerBound *
          N.gauge P.sinTheta₀.operator
        ≤ N.gauge P.problem.data.residual := by
  have hcanonical := FormBoundedGeneralSinThetaProblem.result N P.problem
  exact P.sinTheta₀.same_singular_values.mem_and_mul_gauge_le N
    hcanonical.1 hcanonical.2

end GeneralSinThetaRepresentativeProblem

/-- Literal paper representative for the complex isometric theorem. -/
structure IsometricSinThetaRepresentativeProblem
    (N : KyFanDominantIdealFamily (𝕜 := ℂ)) where
  problem : FormBoundedIsometricSinThetaProblem (𝕜 := ℂ) (E := E) (F := F)
    (G := G) (H := H) N
  sinTheta₀ : SinThetaRepresentative
    ((ContinuousLinearMap.id ℂ E -
      problem.exactMap ∘L problem.exactMap.adjoint) ∘L problem.data.X)

namespace IsometricSinThetaRepresentativeProblem

/-- Original isometric sine theorem with the paper's freedom to choose any
operator realizing the same complete singular-value sequence. -/
theorem result
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (P : IsometricSinThetaRepresentativeProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem P.sinTheta₀.operator ∧
      P.problem.gap *
          N.gauge P.sinTheta₀.operator
        ≤ N.gauge P.problem.data.residual := by
  have hcanonical := FormBoundedIsometricSinThetaProblem.result_complex N P.problem
  exact P.sinTheta₀.same_singular_values.mem_and_mul_gauge_le N
    hcanonical.1 hcanonical.2

end IsometricSinThetaRepresentativeProblem

end Complex

section Real

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The literal real input package for Davis--Kahan Theorem 6.1. -/
structure RealGeneralSinThetaRepresentativeProblem
    (N : KyFanDominantIdealFamily (𝕜 := ℝ)) where
  problem : RealGeneralSinThetaProblem (E := E) (F := F)
    (G := G) (H := H) N
  sinTheta₀ : SinThetaRepresentative
    (directedSinThetaOperatorReal problem.data.X problem.exactMap
      problem.lowerFrame problem.frameLowerBound_pos)

namespace RealGeneralSinThetaRepresentativeProblem

/-- **Davis--Kahan 1970, Theorem 6.1, literal real form.** -/
theorem result
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (P : RealGeneralSinThetaRepresentativeProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem P.sinTheta₀.operator ∧
      P.problem.gap * P.problem.frameLowerBound *
          N.gauge P.sinTheta₀.operator
        ≤ N.gauge P.problem.data.residual := by
  have hcanonical := RealGeneralSinThetaProblem.result N P.problem
  exact P.sinTheta₀.same_singular_values.mem_and_mul_gauge_le N
    hcanonical.1 hcanonical.2

end RealGeneralSinThetaRepresentativeProblem

/-- Literal paper representative for the real isometric theorem. -/
structure RealIsometricSinThetaRepresentativeProblem
    (N : KyFanDominantIdealFamily (𝕜 := ℝ)) where
  problem : FormBoundedIsometricSinThetaProblem (𝕜 := ℝ) (E := E) (F := F)
    (G := G) (H := H) N
  sinTheta₀ : SinThetaRepresentative
    ((ContinuousLinearMap.id ℝ E -
      problem.exactMap ∘L problem.exactMap.adjoint) ∘L problem.data.X)

namespace RealIsometricSinThetaRepresentativeProblem

/-- Original real isometric sine theorem in the literal paper formulation. -/
theorem result
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (P : RealIsometricSinThetaRepresentativeProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem P.sinTheta₀.operator ∧
      P.problem.gap *
          N.gauge P.sinTheta₀.operator
        ≤ N.gauge P.problem.data.residual := by
  have hcanonical := FormBoundedIsometricSinThetaProblem.result_real N P.problem
  exact P.sinTheta₀.same_singular_values.mem_and_mul_gauge_le N
    hcanonical.1 hcanonical.2

end RealIsometricSinThetaRepresentativeProblem

end Real

end

end ExactSinTheta
end DavisKahan
end TauCeti
