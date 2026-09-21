/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sylvester.ShiftedInverse

/-! # Op Norm -/

open TauCeti.DavisKahan.Sylvester

/-!
# Operator-norm `sin Θ` bound from a two-sided shifted inverse
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta


open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- **The unbounded Davis--Kahan `sin Θ` theorem, operator norm, honest
hypotheses.**  For the paper-shaped data `D` (self-adjoint ambient operator,
trial block `A₀`, complementary block `Λ₁`, isometric-into embeddings and the
residual identity), if the quadratic form of `A₀` lies in `[β, α]` while
`Λ₁ - (α+β)/2` has a bounded two-sided inverse of norm at most
`((α-β)/2 + δ)⁻¹`, then `δ ‖X⋆ ∘ F₁‖ ≤ ‖R⋆ ∘ F₁‖`. -/
theorem sinTheta_unbounded_opNorm
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A) (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : TauCeti.LinearPMap.SemiboundedBelow D.A₀ β) (hA₀high : TauCeti.LinearPMap.SemiboundedAbove D.A₀ α)
    (hΛres : TauCeti.LinearPMap.TwoSidedShiftedInverseBound D.Λ₁ ((α + β) / 2)
      ((α - β) / 2 + δ)) :
    δ * ‖D.X.adjoint ∘L D.F₁‖ ≤ ‖D.residual.adjoint ∘L D.F₁‖ := by
  have hEq := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have h := norm_sylvester_le_of_exteriorInterval
    (A := D.A₀) (B := D.Λ₁)
    (TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint hA₀) hA₀.dense_domain hβα hδ hA₀low hA₀high hΛres hEq
  simpa [norm_neg] using h

omit [CompleteSpace E] [CompleteSpace G] in
/-- **A self-adjoint `A₀` is symmetric**, in the form the unbounded sin-Theta
bounds use.  Derived identically here and in `Gauge.lean`. -/
theorem isSymmetric_A₀_of_isSelfAdjoint
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA₀ : _root_.IsSelfAdjoint D.A₀) :
    TauCeti.LinearPMap.IsSymmetric D.A₀ := by
  have hformal := LinearPMap.adjoint_isFormalAdjoint hA₀.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA₀] at hformal
  intro x y
  exact hformal x y

end ExactSinTheta
end DavisKahan
end TauCeti
