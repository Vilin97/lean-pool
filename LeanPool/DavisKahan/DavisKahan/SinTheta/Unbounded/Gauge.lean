/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sylvester.ShiftedInverseGauge
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.OpNorm

/-! # Gauge -/

open TauCeti.DavisKahan.Sylvester

/-!
# Ideal-gauge `sin Θ` bound from a two-sided shifted inverse
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

/-- **The unbounded Davis--Kahan `sin Θ` theorem at unitary-invariant ideal
scope.**  For the paper-shaped `UnboundedSinThetaData` with the trial
block's quadratic form in `[β, α]` and the complementary block's shifted
resolvent bounded by `((α-β)/2 + δ)⁻¹`, if the projected residual
`R⋆ ∘ F₁` lies in the rectangular symmetric ideal family `N`, then so does
`X⋆ ∘ F₁`, with `δ · gauge (X⋆ ∘ F₁) ≤ gauge (R⋆ ∘ F₁)`. -/
theorem sinTheta_unbounded_gauge
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : _root_.IsSelfAdjoint D.A) (hA₀ : _root_.IsSelfAdjoint D.A₀)
    (hΛ₁ : _root_.IsSelfAdjoint D.Λ₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : TauCeti.LinearPMap.SemiboundedBelow D.A₀ β) (hA₀high : TauCeti.LinearPMap.SemiboundedAbove D.A₀ α)
    (hΛres : TwoSidedShiftedInverseBound D.Λ₁ ((α + β) / 2)
      ((α - β) / 2 + δ))
    (hC : N.Mem (D.residual.adjoint ∘L D.F₁)) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gaugeReal (D.X.adjoint ∘L D.F₁) ≤
        N.gaugeReal (D.residual.adjoint ∘L D.F₁) := by
  obtain ⟨S, hSnorm, hSeq⟩ :=
    exists_bounded_shift_extension
      (TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint hA₀)
      hA₀.dense_domain hβα hA₀low hA₀high
  obtain ⟨J, hdom, _hleft, hright, hJnorm⟩ := hΛres
  have hEqu := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hρ : (0 : ℝ) ≤ (α - β) / 2 := by linarith
  have hEq' : ∀ y : D.Λ₁.domain,
      S ((D.X.adjoint ∘L D.F₁) (y : G)) -
        ((D.X.adjoint ∘L D.F₁) (D.Λ₁ y) -
          (((α + β) / 2 : ℝ) : 𝕜) • (D.X.adjoint ∘L D.F₁) (y : G)) =
      (-(D.residual.adjoint ∘L D.F₁)) (y : G) := by
    intro y
    have h1 := hEqu.equation y
    have h2 := hSeq ⟨(D.X.adjoint ∘L D.F₁) (y : G), hEqu.mapsTo_domain y⟩
    rw [h2]
    calc D.A₀
          ⟨(D.X.adjoint ∘L D.F₁) (y : G), hEqu.mapsTo_domain y⟩ -
            (((α + β) / 2 : ℝ) : 𝕜) • (D.X.adjoint ∘L D.F₁) (y : G) -
          ((D.X.adjoint ∘L D.F₁) (D.Λ₁ y) -
            (((α + β) / 2 : ℝ) : 𝕜) • (D.X.adjoint ∘L D.F₁) (y : G))
        = D.A₀
            ⟨(D.X.adjoint ∘L D.F₁) (y : G), hEqu.mapsTo_domain y⟩ -
          (D.X.adjoint ∘L D.F₁) (D.Λ₁ y) := by abel
      _ = (-(D.residual.adjoint ∘L D.F₁)) (y : G) := h1
  have hmain := mem_and_gauge_le_of_boundedLeft_exteriorRight N hρ hδ
    hSnorm hdom hright hJnorm hEq' (N.neg_mem hC)
  refine ⟨hmain.1, ?_⟩
  have hgC : N.gaugeReal (-(D.residual.adjoint ∘L D.F₁)) =
      N.gaugeReal (D.residual.adjoint ∘L D.F₁) := N.gaugeReal_neg hC
  calc δ * N.gaugeReal (D.X.adjoint ∘L D.F₁)
      ≤ N.gaugeReal (-(D.residual.adjoint ∘L D.F₁)) := hmain.2
    _ = N.gaugeReal (D.residual.adjoint ∘L D.F₁) := hgC

end ExactSinTheta
end DavisKahan
end TauCeti
