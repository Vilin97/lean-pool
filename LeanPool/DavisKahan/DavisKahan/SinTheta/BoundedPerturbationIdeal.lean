/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.BoundedPerturbation
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # Bounded Perturbation Ideal -/

open TauCeti.DavisKahan.Sylvester

/-!
# Ideal-gauge bounded-perturbation adapter for unbounded sine theta

This leaf module lifts the accepted genuine-spectrum unbounded sine-theta
estimate from the projected residual block to the original bounded
perturbation.  The proof uses only the existing rectangular symmetric ideal
interface: adjoint invariance and two-sided contraction under composition.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan


open TauCeti.DavisKahan.ExactSinTheta

universe v

variable {H F G : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Ideal-gauge counterpart of
`sinTheta_addBounded_opNorm_of_spectrum_gap_isometric`.  If the bounded
perturbation belongs to the rectangular symmetric ideal family, then the
isometric overlap block belongs to the same family with the sharp
constant-one gap estimate. -/
theorem sinTheta_addBounded_gauge_of_spectrum_gap_isometric
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (V : H →L[ℂ] H) (hV : V.IsSymmetric)
    (A₀ : F →ₗ.[ℂ] F) (hA₀ : IsSelfAdjoint A₀)
    (Λ₁ : G →ₗ.[ℂ] G) (hΛ₁ : IsSelfAdjoint Λ₁)
    (X : F →L[ℂ] H) (F₁ : G →L[ℂ] H)
    (hXdom : ∀ x : A₀.domain, X (x : F) ∈ A.domain)
    (hXintertwines : ∀ x : A₀.domain,
      A ⟨X (x : F), hXdom x⟩ = X (A₀ x))
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hF₁intertwines : ∀ y : Λ₁.domain,
      (TauCeti.LinearPMap.addBounded A V) ⟨F₁ (y : G), hF₁dom y⟩ =
        F₁ (Λ₁ y))
    (hXiso : IsometricEmbedding X) (hF₁iso : IsometricEmbedding F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : TauCeti.LinearPMap.SemiboundedBelow A₀ β) (hA₀high : TauCeti.LinearPMap.SemiboundedAbove A₀ α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum Λ₁)
    (hVmem : N.Mem V) :
    N.Mem (X.adjoint ∘L F₁) ∧
      δ * N.gaugeReal (X.adjoint ∘L F₁) ≤ N.gaugeReal V := by
  let D := boundedPerturbationSinThetaData A V A₀ Λ₁ X F₁
    hXdom hXintertwines hF₁dom hF₁intertwines
  have hD : _root_.IsSelfAdjoint D.A := by
    change _root_.IsSelfAdjoint (TauCeti.LinearPMap.addBounded A V)
    exact addBounded_isSelfAdjoint A hA V hV
  have hVadj : N.Mem V.adjoint := N.adjoint_mem hVmem
  have hLeftMem : N.Mem (X.adjoint ∘L V.adjoint) :=
    N.comp_left_mem (E := H) (F := H) (G := F) X.adjoint hVadj
  have hProjectedMem : N.Mem ((V ∘L X).adjoint ∘L F₁) := by
    rw [ContinuousLinearMap.adjoint_comp]
    exact N.comp_right_mem (E := H) (F := F) (H := G) F₁ hLeftMem
  have hRaw := sinTheta_unbounded_gauge_of_spectrum_gap
    N D hD hA₀ hΛ₁ hβα hδ hA₀low hA₀high hΛspec hProjectedMem
  have hRaw' :
      N.Mem (X.adjoint ∘L F₁) ∧
        δ * N.gaugeReal (X.adjoint ∘L F₁) ≤
          N.gaugeReal ((V ∘L X).adjoint ∘L F₁) := by
    change
      N.Mem (X.adjoint ∘L F₁) ∧
        δ * N.gaugeReal (X.adjoint ∘L F₁) ≤
          N.gaugeReal ((V ∘L X).adjoint ∘L F₁) at hRaw
    exact hRaw
  have hXadjNorm : ‖X.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact opNorm_le_one_of_isometry hXiso
  have hF₁norm : ‖F₁‖ ≤ 1 := opNorm_le_one_of_isometry hF₁iso
  have hLeftGauge :
      N.gaugeReal (X.adjoint ∘L V.adjoint) ≤ N.gaugeReal V.adjoint :=
    N.gaugeReal_comp_left_le (E := H) (F := H) (G := F)
      X.adjoint hVadj hXadjNorm
  have hProjectedGauge :
      N.gaugeReal ((V ∘L X).adjoint ∘L F₁) ≤ N.gaugeReal V := by
    rw [ContinuousLinearMap.adjoint_comp]
    calc
      N.gaugeReal ((X.adjoint ∘L V.adjoint) ∘L F₁) ≤
          N.gaugeReal (X.adjoint ∘L V.adjoint) :=
        N.gaugeReal_comp_right_le (E := H) (F := F) (H := G)
          F₁ hLeftMem hF₁norm
      _ ≤ N.gaugeReal V.adjoint := hLeftGauge
      _ = N.gaugeReal V := N.gaugeReal_adjoint hVmem
  exact ⟨hRaw'.1, hRaw'.2.trans hProjectedGauge⟩

/-- **Block form of the ideal-gauge bounded-perturbation sine-theta estimate.**

`sinTheta_addBounded_gauge_of_spectrum_gap_isometric` finishes by contracting the
projected perturbation block back to the whole perturbation, which costs the
sharpness that the double-angle argument needs.  This is the same estimate one
step earlier: the right-hand side is the single block of the perturbation
between the two subspaces, which is what the Sylvester engine actually produces.

The isometry hypotheses are absent because only the contraction step used them.
-/
theorem sinTheta_addBounded_gauge_block_of_spectrum_gap
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (V : H →L[ℂ] H) (hV : V.IsSymmetric)
    (A₀ : F →ₗ.[ℂ] F) (hA₀ : IsSelfAdjoint A₀)
    (Λ₁ : G →ₗ.[ℂ] G) (hΛ₁ : IsSelfAdjoint Λ₁)
    (X : F →L[ℂ] H) (F₁ : G →L[ℂ] H)
    (hXdom : ∀ x : A₀.domain, X (x : F) ∈ A.domain)
    (hXintertwines : ∀ x : A₀.domain,
      A ⟨X (x : F), hXdom x⟩ = X (A₀ x))
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hF₁intertwines : ∀ y : Λ₁.domain,
      (TauCeti.LinearPMap.addBounded A V) ⟨F₁ (y : G), hF₁dom y⟩ =
        F₁ (Λ₁ y))
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : TauCeti.LinearPMap.SemiboundedBelow A₀ β) (hA₀high : TauCeti.LinearPMap.SemiboundedAbove A₀ α)
    (hΛspec : ∀ lam ∈ Set.Ioo (β - δ) (α + δ),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum Λ₁)
    (hVmem : N.Mem V) :
    N.Mem (X.adjoint ∘L F₁) ∧
      δ * N.gaugeReal (X.adjoint ∘L F₁) ≤
        N.gaugeReal ((V ∘L X).adjoint ∘L F₁) := by
  let D := boundedPerturbationSinThetaData A V A₀ Λ₁ X F₁
    hXdom hXintertwines hF₁dom hF₁intertwines
  have hD : _root_.IsSelfAdjoint D.A := by
    change _root_.IsSelfAdjoint (TauCeti.LinearPMap.addBounded A V)
    exact addBounded_isSelfAdjoint A hA V hV
  have hVadj : N.Mem V.adjoint := N.adjoint_mem hVmem
  have hLeftMem : N.Mem (X.adjoint ∘L V.adjoint) :=
    N.comp_left_mem (E := H) (F := H) (G := F) X.adjoint hVadj
  have hProjectedMem : N.Mem ((V ∘L X).adjoint ∘L F₁) := by
    rw [ContinuousLinearMap.adjoint_comp]
    exact N.comp_right_mem (E := H) (F := F) (H := G) F₁ hLeftMem
  have hRaw := sinTheta_unbounded_gauge_of_spectrum_gap
    N D hD hA₀ hΛ₁ hβα hδ hA₀low hA₀high hΛspec hProjectedMem
  change
    N.Mem (X.adjoint ∘L F₁) ∧
      δ * N.gaugeReal (X.adjoint ∘L F₁) ≤
        N.gaugeReal ((V ∘L X).adjoint ∘L F₁) at hRaw
  exact hRaw

end DavisKahan
end TauCeti
