/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.Real.Canonical

/-! # Specializations -/

open TauCeti.DavisKahan.Sylvester

/-!
# Real bounded specialization of the generalized theorem

Bounded real data is embedded as full-domain closed-operator data and then
sent through the real canonical unbounded theorem.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Bounded real source package for the generalized sine theorem. -/
structure RealBoundedGeneralSinThetaProblem
    (N : KyFanDominantIdealFamily (𝕜 := ℝ)) where
  A : E →L[ℝ] E
  A₀ : F →L[ℝ] F
  Λ₁ : G →L[ℝ] G
  X : F →L[ℝ] E
  F₀ : H →L[ℝ] E
  F₁ : G →L[ℝ] E
  ambient_symmetric : A.IsSymmetric
  trial_symmetric : A₀.IsSymmetric
  complement_symmetric : Λ₁.IsSymmetric
  exact_decomposition : OrthogonalExactDecomposition F₀ F₁
  intertwines : A ∘L F₁ = F₁ ∘L Λ₁
  gap : ℝ
  frameLowerBound : ℝ
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound X frameLowerBound
  spectral_gap : FormBoundedSylvesterGap
    ((A₀.toLinearMap.toPMap ⊤))
    ((Λ₁.toLinearMap.toPMap ⊤)) gap
  residual_mem : N.Mem
    (generalResidual A X A₀)

namespace RealBoundedGeneralSinThetaProblem

/-- Embed bounded real data into the real canonical unbounded package. -/
noncomputable def toGeneral
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (P : RealBoundedGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    RealGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N := by
  let D : UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := F) (G := G) := {
    A := (P.A.toLinearMap.toPMap ⊤)
    A₀ := (P.A₀.toLinearMap.toPMap ⊤)
    Λ₁ := (P.Λ₁.toLinearMap.toPMap ⊤)
    X := P.X
    F₁ := P.F₁
    residual := generalResidual P.A P.X P.A₀
    X_maps_domain := by intro x; simp
    F₁_maps_domain := by intro y; simp
    residual_eq := by
      intro x
      change P.A (P.X (x : F)) - P.X (P.A₀ (x : F)) =
        (generalResidual P.A P.X P.A₀) (x : F)
      simp only [generalResidual, ContinuousLinearMap.comp_apply, sub_apply]
    intertwines := by
      intro y
      have hy := congrArg (fun T : G →L[ℝ] E => T (y : G)) P.intertwines
      change P.A (P.F₁ (y : G)) = P.F₁ (P.Λ₁ (y : G))
      simpa only [ContinuousLinearMap.comp_apply] using hy
  }
  exact {
    data := D
    exactMap := P.F₀
    ambient_selfAdjoint :=
      TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.ambient_symmetric)
    trial_selfAdjoint :=
      TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.A₀)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.trial_symmetric)
    complement_selfAdjoint :=
      TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.Λ₁)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.complement_symmetric)
    exact_decomposition := P.exact_decomposition
    gap := P.gap
    frameLowerBound := P.frameLowerBound
    gap_pos := P.gap_pos
    frameLowerBound_pos := P.frameLowerBound_pos
    lowerFrame := P.lowerFrame
    spectral_gap := P.spectral_gap
    residual_mem := P.residual_mem
  }

/-- Bounded real generalized theorem derived through the canonical real
unbounded theorem. -/
theorem result
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (P : RealBoundedGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        (directedSinThetaOperatorReal P.X P.F₀ P.lowerFrame
          P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.gauge
            (directedSinThetaOperatorReal P.X P.F₀ P.lowerFrame
              P.frameLowerBound_pos)
        ≤ N.gauge
            (generalResidual P.A P.X P.A₀) :=
  RealGeneralSinThetaProblem.result N (P.toGeneral N)

end RealBoundedGeneralSinThetaProblem

end

end ExactSinTheta
end DavisKahan
end TauCeti
