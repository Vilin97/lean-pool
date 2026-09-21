/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.Canonical

/-! # Specializations -/

open TauCeti.DavisKahan.Sylvester

/-!
# Specialization bridges from the canonical unbounded sine theorem

This module records how bounded problems enter the canonical API.  The
lower-frame bridge is complex because it uses the positive continuous
functional calculus.  The independent scalar-generic isometric theorem in
`Bounded.lean` remains available.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

section Complex

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded data packaged for derivation from the canonical generalized
unbounded theorem. -/
structure BoundedGeneralSinThetaProblem
    (N : KyFanDominantIdealFamily (𝕜 := ℂ)) where
  A : E →L[ℂ] E
  A₀ : F →L[ℂ] F
  Λ₁ : G →L[ℂ] G
  X : F →L[ℂ] E
  F₀ : H →L[ℂ] E
  F₁ : G →L[ℂ] E
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

namespace BoundedGeneralSinThetaProblem

/-- Embed a bounded problem into the full-domain closed-operator problem used
by the canonical theorem. -/
noncomputable def toGeneral
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (P : BoundedGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    FormBoundedGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N := by
  let D : UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := F) (G := G) := {
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
      have hy := congrArg (fun T : G →L[ℂ] E => T (y : G)) P.intertwines
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

/-- Bounded generalized sine theorem derived from the canonical theorem. -/
theorem result
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (P : BoundedGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        (directedSinThetaOperator P.X P.F₀ P.lowerFrame
          P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.gauge
            (directedSinThetaOperator P.X P.F₀ P.lowerFrame
              P.frameLowerBound_pos)
        ≤ N.gauge
            (generalResidual P.A P.X P.A₀) :=
  FormBoundedGeneralSinThetaProblem.result N (P.toGeneral N)

end BoundedGeneralSinThetaProblem

end Complex

section Generic

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Convert the bounded interval/exterior predicate to the legacy
closed-operator gap predicate.  Both predicates use the same legacy spectrum
by definition. -/
theorem intervalExteriorGap_to_unbounded
    {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    {β α δ : ℝ}
    (hgap : IntervalExteriorGap A B β α δ) :
    RealSpectrumIntervalExteriorGap
      ((A.toLinearMap.toPMap ⊤))
      ((B.toLinearMap.toPMap ⊤))
      β α δ := by
  exact hgap

end Generic

end ExactSinTheta
end DavisKahan
end TauCeti
