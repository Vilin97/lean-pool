/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SinTheta.Canonical
import LeanPool.DavisKahan.DavisKahan.SinTheta.Real.Generalized

/-! # Canonical -/

open TauCeti.DavisKahan.Sylvester

/-!
# Real source-shaped unbounded sine-theta problems

The complex source package is retained unchanged.  This module supplies the
parallel real lower-frame package and clean real result fields, while reusing
the scalar-generic isometric input package.
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

/-- Complete real input package for the generalized unbounded theorem. -/
structure RealGeneralSinThetaProblem
    (N : KyFanDominantIdealFamily (𝕜 := ℝ)) where
  /-- The ambient, trial, and complementary operator data for the sine-angle problem. -/
  data : UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := F) (G := G)
  /-- The isometric parametrization of the exact subspace in the orthogonal decomposition. -/
  exactMap : H →L[ℝ] E
  ambient_selfAdjoint : _root_.IsSelfAdjoint data.A
  trial_selfAdjoint : _root_.IsSelfAdjoint data.A₀
  complement_selfAdjoint : _root_.IsSelfAdjoint data.Λ₁
  exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁
  /-- The positive form gap between the trial operator and the complementary restriction. -/
  gap : ℝ
  /-- The positive lower frame bound for the trial map. -/
  frameLowerBound : ℝ
  gap_pos : 0 < gap
  frameLowerBound_pos : 0 < frameLowerBound
  lowerFrame : LowerFrameBound data.X frameLowerBound
  spectral_gap : FormBoundedSylvesterGap data.A₀ data.Λ₁ gap
  residual_mem : N.Mem data.residual

namespace RealGeneralSinThetaProblem

/-- Complete real generalized source target. -/
theorem result
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (P : RealGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        (directedSinThetaOperatorReal P.data.X P.exactMap
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.gauge
            (directedSinThetaOperatorReal P.data.X P.exactMap
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.gauge P.data.residual :=
  generalizedSinTheta_unbounded_exact_real
    N P.data P.exactMap P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.exact_decomposition P.gap_pos
      P.frameLowerBound_pos P.lowerFrame P.spectral_gap P.residual_mem

/-- Real generalized complementary-block source target. -/
theorem complementaryBlock_result
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (P : RealGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        (sinThetaBlockReal P.data.X P.data.F₁
          P.lowerFrame P.frameLowerBound_pos) ∧
      P.gap * P.frameLowerBound *
          N.gauge
            (sinThetaBlockReal P.data.X P.data.F₁
              P.lowerFrame P.frameLowerBound_pos)
        ≤ N.gauge P.data.residual :=
  generalizedSinTheta_unbounded_real
    N P.data P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.exact_decomposition.isometry₁ P.gap_pos
      P.frameLowerBound_pos P.lowerFrame P.spectral_gap P.residual_mem

end RealGeneralSinThetaProblem

namespace FormBoundedIsometricSinThetaProblem

/-- Real specialization of the source-shaped isometric problem. -/
theorem result_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (P : FormBoundedIsometricSinThetaProblem (𝕜 := ℝ) (E := E) (F := F)
      (G := G) (H := H) N) :
    N.Mem
        ((ContinuousLinearMap.id ℝ E -
          P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X) ∧
      P.gap * N.gauge
          ((ContinuousLinearMap.id ℝ E -
            P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X)
        ≤ N.gauge P.data.residual :=
  sinTheta_unbounded_exact_real
    N P.data P.exactMap P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.trial_isometry P.exact_decomposition
      P.gap_pos P.spectral_gap P.residual_mem

/-- Regard a real isometric problem as a real generalized problem with lower
frame constant one. -/
noncomputable def toGeneralReal
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (P : FormBoundedIsometricSinThetaProblem (𝕜 := ℝ) (E := E) (F := F)
      (G := G) (H := H) N) :
    RealGeneralSinThetaProblem (E := E) (F := F)
      (G := G) (H := H) N where
  data := P.data
  exactMap := P.exactMap
  ambient_selfAdjoint := P.ambient_selfAdjoint
  trial_selfAdjoint := P.trial_selfAdjoint
  complement_selfAdjoint := P.complement_selfAdjoint
  exact_decomposition := P.exact_decomposition
  gap := P.gap
  frameLowerBound := 1
  gap_pos := P.gap_pos
  frameLowerBound_pos := zero_lt_one
  lowerFrame := lowerFrameBound_one_of_isometry P.trial_isometry
  spectral_gap := P.spectral_gap
  residual_mem := P.residual_mem

end FormBoundedIsometricSinThetaProblem

end

end ExactSinTheta
end DavisKahan
end TauCeti
