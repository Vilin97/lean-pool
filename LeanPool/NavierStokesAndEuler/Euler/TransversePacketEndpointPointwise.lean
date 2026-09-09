/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointPointwise
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketEndpoint
public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalInitialData

@[expose] public section

/-!
The actual compact-terminal source history is the manuscript's pointwise
stationary history multiplied by the literal cutoff and periodic wave.
-/

noncomputable section

namespace EulerTransversePacketProvider.Data

open ContinuousLinearMap EulerSmoothLimit EulerTransverseFrameCoordinates EulerTransverseSourceFrame

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)

def coordinateEmbedding : U →L[ℝ] Space := referenceEmbedding D.m₀ D.R

def coordinateRetraction : Space →L[ℝ] U :=
  D.R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (referencePlane D.m₀).orthogonalProjectionOnto

theorem coordinateRetraction_embedding (v : U) :
    D.coordinateRetraction (D.coordinateEmbedding v) = v := by
  change D.R.symm ((referencePlane D.m₀).orthogonalProjectionOnto (D.R v : Space)) = v
  rw [(referencePlane D.m₀).orthogonalProjectionOnto_mem_subspace_eq_self]
  exact D.R.symm_apply_apply v

end EulerTransversePacketProvider.Data

namespace EulerTransversePacketEndpoint

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerMetricTransport EulerCylinderSmoothOrbit
  EulerTransversePacketProvider

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D) (Y : InitialData P D)

theorem velocityPath_eq_history (f : LiftDomain P → U) (hf : Continuous f)
    (hrep : (Y.value : CylinderL2 P U) =ᵐ[liftMeasure P] f)
    (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    pointField P (velocityPath B Y) (velocityPath_orbit B Y) t x =
      B.coefficients.labelVelocity x.1 (f x) t :=
  B.coefficients.endpointVelocity_pointwise P D.coordinateEmbedding D.coordinateRetraction
    D.frame.translation_contDiff D.frameDerivative.translation_contDiff B.H.translation_contDiff
    Y.value Y.orbit D.coordinateRetraction_embedding f hf hrep x t

end EulerTransversePacketEndpoint

namespace EulerPacketTerminalDatum

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMetricTransport
  EulerLpCylinderTranslation EulerTransversePacketProvider EulerTransversePacketEndpoint
  EulerCylinderSmoothOrbit EulerSpatialCutoffs

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D) (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support)

theorem compact_wave_history (t : Icc (0 : ℝ) D.T) (x : LiftDomain period) :
    pointField period (velocityPath B (initialData D δ hδ ξ hs))
      (velocityPath_orbit B (initialData D δ hδ ξ hs)) t x =
      scalarField δ x • B.coefficients.labelVelocity x.1 ξ t := by
  rw [velocityPath_eq_history B (initialData D δ hδ ξ hs) (field δ ξ)
    (smoothField_continuous period _ (field_smooth δ hδ ξ)) (terminal_ae δ hδ ξ)]
  change B.coefficients.labelVelocity x.1 (scalarField δ x • ξ) t = _
  rw [map_smul,ContinuousMap.smul_apply]

end EulerPacketTerminalDatum
