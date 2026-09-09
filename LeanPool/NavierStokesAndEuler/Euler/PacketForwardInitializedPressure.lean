/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourcePressureAssembly
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedProfiles

@[expose] public section

/-! The finite zero-history pressure and its actual lifted gradient. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketPointJets
  EulerPacketPressure EulerPacketCoordinates EulerLiftedGradientSpace

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

def forwardInitializedPressure (N : ℕ) (κ : ℝ) : ScalarField :=
  fieldSum (N+1) κ (assembledPressure N (forwardInitializedProfiles M D δ hδ ξ hs α))

def forwardInitializedPressureWitness (N : ℕ) (κ : ℝ) :
    GradientWitness period M.T κ D.m₀ (forwardInitializedPressure M D δ hδ ξ hs α N κ) :=
  sourcePressureWitness period M D hTime (InitialData.zero period D)
    (initialData D δ hδ (α • ξ) hs) κ D.m₀ N κ

def forwardInitializedCoordinatePressureField (N : ℕ) (k : ℝ) (hk : k ≠ 0) :
    Field period D.T (coordinatePressure D k
      (forwardInitializedPressure M D δ hδ ξ hs α N k⁻¹)) :=
  pressureField D k hk
    ((forwardInitializedPressureWitness M D hTime δ hδ ξ hs α N k⁻¹).changeTime hTime)

theorem forwardInitializedCoordinatePressureField_mem (N : ℕ) (k : ℝ) (hk : k ≠ 0)
    (t : Icc (0 : ℝ) D.T) :
    (forwardInitializedCoordinatePressureField M D hTime δ hδ ξ hs α N k hk).path t ∈
      gradientSpace period k⁻¹ D.m₀ :=
  pressureField_mem D k hk _ t

end EulerPacketTerminalDatum
