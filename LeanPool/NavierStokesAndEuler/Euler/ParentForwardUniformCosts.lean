/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceUniformEnvelope
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCoefficientBudgets
import LeanPool.NavierStokesAndEuler.Euler.ParentForwardRadiusPolynomial

/-! The actual first-normal-stage geometry supplies the same polynomial
source guard for its direct-forward packet. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketSourceGeometry
  EulerParentInitializedRadius EulerPacketUniformSource EulerPacketTerminalDatum
  EulerPacketCylinderField EulerMeanHarmonic

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {G : Parent} (L : LabelData G) (H : LowBounds G)
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S)
  (P : ParentFrame (G.transverseData m hm R S hS) 0) (J : ForwardGuards P)
  (hball : (1 / 2 : ℝ) ≤ J.radius)
  (Ti : ℝ) (hT1 : G.T ≤ 1) (hTi : G.T⁻¹ ≤ Ti)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
  (hsub : S ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))

local notation "A" => L.geometryForwardInputs H m hm R S hS P J hball
  Ω hΩ hΩo hsub hΩball Ti hT1 hTi
local notation "BC" => forwardCoefficientBudget period (G.meanData H)
  (G.transverseData m hm R S hS) rfl (ForwardInputs.normal A)

/-- Geometry forward parameter size, given by `parameterSize L.K 0 Ti
(560*P.horizon^10/P.epsilon) H.L J.δ ‖ξ‖+J.hchild`. -/
def geometryForwardParameterSize (ξ : U) : ℝ :=
  parameterSize L.K 0 Ti (560*P.horizon^10/P.epsilon) H.L J.δ ‖ξ‖+J.hchild

theorem geometryForward_uniform_primitives (ξ : U) (hδ : 0 < J.δ) (hδ1 : J.δ ≤ 1) :
    let X := L.geometryForwardParameterSize H m hm R S hS P J Ti ξ
    EulerPacketForwardRadius.RadiusPrimitives (A).linear (A).mean (A).normal BC J.δ ξ
      (profileEnvelope X) ∧
    (∀ t, J.primaryAmplitude hball*(A).linear.g t ≤ profileEnvelope X) ∧
    EulerPacketInitializedOutputCost.uniformConstant *
      (profileEnvelope X)^EulerPacketInitializedOutputCost.uniformPower ≤
      frequencyConstant*X^frequencyPower := by
  let X := L.geometryForwardParameterSize H m hm R S hS P J Ti ξ
  have hL0 : 0 ≤ H.L := (mul_nonneg boundaryLocalizationC1_nonneg H.Bc_nonneg).trans H.L_lower
  obtain ⟨hx,hK,_,hI,hC,hB,hD,hN⟩ := parameterSize_bounds L.K 0 Ti
    (560*P.horizon^10/P.epsilon) H.L J.δ ‖ξ‖ (zero_le_one.trans L.K_one) le_rfl
    ((inv_pos.mpr G.T_pos).le.trans hTi) J.growth_constant_pos.le hL0 hδ (norm_nonneg ξ)
  have hbase : parameterSize L.K 0 Ti (560*P.horizon^10/P.epsilon) H.L J.δ ‖ξ‖ ≤ X :=
    le_add_of_nonneg_right J.child_nonneg
  have hX : 1 ≤ X := hx.trans hbase
  have hhX : J.hchild ≤ X := le_add_of_nonneg_left (zero_le_one.trans hx)
  have hp := L.geometryForward_radius_primitives H m hm R S hS P J hball
    Ω hΩ hΩo hsub hΩball Ti hT1 hTi J.δ ξ X
    (hK.trans hbase) (hI.trans hbase) (hC.trans hbase) (hB.trans hbase)
    (hD.trans hbase) (hN.trans hbase)
  have hu := J.source_uniform_primitives hball (A).linear rfl (A).mean (A).normal
    BC ξ X hX hhX hδ1 hp
  exact ⟨hu.1,hu.2,frequency_bound X hX⟩

end EulerParentPacketFrames.LabelData
