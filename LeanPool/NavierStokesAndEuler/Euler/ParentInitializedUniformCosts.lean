/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceUniformEnvelope
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketJoinedInput
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryJoinedBudget

/-! The actual parent and chosen geometric profile supply every primitive
of the uniform correction and physical-output comparison. -/

section

/-! The actual activation geometry fills the remaining propagator input
in the parent-to-packet constructor. All three source budgets share one
radius and retain the growth profile derived from that geometry. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketSourceGeometry

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {G : Parent} (L : LabelData G) (H : LowBounds G)
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)
  (J : Guards hτ hτT P (G.historyOn H m hm R S hS τ hτ hτT))
  (hball : (1 / 2 : ℝ) ≤ J.radius)
  (Ti TiTotal : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)
  (hT1 : G.T ≤ 1) (hTiTotal : G.T⁻¹ ≤ TiTotal)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
  (hsub : S ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))

/-- Geometry inputs, constructed using `L.joinedInputs`. -/
def geometryInputs :
    JoinedInputs (G.meanData H) (G.transverseData m hm R S hS) τ hτ hτT
      (G.historyOn H m hm R S hS τ hτ hτT) :=
  L.joinedInputs H m hm R S hS τ hτ hτT Ti (560*P.horizon^10/P.epsilon)
    hτ1 hTi J.growth_constant_pos.le (J.sourceGrowthProfile hball)
    (J.sourceGrowthProfile_positive hball) (J.sourceGrowthProfile_initial hball)
    Ω hΩ hΩo hsub hΩball (J.sourceGrowthProfile_propagator hball) TiTotal hT1 hTiTotal

theorem geometryInputs_growth :
    (L.geometryInputs H m hm R S hS τ hτ hτT P J hball Ti TiTotal hτ1 hTi
      hT1 hTiTotal Ω hΩ hΩo hsub hΩball).linear.g=J.sourceGrowthProfile hball := rfl

end EulerParentPacketFrames.LabelData

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketSourceGeometry
  EulerParentInitializedRadius EulerPacketUniformSource EulerPacketTerminalDatum
  EulerPacketCylinderField EulerMeanHarmonic

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {G : Parent} (L : LabelData G) (H : LowBounds G)
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)
  (J : Guards hτ hτT P (G.historyOn H m hm R S hS τ hτ hτT))
  (hball : (1 / 2 : ℝ) ≤ J.radius)
  (Ti TiTotal : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)
  (hT1 : G.T ≤ 1) (hTiTotal : G.T⁻¹ ≤ TiTotal)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
  (hsub : S ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))

local notation "A" => L.geometryInputs H m hm R S hS τ hτ hτT P J hball Ti TiTotal
  hτ1 hTi hT1 hTiTotal Ω hΩ hΩo hsub hΩball
local notation "BC" => joinedCoefficientBudget period (G.meanData H)
  (G.transverseData m hm R S hS) rfl τ hτ hτT (G.historyOn H m hm R S hS τ hτ hτT)
  (JoinedInputs.normal A)

/-- Geometry parameter size, given by `parameterSize L.K Ti TiTotal (560*P.horizon^10/P.epsilon)
H.L J.δ ‖ξ‖+J.hchild`. -/
def geometryParameterSize (ξ : U) : ℝ :=
  parameterSize L.K Ti TiTotal (560*P.horizon^10/P.epsilon) H.L J.δ ‖ξ‖+J.hchild

theorem geometry_uniform_primitives (ξ : U) (hδ : 0 < J.δ) (hδ1 : J.δ ≤ 1) :
    let X := L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ
    EulerPacketRadiusPolynomial.RadiusPrimitives (A).mean (A).linear (A).normal BC J.δ ξ
      (profileEnvelope X) ∧
    (∀ t, J.primaryAmplitude hball*(A).linear.fullProfile t ≤ profileEnvelope X) ∧
    EulerPacketInitializedOutputCost.uniformConstant *
      (profileEnvelope X)^EulerPacketInitializedOutputCost.uniformPower ≤
      frequencyConstant*X^frequencyPower := by
  let X := L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ
  have hL0 : 0 ≤ H.L := (mul_nonneg boundaryLocalizationC1_nonneg H.Bc_nonneg).trans H.L_lower
  obtain ⟨hx,hK,hI,hIT,hC,hB,hD,hN⟩ := parameterSize_bounds L.K Ti TiTotal
    (560*P.horizon^10/P.epsilon) H.L J.δ ‖ξ‖ (zero_le_one.trans L.K_one)
    ((inv_pos.mpr hτ).le.trans hTi) ((inv_pos.mpr G.T_pos).le.trans hTiTotal)
    J.growth_constant_pos.le hL0 hδ (norm_nonneg ξ)
  have hbase : parameterSize L.K Ti TiTotal (560*P.horizon^10/P.epsilon) H.L J.δ ‖ξ‖ ≤ X :=
    le_add_of_nonneg_right J.child_nonneg
  have hX : 1 ≤ X := hx.trans hbase
  have hhX : J.hchild ≤ X := le_add_of_nonneg_left (zero_le_one.trans hx)
  have hp := L.joined_radius_primitives H m hm R S hS τ hτ hτT Ti
    (560*P.horizon^10/P.epsilon) hτ1 hTi J.growth_constant_pos.le
    (J.sourceGrowthProfile hball) (J.sourceGrowthProfile_positive hball)
    (J.sourceGrowthProfile_initial hball) Ω hΩ hΩo hsub hΩball
    (J.sourceGrowthProfile_propagator hball) TiTotal hT1 hTiTotal J.δ ξ X
    (hK.trans hbase) (hI.trans hbase) (hIT.trans hbase) (hC.trans hbase)
    (hB.trans hbase) (hD.trans hbase) (hN.trans hbase)
  have hu := J.source_uniform_primitives hball (A).linear rfl (A).mean (A).normal
    BC ξ X hX hhX hδ1 hp
  exact ⟨hu.1,hu.2,frequency_bound X hX⟩

end EulerParentPacketFrames.LabelData
