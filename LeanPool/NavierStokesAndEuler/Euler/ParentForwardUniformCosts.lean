/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceUniformEnvelope
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCoefficientBudgets
public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.ParentForwardGeometryInput

/-! The actual first-normal-stage geometry supplies the same polynomial
source guard for its direct-forward packet. -/

section

/-! The first normal stage's actual direct-forward factory has a canonical
radius controlled by the same fixed parent polynomial. Its genuine geometric
propagator constant is retained, without replacing the growth profile. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerGevrey EulerMeanHarmonic EulerPacketParentLabelBounds
  EulerParentCoefficientPolynomial EulerParentCorrectionCost EulerPacketSourceRadius
  EulerParentInitializedRadius EulerPacketTerminalDatum EulerPacketCylinderField
  EulerTransversePacketProvider EulerPacketSourceGeometry

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {A : Parent} (L : LabelData A) (H : LowBounds A)
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S)
  (P : ParentFrame (A.transverseData m hm R S hS) 0) (G : ForwardGuards P)
  (hball : (1 / 2 : ℝ) ≤ G.radius)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
  (hsub : S ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
  (Ti : ℝ) (hT1 : A.T ≤ 1) (hTi : A.T⁻¹ ≤ Ti)

local notation "J" => L.geometryForwardInputs H m hm R S hS P G hball Ω hΩ hΩo hsub hΩball Ti hT1
    hTi
local notation "BC" => forwardCoefficientBudget period (A.meanData H) (A.transverseData m hm R S hS)
  rfl (ForwardInputs.normal J)
local notation "Cp" => (560*P.horizon^10/P.epsilon)

/-- Geometry canonical radius, given by `EulerPacketForwardRadius.canonicalRadius (J).linear
(J).mean (J).normal BC δ ξ`. -/
def geometryCanonicalRadius (δ : ℝ) (ξ : U) : ℝ :=
  EulerPacketForwardRadius.canonicalRadius (J).linear (J).mean (J).normal BC δ ξ

theorem geometryForward_radius_primitives (δ : ℝ) (ξ : U) (X : ℝ)
    (hKX : L.K ≤ X) (hTiX : Ti ≤ X) (hCpX : Cp ≤ X)
    (hLX : H.L ≤ X) (hδX : δ⁻¹ ≤ X) (hξX : ‖ξ‖ ≤ X) :
    EulerPacketForwardRadius.RadiusPrimitives (J).linear (J).mean (J).normal BC δ ξ (sourceEnvelope
        X) := by
  let W := inputEnvelope X
  let V := sourceRadiusEnvelope W
  have hK0 := zero_le_one.trans L.K_one
  have hb := inputEnvelope_bounds L.K X L.K_one hKX
  have hW : 1 ≤ W := hb.1
  have hW0 := zero_le_one.trans hW
  have hWV : W ≤ V := le_sourceRadiusEnvelope W hW0
  have hXV : X ≤ V := hb.2.1.trans hWV
  have hLW : leafEnvelope L.K ≤ W := hb.2.2.1
  have hLV := hLW.trans hWV
  have hPW : EulerPacketParentPhysicalBudgets.physicalCost L.K Cp ≤ W :=
    hb.2.2.2.2 Cp G.growth_constant_pos.le hCpX
  obtain ⟨_,hr,hgK,hf,hh,hn,hni,hnr,hgram,hi,_⟩ := leaf_bounds L.K hK0
  have hTi0 : 0 ≤ Ti := (inv_pos.mpr A.T_pos).le.trans hTi
  have hL0 : 0 ≤ H.L := (mul_nonneg boundaryLocalizationC1_nonneg H.Bc_nonneg).trans H.L_lower
  have hraw : EulerPacketParentForwardBudget.radius 6 A.T
      (coefficientRadius L.K) (frameAmplitude L.K) (gradientAmplitude L.K)
      (EulerPacketParentPhysicalBudgets.physicalCost L.K Cp) ≤ V :=
    EulerPacketForwardRadius.source_radius_le A.T (coefficientRadius L.K) (frameAmplitude L.K)
      (gradientAmplitude L.K) (EulerPacketParentPhysicalBudgets.physicalCost L.K Cp) W hW
      A.T_pos.le hT1 (coefficientRadius_nonneg L.K) (hr.trans hLW)
      (frameAmplitude_nonneg L.K) (hf.trans hLW) (gradientAmplitude_nonneg L.K) (hgK.trans hLW)
      (EulerPacketParentPhysicalBudgets.physicalCost_nonneg L.K Cp G.growth_constant_pos.le) hPW
          (hi.trans hLW)
  have hmean : EulerPacketParentMeanBudget.radius 6 A.T Ti (coefficientRadius L.K)
      (frameAmplitude L.K) (gradientAmplitude L.K) (gradientAmplitude L.K) H.L ≤ V :=
    mean_radius_le A.T Ti (coefficientRadius L.K) (frameAmplitude L.K)
      (gradientAmplitude L.K) (gradientAmplitude L.K) H.L W hW A.T_pos.le hT1 hTi0
      (hTiX.trans hb.2.1) (coefficientRadius_nonneg L.K) (hr.trans hLW)
      (frameAmplitude_nonneg L.K) (hf.trans hLW) (gradientAmplitude_nonneg L.K) (hgK.trans hLW)
      (gradientAmplitude_nonneg L.K) hL0 (hLX.trans hb.2.1) (hh.trans hLW)
      ((leaf_bounds L.K hK0).2.2.2.2.2.2.2.2.2.2.trans hLW) (hgram.trans hLW)
  have hJR : (J).linear.R ≤ V := by
    change max _ (max _ _) ≤ V
    exact max_le hraw (max_le (hnr.trans hLV) hmean)
  have hBC := (BC).parent_primitive_bound L.K hK0 hr hn
  change EulerPacketForwardRadius.RadiusPrimitives (J).linear (J).mean (J).normal BC δ ξ V
  exact {
    one := hW.trans hWV
    total_time := hT1
    mean_time := hT1
    mean_inverse_time := hTi.trans (hTiX.trans hXV)
    original_forward := hJR
    original_mean := hJR
    forward_radius := hr.trans hLV
    forward_frame := hf.trans hLV
    forward_first := hgK.trans hLV
    forward_inverse := hi.trans hLV
    normal_radius := hr.trans hLV
    normal_amplitude := hn.trans hLV
    normal_inverse := hni.trans hLV
    mean_radius := hr.trans hLV
    mean_frame := hf.trans hLV
    mean_first := hgK.trans hLV
    mean_forcing := hW.trans hWV
    coefficient_radius := hr.trans hLV
    coefficient_cost := hBC.2.trans (hb.2.2.2.1.trans hWV)
    delta_inverse := hδX.trans hXV
    terminal := hξX.trans hXV }

theorem geometryCanonicalRadius_power (δ : ℝ) (hδ : 0 < δ) (ξ : U) (X : ℝ)
    (hKX : L.K ≤ X) (hTiX : Ti ≤ X) (hCpX : Cp ≤ X)
    (hLX : H.L ≤ X) (hδX : δ⁻¹ ≤ X) (hξX : ‖ξ‖ ≤ X) :
    L.geometryCanonicalRadius H m hm R S hS P G hball Ω hΩ hΩo hsub hΩball Ti hT1 hTi δ ξ ≤
      fullConstant*X^fullPower := by
  have hp := L.geometryForward_radius_primitives H m hm R S hS P G hball Ω hΩ hΩo hsub hΩball
    Ti hT1 hTi δ ξ X hKX hTiX hCpX hLX hδX hξX
  exact (EulerPacketForwardRadius.canonicalRadius_le_envelope (J).linear (J).mean (J).normal BC δ ξ
    (sourceEnvelope X) hδ hp).trans (fullEnvelope_power X (L.K_one.trans hKX))

theorem geometryForward_radius_primitive_polynomial (δ : ℝ) (hδ : 0 < δ) (ξ : U) :
    let X := parameterSize L.K 0 Ti Cp H.L δ ‖ξ‖
    EulerPacketForwardRadius.RadiusPrimitives (J).linear (J).mean (J).normal BC δ ξ (sourceEnvelope
        X) ∧
      sourceEnvelope X ≤ sourceConstant*X^sourcePower := by
  have hL0 : 0 ≤ H.L := (mul_nonneg boundaryLocalizationC1_nonneg H.Bc_nonneg).trans H.L_lower
  obtain ⟨h1,hK,_,hIT,hC,hB,hD,hN⟩ := parameterSize_bounds L.K 0 Ti Cp H.L δ ‖ξ‖
    (zero_le_one.trans L.K_one) le_rfl ((inv_pos.mpr A.T_pos).le.trans hTi)
    G.growth_constant_pos.le hL0 hδ (norm_nonneg ξ)
  exact ⟨L.geometryForward_radius_primitives H m hm R S hS P G hball Ω hΩ hΩo hsub hΩball
    Ti hT1 hTi δ ξ _ hK hIT hC hB hD hN,sourceEnvelope_power _ h1⟩

theorem geometryCanonicalRadius_polynomial (δ : ℝ) (hδ : 0 < δ) (ξ : U) :
    L.geometryCanonicalRadius H m hm R S hS P G hball Ω hΩ hΩo hsub hΩball Ti hT1 hTi δ ξ ≤
      fullConstant*(parameterSize L.K 0 Ti Cp H.L δ ‖ξ‖)^fullPower := by
  have hL0 : 0 ≤ H.L := (mul_nonneg boundaryLocalizationC1_nonneg H.Bc_nonneg).trans H.L_lower
  obtain ⟨_,hK,_,hIT,hC,hB,hD,hN⟩ := parameterSize_bounds L.K 0 Ti Cp H.L δ ‖ξ‖
    (zero_le_one.trans L.K_one) le_rfl ((inv_pos.mpr A.T_pos).le.trans hTi)
    G.growth_constant_pos.le hL0 hδ (norm_nonneg ξ)
  exact L.geometryCanonicalRadius_power H m hm R S hS P G hball Ω hΩ hΩo hsub hΩball
    Ti hT1 hTi δ hδ ξ _ hK hIT hC hB hD hN

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
