/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceUniformEnvelope
public import LeanPool.NavierStokesAndEuler.Euler.BasePacketSetup
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCoefficientBudgets
public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketForwardInput

/-! The concrete compact base Euler solution supplies a uniform polynomial
source envelope for its first packet, independent of beta and the support scale. -/

section

/-! The genuine short-time forward factory obeys the same source
polynomial, using its proved constant profile and physical propagator cost 2. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerGevrey EulerMeanHarmonic EulerPacketParentLabelBounds
  EulerParentCoefficientPolynomial EulerParentCorrectionCost EulerPacketSourceRadius
  EulerParentInitializedRadius EulerPacketTerminalDatum EulerPacketCylinderField
  EulerTransversePacketProvider

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {A : Parent} (L : LabelData A) (H : LowBounds A)
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S)
  (CM : ℝ) (hCM : 0 ≤ CM)
  (hM : ∀ t x, ‖x‖ ≤ (1 / 2 : ℝ) → ‖A.strain.field t x‖ ≤ CM)
  (hshort : CM * A.T ≤ 1 / 2)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
  (hsub : S ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
  (Ti : ℝ) (hT1 : A.T ≤ 1) (hTi : A.T⁻¹ ≤ Ti)

local notation "J" => L.forwardInputs H m hm R S hS CM hCM hM Ω hΩ hΩo hsub hΩball hshort Ti hT1 hTi
local notation "BC" => forwardCoefficientBudget period (A.meanData H) (A.transverseData m hm R S hS)
  rfl (ForwardInputs.normal J)
local notation "Cp" => (2 : ℝ)

/-- Short forward canonical radius, given by `EulerPacketForwardRadius.canonicalRadius
(J).linear (J).mean (J).normal BC δ ξ`. -/
def shortForwardCanonicalRadius (δ : ℝ) (ξ : U) : ℝ :=
  EulerPacketForwardRadius.canonicalRadius (J).linear (J).mean (J).normal BC δ ξ

theorem shortForward_radius_primitives (δ : ℝ) (ξ : U) (X : ℝ)
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
    hb.2.2.2.2 Cp (by norm_num : (0 : ℝ) ≤ 2) hCpX
  obtain ⟨_,hr,hgK,hf,hh,hn,hni,hnr,hgram,hi,_⟩ := leaf_bounds L.K hK0
  have hTi0 : 0 ≤ Ti := (inv_pos.mpr A.T_pos).le.trans hTi
  have hL0 : 0 ≤ H.L := (mul_nonneg boundaryLocalizationC1_nonneg H.Bc_nonneg).trans H.L_lower
  have hRs : L.scaledRadius ≤ coefficientRadius L.K := by
    unfold scaledRadius
    exact mul_le_of_le_one_left (coefficientRadius_nonneg L.K) A.ell_le_one
  have hIs : EulerPacketParentTransverseCosts.inverseRadius L.scaledRadius (frameAmplitude L.K) ≤
      EulerPacketParentTransverseCosts.inverseRadius (coefficientRadius L.K) (frameAmplitude L.K)
          := by
    have hF := frameAmplitude_nonneg L.K
    unfold EulerPacketParentTransverseCosts.inverseRadius
        EulerPacketParentMeanCoercivity.gramInverseEnvelope
    gcongr
  have hFW : 6*(frameAmplitude L.K)^3 ≤ W := by
    convert hPW using 1; unfold EulerPacketParentPhysicalBudgets.physicalCost; ring
  have hraw : EulerPacketParentForwardBudget.radius 6 A.T
      L.scaledRadius (frameAmplitude L.K) (gradientAmplitude L.K)
      (6*(frameAmplitude L.K)^3) ≤ V :=
    EulerPacketForwardRadius.source_radius_le A.T L.scaledRadius (frameAmplitude L.K)
      (gradientAmplitude L.K) (6*(frameAmplitude L.K)^3) W hW
      A.T_pos.le hT1 L.scaledRadius_nonneg (hRs.trans (hr.trans hLW))
      (frameAmplitude_nonneg L.K) (hf.trans hLW) (gradientAmplitude_nonneg L.K) (hgK.trans hLW)
      (by positivity [frameAmplitude_nonneg L.K]) hFW (hIs.trans (hi.trans hLW))
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
    forward_radius := hRs.trans (hr.trans hLV)
    forward_frame := hf.trans hLV
    forward_first := hgK.trans hLV
    forward_inverse := hIs.trans (hi.trans hLV)
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

theorem shortForward_radius_primitive_polynomial (δ : ℝ) (hδ : 0 < δ) (ξ : U) :
    let X := parameterSize L.K 0 Ti 2 H.L δ ‖ξ‖
    EulerPacketForwardRadius.RadiusPrimitives (J).linear (J).mean (J).normal BC δ ξ (sourceEnvelope
        X) ∧
      sourceEnvelope X ≤ sourceConstant*X^sourcePower := by
  have hL0 : 0 ≤ H.L := (mul_nonneg boundaryLocalizationC1_nonneg H.Bc_nonneg).trans H.L_lower
  obtain ⟨h1,hK,_,hIT,hC,hB,hD,hN⟩ := parameterSize_bounds L.K 0 Ti 2 H.L δ ‖ξ‖
    (zero_le_one.trans L.K_one) le_rfl ((inv_pos.mpr A.T_pos).le.trans hTi)
    (by norm_num) hL0 hδ (norm_nonneg ξ)
  exact ⟨L.shortForward_radius_primitives H m hm R S hS CM hCM hM hshort
    Ω hΩ hΩo hsub hΩball Ti hT1 hTi δ ξ _ hK hIT hC hB hD hN,sourceEnvelope_power _ h1⟩

end EulerParentPacketFrames.LabelData

end
end

end

@[expose] public section

noncomputable section

namespace EulerBaseDatum

open Set EulerSmoothLimit EulerPacketSupport EulerParentPacketFrames
  EulerPacketTerminalDatum EulerPacketCylinderField EulerPacketUniformSource
  EulerParentInitializedRadius

/-- First parameter size, given by `4+solutionLabelConstant+T⁻¹+δ⁻¹+hchild`. -/
def firstParameterSize (T δ hchild : ℝ) : ℝ :=
  4+solutionLabelConstant+T⁻¹+δ⁻¹+hchild

theorem firstParameterSize_bounds (T δ hchild : ℝ) (hT : 0 < T) (hδ : 0 < δ)
    (hh : 0 ≤ hchild) :
    1 ≤ firstParameterSize T δ hchild ∧ solutionLabelConstant ≤ firstParameterSize T δ hchild ∧
    T⁻¹ ≤ firstParameterSize T δ hchild ∧ 2 ≤ firstParameterSize T δ hchild ∧
    δ⁻¹ ≤ firstParameterSize T δ hchild ∧ hchild ≤ firstParameterSize T δ hchild := by
  have hK := solutionLabelConstant_one
  have hTi := (inv_pos.mpr hT).le
  have hdi := (inv_pos.mpr hδ).le
  unfold firstParameterSize
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (T : ℝ) (hT : 0 < T) (hTB : T ≤ initialTime)

local notation "A" => firstPacketInputs β hβ ell hell hell1 T hT hTB
local notation "G" => packetBaseParent β hβ ell hell hell1 T hT hTB
local notation "L" => SmoothState.labels (packetBaseState β hβ ell hell hell1 T hT hTB)
local notation "H" => packetBaseLowBounds β hβ ell hell hell1 T hT hTB
local notation "D" => Parent.transverseData G firstNormal firstNormal_unit firstFrame support
    compact
local notation "BC" => forwardCoefficientBudget period (Parent.meanData G H) D rfl
    (ForwardInputs.normal A)

theorem firstPacket_uniform_primitives (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hchild : ℝ) (hh : 0 ≤ hchild) :
    let X := firstParameterSize T δ hchild
    EulerPacketForwardRadius.RadiusPrimitives (A).linear (A).mean (A).normal BC δ firstCoordinate
      (profileEnvelope X) ∧
    (∀ t, (δ*hchild)*(A).linear.g t ≤ profileEnvelope X) ∧
    EulerPacketInitializedOutputCost.uniformConstant *
      (profileEnvelope X)^EulerPacketInitializedOutputCost.uniformPower ≤
      frequencyConstant*X^frequencyPower := by
  let X := firstParameterSize T δ hchild
  obtain ⟨hX,hK,hTi,h2,hd,hhX⟩ := firstParameterSize_bounds T δ hchild hT hδ hh
  have hr := (L).shortForward_radius_primitives H firstNormal firstNormal_unit firstFrame support
      compact
    initialCoefficientCost initialCoefficientCost_nonneg
    (fun t x _ => packetBase_strain_bound β hβ ell hell hell1 T hT hTB t x)
    (packetBase_short T hTB) (Metric.ball 0 (1/2 : ℝ)) Metric.isOpen_ball.measurableSet
    Metric.isOpen_ball subset_halfBall
    (fun x hx => le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hx))
    T⁻¹ (hTB.trans initialTime_le_one) le_rfl δ firstCoordinate X hK hTi h2
    (zero_le_one.trans hX) hd (by simpa only [firstCoordinate_norm] using hX)
  have hSX : X ≤ sourceEnvelope X :=
    (inputEnvelope_bounds X X hX le_rfl).2.1.trans
      (EulerPacketSourceRadius.le_sourceRadiusEnvelope _
        (zero_le_one.trans (inputEnvelope_bounds X X hX le_rfl).1))
  refine ⟨hr.mono (profileEnvelope_bounds X hX).2.1,?_,frequency_bound X hX⟩
  intro t
  change (δ*hchild)*1 ≤ _
  rw [mul_one]
  exact ((mul_le_mul_of_nonneg_right hδ1 hh).trans_eq (one_mul _)).trans
    (hhX.trans (hSX.trans (profileEnvelope_bounds X hX).2.1))

end EulerBaseDatum
