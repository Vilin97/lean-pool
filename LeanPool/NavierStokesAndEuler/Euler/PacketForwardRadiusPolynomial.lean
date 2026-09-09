/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCommonRadius
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentForwardBudget

@[expose] public section

/-! The direct-forward source radius and its literal common-radius
enlargement obey the same fixed polynomial envelope as the joined branch.
The homogeneous growth constant is arbitrary and remains an input. -/

noncomputable section

namespace EulerPacketForwardRadius

open EulerParameterWordGevrey EulerPacketRadiusPolynomial EulerPacketSourceRadius
  EulerPacketTerminalDatum EulerPacketCylinderField EulerPacketProfileRecursion
  EulerTransversePacketProvider

theorem source_radius_le (T R C C1 Cp W : ℝ) (hW : 1 ≤ W)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (hR0 : 0 ≤ R) (hR : R ≤ W)
    (hC0 : 0 ≤ C) (hC : C ≤ W) (hC10 : 0 ≤ C1) (hC1 : C1 ≤ W)
    (hCp0 : 0 ≤ Cp) (hCp : Cp ≤ W)
    (hRi : EulerPacketParentTransverseCosts.inverseRadius R C ≤ W) :
    EulerPacketParentForwardBudget.radius 6 T R C C1 Cp ≤ sourceRadiusEnvelope W := by
  let V := primitiveLift W
  let Ri := EulerPacketParentTransverseCosts.inverseRadius R C
  have hW0 := zero_le_one.trans hW
  have hb := primitiveLift_bounds W hW0
  have hV : 1 ≤ V := hb.1
  have hV0 := zero_le_one.trans hV
  have hWV : W ≤ V := (by linarith : W ≤ W+2).trans hb.2.1
  have hCV : C ≤ V := hC.trans hWV
  have hC1V : C1 ≤ V := hC1.trans hWV
  have hRV : R ≤ V := hR.trans hWV
  have hi0 : 0 ≤ Ri := EulerPacketParentTransverseCosts.inverseRadius_nonneg R C hR0
  have hiv : Ri ≤ V := hRi.trans hWV
  have hpf := (projected_scalar_le Ri C W hi0 hC0 hW0 hRi hC).trans hb.2.2.2.2.2.2.2
  have hpf0 : 0 ≤ EulerSourceCylinderForwardSobolev.forcingCost (Fin 4) 6 Ri C := by
    have hc := coeff_nonneg (4*Ri) (3*Ri*C) (by positivity) (by positivity)
    unfold EulerSourceCylinderForwardSobolev.forcingCost
    positivity
  have hforward : EulerPacketParentTransverseCosts.forwardCost 6 T 0 R C C1 Cp ≤ forwardEnvelope V
    := by
    apply forward_scalar_le T Cp (0+2) _ (18*Ri*C*C1) (4*Ri) V
      hT0 hT1 hCp0 (by norm_num) hpf0 (by positivity) (by positivity) hV0
      (hCp.trans hWV) ((by linarith : 0+2 ≤ W+2).trans hb.2.1) hpf
    · calc
        18*Ri*C*C1 ≤ 18*V*V*V := by gcongr
        _ = _ := by ring
    · gcongr
  have hwi := weakEnvelope_lower_inputs V hV
  have hw1 : 1 ≤ weakEnvelope V := inverseBlockCost_one_le 6
    (hV0.trans hwi.1) hV0 (hV0.trans hwi.2.1) (hV0.trans hwi.2.2)
  have hfw := forwardEnvelope_nonneg V hV0
  unfold EulerPacketParentForwardBudget.radius
  simp only [coefficientRadius_eq]
  calc
    _ ≤ 1+16*V+16*(4*V)+2*forwardEnvelope V*(16*(4*V)+1) := by gcongr
    _ ≤ sourceRadiusEnvelope W := by
      change _ ≤ 1+V+6*weakEnvelope V*(16*V+1)+64*V+2*forwardEnvelope V*(64*V+1)
      nlinarith only [hV0,mul_nonneg (sub_nonneg.mpr hw1) (by positivity : 0 ≤ 16*V+1)]

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (L : EulerTransversePacketForward.Budget D (Fin 4) 6)

theorem inverse_nonneg : 0 ≤ L.Ri :=
  (EulerTransverseForwardCoefficientGevrey.inverseRadius_bounds D.frameLower L.C₀ L.Rc L.Ri
    D.frameLower_pos L.Rc_nonneg L.forward_inverse).1

theorem common_le (W : ℝ) (hW : 0 ≤ W) (hR : L.Rc ≤ W)
    (hC : L.C₀ ≤ W) (hC1 : L.C₁ ≤ W) (hI : L.Ri ≤ W) :
    L.commonCost ≤ commonEnvelope W := by
  have ha := coeff_nonneg W W hW hW
  have hc : coeff L.Rc L.C₀ ≤ coeff W W :=
    sobolevCoefficientAmplitude_mono_all 6 L.Rc_nonneg L.C₀_nonneg hR hC
  have hp := physicalCost_le L.Ri L.C₀ L.C₁ 1 1 W (inverse_nonneg L)
    L.C₀_nonneg L.C₁_nonneg zero_le_one zero_le_one hW hI hC hC1 le_rfl le_rfl
  unfold EulerTransversePacketForward.Budget.commonCost
    EulerTransversePacketForward.Budget.velocityCost
    EulerTransversePacketForward.Budget.derivativeCost
  calc
    _ ≤ 3*coeff W W+physicalEnvelope W := add_le_add (by gcongr) hp
    _ ≤ commonEnvelope W := by
      unfold commonEnvelope
      nlinarith only [ha,mul_nonneg ha (by positivity : 0 ≤ 2*W+2)]

theorem grade_sum_le (N : EulerTransversePacketJoin.NormalBudget D 6 L.R)
    (W : ℝ) (hW : 0 ≤ W) (hNR : N.Rc ≤ W) (hNC : N.C ≤ W) (hNI : N.Ri ≤ W)
    (hcommon : L.commonCost ≤ commonEnvelope W) :
    L.commonCost+L.correctorAmplitude (P := period) N+L.correctorTimeAmplitude (P := period) N+
      3*L.pressureAmplitude (P := period) N ≤ gradeEnvelope W := by
  have hn := normal_block_le N W hW hNR hNC hNI
  have hp := pressureCost_le N.Ri N.C 1 L.commonCost W N.Ri_nonneg N.C_nonneg zero_le_one
    L.commonCost_nonneg hW hNI hNC le_rfl hcommon
  have hN0 := N.blockAmplitude_nonneg
  have hN := normalEnvelope_nonneg W hW
  have hC0 := L.commonCost_nonneg
  have hC := commonEnvelope_nonneg W hW
  have hP := (Fact.out : 0 < period).le
  unfold EulerTransversePacketForward.Budget.correctorAmplitude
    EulerTransversePacketForward.Budget.correctorTimeAmplitude
    EulerTransversePacketForward.Budget.pressureAmplitude
  calc
    _ ≤ commonEnvelope W+27*(normalEnvelope W)^2*(period*commonEnvelope W)+
        108*(normalEnvelope W)^2*(period*commonEnvelope W)+3*(period*pressureEnvelope W) := by
          gcongr
    _ = _ := by unfold gradeEnvelope; ring

variable {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (N : EulerTransversePacketJoin.NormalBudget D 6 L.R) (BC : CoefficientBudget C)
  (δ : ℝ) (ξ : U)

def canonicalRadius : ℝ :=
  EulerPacketForwardCommonRadius.commonRadius LM L N BC
    (wordCost (Fin 4) 6 δ*‖ξ‖) (wordRadius (Fin 4) δ)

structure RadiusPrimitives (W : ℝ) : Prop where
  one : 1 ≤ W
  total_time : D.T ≤ 1
  mean_time : M.T ≤ 1
  mean_inverse_time : M.T⁻¹ ≤ W
  original_forward : L.R ≤ W
  original_mean : Rm ≤ W
  forward_radius : L.Rc ≤ W
  forward_frame : L.C₀ ≤ W
  forward_first : L.C₁ ≤ W
  forward_inverse : L.Ri ≤ W
  normal_radius : N.Rc ≤ W
  normal_amplitude : N.C ≤ W
  normal_inverse : N.Ri ≤ W
  mean_radius : LM.Rc ≤ W
  mean_frame : LM.CF ≤ W
  mean_first : LM.CF₁ ≤ W
  mean_forcing : LM.Cf ≤ W
  coefficient_radius : BC.Rc ≤ W
  coefficient_cost : BC.termCost ≤ W
  delta_inverse : δ⁻¹ ≤ W
  terminal : ‖ξ‖ ≤ W

theorem canonicalRadius_le_envelope (W : ℝ) (hδ : 0 < δ)
    (H : RadiusPrimitives L LM N BC δ ξ W) :
    canonicalRadius L LM N BC δ ξ ≤ radiusEnvelope W := by
  have hW0 := zero_le_one.trans H.one
  have hc := common_le L W hW0 H.forward_radius H.forward_frame H.forward_first H.forward_inverse
  have hg := grade_sum_le L N W hW0 H.normal_radius H.normal_amplitude H.normal_inverse hc
  have hm := mean_costs_le LM W hW0 H.mean_time H.mean_inverse_time H.mean_radius
    H.mean_frame H.mean_first H.mean_forcing
  have ht := terminal_cost_le δ W ξ hδ H.delta_inverse H.terminal
  have ht0 : 0 ≤ wordCost (Fin 4) 6 δ*‖ξ‖ := mul_nonneg (wordCost_nonneg 6 δ) (norm_nonneg ξ)
  have hg0 := gradeEnvelope_nonneg W hW0
  have htW0 := terminalEnvelope_nonneg W hW0
  have h0 := L.commonCost_nonneg
  have h1 := L.correctorAmplitude_nonneg (P := period) N
  have h2 := L.correctorTimeAmplitude_nonneg (P := period) N
  have h3 := L.pressureAmplitude_nonneg (P := period) N
  have hb0 : L.commonCost ≤ gradeEnvelope W := by linarith only [hg,h1,h2,h3]
  have hb1 : L.correctorAmplitude (P := period) N ≤ gradeEnvelope W := by linarith only
    [hg,h0,h2,h3]
  have hb2 : L.correctorTimeAmplitude (P := period) N ≤ gradeEnvelope W := by linarith only
    [hg,h0,h1,h3]
  have hb3 : 3*L.pressureAmplitude (P := period) N ≤ gradeEnvelope W := by linarith only
    [hg,h0,h1,h2]
  have hgrade (c t : ℝ) (hc0 : 0 ≤ c) (hct : c ≤ t) :
      L.gradeRadius (P := period) N c ≤ W+gradeEnvelope W*t := by
    have ht0 := hc0.trans hct
    have hmul {a : ℝ} (ha : a ≤ gradeEnvelope W) : a*c ≤ W+gradeEnvelope W*t :=
      (mul_le_mul ha hct hc0 hg0).trans (le_add_of_nonneg_left hW0)
    unfold EulerTransversePacketForward.Budget.gradeRadius
    exact max_le (H.original_forward.trans (le_add_of_nonneg_right (mul_nonneg hg0 ht0)))
      (max_le (hmul hb0) (max_le (hmul hb1) (max_le (hmul hb2) (hmul hb3))))
  have hg1 := hgrade 1 1 zero_le_one le_rfl
  have hgT := hgrade (wordCost (Fin 4) 6 δ*‖ξ‖) (terminalEnvelope W) ht0 ht
  have hj : wordRadius (Fin 4) δ ≤ 16*jetEnvelope W := by
    rw [wordRadius,coefficientRadius_eq]
    exact mul_le_mul_of_nonneg_left (jetRadius_le δ W hδ H.delta_inverse) (by norm_num)
  have hj0 : 0 ≤ 16*jetEnvelope W := by unfold jetEnvelope; positivity
  have hextra := max_le hj0 hj
  have hweak := weakEnvelope_nonneg W hW0
  have hstrong := strongEnvelope_nonneg W hW0
  have hforward := forwardEnvelope_nonneg W hW0
  have hreq : W+16*jetEnvelope W ≤ requiredEnvelope W := by
    unfold requiredEnvelope
    nlinarith only [mul_nonneg (add_nonneg hweak hstrong) (by positivity : 0 ≤ 16*W+1),
      mul_nonneg hforward (by positivity : 0 ≤ 64*W+1)]
  have hjW : W ≤ 16*jetEnvelope W := by
    unfold jetEnvelope
    nlinarith only [sq_nonneg (W-1)]
  unfold canonicalRadius EulerPacketForwardCommonRadius.commonRadius
  rw [coefficientRadius_eq]
  have hb : 16*BC.Rc ≤ 16*W := by gcongr; exact H.coefficient_radius
  unfold radiusEnvelope
  nlinarith only
    [H.original_mean,H.original_forward,H.coefficient_cost,hb,hm,hg1,hgT,hextra,hreq,hjW]

theorem canonicalRadius_power (W : ℝ) (hδ : 0 < δ)
    (H : RadiusPrimitives L LM N BC δ ξ W) :
    canonicalRadius L LM N BC δ ξ ≤ radiusConstant*W^radiusPower :=
  (canonicalRadius_le_envelope L LM N BC δ ξ W hδ H).trans (radiusEnvelope_power W H.one)

end EulerPacketForwardRadius
