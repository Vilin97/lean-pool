/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentMeanBudget
public import LeanPool.NavierStokesAndEuler.Euler.ParentCoefficientPolynomial

@[expose] public section

/-! Polynomial control of the original source-solver radii, before the
canonical primary/common enlargement. The boundary coefficient L is an
explicit primitive input. -/

noncomputable section

namespace EulerPacketSourceRadius

open EulerParameterWordGevrey EulerPacketRadiusPolynomial EulerPacketParentMeanCoercivity
  EulerTransverseCoefficientGevrey EulerTransverseFixedSobolev EulerTimeLpGramSobolev
  EulerTimeLpAccelerationSobolev EulerLinearDuhamel EulerMeanTranslatedGevrey
  EulerMeanBoundary EulerPolynomialCost

attribute [local gcongr] sobolevCoefficientAmplitude_mono_all inverseBlockCost_mono_all
  sobolevInverseCost_mono

def forcingEnvelope (W : ℝ) : ℝ := 3*coeff W (2*W)
def accelerationEnvelope (W : ℝ) : ℝ := 3*coeff W W*(1+6*coeff W W*(W+2))
def operatorEnvelope (W : ℝ) : ℝ := 36*W^2*(1+2*W+W*scaledBoundaryOperatorAmplitude)
def projectedEnvelope (W : ℝ) : ℝ := 3*coeff (4*W) (3*W^2)

def primitiveLift (W : ℝ) : ℝ :=
  1+(W+2)+formEnvelope W+forcingEnvelope W+3*W^2+accelerationEnvelope W+
    operatorEnvelope W+projectedEnvelope W

def sourceRadiusEnvelope (W : ℝ) : ℝ :=
  let V := primitiveLift W
  1+V+6*weakEnvelope V*(16*V+1)+64*V+2*forwardEnvelope V*(64*V+1)

theorem primitiveLift_bounds (W : ℝ) (hW : 0 ≤ W) :
    1 ≤ primitiveLift W ∧ W+2 ≤ primitiveLift W ∧
    formEnvelope W ≤ primitiveLift W ∧ forcingEnvelope W ≤ primitiveLift W ∧
    3*W^2 ≤ primitiveLift W ∧ accelerationEnvelope W ≤ primitiveLift W ∧
    operatorEnvelope W ≤ primitiveLift W ∧ projectedEnvelope W ≤ primitiveLift W := by
  have ha := coeff_nonneg W W hW hW
  have hb := coeff_nonneg W (2*W) hW (by positivity)
  have hc := coeff_nonneg (4*W) (3*W^2) (by positivity) (by positivity)
  have hbound := scaledBoundaryOperatorAmplitude_nonneg
  have hf : 0 ≤ formEnvelope W := by unfold formEnvelope; positivity
  have hfo : 0 ≤ forcingEnvelope W := by unfold forcingEnvelope; positivity
  have hac : 0 ≤ accelerationEnvelope W := by unfold accelerationEnvelope; positivity
  have hop : 0 ≤ operatorEnvelope W := by unfold operatorEnvelope; positivity
  have hp : 0 ≤ projectedEnvelope W := by unfold projectedEnvelope; positivity
  unfold primitiveLift
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith,by
    nlinarith,by nlinarith⟩

theorem coeff_self_lower (W : ℝ) (hW : 0 ≤ W) : W ≤ coeff W W := by
  have hr : 0 ≤ sobolevCoefficientRadius (Fin 4) W := sobolevCoefficientRadius_nonneg W hW
  have hs : (1 : ℝ) ≤ ∑ k ∈ Finset.range 7, sobolevCoefficientRadius (Fin 4) W^k*(k.factorial :
    ℝ)^2 := by
    have hh := Finset.single_le_sum (f := fun k : ℕ => sobolevCoefficientRadius (Fin 4)
      W^k*(k.factorial : ℝ)^2)
      (fun k (_ : k ∈ Finset.range 7) => mul_nonneg (pow_nonneg hr k) (sq_nonneg _))
      (show 0 ∈ Finset.range 7 by norm_num)
    simpa only [pow_zero,Nat.factorial_zero,Nat.cast_one,one_pow,mul_one] using hh
  change W ≤ (2 : ℝ)^6*W*(∑ k ∈ Finset.range (6+1), sobolevCoefficientRadius (Fin 4)
    W^k*(k.factorial : ℝ)^2)
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (2 : ℝ)^6*W)
  norm_num only [mul_one,pow_succ,pow_zero] at hm ⊢
  nlinarith

theorem weakEnvelope_lower_inputs (V : ℝ) (hV : 1 ≤ V) :
    V ≤ EulerPacketRadiusPolynomial.inverseEnvelope V ∧ V ≤ formEnvelope V ∧
    V ≤ 3*coeff V (2*V)*endpointEnvelope V := by
  have hv0 := zero_le_one.trans hV
  have hv2 : V ≤ V^2 := by nlinarith
  have hv5 : 0 ≤ V^5 := pow_nonneg hv0 5
  have hinner : V ≤ 1+2*V^5+2*V^2 := by nlinarith
  have hinner1 : 1 ≤ 1+2*V^5+2*V^2 := by nlinarith only [hv5,sq_nonneg V]
  have hi2 : 1+2*V^5+2*V^2 ≤ (1+2*V^5+2*V^2)^2 := by nlinarith
  have ha := coeff_self_lower V hv0
  have hb : coeff V V ≤ coeff V (2*V) := sobolevCoefficientAmplitude_mono_all 6 hv0 hv0 le_rfl (by
    linarith)
  have he : V ≤ endpointEnvelope V := by
    unfold endpointEnvelope
    nlinarith only [mul_le_mul_of_nonneg_right ha hv0,hv2]
  refine ⟨by unfold EulerPacketRadiusPolynomial.inverseEnvelope; nlinarith,?_,?_⟩
  · unfold formEnvelope
    nlinarith only [mul_nonneg (sq_nonneg V) hv0,hv2]
  · have hprod := mul_le_mul_of_nonneg_right (ha.trans hb) (show 0 ≤ endpointEnvelope V by
      unfold endpointEnvelope
      exact mul_nonneg (by nlinarith : 0 ≤ 6*coeff V V) hv0)
    nlinarith only [hprod,mul_nonneg (sub_nonneg.mpr hV) (by nlinarith only [he,hv0] : 0 ≤
      endpointEnvelope V),he]

theorem block_le_weak (V : ℝ) (hV : 1 ≤ V) (I R C D : ℝ)
    (hI0 : 0 ≤ I) (hR0 : 0 ≤ R) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hI : I ≤ V) (hR : R ≤ V) (hC : C ≤ V) (hD : D ≤ V) :
    inverseBlockCost (Fin 4) 6 I R C D ≤ weakEnvelope V := by
  have hb := weakEnvelope_lower_inputs V hV
  exact inverseBlockCost_mono_all 6 hI0 hR0 hC0 hD0
    (hI.trans hb.1) hR (hC.trans hb.2.1) (hD.trans hb.2.2)


theorem form_scalar_le (T C C1 H W : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (hC : 0 ≤ C) (hC1 : 0 ≤ C1) (hH : 0 ≤ H)
    (hCW : C ≤ W) (hC1W : C1 ≤ W) (hHW : H ≤ W) :
    9*(T*C1+C)^2*(1+T^2*H) ≤ formEnvelope W := by
  calc
    _ ≤ 9*(1*W+W)^2*(1+1^2*W) := by gcongr
    _ = _ := by unfold formEnvelope; ring

theorem forcing_scalar_le (T R C C1 W : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hC1 : 0 ≤ C1)
    (hRW : R ≤ W) (hCW : C ≤ W) (hC1W : C1 ≤ W) :
    3*coeff R (T*(T*C1+C)) ≤ forcingEnvelope W := by
  have hd : T*(T*C1+C) ≤ 2*W := by
    calc
      _ ≤ 1*(1*W+W) := by gcongr
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_left (sobolevCoefficientAmplitude_mono_all 6 hR (by positivity) hRW
    hd) (by norm_num)

theorem acceleration_scalar_le (R C C1 Cv W : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hC1 : 0 ≤ C1) (hCv : 0 ≤ Cv) (hW : 0 ≤ W)
    (hRW : R ≤ W) (hCW : C ≤ W) (hC1W : C1 ≤ W) (hCvW : Cv ≤ W+2) :
    accelerationBlockAmplitude (Fin 4) 6 R C C1 1 Cv ≤ accelerationEnvelope W := by
  have ha := coeff_nonneg R C hR hC
  have hb := coeff_nonneg R C1 hR hC1
  have hc := coeff_nonneg W W hW hW
  have hca : coeff R C ≤ coeff W W := sobolevCoefficientAmplitude_mono_all 6 hR hC hRW hCW
  have hcb : coeff R C1 ≤ coeff W W := sobolevCoefficientAmplitude_mono_all 6 hR hC1 hRW hC1W
  unfold accelerationBlockAmplitude accelerationEnvelope
  gcongr

theorem operator_scalar_le (T C C1 H L W : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (hC : 0 ≤ C) (hC1 : 0 ≤ C1) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hCW : C ≤ W) (hC1W : C1 ≤ W) (hHW : H ≤ W) (hLW : L ≤ W) :
    operatorAmplitude T C C1 H C1 scaledBoundaryOperatorAmplitude L ≤ operatorEnvelope W := by
  have ha := scaledBoundaryOperatorAmplitude_nonneg
  have ht : T^2/2 ≤ 1 := by nlinarith
  unfold operatorAmplitude
  rw [abs_of_nonneg hL]
  calc
    _ ≤ 9*(1*W+W)^2*(1+1*W+1*(W+W*scaledBoundaryOperatorAmplitude)) := by gcongr
    _ = _ := by unfold operatorEnvelope; ring

theorem projected_scalar_le (Ri C W : ℝ) (hRi : 0 ≤ Ri) (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hi : Ri ≤ W) (hc : C ≤ W) :
    EulerSourceCylinderForwardSobolev.forcingCost (Fin 4) 6 Ri C ≤ projectedEnvelope W := by
  apply mul_le_mul_of_nonneg_left
  · apply sobolevCoefficientAmplitude_mono_all 6 (by positivity) (by positivity) (by gcongr)
    calc
      3*Ri*C ≤ 3*W*W := by gcongr
      _ = 3*W^2 := by ring
  · norm_num

theorem forward_scalar_le (T C A D CB R V : ℝ)
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hCB : 0 ≤ CB) (hR : 0 ≤ R) (hV : 0 ≤ V)
    (hCV : C ≤ V) (hAV : A ≤ V) (hDV : D ≤ V)
    (hCBV : CB ≤ 18*V^3) (hRV : R ≤ 4*V) :
    forwardSobolevCost (Fin 4) 6 T C A D CB R ≤ forwardEnvelope V := by
  have hraw : frozenAmplitude T C CB ≤ 1+36*V^4 := by
    unfold frozenAmplitude
    calc
      _ ≤ 1+2*V*1*(18*V^3) := by gcongr
      _ = _ := by ring
  have hr0 : 0 ≤ frozenAmplitude T C CB := by unfold frozenAmplitude; positivity
  have hb : forwardSobolevAmplitude (Fin 4) 6 T C CB R ≤ coeff (4*V) (1+36*V^4) :=
    sobolevCoefficientAmplitude_mono_all 6 hR hr0 hRV hraw
  have hb0 : 0 ≤ forwardSobolevAmplitude (Fin 4) 6 T C CB R :=
    coeff_nonneg R (frozenAmplitude T C CB) hR hr0
  have hbV := coeff_nonneg (4*V) (1+36*V^4) (by positivity) (by positivity)
  have hsi := sobolevInverseCost_mono zero_le_one hb0 le_rfl hb 6
  have hsiV := sobolevInverseCost_nonneg 1 (coeff (4*V) (1+36*V^4)) zero_le_one hbV 6
  have hc : C*A+C*T*D ≤ V*(2*V+2) := by
    calc
      _ ≤ V*V+V*1*V := by gcongr
      _ ≤ _ := by nlinarith
  unfold forwardSobolevCost forwardEnvelope
  apply add_le_add le_rfl
  apply mul_le_mul hsi _ (by positivity) hsiV
  linarith only [hb,hc]


theorem joined_radius_le (T S Ti R C C1 C2 Cp W : ℝ) (hW : 1 ≤ W)
    (hT0 : 0 ≤ T) (hT : T ≤ 1) (hS0 : 0 ≤ S) (hS : S ≤ 1)
    (hTi0 : 0 ≤ Ti) (hTi : Ti ≤ W) (hR0 : 0 ≤ R) (hR : R ≤ W)
    (hC0 : 0 ≤ C) (hC : C ≤ W) (hC10 : 0 ≤ C1) (hC1 : C1 ≤ W)
    (hC20 : 0 ≤ C2) (hCp0 : 0 ≤ Cp) (hCp : Cp ≤ W)
    (hH : 27*C^2*C2 ≤ W)
    (hI : EulerPacketParentMeanCoercivity.inverseEnvelope C C1 ≤ W)
    (hGram : gramInverseEnvelope C ≤ W)
    (hRi : EulerPacketParentTransverseCosts.inverseRadius R C ≤ W) :
    EulerPacketParentTransverseCosts.radius 6 T S Ti R C C1 C2 Cp ≤ sourceRadiusEnvelope W := by
  let V := primitiveLift W
  have hW0 := zero_le_one.trans hW
  have hb := primitiveLift_bounds W hW0
  have hV : 1 ≤ V := hb.1
  have hV0 := zero_le_one.trans hV
  have hWV : W ≤ V := (by linarith : W ≤ W+2).trans hb.2.1
  have hCV : C ≤ V := hC.trans hWV
  have hC1V : C1 ≤ V := hC1.trans hWV
  have hRV : R ≤ V := hR.trans hWV
  have hH0 : 0 ≤ 27*C^2*C2 := by positivity
  have hform := (form_scalar_le T C C1 (27*C^2*C2) W hT0 hT hC0 hC10 hH0 hC hC1 hH).trans hb.2.2.1
  have hforce := (forcing_scalar_le T R C C1 W hT0 hT hR0 hC0 hC10 hR hC hC1).trans hb.2.2.2.1
  have hf0 : 0 ≤ 3*coeff R (T*(T*C1+C)) := by
    have hh := coeff_nonneg R (T*(T*C1+C)) hR0 (by positivity)
    positivity
  have hh : EulerPacketParentTransverseCosts.historyCost 6 T R C C1 C2 ≤ weakEnvelope V := by
    apply block_le_weak V hV _ _ _ _ (inverseEnvelope_nonneg C C1) hR0
      (by positivity)
      (by simpa only [forcingBlockAmplitude,derivativeCost,mul_one] using hf0)
      (hI.trans hWV) (hR.trans hWV) hform
    simpa only [forcingBlockAmplitude,derivativeCost,mul_one] using hforce
  have hacc (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ W+2) :
      EulerPacketParentTransverseCosts.accelerationCost 6 R C C1 v ≤ weakEnvelope V := by
    apply block_le_weak V hV _ _ _ _ (by unfold gramInverseEnvelope; positivity) hR0
      (by positivity) (accelerationBlockAmplitude_nonneg 6 R C C1 1 v hR0 hC0 hC10 zero_le_one hv0)
      (hGram.trans hWV) (hR.trans hWV)
    · exact (by nlinarith only [pow_le_pow_left₀ hC0 hC 2] : 3*C^2 ≤ 3*W^2).trans hb.2.2.2.2.1
    · exact (acceleration_scalar_le R C C1 v W hR0 hC0 hC10 hv0 hW0 hR hC hC1 hv).trans
      hb.2.2.2.2.2.1
  have ha1 := hacc 1 zero_le_one (by linarith)
  have ha2 := hacc (Ti+2) (by positivity) (by linarith)
  let Ri := EulerPacketParentTransverseCosts.inverseRadius R C
  have hi0 : 0 ≤ Ri := EulerPacketParentTransverseCosts.inverseRadius_nonneg R C hR0
  have hiv : Ri ≤ V := hRi.trans hWV
  have hpf := (projected_scalar_le Ri C W hi0 hC0 hW0 hRi hC).trans hb.2.2.2.2.2.2.2
  have hpf0 : 0 ≤ EulerSourceCylinderForwardSobolev.forcingCost (Fin 4) 6 Ri C := by
    have hc := coeff_nonneg (4*Ri) (3*Ri*C) (by positivity) (by positivity)
    unfold EulerSourceCylinderForwardSobolev.forcingCost
    positivity
  have hforward : EulerPacketParentTransverseCosts.forwardCost 6 S Ti R C C1 Cp ≤ forwardEnvelope V
    := by
    apply forward_scalar_le S Cp (Ti+2) _ (18*Ri*C*C1) (4*Ri) V
      hS0 hS hCp0 (by positivity) hpf0 (by positivity) (by positivity) hV0
      (hCp.trans hWV) ((by linarith : Ti+2 ≤ W+2).trans hb.2.1) hpf
    · calc
        18*Ri*C*C1 ≤ 18*V*V*V := by gcongr
        _ = _ := by ring
    · gcongr
  have hh0 := EulerPacketParentTransverseCosts.historyCost_nonneg 6 T R C C1 C2 hT0 hR0 hC0 hC10
    hC20
  have ha10 := EulerPacketParentTransverseCosts.accelerationCost_nonneg 6 R C C1 1 hR0 hC0 hC10
    zero_le_one
  have ha20 := EulerPacketParentTransverseCosts.accelerationCost_nonneg 6 R C C1 (Ti+2) hR0 hC0
    hC10 (by positivity)
  have hww := weakEnvelope_nonneg V hV0
  have hfw := forwardEnvelope_nonneg V hV0
  unfold EulerPacketParentTransverseCosts.radius
  simp only [coefficientRadius_eq]
  calc
    _ ≤ 1+2*(weakEnvelope V+weakEnvelope V+weakEnvelope V)*(16*V+1)+
        16*(4*V)+2*forwardEnvelope V*(16*(4*V)+1) := by gcongr
    _ ≤ sourceRadiusEnvelope W := by
      change _ ≤ 1+V+6*weakEnvelope V*(16*V+1)+64*V+2*forwardEnvelope V*(64*V+1)
      nlinarith only [hV0]

theorem mean_radius_le (T Ti R C C1 C2 L W : ℝ) (hW : 1 ≤ W)
    (hT0 : 0 ≤ T) (hT : T ≤ 1)
    (hTi0 : 0 ≤ Ti) (hTi : Ti ≤ W) (hR0 : 0 ≤ R) (hR : R ≤ W)
    (hC0 : 0 ≤ C) (hC : C ≤ W) (hC10 : 0 ≤ C1) (hC1 : C1 ≤ W)
    (hC20 : 0 ≤ C2) (hL0 : 0 ≤ L) (hL : L ≤ W)
    (hH : 27*C^2*C2 ≤ W)
    (hI : EulerPacketParentMeanCoercivity.inverseEnvelope C C1 ≤ W)
    (hGram : gramInverseEnvelope C ≤ W) :
    EulerPacketParentMeanBudget.radius 6 T Ti R C C1 C2 L ≤ sourceRadiusEnvelope W := by
  let V := primitiveLift W
  have hW0 := zero_le_one.trans hW
  have hb := primitiveLift_bounds W hW0
  have hV : 1 ≤ V := hb.1
  have hV0 := zero_le_one.trans hV
  have hWV : W ≤ V := (by linarith : W ≤ W+2).trans hb.2.1
  have hRV : R ≤ V := hR.trans hWV
  have hH0 : 0 ≤ 27*C^2*C2 := by positivity
  have hop := (operator_scalar_le T C C1 (27*C^2*C2) L W
    hT0 hT hC0 hC10 hH0 hL0 hC hC1 hH hL).trans hb.2.2.2.2.2.2.1
  have hforce := (forcing_scalar_le T R C C1 W hT0 hT hR0 hC0 hC10 hR hC hC1).trans hb.2.2.2.1
  have hf0 : 0 ≤ 3*coeff R (T*(T*C1+C)) := by
    have hh := coeff_nonneg R (T*(T*C1+C)) hR0 (by positivity)
    positivity
  have hw : EulerPacketParentMeanBudget.weakCost 6 T R C C1 C2 L ≤ weakEnvelope V := by
    have hh := block_le_weak V hV (EulerPacketParentMeanCoercivity.inverseEnvelope C C1) R
      (operatorAmplitude T C C1 (27*C^2*C2) C1 scaledBoundaryOperatorAmplitude L)
      (3*coeff R (T*(T*C1+C))) (inverseEnvelope_nonneg C C1) hR0
      (operatorAmplitude_nonneg T C C1 (27*C^2*C2) C1 scaledBoundaryOperatorAmplitude L
        hT0 hH0 hC10 scaledBoundaryOperatorAmplitude_nonneg) hf0
      (hI.trans hWV) hRV hop hforce
    simpa only [EulerPacketParentMeanBudget.weakCost,EulerPacketParentMeanBudget.operatorCost,
      EulerMeanFixedSobolevGevrey.operatorBlockAmplitude,EulerPacketParentMeanBudget.curvatureAmplitude,
      EulerPacketParentMeanBudget.forcingCost,EulerMeanFixedSobolevGevrey.forcingBlockAmplitude,
      mul_one,inverseBlockCost] using hh
  have hgram (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ W+2) :
      EulerPacketParentMeanBudget.gramCost 6 R C C1 v ≤ weakEnvelope V := by
    apply block_le_weak V hV _ _ _ _ (by unfold gramInverseEnvelope; positivity) hR0
      (by positivity) (accelerationBlockAmplitude_nonneg 6 R C C1 1 v hR0 hC0 hC10 zero_le_one hv0)
      (hGram.trans hWV) hRV
    · exact (by nlinarith only [pow_le_pow_left₀ hC0 hC 2] : 3*C^2 ≤ 3*W^2).trans hb.2.2.2.2.1
    · exact (acceleration_scalar_le R C C1 v W hR0 hC0 hC10 hv0 hW0 hR hC hC1 hv).trans
      hb.2.2.2.2.2.1
  have ha1 := hgram 1 zero_le_one (by linarith)
  have ha2 := hgram (Ti+2) (by positivity) (by linarith)
  have hw0 := zero_le_one.trans (EulerPacketParentMeanBudget.weakCost_one_le 6 T R C C1 C2 L hT0
    hR0 hC0 hC10 hC20)
  have ha10 := EulerPacketParentMeanBudget.gramCost_nonneg 6 R C C1 1 hR0 hC0 hC10 zero_le_one
  have ha20 := EulerPacketParentMeanBudget.gramCost_nonneg 6 R C C1 (Ti+2) hR0 hC0 hC10 (by
    positivity)
  have hww := weakEnvelope_nonneg V hV0
  have hfw := forwardEnvelope_nonneg V hV0
  unfold EulerPacketParentMeanBudget.radius
  simp only [coefficientRadius_eq]
  calc
    _ ≤ 1+2*(weakEnvelope V+weakEnvelope V+weakEnvelope V)*(16*V+1) := by gcongr
    _ ≤ sourceRadiusEnvelope W := by
      change _ ≤ 1+V+6*weakEnvelope V*(16*V+1)+64*V+2*forwardEnvelope V*(64*V+1)
      nlinarith only [hV0,mul_nonneg hfw (by positivity : 0 ≤ 64*V+1)]

theorem le_sourceRadiusEnvelope (W : ℝ) (hW : 0 ≤ W) : W ≤ sourceRadiusEnvelope W := by
  have hv := (primitiveLift_bounds W hW).1
  have hv0 := zero_le_one.trans hv
  have hw := (primitiveLift_bounds W hW).2.1
  have hweak := weakEnvelope_nonneg (primitiveLift W) hv0
  have hforward := forwardEnvelope_nonneg (primitiveLift W) hv0
  unfold sourceRadiusEnvelope
  nlinarith only [hw,hv0,
    mul_nonneg hweak (by positivity : 0 ≤ 16*primitiveLift W+1),
    mul_nonneg hforward (by positivity : 0 ≤ 64*primitiveLift W+1)]

def primitivePolynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let a := coeffPoly X X
  1+(X+2)+36*X^2*(1+X)+3*coeffPoly X (2*X)+3*X^2+
    3*a*(1+6*a*(X+2))+36*X^2*(1+2*X+X*Polynomial.C scaledBoundaryOperatorAmplitude)+
    3*coeffPoly (4*X) (3*X^2)

theorem primitivePolynomial_eval (W : ℝ) : primitivePolynomial.eval W=primitiveLift W := by
  simp only [primitivePolynomial,primitiveLift,formEnvelope,forcingEnvelope,accelerationEnvelope,
    operatorEnvelope,projectedEnvelope,coeffPoly,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X,Polynomial.eval_C,
    coefficientPolynomial_eval,coeff]

def sourceRadiusPolynomial : Polynomial ℝ :=
  let V := primitivePolynomial
  let endpoint := 6*coeffPoly V V*V
  let weak := inverseBlockPolynomial 6 (2*(1+2*V^5+2*V^2)^2) V (36*V^2*(1+V))
    (3*coeffPoly V (2*V)*endpoint)
  let b := coeffPoly (4*V) (1+36*V^4)
  let forward := 1+inversePolynomial 1 b 6*(b+V*(2*V+2))
  1+V+6*weak*(16*V+1)+64*V+2*forward*(64*V+1)

theorem sourceRadiusPolynomial_eval (W : ℝ) : sourceRadiusPolynomial.eval W=sourceRadiusEnvelope W
  := by
  simp only [sourceRadiusPolynomial,sourceRadiusEnvelope,weakEnvelope,forwardEnvelope,
    EulerPacketRadiusPolynomial.inverseEnvelope,formEnvelope,endpointEnvelope,
    coeffPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
    Polynomial.eval_one,inversePolynomial_eval,inverseBlockPolynomial_eval,
    coefficientPolynomial_eval,primitivePolynomial_eval,coeff]

def sourceRadiusConstant : ℝ := coefficientCost sourceRadiusPolynomial
def sourceRadiusPower : ℕ := sourceRadiusPolynomial.natDegree

theorem sourceRadiusConstant_pos : 0 < sourceRadiusConstant := coefficientCost_pos _

theorem sourceRadiusEnvelope_power (W : ℝ) (hW : 1 ≤ W) :
    sourceRadiusEnvelope W ≤ sourceRadiusConstant*W^sourceRadiusPower := by
  rw [← sourceRadiusPolynomial_eval]
  exact (le_abs_self _).trans (eval_bound sourceRadiusPolynomial W hW)

end EulerPacketSourceRadius
