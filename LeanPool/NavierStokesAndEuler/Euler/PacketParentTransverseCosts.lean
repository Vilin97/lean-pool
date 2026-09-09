/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketParentMeanCoercivity
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCostMonotone
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketBudget

@[expose] public section

/-! Polynomial source envelopes for all transverse inverse radius guards.
The input inverse bound is derived from determinant-one deformation data;
no inverse solver norm or forcing-dependent constant appears in the final
radius. -/

noncomputable section

namespace EulerPacketParentTransverseCosts

open EulerParameterWordGevrey EulerTransverseGevreyInverse
  EulerTransverseCoefficientGevrey EulerTransverseFixedSobolev
  EulerTimeLpGramSobolev EulerTimeLpAccelerationSobolev EulerFixedEvolutionSobolev
  EulerSourceCylinderForwardSobolev EulerLinearDuhamel EulerPacketParentMeanCoercivity

def curvatureAmplitude (C C₂ : ℝ) : ℝ := 27*C^2*C₂

def historyCost (q : ℕ) (T R C C₁ C₂ : ℝ) : ℝ :=
  inverseBlockCost (Fin 4) q (inverseEnvelope C C₁) R
    (formCost T C C₁ (curvatureAmplitude C C₂))
    (forcingBlockAmplitude (Fin 4) q T R C C₁ 1)

def accelerationCost (q : ℕ) (R C C₁ V : ℝ) : ℝ :=
  inverseBlockCost (Fin 4) q (gramInverseEnvelope C) R (3*C^2)
    (accelerationBlockAmplitude (Fin 4) q R C C₁ 1 V)

def inverseRadius (R C : ℝ) : ℝ :=
  2*(1+gramInverseEnvelope C*(3*C^2+2))*(R+1)

def forwardCost (q : ℕ) (S Ti R C C₁ Cp : ℝ) : ℝ :=
  forwardSobolevCost (Fin 4) q S Cp (Ti+2)
    (EulerSourceCylinderForwardSobolev.forcingCost (Fin 4) q (inverseRadius R C) C)
    (18*inverseRadius R C*C*C₁) (4*inverseRadius R C)

def radius (q : ℕ) (T S Ti R C C₁ C₂ Cp : ℝ) : ℝ :=
  1+2*(historyCost q T R C C₁ C₂+accelerationCost q R C C₁ 1+
    accelerationCost q R C C₁ (Ti+2))*(sobolevCoefficientRadius (Fin 4) R+1)+
    sobolevCoefficientRadius (Fin 4) (4*inverseRadius R C)+
    2*forwardCost q S Ti R C C₁ Cp*(sobolevCoefficientRadius (Fin 4) (4*inverseRadius R C)+1)

theorem inverseCost_le (T C C₁ c : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hc : 0 < c)
    (hi : c⁻¹ ≤ gramInverseEnvelope C) : inverseCost T C C₁ c ≤ inverseEnvelope C C₁ := by
  have hc0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hi0 : 0 ≤ gramInverseEnvelope C := by unfold gramInverseEnvelope; positivity
  have ht0 : 0 ≤ transportCeiling T C C₁ c := by unfold transportCeiling; positivity
  have ht : transportCeiling T C C₁ c ≤ transportEnvelope C C₁ := by
    unfold transportCeiling transportEnvelope
    calc
      _ ≤ 1+((2*(gramInverseEnvelope C)^2*C^2*C₁+gramInverseEnvelope C*C₁)*1+
        gramInverseEnvelope C*C) := by gcongr
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht 2) (by norm_num)

theorem historyCost_nonneg (q : ℕ) (T R C C₁ C₂ : ℝ)
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    0 ≤ historyCost q T R C C₁ C₂ := by
  have hf : 0 ≤ formCost T C C₁ (curvatureAmplitude C C₂) := by
    unfold formCost derivativeCost curvatureAmplitude; positivity
  have hb := forcingBlockAmplitude_nonneg (Fin 4) q T R C C₁ 1 hT hR hC hC₁ zero_le_one
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q R _ hR hf
  have hs := sobolevInverseCost_nonneg (inverseEnvelope C C₁) _ (inverseEnvelope_nonneg C C₁) ha q
  unfold historyCost inverseBlockCost
  positivity

theorem accelerationCost_nonneg (q : ℕ) (R C C₁ V : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hV : 0 ≤ V) :
    0 ≤ accelerationCost q R C C₁ V := by
  have hi : 0 ≤ gramInverseEnvelope C := by unfold gramInverseEnvelope; positivity
  have hb := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q R (3*C^2) hR (by positivity)
  have hs := sobolevInverseCost_nonneg (gramInverseEnvelope C) _ hi hb q
  have hd := accelerationBlockAmplitude_nonneg (ι := Fin 4) q R C C₁ 1 V hR hC hC₁ zero_le_one hV
  unfold accelerationCost inverseBlockCost
  positivity

theorem inverseRadius_nonneg (R C : ℝ) (hR : 0 ≤ R) : 0 ≤ inverseRadius R C := by
  unfold inverseRadius gramInverseEnvelope
  positivity

theorem forwardCost_nonneg (q : ℕ) (S Ti R C C₁ Cp : ℝ)
    (hS : 0 ≤ S) (hTi : 0 ≤ Ti) (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hCp : 0 ≤ Cp) :
    0 ≤ forwardCost q S Ti R C C₁ Cp := by
  have hi := inverseRadius_nonneg R C hR
  have ha : 0 ≤ forwardSobolevAmplitude (Fin 4) q S Cp (18*inverseRadius R C*C*C₁) (4*inverseRadius
    R C) := by
    apply sobolevCoefficientAmplitude_nonneg _ _ _ (by positivity)
    unfold frozenAmplitude; positivity
  have hs := sobolevInverseCost_nonneg 1 _ zero_le_one ha q
  have hf : 0 ≤ EulerSourceCylinderForwardSobolev.forcingCost (Fin 4) q (inverseRadius R C) C := by
    unfold EulerSourceCylinderForwardSobolev.forcingCost
    exact mul_nonneg (by norm_num) (sobolevCoefficientAmplitude_nonneg _ _ _ (by positivity) (by
      positivity))
  unfold forwardCost forwardSobolevCost
  positivity

theorem historyCost_bound (q : ℕ) (T R C C₁ C₂ c : ℝ)
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hc : 0 < c) (hi : c⁻¹ ≤ gramInverseEnvelope C) :
    blockCost (Fin 4) q T R C C₁ (curvatureAmplitude C C₂) c 1 ≤ historyCost q T R C C₁ C₂ := by
  have hI : 0 ≤ inverseCost T C C₁ c := by unfold inverseCost; positivity
  have hf : 0 ≤ formCost T C C₁ (curvatureAmplitude C C₂) := by
    unfold formCost derivativeCost curvatureAmplitude; positivity
  exact inverseBlockCost_mono q hI hR hf
    (forcingBlockAmplitude_nonneg (Fin 4) q T R C C₁ 1 hT hR hC hC₁ zero_le_one)
    (inverseCost_le T C C₁ c hT hT1 hC hC₁ hc hi) le_rfl le_rfl

theorem accelerationCost_bound (q : ℕ) (R C C₁ c V W : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hc : 0 < c)
    (hi : c⁻¹ ≤ gramInverseEnvelope C) (hV : 0 ≤ V) (hVW : V ≤ W) :
    gramBlockCost (Fin 4) q c R C (accelerationBlockAmplitude (Fin 4) q R C C₁ 1 V) ≤
      accelerationCost q R C C₁ W := by
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q R C hR hC
  have hb := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q R C₁ hR hC₁
  have hd := accelerationBlockAmplitude_nonneg (ι := Fin 4) q R C C₁ 1 V hR hC hC₁ zero_le_one hV
  apply inverseBlockCost_mono q (inv_nonneg.mpr hc.le) hR (by positivity) hd hi le_rfl
  unfold accelerationBlockAmplitude
  gcongr

theorem inverseRadius_bound (R C c : ℝ) (hR : 0 ≤ R)
    (hi : c⁻¹ ≤ gramInverseEnvelope C) :
    2*EulerTimeLpGramGevrey.gramCost c C 1*(R+1) ≤ inverseRadius R C := by
  have hi0 : 0 ≤ gramInverseEnvelope C := by unfold gramInverseEnvelope; positivity
  unfold EulerTimeLpGramGevrey.gramCost inverseRadius
  rw [show 3*C^2+(1 : ℝ)+1=3*C^2+2 by ring]
  gcongr

theorem traceCost_le (T Ti : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hi : T⁻¹ ≤ Ti) :
    traceCost T ≤ Ti+2 := by
  have hTi : 0 ≤ Ti := (inv_nonneg.mpr hT.le).trans hi
  have hs : Real.sqrt T ≤ 1 := by nlinarith [Real.sqrt_nonneg T,Real.sq_sqrt hT.le]
  have hm := mul_le_mul hi hs (Real.sqrt_nonneg T) hTi
  unfold traceCost
  nlinarith

theorem forwardCost_bound (q : ℕ) (S Ti R C C₁ Cp V : ℝ)
    (hS : 0 ≤ S) (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hCp : 0 ≤ Cp)
    (hV : V ≤ Ti+2) :
    forwardSobolevCost (Fin 4) q S Cp V
      (EulerSourceCylinderForwardSobolev.forcingCost (Fin 4) q (inverseRadius R C) C)
      (18*inverseRadius R C*C*C₁) (4*inverseRadius R C) ≤ forwardCost q S Ti R C C₁ Cp := by
  have hi := inverseRadius_nonneg R C hR
  have ha : 0 ≤ forwardSobolevAmplitude (Fin 4) q S Cp (18*inverseRadius R C*C*C₁) (4*inverseRadius
    R C) := by
    apply sobolevCoefficientAmplitude_nonneg _ _ _ (by positivity)
    unfold frozenAmplitude; positivity
  have hs := sobolevInverseCost_nonneg 1 _ zero_le_one ha q
  unfold forwardCost forwardSobolevCost
  gcongr

theorem radius_guards (q : ℕ) (T S Ti R C C₁ C₂ Cp : ℝ)
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hTi : 0 ≤ Ti) (hR : 0 ≤ R)
    (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCp : 0 ≤ Cp) :
    2*historyCost q T R C C₁ C₂*(sobolevCoefficientRadius (Fin 4) R+1) ≤ radius q T S Ti R C C₁ C₂
      Cp ∧
    2*accelerationCost q R C C₁ 1*(sobolevCoefficientRadius (Fin 4) R+1) ≤ radius q T S Ti R C C₁
      C₂ Cp ∧
    2*accelerationCost q R C C₁ (Ti+2)*(sobolevCoefficientRadius (Fin 4) R+1) ≤ radius q T S Ti R C
      C₁ C₂ Cp ∧
    sobolevCoefficientRadius (Fin 4) (4*inverseRadius R C) ≤ radius q T S Ti R C C₁ C₂ Cp ∧
    2*forwardCost q S Ti R C C₁ Cp*(sobolevCoefficientRadius (Fin 4) (4*inverseRadius R C)+1) ≤
      radius q T S Ti R C C₁ C₂ Cp := by
  have hw := historyCost_nonneg q T R C C₁ C₂ hT hR hC hC₁ hC₂
  have hg := accelerationCost_nonneg q R C C₁ 1 hR hC hC₁ zero_le_one
  have hc := accelerationCost_nonneg q R C C₁ (Ti+2) hR hC hC₁ (by positivity)
  have hf := forwardCost_nonneg q S Ti R C C₁ Cp hS hTi hR hC hC₁ hCp
  have hr := sobolevCoefficientRadius_nonneg (ι := Fin 4) R hR
  have hi := sobolevCoefficientRadius_nonneg (ι := Fin 4) (4*inverseRadius R C)
    (mul_nonneg (by norm_num) (inverseRadius_nonneg R C hR))
  have hwr := mul_nonneg hw (add_nonneg hr zero_le_one)
  have hgr := mul_nonneg hg (add_nonneg hr zero_le_one)
  have hcr := mul_nonneg hc (add_nonneg hr zero_le_one)
  have hfr := mul_nonneg hf (add_nonneg hi zero_le_one)
  unfold radius
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end EulerPacketParentTransverseCosts
