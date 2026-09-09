/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BasePacketSetup
public import LeanPool.NavierStokesAndEuler.Euler.PacketFirstLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryLowBounds

@[expose] public section

/-! Fixed low-order constants are chosen before the stage and base scale.
Their slack absorbs the universal good-time and first-packet ratios. -/

noncomputable section

namespace EulerPacketLowConstants

open EulerBaseDatum EulerPacketFirstLowBounds EulerPacketGeometryLowBounds

def gradientConstant : ℝ := 8*(1+initialCoefficientCost+firstRatio+goodRatio)
def hessianConstant : ℝ := 8*(1+initialCoefficientCost+2*gradientConstant*(firstRatio+goodRatio))
def frameConstant : ℝ := 1+gradientConstant+hessianConstant

theorem gradient_properties : 4 ≤ gradientConstant ∧
    initialCoefficientCost+firstRatio+1 ≤ gradientConstant ∧ 4*goodRatio ≤ gradientConstant := by
  have h0 := initialCoefficientCost_nonneg
  have h1 := firstRatio_pos
  have h2 := goodRatio_pos
  unfold gradientConstant
  exact ⟨by linarith,by linarith,by linarith⟩

theorem gradient_nonneg : 0 ≤ gradientConstant := (by norm_num : (0 : ℝ) ≤ 4).trans
  gradient_properties.1

theorem hessian_properties : 4 ≤ hessianConstant ∧
    initialCoefficientCost+2*initialCoefficientCost*firstRatio+1 ≤ hessianConstant ∧
    8*gradientConstant*goodRatio ≤ hessianConstant := by
  have h0 := initialCoefficientCost_nonneg
  have h1 := firstRatio_pos
  have h2 := goodRatio_pos
  have hM := gradient_properties.2.1
  have hMc : initialCoefficientCost ≤ gradientConstant := by linarith only [hM,h1]
  have h0M := gradient_nonneg
  have hf := mul_le_mul_of_nonneg_right hMc h1.le
  have hff := mul_nonneg h0M h1.le
  have hfg := mul_nonneg h0M h2.le
  unfold hessianConstant
  exact ⟨by nlinarith,by nlinarith,by nlinarith⟩

theorem hessian_nonneg : 0 ≤ hessianConstant := (by norm_num : (0 : ℝ) ≤ 4).trans
  hessian_properties.1

theorem frame_properties : 1 ≤ frameConstant ∧ gradientConstant ≤ frameConstant ∧
    gradientConstant^2+hessianConstant ≤ frameConstant^2 := by
  have hm := gradient_nonneg
  have hh := hessian_nonneg
  unfold frameConstant
  exact ⟨by linarith,by linarith,by nlinarith [sq_nonneg hessianConstant]⟩

theorem initial_bounds (h e : ℝ) (hh : 1 ≤ h) (he : e ≤ 1) :
    initialCoefficientCost+h*firstRatio+e ≤ gradientConstant*h ∧
    initialCoefficientCost+2*initialCoefficientCost*(h*firstRatio)+e ≤ hessianConstant*h := by
  have h0 := initialCoefficientCost_nonneg
  have hc := mul_le_mul_of_nonneg_left hh h0
  have hm := mul_le_mul_of_nonneg_right gradient_properties.2.1 (zero_le_one.trans hh)
  have hH := mul_le_mul_of_nonneg_right hessian_properties.2.1 (zero_le_one.trans hh)
  constructor <;> nlinarith only [hc,hm,hH,hh,he]

end EulerPacketLowConstants
