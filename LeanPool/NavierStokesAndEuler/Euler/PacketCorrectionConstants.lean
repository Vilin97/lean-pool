/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteCoarseBounds

@[expose] public section

/-! Fixed source costs for the normalized packet and its smaller transport drift. -/

noncomputable section

namespace EulerPacketCorrectionConstants

open EulerPacketCylinderField

def velocity (R H C : ℝ) : ℝ :=
  C*(fixedVelocityGradeCost R H 1+fixedVelocityGradeCost R H 2+1)

def normal (R H C : ℝ) : ℝ := C*(fixedVelocityGradeCost R H 2+2)

def drift (R H C : ℝ) : ℝ := 2*(3*velocity R H C+normal R H C)

theorem velocity_nonneg (R H C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    0 ≤ velocity R H C := by
  have h₁ := fixedVelocityGradeCost_nonneg R H hR 1
  have h₂ := fixedVelocityGradeCost_nonneg R H hR 2
  unfold velocity
  positivity

theorem normal_nonneg (R H C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    0 ≤ normal R H C := by
  have h₂ := fixedVelocityGradeCost_nonneg R H hR 2
  unfold normal
  positivity

theorem drift_nonneg (R H C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    0 ≤ drift R H C := by
  have hv := velocity_nonneg R H C hR hC
  have hn := normal_nonneg R H C hR hC
  unfold drift
  positivity

theorem drift_div_frequency (R H C k : ℝ) (hk : 0 < k) :
    2*(3*|k⁻¹| * velocity R H C+normal R H C/k) = drift R H C/k := by
  rw [abs_of_pos (inv_pos.mpr hk)]
  unfold drift
  ring

end EulerPacketCorrectionConstants
