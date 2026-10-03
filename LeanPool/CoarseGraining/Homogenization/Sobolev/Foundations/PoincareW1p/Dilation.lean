/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p.Core
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.Dilation

/-! # Dilation -/

@[expose] public section

namespace Homogenization

open scoped ENNReal Pointwise

noncomputable section

namespace W1pMeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}

/-- Pull a mean-zero `W^{1,p}(a • U)` witness back to a mean-zero witness on
`U` by positive dilation. -/
noncomputable def unscale {a : ℝ} (ha : 0 < a)
    (u : W1pMeanZeroFunction (a • U) p) : W1pMeanZeroFunction U p where
  toW1pFunction := u.toW1pFunction.unscale ha
  meanZero := W1pFunction.meanZeroOn_unscale ha u.toW1pFunction u.meanZero

@[simp] theorem unscale_toW1pFunction {a : ℝ} (ha : 0 < a)
    (u : W1pMeanZeroFunction (a • U) p) :
    (u.unscale ha).toW1pFunction = u.toW1pFunction.unscale ha :=
  rfl

/-- The scalar mean-zero seminorm under positive dilation pullback. -/
theorem valueLpSeminorm_unscale_eq {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (u : W1pMeanZeroFunction (a • U) p) :
    (u.unscale ha).valueLpSeminorm =
      W1pFunction.dilationLpFactor d p a⁻¹ * u.valueLpSeminorm := by
  exact W1pFunction.valueLpSeminorm_unscale_eq ha hp_top u.toW1pFunction

/-- The coordinate-sum gradient seminorm under positive dilation pullback. -/
theorem gradientCoordLpSeminormSum_unscale_eq {a : ℝ} (ha : 0 < a)
    (hp_top : p ≠ ∞) (u : W1pMeanZeroFunction (a • U) p) :
    (u.unscale ha).gradientCoordLpSeminormSum =
      a * W1pFunction.dilationLpFactor d p a⁻¹ * u.gradientCoordLpSeminormSum := by
  exact W1pFunction.gradientCoordLpSeminormSum_unscale_eq ha hp_top u.toW1pFunction

end W1pMeanZeroFunction

namespace W1pPoincareEstimate

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}

/-- Transport a finite-`p` mean-zero Poincare estimate to a positive dilation
of its domain.  The constant gains exactly one factor of the dilation scale. -/
noncomputable def dilate {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (hC : W1pPoincareEstimate U p) : W1pPoincareEstimate (a • U) p where
  fixedValue := a * hC.fixedValue
  constant_nonneg := mul_nonneg ha.le hC.constant_nonneg
  bound := by
    intro u
    let v : W1pMeanZeroFunction U p := u.unscale ha
    have hv := hC.bound v
    have hvalue := W1pMeanZeroFunction.valueLpSeminorm_unscale_eq ha hp_top u
    have hgrad := W1pMeanZeroFunction.gradientCoordLpSeminormSum_unscale_eq ha hp_top u
    have hfactor_pos : 0 < W1pFunction.dilationLpFactor d p a⁻¹ :=
      W1pFunction.dilationLpFactor_pos d p (inv_pos.mpr ha)
    have hscaled :
        W1pFunction.dilationLpFactor d p a⁻¹ * u.valueLpSeminorm ≤
          hC.fixedValue *
            (a * W1pFunction.dilationLpFactor d p a⁻¹ * u.gradientCoordLpSeminormSum) := by
      simpa [v, hvalue, hgrad] using hv
    have hscaled' :
        W1pFunction.dilationLpFactor d p a⁻¹ * u.valueLpSeminorm ≤
          W1pFunction.dilationLpFactor d p a⁻¹ *
            ((a * hC.fixedValue) * u.gradientCoordLpSeminormSum) := by
      calc
        W1pFunction.dilationLpFactor d p a⁻¹ * u.valueLpSeminorm ≤
            hC.fixedValue *
              (a * W1pFunction.dilationLpFactor d p a⁻¹ * u.gradientCoordLpSeminormSum) := hscaled
        _ = W1pFunction.dilationLpFactor d p a⁻¹ *
              ((a * hC.fixedValue) * u.gradientCoordLpSeminormSum) := by
              ring
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_iff_right₀ hfactor_pos).mp hscaled'

@[simp] theorem dilate_constant {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (hC : W1pPoincareEstimate U p) :
    (hC.dilate ha hp_top).fixedValue = a * hC.fixedValue :=
  rfl

end W1pPoincareEstimate

end

end Homogenization
