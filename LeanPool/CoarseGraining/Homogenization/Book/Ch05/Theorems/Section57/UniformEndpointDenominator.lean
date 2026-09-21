/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformHighTop

/-! # Uniform Endpoint Denominator -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Denominator selection at the uniform endpoint

The endpoint high-bottom branch needs the high denominator squared and the
crude cutoff denominator to the power `(d - 2t) / t`.  We deliberately choose a
slightly oversized denominator, avoiding roots; the later scale-compression
step absorbs this polynomial dependence into the `exp(C log^2)` envelope.
-/

noncomputable section

/-- Common high-branch denominator for the `Γ∞` endpoint. -/
noncomputable def uniformEndpointHighDenominator
    (Dhigh Dcrude t d : ℝ) : ℝ :=
  max 1 (Dhigh ^ (2 : ℝ) *
    (max 1 Dcrude) ^ ((d - 2 * t) / t))

theorem uniformEndpointHighDenominator_pos
    {Dhigh Dcrude t d : ℝ} :
    0 < uniformEndpointHighDenominator Dhigh Dcrude t d := by
  dsimp [uniformEndpointHighDenominator]
  exact lt_of_lt_of_le zero_lt_one (le_max_left 1 _)

theorem one_le_uniformEndpointHighDenominator
    {Dhigh Dcrude t d : ℝ} :
    1 ≤ uniformEndpointHighDenominator Dhigh Dcrude t d := by
  dsimp [uniformEndpointHighDenominator]
  exact le_max_left 1 _

theorem uniformEndpointHighDenominator_dom_bottom
    {Dhigh Dcrude t d : ℝ} (hd : 1 ≤ d) :
    Dhigh ^ (2 : ℝ) *
        (max 1 Dcrude) ^ ((d - 2 * t) / t) ≤
      (uniformEndpointHighDenominator Dhigh Dcrude t d) ^ d := by
  let Den : ℝ := uniformEndpointHighDenominator Dhigh Dcrude t d
  have hprod_le : Dhigh ^ (2 : ℝ) *
        (max 1 Dcrude) ^ ((d - 2 * t) / t) ≤ Den := by
    dsimp [Den, uniformEndpointHighDenominator]
    exact le_max_right 1 _
  have hDen_one : 1 ≤ Den := by
    dsimp [Den]
    exact one_le_uniformEndpointHighDenominator
  have hDen_le_pow : Den ≤ Den ^ d :=
    Real.self_le_rpow_of_one_le hDen_one hd
  exact hprod_le.trans hDen_le_pow

theorem uniformEndpointHighDenominator_dom_top
    {Dhigh Dcrude t d : ℝ} (hDhigh : 0 ≤ Dhigh)
    (ht : 0 < t) (htb : t ≤ d / 2) (hd : 1 ≤ d) :
    Dhigh ^ (2 : ℝ) ≤
      (uniformEndpointHighDenominator Dhigh Dcrude t d) ^ d := by
  have hκ_nonneg : 0 ≤ (d - 2 * t) / t := by
    have hnum : 0 ≤ d - 2 * t := by linarith
    positivity
  have hfactor_one :
      1 ≤ (max 1 Dcrude) ^ ((d - 2 * t) / t) :=
    Real.one_le_rpow (le_max_left 1 Dcrude) hκ_nonneg
  have hDhigh_sq_nonneg : 0 ≤ Dhigh ^ (2 : ℝ) := by
    exact Real.rpow_nonneg hDhigh _
  have htop_to_product :
      Dhigh ^ (2 : ℝ) ≤
        Dhigh ^ (2 : ℝ) *
          (max 1 Dcrude) ^ ((d - 2 * t) / t) := by
    calc
      Dhigh ^ (2 : ℝ) = Dhigh ^ (2 : ℝ) * 1 := by ring
      _ ≤ Dhigh ^ (2 : ℝ) *
          (max 1 Dcrude) ^ ((d - 2 * t) / t) :=
        mul_le_mul_of_nonneg_left hfactor_one hDhigh_sq_nonneg
  exact htop_to_product.trans
    (uniformEndpointHighDenominator_dom_bottom
      (Dhigh := Dhigh) (Dcrude := Dcrude) (t := t) (d := d) hd)

end

end Section57
end Ch05
end Book
end Homogenization
