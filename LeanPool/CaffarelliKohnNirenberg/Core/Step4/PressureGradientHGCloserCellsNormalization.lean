/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsOperatorTime

/-! # Cancellation of the cell scale in the concrete Riesz bound

The parabolic Morrey normalization cancels the radius powers in both the
near-source term and the annular tail. The resulting bound is independent
of the centre, radius, and number of source annuli.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

private theorem radius_power_product {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    ENNReal.ofReal r ^ a * ENNReal.ofReal r ^ b = ENNReal.ofReal r ^ (a + b) :=
  (ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top).symm

private theorem normalized_near_radius {r : ℝ} (hr : 0 < r) (γ : ℝ) :
    ENNReal.ofReal r ^ (-γ) * ENNReal.ofReal (2 * r) ^ γ = (2 : ℝ≥0∞) ^ γ := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [ENNReal.mul_rpow_of_ne_top (by norm_num) ENNReal.ofReal_ne_top]
  calc
    _ = (2 : ℝ≥0∞) ^ γ * (ENNReal.ofReal r ^ (-γ) * ENNReal.ofReal r ^ γ) := by ac_rfl
    _ = _ := by rw [radius_power_product hr, neg_add_cancel, ENNReal.rpow_zero, mul_one]

private theorem normalized_far_radius {κ r : ℝ} (hr : 0 < r) (x : Vec3) :
    ENNReal.ofReal r ^ (-(25 / 6 - 5 / κ)) * volume (vec3Ball x r) ^ (5 / 6 : ℝ) *
      ENNReal.ofReal (Real.pi * 4 / 3) ^ (1 / 6 : ℝ) *
        ENNReal.ofReal (4 * r) ^ (5 / 3 - 5 / κ) =
      ENNReal.ofReal (Real.pi * 4 / 3) * (4 : ℝ≥0∞) ^ (5 / 3 - 5 / κ) := by
  let v : ℝ≥0∞ := ENNReal.ofReal (Real.pi * 4 / 3)
  have hv0 : v ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < Real.pi * 4 / 3)).ne'
  have hvtop : v ≠ ⊤ := ENNReal.ofReal_ne_top
  have hvol : volume (vec3Ball x r) ^ (5 / 6 : ℝ) =
      ENNReal.ofReal r ^ (5 / 2 : ℝ) * v ^ (5 / 6 : ℝ) := by
    rw [volume_vec3Ball_eq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 5 / 6),
      show (ENNReal.ofReal r) ^ (3 : ℕ) = ENNReal.ofReal r ^ (3 : ℝ) by norm_cast,
      ← ENNReal.rpow_mul]
    norm_num
    rfl
  rw [hvol, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [ENNReal.mul_rpow_of_ne_top (by norm_num) ENNReal.ofReal_ne_top]
  change ENNReal.ofReal r ^ (-(25 / 6 - 5 / κ)) *
    (ENNReal.ofReal r ^ (5 / 2 : ℝ) * v ^ (5 / 6 : ℝ)) * v ^ (1 / 6 : ℝ) *
    ((4 : ℝ≥0∞) ^ (5 / 3 - 5 / κ) * ENNReal.ofReal r ^ (5 / 3 - 5 / κ)) = _
  calc
    _ = (v ^ (5 / 6 : ℝ) * v ^ (1 / 6 : ℝ)) * (4 : ℝ≥0∞) ^ (5 / 3 - 5 / κ) *
        ((ENNReal.ofReal r ^ (-(25 / 6 - 5 / κ)) * ENNReal.ofReal r ^ (5 / 2 : ℝ)) *
          ENNReal.ofReal r ^ (5 / 3 - 5 / κ)) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.rpow_add _ _ hv0 hvtop,
        show (5 / 6 : ℝ) + 1 / 6 = 1 by norm_num, ENNReal.rpow_one,
        radius_power_product hr, radius_power_product hr,
        show -(25 / 6 - 5 / κ) + (5 / 2 : ℝ) + (5 / 3 - 5 / κ) = 0 by ring,
        ENNReal.rpow_zero, mul_one]

/-- The normalized temporal norm of every finite source decomposition is
bounded independently of the cell and the number of annuli. -/
theorem pressure_riesz_finite_annuli_normalized_time_bound
    (i j : Fin 3) {κ : ℝ} (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9)
    {F : ParabolicPoint → ℝ} (hF : AEMeasurable F volume)
    (hFs : ∀ᵐ s ∂volume, MemLp (fun y : Vec3 => F (y, s))
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (x : Vec3) (t : ℝ) {r : ℝ} (hr : 0 < r) (N : ℕ) :
    ENNReal.ofReal r ^ (-(5 * (1 - (6 / 5 : ℝ) / κ) / (6 / 5))) *
      (∫⁻ s in Ioc (t - r ^ 2) t,
        eLpNorm (rieszSecondGradientExtensionOperator
          (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j)
          ((vec3Ball x ((2 : ℝ) ^ N * (2 * r))).indicator (fun y => F (y, s))))
          (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball x r)) ^ (6 / 5 : ℝ)) ^
            (5 / 6 : ℝ) ≤
      (ENNReal.ofReal (czGradientComponentConstant rieszSecondWeakTypeConstant 1) *
        (2 : ℝ≥0∞) ^ (25 / 6 - 5 / κ) +
      ENNReal.ofReal (6912 * (4 * Real.pi)⁻¹) * ENNReal.ofReal (Real.pi * 4 / 3) *
        (4 : ℝ≥0∞) ^ (5 / 3 - 5 / κ) * (1 - (2 : ℝ≥0∞) ^ (-2 / 15 : ℝ))⁻¹) *
          morreyNorm (6 / 5 : ℝ) κ F := by
  have h := pressure_riesz_finite_annuli_time_bound i j hκ hκhi hF hFs x t hr N
  have hexp : -(5 * (1 - (6 / 5 : ℝ) / κ) / (6 / 5)) = -(25 / 6 - 5 / κ) := by ring
  rw [hexp]
  refine (mul_le_mul_right h (ENNReal.ofReal r ^ (-(25 / 6 - 5 / κ)))).trans_eq ?_
  rw [mul_add]
  have hn := normalized_near_radius hr (25 / 6 - 5 / κ)
  have hf := normalized_far_radius (κ := κ) hr x
  calc
    _ = (ENNReal.ofReal (czGradientComponentConstant rieszSecondWeakTypeConstant 1) *
        (ENNReal.ofReal r ^ (-(25 / 6 - 5 / κ)) * ENNReal.ofReal (2 * r) ^ (25 / 6 - 5 / κ)) +
      ENNReal.ofReal (6912 * (4 * Real.pi)⁻¹) *
        (ENNReal.ofReal r ^ (-(25 / 6 - 5 / κ)) * volume (vec3Ball x r) ^ (5 / 6 : ℝ) *
          ENNReal.ofReal (Real.pi * 4 / 3) ^ (1 / 6 : ℝ) *
            ENNReal.ofReal (4 * r) ^ (5 / 3 - 5 / κ)) *
              (1 - (2 : ℝ≥0∞) ^ (-2 / 15 : ℝ))⁻¹) * morreyNorm (6 / 5 : ℝ) κ F := by ring
    _ = _ := by rw [hn, hf]; ring

end CKN.Core.Step4
