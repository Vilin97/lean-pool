/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic

/-!
# Quantitative scalar multiplication in Morrey seminorms

The absolute scalar factor is retained in the bound, including when the
scalar vanishes or the unscaled seminorm is infinite.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey


noncomputable section

namespace CKN.Core.Endgame

/-- Multiplication by a real constant scales the Morrey seminorm by at most
its absolute value. No measurability or finiteness assumptions are needed. -/
theorem morreyNorm_const_mul_le {P τ : ℝ} (hP : 0 < P)
    (c : ℝ) (f : ParabolicPoint → ℝ) :
    morreyNorm P τ (fun z => c * f z) ≤ ENNReal.ofReal |c| * morreyNorm P τ f := by
  have hcell : ∀ z : ParabolicPoint, ∀ r : {r : ℝ // 0 < r},
      morreyCell P τ (fun w => c * f w) z r.1 =
        ENNReal.ofReal |c| * morreyCell P τ f z r.1 := by
    intro z r
    have hI : cylinderPowerIntegral P (fun w => c * f w) z r.1 =
        ENNReal.ofReal |c| ^ P * cylinderPowerIntegral P f z r.1 := by
      unfold cylinderPowerIntegral
      calc
        _ = ∫⁻ w in parabolicCylinder z.1 z.2 r.1,
            ENNReal.ofReal |c| ^ P * ENNReal.ofReal |f w| ^ P := by
          apply lintegral_congr
          intro w
          rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg c),
            ENNReal.mul_rpow_of_nonneg _ _ hP.le]
        _ = _ := lintegral_const_mul' _ _
          (ENNReal.rpow_ne_top_of_nonneg hP.le ENNReal.ofReal_ne_top)
    have hroot :
        (ENNReal.ofReal |c| ^ P * cylinderPowerIntegral P f z r.1) ^ (1 / P : ℝ) =
          ENNReal.ofReal |c| * (cylinderPowerIntegral P f z r.1) ^ (1 / P : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hP.le),
        ← ENNReal.rpow_mul, mul_one_div_cancel hP.ne', ENNReal.rpow_one]
    rw [morreyCell_eq, hI, hroot, morreyCell_eq]
    exact mul_left_comm _ _ _
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  rw [hcell]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact le_iSup_of_le z (le_iSup (fun s : {s : ℝ // 0 < s} =>
    morreyCell P τ f z s.1) r)

end CKN.Core.Endgame
