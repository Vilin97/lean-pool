/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.FoldNorm
public import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent

/-!
# Finite-`p` norm transport under the even fold

This module upgrades the exact `L²` transport in `FoldNorm` to every finite
exponent used by the `W^{1,p}` development.  The measure transport itself
remains `lintegral_foldComp`; only the outer `p`-th root is new here.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory Homogenization
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {d : ℕ}

private theorem finiteLpExponent_ne_zero (p : FiniteLpExponent) : p.exponent ≠ 0 :=
  (zero_lt_one.trans p.one_lt).ne'

private theorem finiteLpExponent_toReal_pos (p : FiniteLpExponent) :
    0 < p.exponent.toReal :=
  ENNReal.toReal_pos (finiteLpExponent_ne_zero p) p.lt_top.ne

/-- Exact finite-`p` norm transport for composition with the coordinatewise
even fold. -/
theorem eLpNorm_foldComp_finiteLp {v : Vec d → ℝ} (p : FiniteLpExponent)
    (hv : Measurable v) (lo hi : Vec d) (hlt : ∀ k, lo k < hi k) :
    eLpNorm (fun x => v (Fold lo hi x)) p.exponent (volume.restrict (Box3 lo hi))
      = ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
          eLpNorm v p.exponent (volume.restrict (Box lo hi)) := by
  have hcomp : AEStronglyMeasurable (fun x => v (Fold lo hi x))
      (volume.restrict (Box3 lo hi)) :=
    (hv.comp (continuous_Fold lo hi (fun k => (hlt k).le)).measurable).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (finiteLpExponent_ne_zero p) p.lt_top.ne hcomp,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (finiteLpExponent_ne_zero p) p.lt_top.ne
      hv.aestronglyMeasurable]
  have hgmeas : Measurable (fun x : Vec d => ‖v x‖ₑ ^ p.exponent.toReal) :=
    ENNReal.continuous_rpow_const.measurable.comp hv.enorm
  have htrans : ∫⁻ x in Box3 lo hi, ‖v (Fold lo hi x)‖ₑ ^ p.exponent.toReal
      = (3 : ℝ≥0∞) ^ d * ∫⁻ x in Box lo hi, ‖v x‖ₑ ^ p.exponent.toReal :=
    lintegral_foldComp (g := fun x => ‖v x‖ₑ ^ p.exponent.toReal) hgmeas lo hi hlt
  rw [htrans, ENNReal.mul_rpow_of_nonneg _ _
    (one_div_nonneg.mpr (finiteLpExponent_toReal_pos p).le)]

/-- A coordinate derivative transported by the fold, including its reflection
sign, has no larger finite-`p` norm than the exactly scaled original field. -/
theorem eLpNorm_foldComp_mul_foldSign_le_finiteLp {D : Vec d → ℝ}
    (p : FiniteLpExponent) (hD : Measurable D) (lo hi : Vec d)
    (hlt : ∀ k, lo k < hi k) (i : Fin d) :
    eLpNorm (fun x => D (Fold lo hi x) * foldSign (lo i) (hi i) (x i))
        p.exponent (volume.restrict (Box3 lo hi))
      ≤ ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
          eLpNorm D p.exponent (volume.restrict (Box lo hi)) := by
  calc
    eLpNorm (fun x => D (Fold lo hi x) * foldSign (lo i) (hi i) (x i))
        p.exponent (volume.restrict (Box3 lo hi))
      ≤ eLpNorm (fun x => D (Fold lo hi x)) p.exponent
          (volume.restrict (Box3 lo hi)) := by
        have hsign : Measurable (foldSign (lo i) (hi i)) := by
          unfold foldSign
          refine Measurable.ite (measurableSet_lt measurable_id measurable_const)
            measurable_const ?_
          exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
            measurable_const measurable_const
        have hmeas : AEStronglyMeasurable
            (fun x => D (Fold lo hi x) * foldSign (lo i) (hi i) (x i))
            (volume.restrict (Box3 lo hi)) :=
          ((hD.comp (continuous_Fold lo hi (fun k => (hlt k).le)).measurable).mul
            (hsign.comp (measurable_pi_apply i))).aestronglyMeasurable
        refine eLpNorm_mono hmeas (fun x => ?_)
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (by
          unfold foldSign
          split_ifs <;> norm_num)
    _ = ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
          eLpNorm D p.exponent (volume.restrict (Box lo hi)) :=
      eLpNorm_foldComp_finiteLp p hD lo hi hlt

end

end Homogenization
