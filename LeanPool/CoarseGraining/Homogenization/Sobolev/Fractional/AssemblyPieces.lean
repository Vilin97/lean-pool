/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.Definitions
import LeanPool.CoarseGraining.Homogenization.Multiscale.OverlapLp

/-!
# Assembly pieces for the Besov-to-Gagliardo direction

Three small bridges used by the final estimate:

* `MemWsp`-side restriction: global `L^p` membership on the parent cube
  restricts to every enlarged center cube (with the normalization change
  absorbed into a finite scalar);
* the kernel identification: the `p`-th enorm power of the Gagliardo kernel
  is exactly the distance power times the difference power (U4);
* the lintegral of the Gagliardo product measure as a normalized plain
  product integral.
-/

namespace Homogenization
namespace Gagliardo

noncomputable section

open MeasureTheory ScalarOverlap
open scoped ENNReal

variable {d : ℕ}

/-- Restriction step: `L^p` membership for the parent's normalized measure
implies membership for every center's normalized enlarged-cube measure. -/
theorem memLp_overlap_of_memLp {Q : TriadicCube d} {p : ℝ≥0∞}
    {u : Vec d → ℝ} (hu : MemLp u p (normalizedCubeMeasure Q))
    {j : ℕ} {S : TriadicCube d} (hS : S ∈ ScalarOverlap.centersAtDepth Q j) :
    MemLp u p (ScalarOverlap.normalizedCubeMeasure S) := by
  have hsub : ScalarOverlap.cubeSet S ⊆ Homogenization.cubeSet Q :=
    cubeSet_subset_cubeSet_of_mem_centersAtDepth hS
  -- the enlarged normalized measure is dominated by a finite multiple of the
  -- parent normalized measure
  have hdom : ScalarOverlap.normalizedCubeMeasure S ≤
      (ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ *
        ENNReal.ofReal (cubeVolume Q)) • normalizedCubeMeasure Q := by
    rw [ScalarOverlap.normalizedCubeMeasure, Homogenization.normalizedCubeMeasure]
    rw [smul_smul]
    have hvolQ : (0 : ℝ) < cubeVolume Q := cubeVolume_pos Q
    have hcancel :
        ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ *
            ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal (cubeVolume Q)⁻¹ =
          ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ := by
      rw [mul_assoc, ← ENNReal.ofReal_mul hvolQ.le,
        mul_inv_cancel₀ hvolQ.ne', ENNReal.ofReal_one, mul_one]
    rw [hcancel]
    refine Measure.le_iff'.2 fun A => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    refine mul_le_mul_right ?_ _
    have hres : ScalarOverlap.cubeMeasure S ≤ Homogenization.cubeMeasure Q := by
      rw [ScalarOverlap.cubeMeasure, Homogenization.cubeMeasure]
      exact Measure.restrict_mono hsub le_rfl
    exact Measure.le_iff'.1 hres A
  have hfin : (ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ *
      ENNReal.ofReal (cubeVolume Q)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  exact ((hu.smul_measure hfin).mono_measure hdom)

/-- U4 (kernel identification): pointwise, the `p`-th enorm power of the
Gagliardo kernel splits into the distance power times the difference power.
Both sides vanish on the diagonal, so no case split is needed downstream. -/
theorem enorm_gagliardoKernel_rpow (s : ℝ) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hpt : p ≠ ∞) (u : Vec d → ℝ) (z : Vec d × Vec d) :
    ‖gagliardoKernel s p u z‖ₑ ^ p.toReal =
      ENNReal.ofReal (dist z.1 z.2 ^ (-(s * p.toReal + d))) *
        ‖u z.1 - u z.2‖ₑ ^ p.toReal := by
  have hpr : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hdist : (0 : ℝ) ≤ dist z.1 z.2 := dist_nonneg
  rw [gagliardoKernel_apply]
  rw [enorm_smul]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpr.le]
  congr 1
  -- scalar factor: ‖dist ^ (-kernelExponent)‖ₑ ^ pr = ofReal (dist ^ (-(s pr + d)))
  have hker : -kernelExponent d s p * p.toReal = -(s * p.toReal + d) := by
    rw [kernelExponent, neg_mul, add_mul, div_mul_cancel₀ _ hpr.ne']
  rw [Real.enorm_eq_ofReal_abs,
    abs_of_nonneg (Real.rpow_nonneg hdist _),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hdist _) hpr.le,
    ← Real.rpow_mul hdist, hker]

/-- The Gagliardo cube measure integrates as the volume-normalized plain
product integral over `Q ×ˢ Q`. -/
theorem lintegral_gagliardoCubeMeasure_eq (Q : TriadicCube d)
    (f : Vec d × Vec d → ℝ≥0∞) :
    (∫⁻ z, f z ∂gagliardoCubeMeasure Q) =
      ENNReal.ofReal (cubeVolume Q)⁻¹ *
        ∫⁻ z in Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q, f z
          ∂(MeasureTheory.volume.prod MeasureTheory.volume) := by
  have : SFinite (Homogenization.cubeMeasure Q) := by
    unfold Homogenization.cubeMeasure
    infer_instance
  rw [gagliardoCubeMeasure, Homogenization.normalizedCubeMeasure,
    Measure.prod_smul_left, lintegral_smul_measure]
  congr 1
  rw [Homogenization.cubeMeasure, Measure.prod_restrict]

end

end Gagliardo
end Homogenization
