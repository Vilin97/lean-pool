/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Bounds

/-!
# Kernel

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric


noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic

/-! The convolution variables are written explicitly so that the causal heat
kernel and its spatial derivatives have one common interface. -/

/-- Space-time displacement used as the argument of the translation-invariant heat kernel. -/
def pointSub (w v : ParabolicPoint) : ParabolicPoint :=
  (w.1 - v.1, w.2 - v.2)

/-- Causal heat kernel evaluated at the space-time displacement of two points. -/
def heatPotentialKernel (w v : ParabolicPoint) : ℝ :=
  heatKernelPlus (pointSub w v)

/-- Spatial derivative of the causal heat kernel at a space-time displacement. -/
def heatPotentialSpatialKernel (i : Fin 3) (w v : ParabolicPoint) : ℝ :=
  heatKernelSpaceDerivative (w.1 - v.1) (w.2 - v.2) i

/-- Heat potential of a scalar source and spatial divergence sources. -/
def heatPotential (F : ParabolicPoint → ℝ)
    (G : Fin 3 → ParabolicPoint → ℝ) (w : ParabolicPoint) : ℝ :=
  (∫ v, heatPotentialKernel w v * F v) +
    ∑ i, ∫ v, heatPotentialSpatialKernel i w v * G i v

private lemma heatKernelNorm_component_le {x : Vec3} {t : ℝ} (i : Fin 3) :
    |heatKernelSpaceDerivative x t i| ≤ heatKernelGradientNorm x t := by
  unfold heatKernelGradientNorm
  exact Finset.single_le_sum
    (fun j _hj => abs_nonneg (heatKernelSpaceDerivative x t j))
    (Finset.mem_univ i)

private lemma heatKernelTimeGradientNorm_component_le {x : Vec3} {t : ℝ}
    (i : Fin 3) :
    |heatKernelTimeGradientDerivative x t i| ≤ heatKernelTimeGradientNorm x t := by
  unfold heatKernelTimeGradientNorm
  exact Finset.single_le_sum
    (fun j _hj => abs_nonneg (heatKernelTimeGradientDerivative x t j))
    (Finset.mem_univ i)

private lemma rhoTwo_pos_of_time {x : Vec3} {t : ℝ} (ht : 0 < t) :
    0 < rhoTwo x t := by
  unfold rhoTwo
  exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg _)
    (Real.sqrt_pos.2 ht)

lemma heatPotentialKernel_abs_le {w v : ParabolicPoint} {R : ℝ}
    (hR : 0 < R) (hsep : R ≤ rhoTwo (w.1 - v.1) (w.2 - v.2)) :
    |heatPotentialKernel w v| ≤ 1000 / R ^ 3 := by
  rw [heatPotentialKernel, heatKernelPlus_eq_heatKernel]
  change |heatKernel (w.1 - v.1) (w.2 - v.2)| ≤ 1000 / R ^ 3
  by_cases ht : 0 < w.2 - v.2
  · have hρ : 0 < rhoTwo (w.1 - v.1) (w.2 - v.2) := rhoTwo_pos_of_time ht
    have hkernel := heatKernel_le_rho_inv_cube
      (x := w.1 - v.1) (t := w.2 - v.2) ht
    have hRρ : 0 < R := hR
    have hdiv : 1000 / rhoTwo (w.1 - v.1) (w.2 - v.2) ^ 3 ≤
        1000 / R ^ 3 := by
      gcongr
    exact (abs_of_nonneg (heatKernel_nonneg _ _)).trans_le (hkernel.trans hdiv)
  · rw [heatKernel_eq_zero_of_nonpos (le_of_not_gt ht), abs_zero]
    positivity

lemma heatPotentialSpatialKernel_abs_le {i : Fin 3} {w v : ParabolicPoint}
    {R : ℝ} (hR : 0 < R)
    (hsep : R ≤ rhoTwo (w.1 - v.1) (w.2 - v.2)) :
    |heatPotentialSpatialKernel i w v| ≤ 300000 / R ^ 4 := by
  rw [heatPotentialSpatialKernel]
  by_cases ht : 0 < w.2 - v.2
  · have hρ : 0 < rhoTwo (w.1 - v.1) (w.2 - v.2) := rhoTwo_pos_of_time ht
    have hcomponent := heatKernelNorm_component_le
      (x := w.1 - v.1) (t := w.2 - v.2) i
    have hgrad := heatKernelGradientNorm_le_rho_inv_four
      (x := w.1 - v.1) (t := w.2 - v.2) ht
    have hdiv : 300000 / rhoTwo (w.1 - v.1) (w.2 - v.2) ^ 4 ≤
        300000 / R ^ 4 := by
      gcongr
    exact hcomponent.trans (hgrad.trans hdiv)
  · rw [heatKernelSpaceDerivative, ite_eq_right ht, abs_zero]
    positivity

lemma heatPotentialSpatialTimeKernel_abs_le {i : Fin 3}
    {w v : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    (hsep : R ≤ rhoTwo (w.1 - v.1) (w.2 - v.2)) :
    |heatKernelTimeGradientDerivative (w.1 - v.1) (w.2 - v.2) i| ≤
      30000000000 / R ^ 6 := by
  by_cases ht : 0 < w.2 - v.2
  · have hcomponent := heatKernelTimeGradientNorm_component_le
      (x := w.1 - v.1) (t := w.2 - v.2) i
    have htime := heatKernelTimeGradientNorm_le_rho_inv_six
      (x := w.1 - v.1) (t := w.2 - v.2) ht
    have hdiv : 30000000000 /
          rhoTwo (w.1 - v.1) (w.2 - v.2) ^ 6 ≤ 30000000000 / R ^ 6 := by
      have hρ := rhoTwo_pos_of_time (x := w.1 - v.1) ht
      gcongr
    exact hcomponent.trans (htime.trans hdiv)
  · rw [heatKernelTimeGradientDerivative, ite_eq_right ht, abs_zero]
    positivity


end CKN.Core.HeatPotential
