/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.DuhamelAdjoint
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationDuhamelFinish
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyBalls
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Kernel
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionPotentials
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP8
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.SingletonNull

/-!
# Pointwise Potential

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential
open CKN.Core.Step3


noncomputable section

namespace CKN.Core.Step4

private lemma rhoTwo_eq_parabolicRho₂ {z w : ParabolicPoint}
    {ht : 0 < z.2 - w.2} :
    rhoTwo (z.1 - w.1) (z.2 - w.2) = parabolicRho₂ z w := by
  unfold rhoTwo parabolicRho₂
  rw [abs_of_pos ht]
  ring

private lemma parabolicRho₂_pos_of_time {z w : ParabolicPoint}
    {ht : 0 < z.2 - w.2} : 0 < parabolicRho₂ z w := by
  unfold parabolicRho₂
  exact add_pos_of_pos_of_nonneg
    (Real.sqrt_pos.2 (abs_pos.mpr (ne_of_gt ht)))
    (vec3EuclideanNorm_nonneg _)

lemma heatPotentialKernel_abs_le_riesz₂ (z w : ParabolicPoint) :
    |heatPotentialKernel z w| ≤
      1000 * (parabolicRieszKernel 2 z w).toReal := by
  by_cases ht : 0 < z.2 - w.2
  · rw [heatPotentialKernel, pointSub]
    simp only [heatKernelPlus]
    rw [ite_eq_left ht]
    have hρ : 0 < parabolicRho₂ z w := parabolicRho₂_pos_of_time
      (z := z) (w := w) (ht := ht)
    have hright : (1000 / parabolicRho₂ z w ^ 3 : ℝ) =
        1000 * (parabolicRieszKernel 2 z w).toReal := by
      unfold parabolicRieszKernel
      rw [← ENNReal.toReal_rpow]
      rw [ENNReal.toReal_ofReal (le_of_lt hρ)]
      rw [show -(5 - (2 : ℝ)) = -(3 : ℝ) by norm_num]
      rw [Real.rpow_neg (le_of_lt hρ)]
      simp [div_eq_mul_inv]
    calc
      |heatKernel (z.1 - w.1) (z.2 - w.2)| =
          heatKernel (z.1 - w.1) (z.2 - w.2) :=
        abs_of_nonneg (heatKernel_nonneg _ _)
      _ ≤ 1000 / rhoTwo (z.1 - w.1) (z.2 - w.2) ^ 3 :=
        heatKernel_le_rho_inv_cube ht
      _ = 1000 * (parabolicRieszKernel 2 z w).toReal := by
        rw [rhoTwo_eq_parabolicRho₂ (z := z) (w := w) (ht := ht), hright]
  · rw [heatPotentialKernel, pointSub]
    simp only [heatKernelPlus]
    rw [ite_eq_right ht, abs_zero]
    positivity

lemma heatPotentialSpatialKernel_abs_le_riesz₁ (i : Fin 3)
    (z w : ParabolicPoint) :
    |heatPotentialSpatialKernel i z w| ≤
      300000 * (parabolicRieszKernel 1 z w).toReal := by
  by_cases ht : 0 < z.2 - w.2
  · rw [heatPotentialSpatialKernel]
    have hρ : 0 < parabolicRho₂ z w := parabolicRho₂_pos_of_time
      (z := z) (w := w) (ht := ht)
    have hright : (300000 / parabolicRho₂ z w ^ 4 : ℝ) =
        300000 * (parabolicRieszKernel 1 z w).toReal := by
      unfold parabolicRieszKernel
      rw [← ENNReal.toReal_rpow]
      rw [ENNReal.toReal_ofReal (le_of_lt hρ)]
      rw [show -(5 - (1 : ℝ)) = -(4 : ℝ) by norm_num]
      rw [Real.rpow_neg (le_of_lt hρ)]
      simp [div_eq_mul_inv]
    have hcomponent :
        |heatKernelSpaceDerivative (z.1 - w.1) (z.2 - w.2) i| ≤
          heatKernelGradientNorm (z.1 - w.1) (z.2 - w.2) := by
      unfold heatKernelGradientNorm
      exact Finset.single_le_sum
        (fun j _hj => abs_nonneg (heatKernelSpaceDerivative
          (z.1 - w.1) (z.2 - w.2) j)) (Finset.mem_univ i)
    have hgrad := heatKernelGradientNorm_le_rho_inv_four
      (x := z.1 - w.1) (t := z.2 - w.2) ht
    calc
      |heatKernelSpaceDerivative (z.1 - w.1) (z.2 - w.2) i| ≤
          heatKernelGradientNorm (z.1 - w.1) (z.2 - w.2) := hcomponent
      _ ≤ 300000 / rhoTwo (z.1 - w.1) (z.2 - w.2) ^ 4 := hgrad
      _ = 300000 * (parabolicRieszKernel 1 z w).toReal := by
        rw [rhoTwo_eq_parabolicRho₂ (z := z) (w := w) (ht := ht), hright]
  · rw [heatPotentialSpatialKernel, heatKernelSpaceDerivative]
    rw [ite_eq_right ht, abs_zero]
    positivity












def pointwisePotentialMajorant (g : ParabolicPoint → Vec3)
    (h : Fin 3 → ParabolicPoint → Vec3) : ParabolicPoint → ℝ :=
  fun z =>
    3000 * (parabolicRieszPotential 2
      (fun w => vec3EuclideanNorm (g w)) z).toReal +
    900000 * ∑ j, (parabolicRieszPotential 1
      (fun w => vec3EuclideanNorm (h j w)) z).toReal

















theorem forceLqDataOnBox
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : CKN.localBox Ω I Ω' J) :
    CKN.localVecLp (CKN.spaceTimeSet Ω' J) q f := by
  exact hsol.2.2.2.2.1 Ω' J hbox

end CKN.Core.Step4
