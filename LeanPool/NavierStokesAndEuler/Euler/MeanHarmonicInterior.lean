/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Sobolev
import LeanPool.NavierStokesAndEuler.Euler.MeanScalarSobolev
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicCutoffEnergy
import LeanPool.NavierStokesAndEuler.Euler.MeanScalarProductDerivatives
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicDerivatives
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCalculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A proved interior bound for ordinary three-dimensional harmonic functions

The constant is built from fixed smooth cutoffs and the already proved Fourier
Sobolev inequality. It is independent of the harmonic function. The argument
uses two actual Caccioppoli estimates; no harmonic mean-value theorem or
interior regularity estimate is assumed.
-/

section

/-! The actual second-derivative estimate for the localized harmonic function. -/

section

/-! Actual nested smooth cutoffs, with finite derivative bounds independent of the field. -/

@[expose] public section

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerVectorCalculus
open scoped ContDiff

theorem derivative_bound_exists (f : Space → ℝ) (hc : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (n : ℕ) : ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C :=
  (hc.iteratedFDeriv n).exists_bound_of_continuous (hs.continuous_iteratedFDeriv (by simp))

/-- Derivative bound, given by `max 1 (Classical.choose (derivative_bound_exists f hc hs n))`. -/
def derivativeBound (f : Space → ℝ) (hc : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (n : ℕ) : ℝ :=
  max 1 (Classical.choose (derivative_bound_exists f hc hs n))

theorem one_le_derivativeBound (f : Space → ℝ) (hc : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (n : ℕ) : 1 ≤ derivativeBound f hc hs n := le_max_left _ _

theorem norm_iteratedFDeriv_le_derivativeBound (f : Space → ℝ) (hc : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ derivativeBound f hc hs n :=
  (Classical.choose_spec (derivative_bound_exists f hc hs n) x).trans (le_max_right _ _)

theorem norm_gradient_le_derivativeBound (f : Space → ℝ) (hc : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (x : Space) : ‖gradient f x‖ ≤ derivativeBound f hc hs 1 := by
  have hn : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := (toDual ℝ Space).symm.norm_map _
  rw [hn, ← norm_iteratedFDeriv_one]
  exact norm_iteratedFDeriv_le_derivativeBound f hc hs 1 x

theorem abs_secondPartial_le_derivativeBound (f : Space → ℝ) (hc : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (i : Fin 3) (x : Space) :
    |partialDerivative (partialDerivative f i) i x| ≤ derivativeBound f hc hs 2 := by
  rw [partialDerivative_twice f hs i x, ← Real.norm_eq_abs]
  have h := (iteratedFDeriv ℝ 2 f x).le_opNorm (fun _ : Fin 2 => EuclideanSpace.single i 1)
  have hb : ‖iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => EuclideanSpace.single i 1)‖ ≤
      ‖iteratedFDeriv ℝ 2 f x‖ := by
    simpa only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] using h
  exact hb.trans (norm_iteratedFDeriv_le_derivativeBound f hc hs 2 x)

/-- Inner bump, given by `⟨1/2, 5/8, by norm_num, by norm_num⟩`. -/
def innerBump : ContDiffBump (0 : Space) := ⟨1/2, 5/8, by norm_num, by norm_num⟩
/-- Middle bump, given by `⟨3/4, 13/16, by norm_num, by norm_num⟩`. -/
def middleBump : ContDiffBump (0 : Space) := ⟨3/4, 13/16, by norm_num, by norm_num⟩
/-- Outer bump, given by `⟨7/8, 15/16, by norm_num, by norm_num⟩`. -/
def outerBump : ContDiffBump (0 : Space) := ⟨7/8, 15/16, by norm_num, by norm_num⟩

/-- Inner cutoff, given by `innerBump`. -/
def innerCutoff : Space → ℝ := innerBump
/-- Middle cutoff, given by `middleBump`. -/
def middleCutoff : Space → ℝ := middleBump
/-- Outer cutoff, given by `outerBump`. -/
def outerCutoff : Space → ℝ := outerBump

theorem inner_smooth : ContDiff ℝ ∞ innerCutoff := innerBump.contDiff
theorem middle_smooth : ContDiff ℝ ∞ middleCutoff := middleBump.contDiff
theorem outer_smooth : ContDiff ℝ ∞ outerCutoff := outerBump.contDiff
theorem inner_compact : HasCompactSupport innerCutoff := innerBump.hasCompactSupport
theorem middle_compact : HasCompactSupport middleCutoff := middleBump.hasCompactSupport
theorem outer_compact : HasCompactSupport outerCutoff := outerBump.hasCompactSupport

theorem inner_support : tsupport innerCutoff = Metric.closedBall 0 (5/8 : ℝ) :=
  innerBump.tsupport_eq
theorem middle_support : tsupport middleCutoff = Metric.closedBall 0 (13/16 : ℝ) :=
  middleBump.tsupport_eq
theorem outer_support : tsupport outerCutoff = Metric.closedBall 0 (15/16 : ℝ) :=
  outerBump.tsupport_eq

theorem abs_inner_le_one (x : Space) : |innerCutoff x| ≤ 1 := by
  change |innerBump x| ≤ 1
  rw [abs_of_nonneg innerBump.nonneg]
  exact innerBump.le_one
theorem abs_middle_le_one (x : Space) : |middleCutoff x| ≤ 1 := by
  change |middleBump x| ≤ 1
  rw [abs_of_nonneg middleBump.nonneg]
  exact middleBump.le_one
theorem abs_outer_le_one (x : Space) : |outerCutoff x| ≤ 1 := by
  change |outerBump x| ≤ 1
  rw [abs_of_nonneg outerBump.nonneg]
  exact outerBump.le_one

theorem inner_one_on_halfBall {x : Space} (hx : x ∈ Metric.closedBall 0 (1 / 2 : ℝ)) :
    innerCutoff x = 1 := innerBump.one_of_mem_closedBall hx

theorem middle_one_on_inner_support {x : Space} (hx : x ∈ tsupport innerCutoff) :
    middleCutoff x = 1 := by
  rw [inner_support] at hx
  exact middleBump.one_of_mem_closedBall
    (Metric.closedBall_subset_closedBall (by norm_num [middleBump]) hx)

theorem outer_one_on_middle_support {x : Space} (hx : x ∈ tsupport middleCutoff) :
    outerCutoff x = 1 := by
  rw [middle_support] at hx
  exact outerBump.one_of_mem_closedBall
    (Metric.closedBall_subset_closedBall (by norm_num [outerBump]) hx)

theorem outer_one_on_inner_support {x : Space} (hx : x ∈ tsupport innerCutoff) :
    outerCutoff x = 1 := by
  rw [inner_support] at hx
  exact outerBump.one_of_mem_closedBall
    (Metric.closedBall_subset_closedBall (by norm_num [outerBump]) hx)

theorem outer_support_unitBall : tsupport outerCutoff ⊆ Metric.ball 0 (1 : ℝ) := by
  rw [outer_support]
  exact Metric.closedBall_subset_ball (by norm_num)

theorem middle_support_unitBall : tsupport middleCutoff ⊆ Metric.ball 0 (1 : ℝ) := by
  rw [middle_support]
  exact Metric.closedBall_subset_ball (by norm_num)

end EulerMeanHarmonic

end
end

end

section

/-! Two local energy steps for smooth harmonic functions on the unit ball. -/

@[expose] public section

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
open scoped ContDiff

/-- Outer derivative bound, given by `derivativeBound outerCutoff outer_compact outer_smooth 1`. -/
def outerDerivativeBound : ℝ := derivativeBound outerCutoff outer_compact outer_smooth 1
/-- Middle derivative bound, given by `derivativeBound middleCutoff middle_compact middle_smooth
1`. -/
def middleDerivativeBound : ℝ := derivativeBound middleCutoff middle_compact middle_smooth 1
/-- Inner derivative bound, given by `derivativeBound innerCutoff inner_compact inner_smooth 1`. -/
def innerDerivativeBound : ℝ := derivativeBound innerCutoff inner_compact inner_smooth 1
/-- Inner second bound, given by `derivativeBound innerCutoff inner_compact inner_smooth 2`. -/
def innerSecondBound : ℝ := derivativeBound innerCutoff inner_compact inner_smooth 2

theorem outer_bound_nonneg : 0 ≤ outerDerivativeBound :=
  le_trans (by norm_num) (one_le_derivativeBound _ _ _ _)
theorem middle_bound_nonneg : 0 ≤ middleDerivativeBound :=
  le_trans (by norm_num) (one_le_derivativeBound _ _ _ _)
theorem inner_bound_nonneg : 0 ≤ innerDerivativeBound :=
  le_trans (by norm_num) (one_le_derivativeBound _ _ _ _)
theorem inner_second_nonneg : 0 ≤ innerSecondBound :=
  le_trans (by norm_num) (one_le_derivativeBound _ _ _ _)

theorem outer_gradient_energy_le (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (hLp : MemLp h 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ h x = 0) :
    (∫ x, outerCutoff x ^ 2 * ‖gradient h x‖ ^ 2) ≤
      4 * outerDerivativeBound ^ 2 * (lpNorm h 2 volume) ^ 2 := by
  have hi : Integrable (fun x => (1 : ℝ) ^ 2 * h x ^ 2) := by
    simpa only [one_pow, one_mul] using (memLp_two_iff_integrable_sq hLp.aestronglyMeasurable).1 hLp
  have hb (x : Space) : ‖gradient outerCutoff x‖ ^ 2 ≤
      outerDerivativeBound ^ 2 * (1 : ℝ) ^ 2 := by
    simpa only [one_pow, mul_one, outerDerivativeBound] using pow_le_pow_left₀ (norm_nonneg _)
      (norm_gradient_le_derivativeBound outerCutoff outer_compact outer_smooth x) 2
  have H := caccioppoli_weighted_bound outerCutoff (fun _ => 1) h outerDerivativeBound
    outer_compact outer_smooth hh
    (fun x hx => hharmonic x (outer_support_unitBall hx)) hi hb
  simpa only [one_pow, one_mul, ← lpNorm_sq_eq_integral_sq h hLp] using H

theorem outer_partial_energy_le (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (hLp : MemLp h 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ h x = 0)
    (i : Fin 3) :
    (∫ x, outerCutoff x ^ 2 * partialDerivative h i x ^ 2) ≤
      4 * outerDerivativeBound ^ 2 * (lpNorm h 2 volume) ^ 2 := by
  have hcomp : (∫ x, outerCutoff x ^ 2 * partialDerivative h i x ^ 2) ≤
      ∫ x, outerCutoff x ^ 2 * ‖gradient h x‖ ^ 2 :=
    integral_mono
      (integrable_weighted_square _ _ outer_compact outer_smooth.continuous
        (contDiff_partialDerivative h hh i).continuous)
      (integrable_weighted_gradient_square _ _ outer_compact outer_smooth.continuous hh)
      (fun x => mul_le_mul_of_nonneg_left (partialDerivative_sq_le_gradient_sq h i x)
        (sq_nonneg (outerCutoff x)))
  exact hcomp.trans (outer_gradient_energy_le h hh hLp hharmonic)

theorem middle_second_energy_le (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (hLp : MemLp h 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ h x = 0)
    (i : Fin 3) :
    (∫ x, middleCutoff x ^ 2 * ‖gradient (partialDerivative h i) x‖ ^ 2) ≤
      16 * middleDerivativeBound ^ 2 * outerDerivativeBound ^ 2 * (lpNorm h 2 volume) ^ 2 := by
  have hhi := contDiff_partialDerivative h hh i
  have H := caccioppoli_weighted_bound middleCutoff outerCutoff (partialDerivative h i)
    middleDerivativeBound middle_compact middle_smooth hhi
    (fun x hx => partialDerivative_harmonic_on h hh _ Metric.isOpen_ball hharmonic i x
      (middle_support_unitBall hx))
    (integrable_weighted_square _ _ outer_compact outer_smooth.continuous hhi.continuous)
    (cutoff_gradient_majorant middleCutoff outerCutoff middleDerivativeBound
      (norm_gradient_le_derivativeBound _ middle_compact middle_smooth)
      (fun _ hx => outer_one_on_middle_support hx))
  calc
    _ ≤ 4 * middleDerivativeBound ^ 2 *
        (∫ x, outerCutoff x ^ 2 * partialDerivative h i x ^ 2) := H
    _ ≤ 4 * middleDerivativeBound ^ 2 *
        (4 * outerDerivativeBound ^ 2 * (lpNorm h 2 volume) ^ 2) :=
      mul_le_mul_of_nonneg_left (outer_partial_energy_le h hh hLp hharmonic i) (by positivity)
    _ = _ := by ring

end EulerMeanHarmonic

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
open scoped ContDiff

theorem localized_second_pointwise (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (i : Fin 3) (x : Space) :
    partialDerivative (partialDerivative (innerCutoff * h) i) i x ^ 2 ≤
      3 * (innerSecondBound ^ 2 * h x ^ 2 +
        4 * innerDerivativeBound ^ 2 * (outerCutoff x ^ 2 * ‖gradient h x‖ ^ 2) +
        middleCutoff x ^ 2 * ‖gradient (partialDerivative h i) x‖ ^ 2) := by
  have hη₂ : partialDerivative (partialDerivative innerCutoff i) i x ^ 2 ≤
      innerSecondBound ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _)
      (abs_secondPartial_le_derivativeBound innerCutoff inner_compact inner_smooth i x) 2
    simpa only [sq_abs, innerSecondBound] using h
  have hη₁ : partialDerivative innerCutoff i x ^ 2 ≤
      innerDerivativeBound ^ 2 * outerCutoff x ^ 2 :=
    (partialDerivative_sq_le_gradient_sq innerCutoff i x).trans
      (cutoff_gradient_majorant innerCutoff outerCutoff innerDerivativeBound
        (norm_gradient_le_derivativeBound innerCutoff inner_compact inner_smooth)
        (fun _ hx => outer_one_on_inner_support hx) x)
  have hη₀ : innerCutoff x ^ 2 ≤ middleCutoff x ^ 2 :=
    cutoff_square_majorant innerCutoff middleCutoff abs_inner_le_one
      (fun _ hx => middle_one_on_inner_support hx) x
  have ha : (h x * partialDerivative (partialDerivative innerCutoff i) i x) ^ 2 ≤
      innerSecondBound ^ 2 * h x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hη₂ (sq_nonneg (h x))]
  have hb : (2 * partialDerivative innerCutoff i x * partialDerivative h i x) ^ 2 ≤
      4 * innerDerivativeBound ^ 2 * (outerCutoff x ^ 2 * ‖gradient h x‖ ^ 2) := by
    have H := mul_le_mul hη₁ (partialDerivative_sq_le_gradient_sq h i x)
      (sq_nonneg (partialDerivative h i x)) (by positivity)
    nlinarith
  have hc : (innerCutoff x * partialDerivative (partialDerivative h i) i x) ^ 2 ≤
      middleCutoff x ^ 2 * ‖gradient (partialDerivative h i) x‖ ^ 2 := by
    have H := mul_le_mul hη₀ (partialDerivative_sq_le_gradient_sq (partialDerivative h i) i x)
      (sq_nonneg _) (sq_nonneg _)
    nlinarith
  rw [secondPartial_mul innerCutoff h inner_smooth hh i x]
  have H := sq_add_three_le
    (h x * partialDerivative (partialDerivative innerCutoff i) i x)
    (2 * partialDerivative innerCutoff i x * partialDerivative h i x)
    (innerCutoff x * partialDerivative (partialDerivative h i) i x)
  nlinarith

/-- Interior second energy constant, constructed using `3`. -/
def interiorSecondEnergyConstant : ℝ :=
  3 * (innerSecondBound ^ 2 + 16 * innerDerivativeBound ^ 2 * outerDerivativeBound ^ 2 +
    16 * middleDerivativeBound ^ 2 * outerDerivativeBound ^ 2)

theorem interiorSecondEnergyConstant_nonneg : 0 ≤ interiorSecondEnergyConstant := by
  unfold interiorSecondEnergyConstant
  positivity

theorem localized_second_memLp (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) (i : Fin 3) :
    MemLp (partialDerivative (partialDerivative (innerCutoff * h) i) i) 2 volume := by
  have hc : HasCompactSupport (innerCutoff * h) := inner_compact.mul_right (f' := h)
  have hc₁ : HasCompactSupport (partialDerivative (innerCutoff * h) i) :=
    hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hc₂ : HasCompactSupport (partialDerivative (partialDerivative (innerCutoff * h) i) i) :=
    hc₁.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  exact (contDiff_partialDerivative _
    (contDiff_partialDerivative _ (inner_smooth.mul hh) i) i).continuous.memLp_of_hasCompactSupport
        hc₂

theorem localized_second_energy_le (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (hLp : MemLp h 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ h x = 0)
    (i : Fin 3) :
    (lpNorm (partialDerivative (partialDerivative (innerCutoff * h) i) i) 2 volume) ^ 2 ≤
      interiorSecondEnergyConstant * (lpNorm h 2 volume) ^ 2 := by
  have hL := localized_second_memLp h hh i
  have hiL := (memLp_two_iff_integrable_sq hL.aestronglyMeasurable).1 hL
  have hi₀ := (memLp_two_iff_integrable_sq hLp.aestronglyMeasurable).1 hLp
  have hi₁ := integrable_weighted_gradient_square outerCutoff h outer_compact
      outer_smooth.continuous hh
  have hi₂ := integrable_weighted_gradient_square middleCutoff (partialDerivative h i)
    middle_compact middle_smooth.continuous (contDiff_partialDerivative h hh i)
  have hiA := hi₀.const_mul (innerSecondBound ^ 2)
  have hiB := hi₁.const_mul (4 * innerDerivativeBound ^ 2)
  have hiAB : Integrable (fun x => innerSecondBound ^ 2 * h x ^ 2 +
      4 * innerDerivativeBound ^ 2 * (outerCutoff x ^ 2 * ‖gradient h x‖ ^ 2)) := hiA.add hiB
  have H := integral_mono hiL ((hiAB.add hi₂).const_mul 3)
    (fun x => localized_second_pointwise h hh i x)
  simp only [Pi.add_apply] at H
  rw [integral_const_mul, integral_add hiAB hi₂, integral_add hiA hiB,
    integral_const_mul, integral_const_mul, ← lpNorm_sq_eq_integral_sq h hLp] at H
  rw [lpNorm_sq_eq_integral_sq _ hL]
  calc
    _ ≤ 3 * (innerSecondBound ^ 2 * (lpNorm h 2 volume) ^ 2 +
        4 * innerDerivativeBound ^ 2 *
          (∫ x, outerCutoff x ^ 2 * ‖gradient h x‖ ^ 2) +
        ∫ x, middleCutoff x ^ 2 * ‖gradient (partialDerivative h i) x‖ ^ 2) := H
    _ ≤ 3 * (innerSecondBound ^ 2 * (lpNorm h 2 volume) ^ 2 +
        4 * innerDerivativeBound ^ 2 *
          (4 * outerDerivativeBound ^ 2 * (lpNorm h 2 volume) ^ 2) +
        16 * middleDerivativeBound ^ 2 * outerDerivativeBound ^ 2 * (lpNorm h 2 volume) ^ 2) := by
      gcongr
      · exact outer_gradient_energy_le h hh hLp hharmonic
      · exact middle_second_energy_le h hh hLp hharmonic i
    _ = _ := by unfold interiorSecondEnergyConstant; ring

end EulerMeanHarmonic

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus EulerSobolev
open scoped ContDiff

theorem localized_second_norm_le (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (hLp : MemLp h 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ h x = 0)
    (i : Fin 3) :
    lpNorm (partialDerivative (partialDerivative (innerCutoff * h) i) i) 2 volume ≤
      Real.sqrt interiorSecondEnergyConstant * lpNorm h 2 volume := by
  apply (sq_le_sq₀ lpNorm_nonneg (mul_nonneg (Real.sqrt_nonneg _) lpNorm_nonneg)).1
  rw [mul_pow, Real.sq_sqrt interiorSecondEnergyConstant_nonneg]
  exact localized_second_energy_le h hh hLp hharmonic i

theorem localized_norm_le (h : Space → ℝ) (hLp : MemLp h 2 volume) :
    lpNorm (innerCutoff * h) 2 volume ≤ lpNorm h 2 volume := by
  have H : lpNorm (innerCutoff * h) 2 volume ≤ lpNorm (fun x => ‖h x‖) 2 volume := by
    apply lpNorm_mono_real hLp.norm
    intro x
    calc
      ‖(innerCutoff * h) x‖ = |innerCutoff x| * ‖h x‖ := by
        simp only [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
      _ ≤ 1 * ‖h x‖ := mul_le_mul_of_nonneg_right (abs_inner_le_one x) (norm_nonneg _)
      _ = ‖h x‖ := one_mul _
  simpa only [lpNorm_norm hLp.aestronglyMeasurable] using H

/-- Harmonic interior constant, given by `embeddingConstant 3 2 (by norm_num) * (1 + (2 *
Real.pi) ^ (-2 : ℤ) * (3 * Real.sqrt interiorSecondEnergyConstant))`. -/
def harmonicInteriorConstant : ℝ :=
  embeddingConstant 3 2 (by norm_num) *
    (1 + (2 * Real.pi) ^ (-2 : ℤ) * (3 * Real.sqrt interiorSecondEnergyConstant))

theorem harmonicInteriorConstant_nonneg : 0 ≤ harmonicInteriorConstant := by
  unfold harmonicInteriorConstant embeddingConstant
  positivity

/-- A genuine L²-to-pointwise interior estimate on the unit ball in R³. -/
theorem harmonic_pointwise_halfBall (h : Space → ℝ) (hh : ContDiff ℝ ∞ h)
    (hLp : MemLp h 2 volume) (hharmonic : ∀ x ∈ Metric.ball 0 (1 : ℝ), Δ h x = 0)
    (x : Space) (hx : x ∈ Metric.closedBall 0 (1 / 2 : ℝ)) :
    |h x| ≤ harmonicInteriorConstant * lpNorm h 2 volume := by
  have hc : HasCompactSupport (innerCutoff * h) := inner_compact.mul_right (f' := h)
  have H := scalar_pointwise_le_H2 (innerCutoff * h) (inner_smooth.mul hh) hc x
  have hval : (innerCutoff * h) x = h x := by
    rw [Pi.mul_apply, inner_one_on_halfBall hx, one_mul]
  rw [hval] at H
  have hsum : (∑ i : Fin 3,
      lpNorm (partialDerivative (partialDerivative (innerCutoff * h) i) i) 2 volume) ≤
      3 * (Real.sqrt interiorSecondEnergyConstant * lpNorm h 2 volume) := by
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      localized_second_norm_le h hh hLp hharmonic i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] using hsum
  calc
    _ ≤ embeddingConstant 3 2 (by norm_num) *
        (lpNorm (innerCutoff * h) 2 volume + (2 * Real.pi) ^ (-2 : ℤ) *
          ∑ i : Fin 3, lpNorm (partialDerivative (partialDerivative (innerCutoff * h) i) i) 2
              volume) := H
    _ ≤ embeddingConstant 3 2 (by norm_num) *
        (lpNorm h 2 volume + (2 * Real.pi) ^ (-2 : ℤ) *
          (3 * (Real.sqrt interiorSecondEnergyConstant * lpNorm h 2 volume))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact add_le_add (localized_norm_le h hLp)
        (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = _ := by unfold harmonicInteriorConstant; ring

end EulerMeanHarmonic
