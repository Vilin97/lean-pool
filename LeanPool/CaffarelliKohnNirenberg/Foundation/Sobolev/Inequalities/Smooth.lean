/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Local Sobolev and interpolation inequalities for smooth functions

This file proves local Sobolev and interpolation inequalities for smooth
functions. The corresponding weak H¹ estimate has the form

`‖u‖₆(Bᵣ) ≤ C (‖∇u‖₂(B₂ᵣ) + r⁻¹ ‖u‖₂(B₂ᵣ))`.

Passing from smooth functions to weak H¹ functions requires local approximation
of both the function and its gradient, together with the weak product rule
for a smooth cutoff. Interpolation yields the `L³` and `L^(10/3)` estimates;
for `Q_r = (t-r²,t) × B_r`, the `L³` cylinder factor is `r^(1/2)`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace CKN

noncomputable section

/-- The extended `Lᵖ` seminorm of a function on a measurable set. -/
@[expose]
def lpNormOn (p : ℝ≥0∞) (s : Set (Vec 3)) (u : Vec 3 → ℝ) : ℝ≥0∞ :=
  eLpNorm u p (volume.restrict s)

/-- The extended `Lᵖ` seminorm of the native classical gradient. -/
@[expose]
def gradientLpNormOn (p : ℝ≥0∞) (s : Set (Vec 3)) (u : Vec 3 → ℝ) : ℝ≥0∞ :=
  eLpNorm (classicalGradient u) p (volume.restrict s)

private theorem norm_le_vecEuclideanNorm {d : ℕ} (x : Vec d) :
    ‖x‖ ≤ vecEuclideanNorm x := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖x i‖₊) ≤
      ⟨vecEuclideanNorm x, vecEuclideanNorm_nonneg x⟩ := by
    apply Finset.sup_le
    intro i hi
    exact_mod_cast abs_apply_le_vecEuclideanNorm x i
  exact_mod_cast hnn

private theorem classicalGradient_mul
    {f g : Vec 3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    classicalGradient (fun x => f x * g x) =
      fun x => f x • classicalGradient g x + g x • classicalGradient f x := by
  funext x i
  rw [classicalGradient_apply]
  have h := congrArg (fun L : Vec 3 →L[ℝ] ℝ => L (basisVec i))
    (fderiv_mul (hf x) (hg x))
  have hfun : (fun y => f y * g y) = f * g := by
    funext y
    rfl
  rw [hfun]
  simpa [Pi.mul_apply, smul_eq_mul, classicalGradient_apply, add_comm] using h

theorem fderiv_norm_le_three_classicalGradient
    {f : Vec 3 → ℝ} (x : Vec 3) :
    ‖fderiv ℝ f x‖ ≤ 3 * ‖classicalGradient f x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  calc
    ‖(fderiv ℝ f x) z‖ =
        ‖∑ i : Fin 3, z i • (fderiv ℝ f x) (basisVec i)‖ := by
          have hz : z = ∑ i : Fin 3, z i • basisVec i :=
            (sum_smul_basisVec z).symm
          rw [hz, map_sum]
          simp [Pi.smul_apply, smul_eq_mul]
    _ ≤ ∑ i : Fin 3, ‖z i • (fderiv ℝ f x) (basisVec i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖z‖ * ‖classicalGradient f x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      have hz : |z i| ≤ ‖z‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
      have hg : |(fderiv ℝ f x) (basisVec i)| ≤ ‖classicalGradient f x‖ := by
        simpa only [classicalGradient_apply, Real.norm_eq_abs] using
          norm_le_pi_norm (classicalGradient f x) i
      exact mul_le_mul hz hg (abs_nonneg _) (norm_nonneg _)
    _ = 3 * ‖classicalGradient f x‖ * ‖z‖ := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring

private theorem canonicalBallCutoff_gradient_norm_bound
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) (x : Vec 3) :
    ‖classicalGradient (canonicalBallCutoff x₀ r (2 * r)) x‖ ≤ 32 / r := by
  calc
    ‖classicalGradient (canonicalBallCutoff x₀ r (2 * r)) x‖ ≤
        vecEuclideanNorm (classicalGradient
          (canonicalBallCutoff x₀ r (2 * r)) x) :=
      norm_le_vecEuclideanNorm _
    _ ≤ 32 / ((2 * r) - r) := canonicalBallCutoff_gradient_bound (le_of_lt hr)
      (by linarith only [hr]) x
    _ = 32 / r := by ring_nf

/- The fixed factor is absolute because the ambient dimension is three. -/
/-- Euclidean Sobolev coefficient inherited from Mathlib's compact-support inequality. -/
@[expose]
noncomputable def localSobolevConstant : ℝ≥0∞ :=
  ((3 : NNReal) : ℝ≥0∞) *
    (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
      (2 : ℝ) : ℝ≥0∞)

private theorem smooth_cutoff_gradient_bound
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) (u : Vec 3 → ℝ)
    (hu : ContDiff ℝ 1 u) :
    eLpNorm (fun x =>
        canonicalBallCutoff x₀ r (2 * r) x • classicalGradient u x) 2 volume ≤
      eLpNorm ((euclideanBall x₀ (2 * r)).indicator (classicalGradient u)) 2 volume := by
  let η : Vec 3 → ℝ := canonicalBallCutoff x₀ r (2 * r)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    canonicalBallCutoff_smooth x₀ (le_of_lt hr) (by linarith only [hr])
  have houter : MeasurableSet (euclideanBall x₀ (2 * r)) := by
    change MeasurableSet {x | euclideanSqDist x x₀ < (2 * r) ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const).measurableSet
  have hgrad : AEStronglyMeasurable (classicalGradient u) volume := by
    have hcont : Continuous (classicalGradient u) := by
      apply continuous_pi
      intro i
      simpa only [classicalGradient_apply] using
        (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hcont.aestronglyMeasurable
  apply eLpNorm_mono_ae
    (f := fun x => η x • classicalGradient u x)
    (g := (euclideanBall x₀ (2 * r)).indicator (classicalGradient u))
    (hη.continuous.aestronglyMeasurable.smul hgrad)
  filter_upwards [] with x
  by_cases hx : x ∈ euclideanBall x₀ (2 * r)
  · rw [indicator_of_mem hx]
    rw [norm_smul]
    have hη0 : 0 ≤ η x := canonicalBallCutoff_nonneg x₀ r (2 * r) x
    have hη1 : η x ≤ 1 := canonicalBallCutoff_le_one x₀ r (2 * r) x
    simpa [abs_of_nonneg hη0] using
      (mul_le_mul_of_nonneg_right hη1 (norm_nonneg (classicalGradient u x)))
  · simp only [Set.indicator, hx, ite_false]
    have hxt : x ∉ tsupport η := by
      intro hxt
      exact hx (canonicalBallCutoff_tsupport_subset_outer (le_of_lt hr)
        (by linarith only [hr]) hxt)
    rw [show η x = 0 by exact image_eq_zero_of_notMem_tsupport hxt]
    simp

private theorem smooth_cutoff_u_gradient_bound
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) (u : Vec 3 → ℝ)
    (hu : ContDiff ℝ 1 u) :
    eLpNorm (fun x => u x •
        classicalGradient (canonicalBallCutoff x₀ r (2 * r)) x) 2 volume ≤
      Real.toNNReal (32 / r) •
        eLpNorm ((euclideanBall x₀ (2 * r)).indicator u) 2 volume := by
  let η : Vec 3 → ℝ := canonicalBallCutoff x₀ r (2 * r)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    canonicalBallCutoff_smooth x₀ (le_of_lt hr) (by linarith only [hr])
  have hgradη : AEStronglyMeasurable (classicalGradient η) volume := by
    have hcont : Continuous (classicalGradient η) := by
      apply continuous_pi
      intro i
      simpa only [classicalGradient_apply] using
        (hη.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hcont.aestronglyMeasurable
  have huMeas : AEStronglyMeasurable u volume :=
    hu.continuous.aestronglyMeasurable
  refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (f := fun x => u x • classicalGradient η x)
    (g := (euclideanBall x₀ (2 * r)).indicator u)
    (huMeas.smul hgradη) ?_ 2
  filter_upwards [] with x
  by_cases hx : x ∈ euclideanBall x₀ (2 * r)
  · rw [indicator_of_mem hx]
    have hgrad := canonicalBallCutoff_gradient_norm_bound (x₀ := x₀) hr x
    have hpoint : ‖u x • classicalGradient η x‖ ≤
        (32 / r) * ‖u x‖ := by
      rw [norm_smul]
      simpa [η, mul_comm] using
        (mul_le_mul_of_nonneg_left hgrad (norm_nonneg (u x)))
    have hscale : (Real.toNNReal (32 / r) : ℝ) = 32 / r := by
      exact Real.coe_toNNReal (32 / r) (by positivity)
    rw [← NNReal.coe_le_coe]
    simpa [hscale] using hpoint
  · simp only [Set.indicator, hx, ite_false]
    have hxt : x ∉ tsupport η := by
      intro hxt
      exact hx (canonicalBallCutoff_tsupport_subset_outer (le_of_lt hr)
        (by linarith only [hr]) hxt)
    have hzero : classicalGradient η x = 0 := by
      funext i
      rw [classicalGradient_apply, fderiv_of_notMem_tsupport ℝ hxt]
      simp
    simp [hzero]

theorem smoothSobolevBall
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) {u : Vec 3 → ℝ}
    (hu : ContDiff ℝ 1 u) :
    lpNormOn 6 (euclideanBall x₀ r) u ≤
      localSobolevConstant *
        (gradientLpNormOn 2 (euclideanBall x₀ (2 * r)) u +
          (Real.toNNReal (32 / r) : ℝ≥0∞) *
            lpNormOn 2 (euclideanBall x₀ (2 * r)) u) := by
  let η : Vec 3 → ℝ := canonicalBallCutoff x₀ r (2 * r)
  let v : Vec 3 → ℝ := fun x => η x * u x
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    canonicalBallCutoff_smooth x₀ (le_of_lt hr) (by linarith only [hr])
  have hηC : HasCompactSupport η :=
    canonicalBallCutoff_hasCompactSupport (le_of_lt hr) (by linarith only [hr])
  have hv : ContDiff ℝ 1 v := by
    exact (hη.of_le (by norm_num)).mul hu
  have hvC : HasCompactSupport v := hηC.mul_right (f' := u)
  have hglobal :
      eLpNorm v 6 volume ≤
          (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
            (2 : ℝ) : ℝ≥0∞) *
          eLpNorm (fderiv ℝ v) 2 volume := by
    simpa using
      (MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
        (volume : Measure (Vec 3)) hv hvC
          (by norm_num : (1 : NNReal) ≤ 2)
          (by norm_num : 0 < Module.finrank ℝ (Vec 3))
          (by norm_num : ((6 : NNReal) : ℝ)⁻¹ =
            ((2 : NNReal) : ℝ)⁻¹ - ((Module.finrank ℝ (Vec 3) : ℝ)⁻¹)))
  have hderiv :
      eLpNorm (fderiv ℝ v) 2 volume ≤
        (3 : NNReal) • eLpNorm (classicalGradient v) 2 volume := by
    refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (f := fderiv ℝ v) (g := classicalGradient v)
      (hv.continuous_fderiv (by norm_num)).aestronglyMeasurable ?_ 2
    exact Filter.Eventually.of_forall (fun x => by
      exact_mod_cast fderiv_norm_le_three_classicalGradient (f := v) x)
  have hgrad :
      eLpNorm (classicalGradient v) 2 volume ≤
        eLpNorm ((euclideanBall x₀ (2 * r)).indicator (classicalGradient u)) 2 volume +
          Real.toNNReal (32 / r) •
            eLpNorm ((euclideanBall x₀ (2 * r)).indicator u) 2 volume := by
    rw [show classicalGradient v =
      (fun x => η x • classicalGradient u x + u x • classicalGradient η x) by
        simpa [v, η] using classicalGradient_mul (f := η) (g := u)
          (hη.differentiable (by norm_num)) (hu.differentiable (by norm_num))
          ]
    calc
      eLpNorm (fun x => η x • classicalGradient u x +
          u x • classicalGradient η x) 2 volume ≤
          eLpNorm (fun x => η x • classicalGradient u x) 2 volume +
            eLpNorm (fun x => u x • classicalGradient η x) 2 volume :=
        eLpNorm_add_le (by norm_num)
      _ ≤ eLpNorm ((euclideanBall x₀ (2 * r)).indicator (classicalGradient u)) 2 volume +
          Real.toNNReal (32 / r) •
            eLpNorm ((euclideanBall x₀ (2 * r)).indicator u) 2 volume := by
        exact add_le_add (smooth_cutoff_gradient_bound hr u hu)
          (smooth_cutoff_u_gradient_bound hr u hu)
  have houter : MeasurableSet (euclideanBall x₀ (2 * r)) := by
    change MeasurableSet {x | euclideanSqDist x x₀ < (2 * r) ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const).measurableSet
  have hin : MeasurableSet (euclideanBall x₀ r) := by
    change MeasurableSet {x | euclideanSqDist x x₀ < r ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const).measurableSet
  have hvInner :
      eLpNorm u 6 (volume.restrict (euclideanBall x₀ r)) ≤ eLpNorm v 6 volume := by
    calc
      eLpNorm u 6 (volume.restrict (euclideanBall x₀ r)) =
          eLpNorm v 6 (volume.restrict (euclideanBall x₀ r)) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem hin] with x hx
        simp [v, η, canonicalBallCutoff_eq_one_on_inner
          (x₀ := x₀) (r := r) (R := 2 * r) (x := x)
          (le_of_lt hr) (by linarith only [hr]) hx]
      _ ≤ eLpNorm v 6 volume := eLpNorm_mono_measure v Measure.restrict_le_self
  calc
    lpNormOn 6 (euclideanBall x₀ r) u ≤ eLpNorm v 6 volume := hvInner
    _ ≤ (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
          (2 : ℝ) : ℝ≥0∞) *
          eLpNorm (fderiv ℝ v) 2 volume := hglobal
    _ ≤ (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
          (2 : ℝ) : ℝ≥0∞) *
          (((3 : NNReal) : ℝ≥0∞) * eLpNorm (classicalGradient v) 2 volume) := by
      gcongr
      simpa [ENNReal.smul_def, smul_eq_mul] using hderiv
    _ ≤ localSobolevConstant *
          (gradientLpNormOn 2 (euclideanBall x₀ (2 * r)) u +
            (Real.toNNReal (32 / r) : ℝ≥0∞) *
              lpNormOn 2 (euclideanBall x₀ (2 * r)) u) := by
      rw [localSobolevConstant]
      rw [eLpNorm_indicator_eq_eLpNorm_restrict houter] at hgrad
      rw [eLpNorm_indicator_eq_eLpNorm_restrict houter] at hgrad
      simpa [gradientLpNormOn, lpNormOn, ENNReal.smul_def, smul_eq_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hgrad
          (show 0 ≤ ((3 : NNReal) : ℝ≥0∞) *
            (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
              (2 : ℝ) : ℝ≥0∞) by positivity))

end
end CKN
