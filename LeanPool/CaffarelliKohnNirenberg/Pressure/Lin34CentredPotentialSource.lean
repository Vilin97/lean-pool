/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredSource
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpGrowth
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayGrowthSum
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecay
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallOrigin

/-!
# Lin34 Centred Potential Source

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

open CKN.Foundation.Euclidean

/-!
# Local `L^{3/2}` membership and linear growth of the centred potentials `p₂`–`p₆`

The uniqueness half of the Newtonian representation `ext:newtonian` applies Liouville's
theorem to a function that is `L^{3/2}` on every round ball about the origin, with local
norm growing at most like `1 + R`.  This file produces that pair of statements for the
group `p₂ + p₃ + p₄ + p₅ + p₆` of the pressure decomposition
`prop:pressure-decomposition` of `paper/ckn.tex`, run with the mollified cut-off of
`B_ρ(x₀)` and the doubly centred tensor `eq:Uhat` of `prop:lin34`.

The velocity potentials `p₂, p₃, p₄` have sources that are products of a second- or
first-order derivative of the cut-off with the centred tensor, so they inherit the
`L^{3/2}` bound of `eq:Chat` from the cubic integrability of the mean-free velocity on
`B_ρ(x₀)`.  The pressure potentials `p₅, p₆` have sources that are products of a
derivative of the cut-off with the pressure slice, so they inherit the `L^{3/2}` bound
of the slice itself.  All five sources vanish off a closed ball about the origin, which
is what lets the single-potential engines of
`CKN.Foundation.Euclidean.PotentialLocalLpGrowth` be applied.
-/

/-- The Euclidean norm on `Vec3` is continuous. -/
private lemma lin34_continuous_vec3EuclideanNorm :
    Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
  unfold vec3EuclideanNorm
  fun_prop

/-- The explicit Euclidean ball `euclideanBall x₀ ρ` is Borel measurable, being the
sublevel set of the continuous function `euclideanSqDist · x₀`. -/
private lemma lin34_euclideanBall_measurable {x₀ : Vec3} (ρ : ℝ) :
    MeasurableSet (euclideanBall x₀ ρ) := by
  have hopen : IsOpen (euclideanBall x₀ ρ) := by
    change IsOpen {y : Vec3 | euclideanSqDist y x₀ < ρ ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  exact hopen.measurableSet

/-- The explicit Euclidean ball `euclideanBall x₀ ρ` of positive radius coincides with
the norm ball `vec3Ball x₀ ρ`. -/
private lemma lin34_euclideanBall_eq_vec3Ball {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

/-- The supremum norm on `Vec3` is dominated by the Euclidean norm. -/
private theorem lin34_norm_le_vec3EuclideanNorm (v : Vec3) :
    ‖v‖ ≤ vec3EuclideanNorm v := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg v)]
  intro i
  change |v i| ≤ vec3EuclideanNorm v
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _hj => sq_nonneg (v j))
    (Finset.mem_univ i)

/-- The Euclidean norm on `Vec3` is subadditive. -/
private theorem lin34_vec3EuclideanNorm_add_le (v w : Vec3) :
    vec3EuclideanNorm (v + w) ≤ vec3EuclideanNorm v + vec3EuclideanNorm w := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
    vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

/-- The mollified cut-off of `B_ρ(x₀)` is supported in the open Euclidean ball
`euclideanBall x₀ ρ`. -/
private lemma lin34_cutoff_tsupport_subset_ball (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (mollifiedBallCutoff x₀ hρ) ⊆ euclideanBall x₀ ρ := by
  have hsub : euclideanBall x₀ (3 * ρ / 4) ⊆ euclideanBall x₀ ρ := by
    intro w hw
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by positivity : (0 : ℝ) < 3 * ρ / 4)).1 hw).trans_le (by linarith only [hρ])
  exact (mollifiedBallCutoff_tsupport_subset_outer x₀ hρ).trans hsub

/-- The topological support of a first spatial derivative is contained in the
topological support of the function. -/
private lemma lin34_tsupport_spatialDeriv_subset {η : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hη : tsupport η ⊆ euclideanBall x₀ ρ) (i : Fin 3) :
    tsupport (spatialDeriv η i) ⊆ euclideanBall x₀ ρ :=
  (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hη

/-- The topological support of a mixed second derivative is contained in the
topological support of the function. -/
private lemma lin34_tsupport_mixedSecond_subset {η : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ}
    (hη : tsupport η ⊆ euclideanBall x₀ ρ) (i j : Fin 3) :
    tsupport (mixedSecond η i j) ⊆ euclideanBall x₀ ρ :=
  ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
    ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hη))

/-- Pointwise bound on the spatial Laplacian of the mollified cut-off, obtained by
summing the three diagonal mixed second derivative bounds. -/
private lemma lin34_spatialLaplacian_cutoff_bound (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec3) :
    |spatialLaplacian (mollifiedBallCutoff x₀ hρ) y| ≤
      3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
  have hsum := Finset.abs_sum_le_sum_abs
    (s := (Finset.univ : Finset (Fin 3)))
    (f := fun i : Fin 3 => mixedSecond (mollifiedBallCutoff x₀ hρ) i i y)
  have hbound : ∀ i : Fin 3,
      |mixedSecond (mollifiedBallCutoff x₀ hρ) i i y| ≤
        cutoffSecondDerivativeConstant / ρ ^ 2 :=
    fun i => pressure_cutoff_mixedSecond_bound x₀ hρ y i i
  calc
    |spatialLaplacian (mollifiedBallCutoff x₀ hρ) y| =
        |∑ i : Fin 3, mixedSecond (mollifiedBallCutoff x₀ hρ) i i y| := by
      rfl
    _ ≤ ∑ i : Fin 3, |mixedSecond (mollifiedBallCutoff x₀ hρ) i i y| := hsum
    _ ≤ ∑ _i : Fin 3, cutoffSecondDerivativeConstant / ρ ^ 2 :=
      Finset.sum_le_sum fun i _hi => hbound i
    _ = 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The square of the mean-free velocity is almost everywhere strongly measurable on
the ambient space after multiplication by the indicator of its ball.  This is the
measurability input of the `L^{3/2}` source bound `eq:Chat`, where the velocity enters
only through its slice on `B_ρ(x₀)`. -/
theorem lin34_meanFreeVec_square_indicator_aestronglyMeasurable
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    (hu : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ))) :
    AEStronglyMeasurable
      ((euclideanBall x₀ ρ).indicator
        (fun y => vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ))) volume := by
  have hball : euclideanBall x₀ ρ = vec3Ball x₀ ρ :=
    lin34_euclideanBall_eq_vec3Ball hρ
  have hmeas : MeasurableSet (euclideanBall x₀ ρ) := by
    rw [hball]
    exact (isOpen_vec3Ball x₀ ρ).measurableSet
  rw [aestronglyMeasurable_indicator_iff hmeas, hball]
  have hcv : AEStronglyMeasurable (fun y : Vec3 => meanFreeVec u x₀ ρ s y)
      (volume.restrict (vec3Ball x₀ ρ)) := by
    change AEStronglyMeasurable (fun y : Vec3 => lin34CentredVelocity u x₀ ρ (y, s))
      (volume.restrict (vec3Ball x₀ ρ))
    rw [lin34_centredVelocity_slice_eq]
    exact hu.sub aestronglyMeasurable_const
  have hnorm : AEStronglyMeasurable
      (fun y : Vec3 => vec3EuclideanNorm (meanFreeVec u x₀ ρ s y))
      (volume.restrict (vec3Ball x₀ ρ)) :=
    lin34_continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hcv
  change AEStronglyMeasurable
    ((fun y : Vec3 => vec3EuclideanNorm (meanFreeVec u x₀ ρ s y)) ^ (2 : ℕ))
    (volume.restrict (vec3Ball x₀ ρ))
  exact hnorm.pow 2

/-- A function vanishing off `B(x₀,ρ)` and bounded in absolute value by `M` times the
square of a velocity field there is of class `L^{3/2}`, whenever the velocity cube is
integrable on that ball.  The constant `M` is allowed to be any nonnegative real. -/
theorem lin34_memLp_three_halves_of_scaled_velocity_square_bound
    {g : Vec3 → ℝ} {v : Vec3 → Vec3} {x₀ : Vec3} {ρ M : ℝ} (hM : 0 ≤ M)
    (hg : AEStronglyMeasurable g volume)
    (hvmeas : AEStronglyMeasurable
      ((euclideanBall x₀ ρ).indicator
        (fun y => vec3EuclideanNorm (v y) ^ (2 : ℕ))) volume)
    (hv : IntegrableOn (fun y => vec3EuclideanNorm (v y) ^ (3 : ℕ))
      (euclideanBall x₀ ρ) volume)
    (hzero : ∀ y, y ∉ euclideanBall x₀ ρ → g y = 0)
    (hbound : ∀ y, |g y| ≤ M * vec3EuclideanNorm (v y) ^ (2 : ℕ)) :
    MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
  have h₀mem : MemLp
      ((euclideanBall x₀ ρ).indicator
        (fun y => vec3EuclideanNorm (v y) ^ (2 : ℕ)))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    refine memLp_three_halves_of_velocity_square_bound hvmeas hv ?_ ?_
    · intro y hy
      exact Set.indicator_of_notMem hy _
    · intro y
      by_cases hy : y ∈ euclideanBall x₀ ρ
      · rw [Set.indicator_of_mem hy]
        exact le_of_eq (abs_of_nonneg (by positivity))
      · rw [Set.indicator_of_notMem hy, abs_zero]
        exact pow_nonneg (vec3EuclideanNorm_nonneg _) 2
  have hMm : MemLp (fun y => M *
      (euclideanBall x₀ ρ).indicator
        (fun z => vec3EuclideanNorm (v z) ^ (2 : ℕ)) y)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := h₀mem.const_mul M
  refine MemLp.of_le hMm hg ?_
  filter_upwards with y
  by_cases hy : y ∈ euclideanBall x₀ ρ
  · have hval : (euclideanBall x₀ ρ).indicator
        (fun z => vec3EuclideanNorm (v z) ^ (2 : ℕ)) y =
        vec3EuclideanNorm (v y) ^ (2 : ℕ) := Set.indicator_of_mem hy _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hval,
      abs_of_nonneg (mul_nonneg hM (by positivity))]
    exact hbound y
  · rw [hzero y hy, Real.norm_eq_abs, abs_zero]
    exact norm_nonneg _

/-! ### Measurability of the factors of the five sources -/

/-- The mixed second derivative of the mollified cut-off is almost everywhere strongly
measurable on the ball. -/
private lemma lin34_mixedSecond_cutoff_aestronglyMeasurable (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (i j : Fin 3) :
    AEStronglyMeasurable (mixedSecond (mollifiedBallCutoff x₀ hρ) i j)
      (volume.restrict (vec3Ball x₀ ρ)) :=
  (contDiff_mixedSecond_smooth (mollifiedBallCutoff_smooth x₀ hρ) i
    j).continuous.aestronglyMeasurable.mono_measure
    Measure.restrict_le_self

/-- The first spatial derivative of the mollified cut-off is almost everywhere strongly
measurable on the ball. -/
private lemma lin34_spatialDeriv_cutoff_aestronglyMeasurable (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (i : Fin 3) :
    AEStronglyMeasurable (spatialDeriv (mollifiedBallCutoff x₀ hρ) i)
      (volume.restrict (vec3Ball x₀ ρ)) :=
  (contDiff_spatialDeriv_smooth (mollifiedBallCutoff_smooth x₀ hρ)
    i).continuous.aestronglyMeasurable.mono_measure
    Measure.restrict_le_self

/-- The spatial Laplacian of the mollified cut-off is almost everywhere strongly
measurable on the ball. -/
private lemma lin34_spatialLaplacian_cutoff_aestronglyMeasurable (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) :
    AEStronglyMeasurable (spatialLaplacian (mollifiedBallCutoff x₀ hρ))
      (volume.restrict (vec3Ball x₀ ρ)) :=
  (contDiff_spatialLaplacian_smooth (mollifiedBallCutoff_smooth x₀
    hρ)).continuous.aestronglyMeasurable.mono_measure
    Measure.restrict_le_self

/-- The entry of the centred tensor `eq:Uhat` is almost everywhere strongly measurable
on the ball, being a polynomial in the mean-free velocity slice. -/
private lemma lin34_centredUTensor_aestronglyMeasurable
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} {s : ℝ}
    (hu : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ))) (i j : Fin 3) :
    AEStronglyMeasurable
      (fun y : Vec3 => pressureUTensor (lin34CentredVelocity u x₀ ρ) 0
        ((y, s) : ParabolicPoint) i j) (volume.restrict (vec3Ball x₀ ρ)) := by
  have hcv : AEStronglyMeasurable (fun y : Vec3 => lin34CentredVelocity u x₀ ρ (y, s))
      (volume.restrict (vec3Ball x₀ ρ)) := by
    rw [lin34_centredVelocity_slice_eq]
    exact hu.sub aestronglyMeasurable_const
  have hcomp (k : Fin 3) : AEStronglyMeasurable
      (fun y : Vec3 => lin34CentredVelocity u x₀ ρ (y, s) k)
      (volume.restrict (vec3Ball x₀ ρ)) :=
    (continuous_apply k).comp_aestronglyMeasurable hcv
  simp only [pressureUTensor, Pi.zero_apply, sub_zero]
  exact (hcomp i).neg.mul (hcomp j)

/-- A product `F = A · B` that vanishes off `B(x₀,ρ)` is almost everywhere strongly
measurable on the whole space as soon as both factors are almost everywhere strongly
measurable on the ball. -/
private lemma lin34_product_aestronglyMeasurable_of_zero_off
    {F A B : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hA : AEStronglyMeasurable A (volume.restrict (vec3Ball x₀ ρ)))
    (hB : AEStronglyMeasurable B (volume.restrict (vec3Ball x₀ ρ)))
    (hzero : ∀ y, y ∉ euclideanBall x₀ ρ → F y = 0)
    (hprod : ∀ y, F y = A y * B y) :
    AEStronglyMeasurable F volume := by
  have hball : euclideanBall x₀ ρ = vec3Ball x₀ ρ := lin34_euclideanBall_eq_vec3Ball hρ
  have hzero' : ∀ y, y ∉ vec3Ball x₀ ρ → F y = 0 := fun y hy =>
    hzero y (by rwa [← hball] at hy)
  have hind : (vec3Ball x₀ ρ).indicator F = F := by
    apply Set.indicator_eq_self.2
    exact Function.support_subset_iff'.2 hzero'
  have hFeq : F = A * B := funext hprod
  have hrestrict : AEStronglyMeasurable F (volume.restrict (vec3Ball x₀ ρ)) := by
    rw [hFeq]
    exact hA.mul hB
  have h := (aestronglyMeasurable_indicator_iff
    (isOpen_vec3Ball x₀ ρ).measurableSet).2 hrestrict
  rwa [hind] at h

/-! ### The five sources of the centred potentials -/

/-- The source `g₂` of the centred potential `p₂`: the entry `i j` of the centred
tensor `eq:Uhat` multiplied by the mixed second derivative `∂_i ∂_j η` of the cut-off. -/
@[expose] def lin34CentredTensorHessian (u : ParabolicPoint → Vec3) (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (s : ℝ) (i j : Fin 3) : Vec3 → ℝ :=
  fun y => mixedSecond (mollifiedBallCutoff x₀ hρ) i j y *
    pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j

/-- The source of the centred potential `p₃`: the entry `i j` of the centred tensor
`eq:Uhat` multiplied by the first derivative `∂_i η` of the cut-off. -/
@[expose] def lin34CentredTensorGradientI (u : ParabolicPoint → Vec3) (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (s : ℝ) (i j : Fin 3) : Vec3 → ℝ :=
  fun y => pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j *
    spatialDeriv (mollifiedBallCutoff x₀ hρ) i y

/-- The source of the centred potential `p₄`: the entry `i j` of the centred tensor
`eq:Uhat` multiplied by the first derivative `∂_j η` of the cut-off. -/
@[expose] def lin34CentredTensorGradientJ (u : ParabolicPoint → Vec3) (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (s : ℝ) (i j : Fin 3) : Vec3 → ℝ :=
  fun y => pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j *
    spatialDeriv (mollifiedBallCutoff x₀ hρ) j y

/-- The source of the centred potential `p₅`: the pressure slice multiplied by the
spatial Laplacian `Δη` of the cut-off. -/
@[expose] def lin34CentredPressureLaplacian (p : ParabolicPoint → ℝ) (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (s : ℝ) : Vec3 → ℝ :=
  fun y => p (y, s) * spatialLaplacian (mollifiedBallCutoff x₀ hρ) y

/-- The source of the centred potential `p₆`: the first derivative `∂_j η` of the
cut-off multiplied by the pressure slice. -/
@[expose] def lin34CentredPressureGradient (p : ParabolicPoint → ℝ) (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (s : ℝ) (j : Fin 3) : Vec3 → ℝ :=
  fun y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * p (y, s)

/-! ### Step B: the five sources are `L^{3/2}` and vanish off a closed ball -/

/-- The source `g₂` lies in `L^{3/2}(ℝ³)` and vanishes off the closed ball of radius
`‖x₀‖ + ρ` about the origin. -/
theorem lin34CentredTensorHessian_memLp_and_zero
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    (hu : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hv : IntegrableOn (fun y => vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ))
      (euclideanBall x₀ ρ) volume)
    (i j : Fin 3) :
    MemLp (lin34CentredTensorHessian u x₀ hρ s i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      (∀ y : Vec3, y ∉ closedBall (0 : Vec3) (vec3EuclideanNorm x₀ + ρ) →
        lin34CentredTensorHessian u x₀ hρ s i j y = 0) := by
  let M : ℝ := max (cutoffSecondDerivativeConstant / ρ ^ 2) 0
  have hM : 0 ≤ M := le_max_right _ _
  have hzero : ∀ y, y ∉ euclideanBall x₀ ρ →
      lin34CentredTensorHessian u x₀ hρ s i j y = 0 := by
    intro y hy
    have hout : y ∉ tsupport (mixedSecond (mollifiedBallCutoff x₀ hρ) i j) := fun hmem =>
      hy (lin34_tsupport_mixedSecond_subset (lin34_cutoff_tsupport_subset_ball x₀ hρ) i j hmem)
    have hz : mixedSecond (mollifiedBallCutoff x₀ hρ) i j y = 0 :=
      image_eq_zero_of_notMem_tsupport hout
    change mixedSecond (mollifiedBallCutoff x₀ hρ) i j y *
      pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j = 0
    rw [hz, zero_mul]
  have hmeas : AEStronglyMeasurable (lin34CentredTensorHessian u x₀ hρ s i j) volume :=
    lin34_product_aestronglyMeasurable_of_zero_off hρ
      (lin34_mixedSecond_cutoff_aestronglyMeasurable x₀ hρ i j)
      (lin34_centredUTensor_aestronglyMeasurable hu i j) hzero (fun y => rfl)
  have hbound : ∀ y, |lin34CentredTensorHessian u x₀ hρ s i j y| ≤
      M * vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) := by
    intro y
    have hm : |mixedSecond (mollifiedBallCutoff x₀ hρ) i j y| ≤ M :=
      (pressure_cutoff_mixedSecond_bound x₀ hρ y i j).trans (le_max_left _ _)
    have hU : |pressureUTensor (lin34CentredVelocity u x₀ ρ) 0
        ((y, s) : ParabolicPoint) i j| ≤
        vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) :=
      (pressure_component_abs_le_utensorNorm (lin34CentredVelocity u x₀ ρ) 0 s y i j).trans_eq
        (lin34_pressureUTensorNorm_centred u x₀ ρ s y)
    change |mixedSecond (mollifiedBallCutoff x₀ hρ) i j y *
      pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j| ≤ _
    rw [abs_mul]
    exact mul_le_mul hm hU (abs_nonneg _) hM
  have hclosed : ∀ y : Vec3,
      y ∉ closedBall (0 : Vec3) (vec3EuclideanNorm x₀ + ρ) →
        lin34CentredTensorHessian u x₀ hρ s i j y = 0 := by
    intro y hy
    apply hzero y
    intro hball
    exact hy (vec3Ball_subset_closedBall_zero x₀ ρ
      (by rwa [lin34_euclideanBall_eq_vec3Ball hρ] at hball))
  exact ⟨lin34_memLp_three_halves_of_scaled_velocity_square_bound hM hmeas
      (lin34_meanFreeVec_square_indicator_aestronglyMeasurable hρ hu) hv hzero hbound,
    hclosed⟩

/-- The source of `p₃` lies in `L^{3/2}(ℝ³)` and vanishes off the closed ball of
radius `‖x₀‖ + ρ` about the origin. -/
theorem lin34CentredTensorGradientI_memLp_and_zero
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    (hu : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hv : IntegrableOn (fun y => vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ))
      (euclideanBall x₀ ρ) volume)
    (i j : Fin 3) :
    MemLp (lin34CentredTensorGradientI u x₀ hρ s i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      (∀ y : Vec3, y ∉ closedBall (0 : Vec3) (vec3EuclideanNorm x₀ + ρ) →
        lin34CentredTensorGradientI u x₀ hρ s i j y = 0) := by
  let M : ℝ := max (cutoffGradientConstant / ρ) 0
  have hM : 0 ≤ M := le_max_right _ _
  have hzero : ∀ y, y ∉ euclideanBall x₀ ρ →
      lin34CentredTensorGradientI u x₀ hρ s i j y = 0 := by
    intro y hy
    have hout : y ∉ tsupport (spatialDeriv (mollifiedBallCutoff x₀ hρ) i) := fun hmem =>
      hy (lin34_tsupport_spatialDeriv_subset (lin34_cutoff_tsupport_subset_ball x₀ hρ) i hmem)
    have hz : spatialDeriv (mollifiedBallCutoff x₀ hρ) i y = 0 :=
      image_eq_zero_of_notMem_tsupport hout
    change pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j *
      spatialDeriv (mollifiedBallCutoff x₀ hρ) i y = 0
    rw [hz, mul_zero]
  have hmeas : AEStronglyMeasurable (lin34CentredTensorGradientI u x₀ hρ s i j) volume :=
    lin34_product_aestronglyMeasurable_of_zero_off hρ
      (lin34_centredUTensor_aestronglyMeasurable hu i j)
      (lin34_spatialDeriv_cutoff_aestronglyMeasurable x₀ hρ i) hzero (fun y => rfl)
  have hbound : ∀ y, |lin34CentredTensorGradientI u x₀ hρ s i j y| ≤
      M * vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) := by
    intro y
    have hd : |spatialDeriv (mollifiedBallCutoff x₀ hρ) i y| ≤ M :=
      (pressure_cutoff_spatialDeriv_bound x₀ hρ y i).trans (le_max_left _ _)
    have hU : |pressureUTensor (lin34CentredVelocity u x₀ ρ) 0
        ((y, s) : ParabolicPoint) i j| ≤
        vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) :=
      (pressure_component_abs_le_utensorNorm (lin34CentredVelocity u x₀ ρ) 0 s y i j).trans_eq
        (lin34_pressureUTensorNorm_centred u x₀ ρ s y)
    change |pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j *
      spatialDeriv (mollifiedBallCutoff x₀ hρ) i y| ≤ _
    rw [abs_mul]
    calc
      |pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j| *
          |spatialDeriv (mollifiedBallCutoff x₀ hρ) i y| ≤
          vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) * M :=
        mul_le_mul hU hd (abs_nonneg _) (by positivity)
      _ = M * vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) := by ring
  have hclosed : ∀ y : Vec3,
      y ∉ closedBall (0 : Vec3) (vec3EuclideanNorm x₀ + ρ) →
        lin34CentredTensorGradientI u x₀ hρ s i j y = 0 := by
    intro y hy
    apply hzero y
    intro hball
    exact hy (vec3Ball_subset_closedBall_zero x₀ ρ
      (by rwa [lin34_euclideanBall_eq_vec3Ball hρ] at hball))
  exact ⟨lin34_memLp_three_halves_of_scaled_velocity_square_bound hM hmeas
      (lin34_meanFreeVec_square_indicator_aestronglyMeasurable hρ hu) hv hzero hbound,
    hclosed⟩

/-- The source of `p₄` lies in `L^{3/2}(ℝ³)` and vanishes off the closed ball of
radius `‖x₀‖ + ρ` about the origin. -/
theorem lin34CentredTensorGradientJ_memLp_and_zero
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    (hu : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hv : IntegrableOn (fun y => vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ))
      (euclideanBall x₀ ρ) volume)
    (i j : Fin 3) :
    MemLp (lin34CentredTensorGradientJ u x₀ hρ s i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      (∀ y : Vec3, y ∉ closedBall (0 : Vec3) (vec3EuclideanNorm x₀ + ρ) →
        lin34CentredTensorGradientJ u x₀ hρ s i j y = 0) := by
  let M : ℝ := max (cutoffGradientConstant / ρ) 0
  have hM : 0 ≤ M := le_max_right _ _
  have hzero : ∀ y, y ∉ euclideanBall x₀ ρ →
      lin34CentredTensorGradientJ u x₀ hρ s i j y = 0 := by
    intro y hy
    have hout : y ∉ tsupport (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) := fun hmem =>
      hy (lin34_tsupport_spatialDeriv_subset (lin34_cutoff_tsupport_subset_ball x₀ hρ) j hmem)
    have hz : spatialDeriv (mollifiedBallCutoff x₀ hρ) j y = 0 :=
      image_eq_zero_of_notMem_tsupport hout
    change pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j *
      spatialDeriv (mollifiedBallCutoff x₀ hρ) j y = 0
    rw [hz, mul_zero]
  have hmeas : AEStronglyMeasurable (lin34CentredTensorGradientJ u x₀ hρ s i j) volume :=
    lin34_product_aestronglyMeasurable_of_zero_off hρ
      (lin34_centredUTensor_aestronglyMeasurable hu i j)
      (lin34_spatialDeriv_cutoff_aestronglyMeasurable x₀ hρ j) hzero (fun y => rfl)
  have hbound : ∀ y, |lin34CentredTensorGradientJ u x₀ hρ s i j y| ≤
      M * vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) := by
    intro y
    have hd : |spatialDeriv (mollifiedBallCutoff x₀ hρ) j y| ≤ M :=
      (pressure_cutoff_spatialDeriv_bound x₀ hρ y j).trans (le_max_left _ _)
    have hU : |pressureUTensor (lin34CentredVelocity u x₀ ρ) 0
        ((y, s) : ParabolicPoint) i j| ≤
        vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) :=
      (pressure_component_abs_le_utensorNorm (lin34CentredVelocity u x₀ ρ) 0 s y i j).trans_eq
        (lin34_pressureUTensorNorm_centred u x₀ ρ s y)
    change |pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j *
      spatialDeriv (mollifiedBallCutoff x₀ hρ) j y| ≤ _
    rw [abs_mul]
    calc
      |pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j| *
          |spatialDeriv (mollifiedBallCutoff x₀ hρ) j y| ≤
          vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) * M :=
        mul_le_mul hU hd (abs_nonneg _) (by positivity)
      _ = M * vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) := by ring
  have hclosed : ∀ y : Vec3,
      y ∉ closedBall (0 : Vec3) (vec3EuclideanNorm x₀ + ρ) →
        lin34CentredTensorGradientJ u x₀ hρ s i j y = 0 := by
    intro y hy
    apply hzero y
    intro hball
    exact hy (vec3Ball_subset_closedBall_zero x₀ ρ
      (by rwa [lin34_euclideanBall_eq_vec3Ball hρ] at hball))
  exact ⟨lin34_memLp_three_halves_of_scaled_velocity_square_bound hM hmeas
      (lin34_meanFreeVec_square_indicator_aestronglyMeasurable hρ hu) hv hzero hbound,
    hclosed⟩

/-- The source of `p₅` lies in `L^{3/2}(ℝ³)` and vanishes off the closed ball of
radius `‖x₀‖ + ρ` about the origin. -/
theorem lin34CentredPressureLaplacian_memLp_and_zero
    {p : ParabolicPoint → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    (hp : MemLp (fun y : Vec3 => p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ ρ))) :
    MemLp (lin34CentredPressureLaplacian p x₀ hρ s) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      (∀ y : Vec3, y ∉ closedBall (0 : Vec3) (vec3EuclideanNorm x₀ + ρ) →
        lin34CentredPressureLaplacian p x₀ hρ s y = 0) := by
  let c : ℝ := max (3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) 0
  have hc : 0 ≤ c := le_max_right _ _
  have hzero : ∀ y, y ∉ euclideanBall x₀ ρ →
      lin34CentredPressureLaplacian p x₀ hρ s y = 0 := by
    intro y hy
    have hz : spatialLaplacian (mollifiedBallCutoff x₀ hρ) y = 0 := by
      have hmix : ∀ i : Fin 3, mixedSecond (mollifiedBallCutoff x₀ hρ) i i y = 0 := fun i =>
        image_eq_zero_of_notMem_tsupport (fun hmem =>
          hy (lin34_tsupport_mixedSecond_subset (lin34_cutoff_tsupport_subset_ball x₀ hρ)
            i i hmem))
      change (∑ i : Fin 3, mixedSecond (mollifiedBallCutoff x₀ hρ) i i y) = 0
      simp [hmix]
    change p (y, s) * spatialLaplacian (mollifiedBallCutoff x₀ hρ) y = 0
    rw [hz, mul_zero]
  have hmeas : AEStronglyMeasurable (lin34CentredPressureLaplacian p x₀ hρ s) volume :=
    lin34_product_aestronglyMeasurable_of_zero_off hρ
      (hp.aestronglyMeasurable)
      (lin34_spatialLaplacian_cutoff_aestronglyMeasurable x₀ hρ) hzero (fun y => rfl)
  have hle : ∀ y, ‖lin34CentredPressureLaplacian p x₀ hρ s y‖ ≤ ‖c * p (y, s)‖ := by
    intro y
    have hlap : |spatialLaplacian (mollifiedBallCutoff x₀ hρ) y| ≤ c :=
      (lin34_spatialLaplacian_cutoff_bound x₀ hρ y).trans (le_max_left _ _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc]
    change |p (y, s) * spatialLaplacian (mollifiedBallCutoff x₀ hρ) y| ≤ c * |p (y, s)|
    rw [abs_mul]
    calc
      |p (y, s)| * |spatialLaplacian (mollifiedBallCutoff x₀ hρ) y| ≤ |p (y, s)| * c :=
        mul_le_mul_of_nonneg_left hlap (abs_nonneg _)
      _ = c * |p (y, s)| := by ring
  have hsupp : Function.support (lin34CentredPressureLaplacian p x₀ hρ s) ⊆ vec3Ball x₀ ρ := by
    intro y hy
    by_contra hyB
    exact hy (hzero y (by rwa [lin34_euclideanBall_eq_vec3Ball hρ]))
  have hh : MemLp (lin34CentredPressureLaplacian p x₀ hρ s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball x₀ ρ)) :=
    MemLp.of_le (hp.const_mul c)
      (hmeas.mono_measure Measure.restrict_le_self)
      (Filter.Eventually.of_forall hle)
  have hclosed : ∀ y : Vec3,
      y ∉ closedBall (0 : Vec3) (vec3EuclideanNorm x₀ + ρ) →
        lin34CentredPressureLaplacian p x₀ hρ s y = 0 := by
    intro y hy
    apply hzero y
    intro hball
    exact hy (vec3Ball_subset_closedBall_zero x₀ ρ
      (by rwa [lin34_euclideanBall_eq_vec3Ball hρ] at hball))
  exact ⟨memLp_volume_of_memLp_restrict_of_support hmeas hsupp hh, hclosed⟩

/-- The source of `p₆` lies in `L^{3/2}(ℝ³)` and vanishes off the closed ball of
radius `‖x₀‖ + ρ` about the origin. -/
theorem lin34CentredPressureGradient_memLp_and_zero
    {p : ParabolicPoint → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    (hp : MemLp (fun y : Vec3 => p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ ρ))) (j : Fin 3) :
    MemLp (lin34CentredPressureGradient p x₀ hρ s j) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      (∀ y : Vec3, y ∉ closedBall (0 : Vec3) (vec3EuclideanNorm x₀ + ρ) →
        lin34CentredPressureGradient p x₀ hρ s j y = 0) := by
  let c : ℝ := max (cutoffGradientConstant / ρ) 0
  have hc : 0 ≤ c := le_max_right _ _
  have hzero : ∀ y, y ∉ euclideanBall x₀ ρ →
      lin34CentredPressureGradient p x₀ hρ s j y = 0 := by
    intro y hy
    have hout : y ∉ tsupport (spatialDeriv (mollifiedBallCutoff x₀ hρ) j) := fun hmem =>
      hy (lin34_tsupport_spatialDeriv_subset (lin34_cutoff_tsupport_subset_ball x₀ hρ) j hmem)
    have hz : spatialDeriv (mollifiedBallCutoff x₀ hρ) j y = 0 :=
      image_eq_zero_of_notMem_tsupport hout
    change spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * p (y, s) = 0
    rw [hz, zero_mul]
  have hmeas : AEStronglyMeasurable (lin34CentredPressureGradient p x₀ hρ s j) volume :=
    lin34_product_aestronglyMeasurable_of_zero_off hρ
      (lin34_spatialDeriv_cutoff_aestronglyMeasurable x₀ hρ j)
      (hp.aestronglyMeasurable) hzero (fun y => rfl)
  have hle : ∀ y, ‖lin34CentredPressureGradient p x₀ hρ s j y‖ ≤ ‖c * p (y, s)‖ := by
    intro y
    have hd : |spatialDeriv (mollifiedBallCutoff x₀ hρ) j y| ≤ c :=
      (pressure_cutoff_spatialDeriv_bound x₀ hρ y j).trans (le_max_left _ _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc]
    change |spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * p (y, s)| ≤ c * |p (y, s)|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
  have hsupp : Function.support (lin34CentredPressureGradient p x₀ hρ s j) ⊆ vec3Ball x₀ ρ := by
    intro y hy
    by_contra hyB
    exact hy (hzero y (by rwa [lin34_euclideanBall_eq_vec3Ball hρ]))
  have hh : MemLp (lin34CentredPressureGradient p x₀ hρ s j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball x₀ ρ)) :=
    MemLp.of_le (hp.const_mul c)
      (hmeas.mono_measure Measure.restrict_le_self)
      (Filter.Eventually.of_forall hle)
  have hclosed : ∀ y : Vec3,
      y ∉ closedBall (0 : Vec3) (vec3EuclideanNorm x₀ + ρ) →
        lin34CentredPressureGradient p x₀ hρ s j y = 0 := by
    intro y hy
    apply hzero y
    intro hball
    exact hy (vec3Ball_subset_closedBall_zero x₀ ρ
      (by rwa [lin34_euclideanBall_eq_vec3Ball hρ] at hball))
  exact ⟨memLp_volume_of_memLp_restrict_of_support hmeas hsupp hh, hclosed⟩

end CKN
