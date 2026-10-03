/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialC2

/-!
# Semigroup factorization for the Euclidean heat Hessian

A positive-time heat smoothing of bounded Holder data is itself bounded C2
data.  Combining this fact with uniqueness of the genuine Frechet derivatives
and the Chapman--Kolmogorov law factors a later heat Hessian through any
strictly positive intermediate heat time.  This is the old-time input in the
Duhamel Hessian Holder estimate.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- A coordinate of the heat gradient as a bounded continuous function. -/
def heatSemigroupGradientCoordNDbcf
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (k : Fin n) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (heatSemigroupGradientCoordND t f k)
    (continuous_iff_continuousAt.mpr fun x ↦
      (hasFDerivAt_heatSemigroupGradientCoordND ht f k x).continuousAt)
    (‖f‖ / Real.sqrt (π * t))
    (fun x ↦ by
      rw [Real.norm_eq_abs]
      exact heatSemigroupND_coord_deriv_integral_bound ht x k
        f.continuous.aestronglyMeasurable (fun y ↦ f.norm_coe_le_norm y))

@[simp] theorem heatSemigroupGradientCoordNDbcf_apply
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (k : Fin n)
    (x : Fin n → ℝ) :
    heatSemigroupGradientCoordNDbcf ht f k x =
      heatSemigroupGradientCoordND t f k x := rfl

/-- One entry of the heat Hessian, bundled as a bounded continuous function.
The bound uses cancellation against the supplied spatial Holder modulus. -/
def heatHessianEntryConvolutionNDbcf_of_coordHolder
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) : BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (heatHessianEntryConvolutionND t f j k)
    (continuous_heatHessianEntryConvolutionND (C := ‖f‖) ht f.continuous
      (fun y ↦ by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm y) j k)
    (H * t ^ (-1 + r / 2) * heatHessianEntryHolderMoment n r j k)
    (fun x ↦ by
      rw [Real.norm_eq_abs]
      exact abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
        ht hr hH x j k f.continuous.aestronglyMeasurable
        (fun y ↦ f.norm_coe_le_norm y) (hholder x))

@[simp] theorem heatHessianEntryConvolutionNDbcf_of_coordHolder_apply
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    heatHessianEntryConvolutionNDbcf_of_coordHolder
      ht hr f hH hholder j k x = heatHessianEntryConvolutionND t f j k x := rfl

/-- The cancellation estimate used to construct the bundled Hessian entry is
also a bound for its `C_b` norm. -/
theorem norm_heatHessianEntryConvolutionNDbcf_of_coordHolder_le
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) :
    ‖heatHessianEntryConvolutionNDbcf_of_coordHolder
        ht hr f hH hholder j k‖ ≤
      H * t ^ (-1 + r / 2) * heatHessianEntryHolderMoment n r j k := by
  unfold heatHessianEntryConvolutionNDbcf_of_coordHolder
  apply BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
  exact mul_nonneg (mul_nonneg hH (Real.rpow_nonneg ht.le _))
    (heatHessianEntryHolderMoment_nonneg n r j k)

/-- Positive-time smoothing turns bounded Holder data into bounded C2 data,
with the kernel gradient and full kernel Hessian as its actual derivatives. -/
def heatSmoothedC2Data
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    EuclideanBoundedC2Data n where
  value := heatSemigroupNDbcf ht f
  first := fun k ↦ heatSemigroupGradientCoordNDbcf ht f k
  second := fun j k ↦
    heatHessianEntryConvolutionNDbcf_of_coordHolder ht hr f hH hholder j k
  hasDeriv_value := by
    intro k x
    simpa only [heatSemigroupNDbcf_apply,
      heatSemigroupGradientCoordNDbcf_apply,
      heatSemigroupGradientCoordND] using
      hasDerivAt_heatSemigroupND_coord ht x k
        f.continuous.aestronglyMeasurable (fun y ↦ f.norm_coe_le_norm y)
  hasDeriv_first := by
    intro j k x
    simpa only [heatSemigroupGradientCoordNDbcf_apply,
      heatHessianEntryConvolutionNDbcf_of_coordHolder_apply,
      heatSemigroupGradientCoordND, heatHessianEntryConvolutionND] using
      hasDerivAt_heatSemigroupND_coordGradient_entry ht x j k
        f.continuous.aestronglyMeasurable (fun y ↦ f.norm_coe_le_norm y)

@[simp] theorem heatSmoothedC2Data_value_apply
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    (heatSmoothedC2Data ht hr f hH hholder).value x =
      heatSemigroupND t f x := rfl

@[simp] theorem heatSmoothedC2Data_second_apply
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    (heatSmoothedC2Data ht hr f hH hholder).second j k x =
      heatHessianEntryConvolutionND t f j k x := rfl

/-- Evaluating a coordinate Hessian form on two standard basis vectors
recovers the corresponding matrix entry. -/
@[simp] lemma coordinateHessianCLM_single_single {n : ℕ}
    (A : Fin n → Fin n → ℝ) (j k : Fin n) :
    coordinateHessianCLM A (Pi.single j 1) (Pi.single k 1) = A j k := by
  classical
  simp only [coordinateHessianCLM_apply, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
  · intro a _ ha
    simp [ha]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- The full heat Hessian at time `a+b` factors through heat evolution for
time `a` of the bounded Hessian already produced at time `b`. -/
theorem heatHessianEntryConvolutionND_add_eq_heatSemigroupND
    {n : ℕ} {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 ≤ r)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    heatHessianEntryConvolutionND (a + b) f j k x =
      heatSemigroupND a
        (heatHessianEntryConvolutionNDbcf_of_coordHolder
          hb hr f hH hholder j k) x := by
  let D := heatSmoothedC2Data hb hr f hH hholder
  have hsem : heatSemigroupND a D.value =
      heatSemigroupND (a + b) f := by
    funext z
    exact heatSemigroupND_comp a b ha hb z f.continuous.aestronglyMeasurable
      (fun y ↦ f.norm_coe_le_norm y)
  have hgrad : heatSemigroupGradientCLM a D.value =
      heatSemigroupGradientCLM (a + b) f := by
    funext z
    have hleft := hasFDerivAt_heatSemigroupND ha D.value z
    have hright := hasFDerivAt_heatSemigroupND (add_pos ha hb) f z
    rw [hsem] at hleft
    exact hleft.unique hright
  have hleft := hasFDerivAt_heatSemigroupGradientCLM ha D.value x
  have hright := hasFDerivAt_heatSemigroupGradientCLM (add_pos ha hb) f x
  rw [← hgrad] at hright
  have hhess := hleft.unique hright
  have hentry := congrArg
    (fun A ↦ A (Pi.single j 1) (Pi.single k 1)) hhess
  simp only [heatSemigroupHessianCLM, coordinateHessianCLM_single_single] at hentry
  have hd := D.heatHessianEntryConvolutionND_eq ha j k x
  change heatHessianEntryConvolutionND (a + b) f j k x =
    heatSemigroupND a (D.second j k) x
  exact hentry.symm.trans hd

/-- Near the Duhamel endpoint, the difference of two heat-Hessian values is
controlled by twice the cancellation bound. -/
theorem abs_heatHessianEntryConvolutionND_sub_le_recent
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x y : Fin n → ℝ) :
    |heatHessianEntryConvolutionND t f j k x -
        heatHessianEntryConvolutionND t f j k y| ≤
      2 * (H * t ^ (-1 + r / 2) *
        heatHessianEntryHolderMoment n r j k) := by
  have hx := abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
    ht hr hH x j k f.continuous.aestronglyMeasurable
    (fun z ↦ f.norm_coe_le_norm z) (hholder x)
  have hy := abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
    ht hr hH y j k f.continuous.aestronglyMeasurable
    (fun z ↦ f.norm_coe_le_norm z) (hholder y)
  calc
    |heatHessianEntryConvolutionND t f j k x -
        heatHessianEntryConvolutionND t f j k y| ≤
        |heatHessianEntryConvolutionND t f j k x| +
          |heatHessianEntryConvolutionND t f j k y| := abs_sub _ _
    _ ≤ (H * t ^ (-1 + r / 2) * heatHessianEntryHolderMoment n r j k) +
        (H * t ^ (-1 + r / 2) * heatHessianEntryHolderMoment n r j k) :=
      add_le_add hx hy
    _ = 2 * (H * t ^ (-1 + r / 2) *
        heatHessianEntryHolderMoment n r j k) := by ring

/-- Away from the Duhamel endpoint, semigroup factorization gains one more
spatial derivative.  The resulting Lipschitz bound has the required
`t^(-3/2+r/2)` scaling before elementary simplification of the half-time
factors. -/
theorem abs_heatHessianEntryConvolutionND_sub_le_old
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x y : Fin n → ℝ) :
    |heatHessianEntryConvolutionND t f j k x -
        heatHessianEntryConvolutionND t f j k y| ≤
      (n : ℝ) *
        ((H * (t / 2) ^ (-1 + r / 2) *
          heatHessianEntryHolderMoment n r j k) /
            Real.sqrt (π * (t / 2))) * ‖x - y‖ := by
  have hhalf : 0 < t / 2 := by positivity
  let w := heatHessianEntryConvolutionNDbcf_of_coordHolder
    hhalf hr f hH hholder j k
  have hw : ∀ z, ‖w z‖ ≤
      H * (t / 2) ^ (-1 + r / 2) *
        heatHessianEntryHolderMoment n r j k := by
    intro z
    exact (w.norm_coe_le_norm z).trans
      (norm_heatHessianEntryConvolutionNDbcf_of_coordHolder_le
        hhalf hr f hH hholder j k)
  have hlip := heatSemigroupND_spatial_lipschitz_sqrt_rate_norm
    hhalf w.continuous.aestronglyMeasurable hw x y
  have hfactor (z : Fin n → ℝ) :
      heatHessianEntryConvolutionND t f j k z =
        heatSemigroupND (t / 2) w z := by
    have h := heatHessianEntryConvolutionND_add_eq_heatSemigroupND
      hhalf hhalf hr f hH hholder j k z
    have htime : t / 2 + t / 2 = t := by ring
    simpa only [htime] using h
  rw [hfactor x, hfactor y]
  exact hlip

section OperatorBounds

local instance heatHessianSemigroupCoordinateDualNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance heatHessianSemigroupCoordinateBilinearNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Full operator-norm version of the recent-time Hessian difference bound. -/
theorem norm_heatSemigroupHessianCLM_sub_le_recent
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x y : Fin n → ℝ) :
    ‖heatSemigroupHessianCLM t f x - heatSemigroupHessianCLM t f y‖ ≤
      ∑ j : Fin n, ∑ k : Fin n,
        2 * (H * t ^ (-1 + r / 2) *
          heatHessianEntryHolderMoment n r j k) := by
  have heq : heatSemigroupHessianCLM t f x -
      heatSemigroupHessianCLM t f y =
      coordinateHessianCLM (fun j k ↦
        heatHessianEntryConvolutionND t f j k x -
          heatHessianEntryConvolutionND t f j k y) := by
    ext v w
    simp only [heatSemigroupHessianCLM_apply, coordinateHessianCLM_apply,
      sub_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heq]
  refine (norm_coordinateHessianCLM_le _).trans ?_
  gcongr with j k
  exact abs_heatHessianEntryConvolutionND_sub_le_recent
    ht hr f hH hholder j k x y

/-- Full operator-norm version of the factorized old-time Hessian difference
bound. -/
theorem norm_heatSemigroupHessianCLM_sub_le_old
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x y : Fin n → ℝ) :
    ‖heatSemigroupHessianCLM t f x - heatSemigroupHessianCLM t f y‖ ≤
      ∑ j : Fin n, ∑ k : Fin n,
        (n : ℝ) *
          ((H * (t / 2) ^ (-1 + r / 2) *
            heatHessianEntryHolderMoment n r j k) /
              Real.sqrt (π * (t / 2))) * ‖x - y‖ := by
  have heq : heatSemigroupHessianCLM t f x -
      heatSemigroupHessianCLM t f y =
      coordinateHessianCLM (fun j k ↦
        heatHessianEntryConvolutionND t f j k x -
          heatHessianEntryConvolutionND t f j k y) := by
    ext v w
    simp only [heatSemigroupHessianCLM_apply, coordinateHessianCLM_apply,
      sub_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heq]
  refine (norm_coordinateHessianCLM_le _).trans ?_
  gcongr with j k
  exact abs_heatHessianEntryConvolutionND_sub_le_old
    ht hr f hH hholder j k x y

end OperatorBounds

end AnalyticPDE
end RicciFlow
