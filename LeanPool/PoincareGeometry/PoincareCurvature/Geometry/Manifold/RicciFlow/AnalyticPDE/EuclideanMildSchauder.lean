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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatSecondJet
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialC2
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatParabolicHolder
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelHessianHolder

/-!
# Quantitative Hessian control for the Euclidean mild heat solution

This file proves the full mixed-Hessian operator-norm component of the
Euclidean Schauder estimate.  The homogeneous term uses heat-kernel
cancellation against the spatial Holder modulus of the initial datum; the
inhomogeneous term uses the time-integrated Duhamel Hessian estimate.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

section HessianNorms

local instance mildSchauderCoordinateDualNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance mildSchauderCoordinateBilinearNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance mildSchauderCoordinateBilinearContinuousAdd {n : ℕ} :
    ContinuousAdd ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  IsTopologicalAddGroup.toContinuousAdd

/-- The trace over the standard coordinate directions is bounded by the
dimension times the operator norm of a curried bilinear form. -/
lemma abs_sum_standardBasis_diag_le {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :
    |∑ k : Fin n, A (Pi.single k 1) (Pi.single k 1)| ≤ (n : ℝ) * ‖A‖ := by
  rw [← Real.norm_eq_abs]
  calc
    ‖∑ k : Fin n, A (Pi.single k 1) (Pi.single k 1)‖ ≤
        ∑ k : Fin n, ‖A (Pi.single k 1) (Pi.single k 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, ‖A‖ := by
      gcongr with k
      have he : ‖(Pi.single k (1 : ℝ) : Fin n → ℝ)‖ ≤ 1 := by
        apply (pi_norm_le_iff_of_nonneg zero_le_one).2
        intro ell
        by_cases h : ell = k
        · subst ell
          simp
        · simp [h]
      calc
        ‖A (Pi.single k 1) (Pi.single k 1)‖ ≤
            ‖A (Pi.single k 1)‖ * ‖(Pi.single k (1 : ℝ) : Fin n → ℝ)‖ :=
          (A (Pi.single k 1)).le_opNorm _
        _ ≤ (‖A‖ * ‖(Pi.single k (1 : ℝ) : Fin n → ℝ)‖) *
            ‖(Pi.single k (1 : ℝ) : Fin n → ℝ)‖ := by
          gcongr
          exact A.le_opNorm _
        _ ≤ ‖A‖ * 1 * 1 := by gcongr
        _ = ‖A‖ := by ring
    _ = (n : ℝ) * ‖A‖ := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Full operator-norm form of the homogeneous spatial Hessian Schauder
estimate.  Every mixed Hessian entry is controlled, then the finite entries
are summed to bound the curried bilinear operator norm. -/
theorem norm_heatSemigroupHessianCLM_le_of_coordHolder
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hu₀holder : ∀ x y, |u₀ y - u₀ x| ≤
      H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    ‖heatSemigroupHessianCLM t u₀ x‖ ≤
      ∑ j : Fin n, ∑ k : Fin n,
        H₀ * t ^ (-1 + r / 2) * heatHessianEntryHolderMoment n r j k := by
  unfold heatSemigroupHessianCLM
  refine (norm_coordinateHessianCLM_le _).trans ?_
  gcongr with j k
  exact abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
    ht hr0.le hH₀ x j k u₀.continuous.aestronglyMeasurable
      (fun y ↦ u₀.norm_coe_le_norm y) (hu₀holder x)

/-- The explicit bound stored by a bundled Duhamel Hessian entry is also a
bound for its `C_b` norm. -/
theorem norm_heatDuhamelHessianEntryNDbcf_le
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) :
    ‖heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k‖ ≤
      H * heatHessianEntryHolderMoment n r j k *
        ((t - t₀) ^ (r / 2) / (r / 2)) := by
  unfold heatDuhamelHessianEntryNDbcf
  apply BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
  exact mul_nonneg
    (mul_nonneg hH (heatHessianEntryHolderMoment_nonneg n r j k))
    (div_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hT) _)
      (by positivity))

/-- **Full mixed-Hessian Schauder bound for the actual mild solution.**
At every positive time the genuine Frechet Hessian of
`H_(t-t₀) u₀ + ∫ H_(t-s) q(s) ds` is bounded by the sum of the
homogeneous cancellation constant and the time-integrated Duhamel constants.
This controls the complete bilinear Hessian, not only its diagonal trace. -/
theorem norm_heatMildSpatialHessianCLM_le
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hu₀holder : ∀ x y, |u₀ y - u₀ x| ≤
      H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    ‖heatMildSpatialHessianCLM ht.le hr0 u₀ hq hH hqb hqholder x‖ ≤
      (∑ j : Fin n, ∑ k : Fin n,
        H₀ * (t - t₀) ^ (-1 + r / 2) *
          heatHessianEntryHolderMoment n r j k) +
      ∑ j : Fin n, ∑ k : Fin n,
        ‖heatDuhamelHessianEntryNDbcf ht.le hr0 hq hH hqb hqholder j k‖ := by
  unfold heatMildSpatialHessianCLM
  calc
    ‖heatSemigroupHessianCLM (t - t₀) u₀ x +
        heatDuhamelHessianCLM ht.le hr0 hq hH hqb hqholder x‖ ≤
        ‖heatSemigroupHessianCLM (t - t₀) u₀ x‖ +
          ‖heatDuhamelHessianCLM ht.le hr0 hq hH hqb hqholder x‖ :=
      norm_add_le _ _
    _ ≤ (∑ j : Fin n, ∑ k : Fin n,
          H₀ * (t - t₀) ^ (-1 + r / 2) *
            heatHessianEntryHolderMoment n r j k) +
        ∑ j : Fin n, ∑ k : Fin n,
          ‖heatDuhamelHessianEntryNDbcf ht.le hr0 hq hH hqb hqholder j k‖ :=
      add_le_add
        (norm_heatSemigroupHessianCLM_le_of_coordHolder
          (sub_pos.mpr ht) hr0 u₀ hH₀ hu₀holder x)
        (norm_heatDuhamelHessianCLM_le ht.le hr0 hq hH hqb hqholder x)

/-- Explicit-constant form of `norm_heatMildSpatialHessianCLM_le`.
The source contribution is the finite sum of the time-integrated Holder
moments `H (t-t₀)^(r/2)/(r/2)`. -/
theorem norm_heatMildSpatialHessianCLM_le_explicit
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hu₀holder : ∀ x y, |u₀ y - u₀ x| ≤
      H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    ‖heatMildSpatialHessianCLM ht.le hr0 u₀ hq hH hqb hqholder x‖ ≤
      (∑ j : Fin n, ∑ k : Fin n,
        H₀ * (t - t₀) ^ (-1 + r / 2) *
          heatHessianEntryHolderMoment n r j k) +
      ∑ j : Fin n, ∑ k : Fin n,
        H * heatHessianEntryHolderMoment n r j k *
          ((t - t₀) ^ (r / 2) / (r / 2)) := by
  refine (norm_heatMildSpatialHessianCLM_le ht hr0 u₀ hH₀ hu₀holder
    hq hH hqb hqholder x).trans ?_
  gcongr with j k
  exact norm_heatDuhamelHessianEntryNDbcf_le ht.le hr0 hq hH hqb hqholder j k

/-- **Uniform homogeneous endpoint of the full Hessian estimate.**  With
bounded actual C2 initial data, the homogeneous contribution is controlled by
the initial Hessian itself instead of the singular positive-time smoothing
factor. -/
theorem norm_heatMildSpatialHessianCLM_le_of_boundedC2
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (D : EuclideanBoundedC2Data n)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    ‖heatMildSpatialHessianCLM ht.le hr0 D.value hq hH hqb hqholder x‖ ≤
      (∑ j : Fin n, ∑ k : Fin n, ‖D.second j k‖) +
      ∑ j : Fin n, ∑ k : Fin n,
        H * heatHessianEntryHolderMoment n r j k *
          ((t - t₀) ^ (r / 2) / (r / 2)) := by
  unfold heatMildSpatialHessianCLM
  calc
    ‖heatSemigroupHessianCLM (t - t₀) D.value x +
        heatDuhamelHessianCLM ht.le hr0 hq hH hqb hqholder x‖ ≤
        ‖heatSemigroupHessianCLM (t - t₀) D.value x‖ +
          ‖heatDuhamelHessianCLM ht.le hr0 hq hH hqb hqholder x‖ :=
      norm_add_le _ _
    _ ≤ (∑ j : Fin n, ∑ k : Fin n, ‖D.second j k‖) +
        ∑ j : Fin n, ∑ k : Fin n,
          H * heatHessianEntryHolderMoment n r j k *
            ((t - t₀) ^ (r / 2) / (r / 2)) :=
      add_le_add (D.norm_heatSemigroupHessianCLM_le (sub_pos.mpr ht) x)
        ((norm_heatDuhamelHessianCLM_le ht.le hr0 hq hH hqb hqholder x).trans
          (by
            gcongr with j k
            exact norm_heatDuhamelHessianEntryNDbcf_le
              ht.le hr0 hq hH hqb hqholder j k))

/-- The actual mild Laplacian is bounded by dimension times the norm of the
genuine full Frechet Hessian. -/
theorem abs_heatMildSpatialLaplacianND_le
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    |heatMildSpatialLaplacianND t₀ t u₀ q x| ≤
      (n : ℝ) *
        ‖heatMildSpatialHessianCLM ht.le hr0 u₀ hq hH hqb hqholder x‖ := by
  rw [← sum_heatMildSpatialHessianCLM_diag_eq_laplacian
    ht hr0 u₀ hq hH hqb hqholder x]
  exact abs_sum_standardBasis_diag_le _

/-- Explicit sup estimate for the actual time derivative `∂ₜu = Δu + q`
at a positive-time point. -/
theorem abs_heatMildTimeDerivND_le_explicit
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hu₀holder : ∀ x y, |u₀ y - u₀ x| ≤
      H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    |heatMildTimeDerivND t₀ u₀ q (t, x)| ≤
      (n : ℝ) *
        ((∑ j : Fin n, ∑ k : Fin n,
          H₀ * (t - t₀) ^ (-1 + r / 2) *
            heatHessianEntryHolderMoment n r j k) +
        ∑ j : Fin n, ∑ k : Fin n,
          H * heatHessianEntryHolderMoment n r j k *
            ((t - t₀) ^ (r / 2) / (r / 2))) + C := by
  rw [heatMildTimeDerivND, if_pos ht]
  refine (abs_add_le _ _).trans ?_
  have hLap := abs_heatMildSpatialLaplacianND_le ht hr0 u₀ hq hH hqb hqholder x
  have hHess := norm_heatMildSpatialHessianCLM_le_explicit ht hr0 u₀ hH₀
    hu₀holder hq hH hqb hqholder x
  exact add_le_add (hLap.trans (mul_le_mul_of_nonneg_left hHess (Nat.cast_nonneg n)))
    (by simpa only [Real.norm_eq_abs] using hqb t x)

/-- Uniform positive-time bound for the actual time derivative when the
initial datum is bounded C2. -/
theorem abs_heatMildTimeDerivND_le_of_boundedC2
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (D : EuclideanBoundedC2Data n)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    |heatMildTimeDerivND t₀ D.value q (t, x)| ≤
      (n : ℝ) *
        ((∑ j : Fin n, ∑ k : Fin n, ‖D.second j k‖) +
        ∑ j : Fin n, ∑ k : Fin n,
          H * heatHessianEntryHolderMoment n r j k *
            ((t - t₀) ^ (r / 2) / (r / 2))) + C := by
  rw [heatMildTimeDerivND, if_pos ht]
  refine (abs_add_le _ _).trans ?_
  have hLap := abs_heatMildSpatialLaplacianND_le
    ht hr0 D.value hq hH hqb hqholder x
  have hHess := norm_heatMildSpatialHessianCLM_le_of_boundedC2
    ht hr0 D hq hH hqb hqholder x
  exact add_le_add
    (hLap.trans (mul_le_mul_of_nonneg_left hHess (Nat.cast_nonneg n)))
    (by simpa only [Real.norm_eq_abs] using hqb t x)

/-- Spatial Holder constant for the full Hessian of the mild solution. -/
def heatMildHessianSpatialHolderConstant
    (n : ℕ) (r H₀ H : ℝ) : ℝ :=
  heatInitialHessianSpatialHolderConstant n H₀ +
    heatDuhamelHessianSpatialHolderConstant n r H

/-- **Spatial `r`-Holder estimate for the genuine full Frechet Hessian of the
Euclidean mild solution.**  The constant is uniform down to the initial time:
the homogeneous part uses the actual Holder initial Hessian and the Duhamel
part uses the heat-time split estimate. -/
theorem norm_heatMildSpatialHessianCLM_sub_le_holder
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r) (hr1 : r < 1)
    (D : EuclideanBoundedC2Data n) {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x y : Fin n → ℝ) :
    ‖heatMildSpatialHessianCLM ht.le hr0 D.value hq hH hqb hqholder x -
        heatMildSpatialHessianCLM ht.le hr0 D.value hq hH hqb hqholder y‖ ≤
      heatMildHessianSpatialHolderConstant n r H₀ H * ‖x - y‖ ^ r := by
  have heq :
      heatMildSpatialHessianCLM ht.le hr0 D.value hq hH hqb hqholder x -
        heatMildSpatialHessianCLM ht.le hr0 D.value hq hH hqb hqholder y =
      (heatSemigroupHessianCLM (t - t₀) D.value x -
        heatSemigroupHessianCLM (t - t₀) D.value y) +
      (heatDuhamelHessianCLM ht.le hr0 hq hH hqb hqholder x -
        heatDuhamelHessianCLM ht.le hr0 hq hH hqb hqholder y) := by
    unfold heatMildSpatialHessianCLM
    abel
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  have hhom := norm_heatSemigroupHessianCLM_sub_le_dist_rpow
    D (sub_pos.mpr ht) hr0.le hH₀ hsecondHolder x y
  have hduh := norm_heatDuhamelHessianCLM_sub_le_holder
    ht.le hr0 hr1 hq hH hqb hqholder x y
  calc
    ‖heatSemigroupHessianCLM (t - t₀) D.value x -
          heatSemigroupHessianCLM (t - t₀) D.value y‖ +
        ‖heatDuhamelHessianCLM ht.le hr0 hq hH hqb hqholder x -
          heatDuhamelHessianCLM ht.le hr0 hq hH hqb hqholder y‖ ≤
      heatInitialHessianSpatialHolderConstant n H₀ * ‖x - y‖ ^ r +
        heatDuhamelHessianSpatialHolderConstant n r H * ‖x - y‖ ^ r :=
      add_le_add hhom hduh
    _ = heatMildHessianSpatialHolderConstant n r H₀ H * ‖x - y‖ ^ r := by
      unfold heatMildHessianSpatialHolderConstant
      ring

end HessianNorms

end AnalyticPDE
end RicciFlow
