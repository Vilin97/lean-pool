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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelTime
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanMildFrechet

/-!
# The classical Euclidean mild heat equation

This module joins the independently proved spatial Frechet regularity and
time-generator identities.  The resulting scalar mild solution is genuinely
`C²` in space and differentiable in time, and its time derivative equals the
trace of its genuine spatial Hessian plus the prescribed source.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

section HessianPackaging

/-- The classical spatial Laplacian of the Euclidean mild solution.  Its two
summands are the traces of the genuine homogeneous and Duhamel Hessians. -/
def heatMildSpatialLaplacianND
    {n : ℕ} (t₀ t : ℝ)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  heatSemigroupLaplacianND (t - t₀) u₀ x +
    heatDuhamelLaplacianND t₀ t q x

/-- The trace of the packaged genuine mild Hessian is the displayed spatial
Laplacian. -/
theorem sum_heatMildSpatialHessianCLM_diag_eq_laplacian
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    (∑ k : Fin n, heatMildSpatialHessianCLM ht.le hr0 u₀ hq hH hqb hqholder x
      (Pi.single k 1) (Pi.single k 1)) =
      heatMildSpatialLaplacianND t₀ t u₀ q x := by
  simp only [heatMildSpatialHessianCLM, add_apply,
    Finset.sum_add_distrib, heatSemigroupHessianCLM_apply,
    heatDuhamelHessianCLM_apply, Pi.single_apply]
  rw [heatMildSpatialLaplacianND, heatSemigroupLaplacianND,
    heatDuhamelLaplacianND]
  simp [heatHessianEntryConvolutionND, heatDuhamelHessianEntryND,
    heatHessianCoordConvolutionND]
  apply Finset.sum_congr rfl
  intro k _
  rw [heatDuhamelHessianCoordND]
  apply intervalIntegral.integral_congr
  intro s _
  apply integral_congr_ae
  filter_upwards with y
  simp only [Pi.sub_apply, one_div, mul_inv_rev]

end HessianPackaging

/-- **Classical scalar Euclidean heat equation.**  The complete mild solution
has time derivative equal to its actual spatial Laplacian plus the source at
every time strictly after the initial time. -/
theorem hasDerivAt_heatMildSpatialND_time_eq_laplacian_add_source
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    @HasDerivAt ℝ _ ℝ NormedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun u => heatMildSpatialND t₀ u u₀ q x)
      (heatMildSpatialLaplacianND t₀ t u₀ q x + q t x) t := by
  simpa only [heatMildSpatialND, heatMildClassicalND,
    heatMildSpatialLaplacianND] using
    hasDerivAt_heatMildClassicalND_time ht hr0 u₀ hq hH hqb hqholder x

/-- The time equation written directly as source plus the trace of the
genuine spatial Frechet Hessian. -/
theorem hasDerivAt_heatMildSpatialND_time_eq_hessianTrace_add_source
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    @HasDerivAt ℝ _ ℝ NormedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun u => heatMildSpatialND t₀ u u₀ q x)
      ((∑ k : Fin n,
          heatMildSpatialHessianCLM ht.le hr0 u₀ hq hH hqb hqholder x
            (Pi.single k 1) (Pi.single k 1)) + q t x) t := by
  rw [sum_heatMildSpatialHessianCLM_diag_eq_laplacian
    ht hr0 u₀ hq hH hqb hqholder x]
  exact hasDerivAt_heatMildSpatialND_time_eq_laplacian_add_source
    ht hr0 u₀ hq hH hqb hqholder x

end AnalyticPDE
end RicciFlow
