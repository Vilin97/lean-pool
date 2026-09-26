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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatFrechet

/-!
# Spatial Frechet regularity of the Euclidean mild heat solution

This module combines the homogeneous heat evolution with the inhomogeneous
Duhamel potential.  At every time strictly after the initial time, the full
mild solution is `C²` in space and its genuine first and second Frechet
derivatives are the sums of the packaged gradient and mixed Hessian terms.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- The scalar Euclidean mild heat solution at a fixed final time. -/
def heatMildSpatialND {n : ℕ} (t₀ t : ℝ)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  heatSemigroupND (t - t₀) u₀ x +
    ∫ s in t₀..t, heatSemigroupND (t - s) (q s) x

/-- The genuine spatial gradient candidate for the Euclidean mild solution. -/
def heatMildSpatialGradientCLM {n : ℕ} (t₀ t : ℝ)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  heatSemigroupGradientCLM (t - t₀) u₀ x +
    heatDuhamelGradientCLM t₀ t q x

section HessianPackaging

local instance mildCoordinateDualNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance mildCoordinateBilinearNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The full mixed spatial Hessian candidate for the Euclidean mild solution. -/
def heatMildSpatialHessianCLM
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  heatSemigroupHessianCLM (t - t₀) u₀ x +
    heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder x

end HessianPackaging

/-- The fixed-time Euclidean mild solution has the displayed genuine spatial
Frechet derivative. -/
theorem hasFDerivAt_heatMildSpatialND
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    HasFDerivAt (heatMildSpatialND t₀ t u₀ q)
      (heatMildSpatialGradientCLM t₀ t u₀ q x) x := by
  exact (hasFDerivAt_heatSemigroupND (sub_pos.mpr ht) u₀ x).add
    (hasFDerivAt_heatDuhamelND ht.le hr0 hq hH hqb hqholder x)

/-- The displayed mild-solution gradient has the full mixed Hessian as its
genuine Frechet derivative. -/
theorem hasFDerivAt_heatMildSpatialGradientCLM
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    HasFDerivAt (heatMildSpatialGradientCLM t₀ t u₀ q)
      (heatMildSpatialHessianCLM ht.le hr0 u₀ hq hH hqb hqholder x) x := by
  exact (hasFDerivAt_heatSemigroupGradientCLM (sub_pos.mpr ht) u₀ x).add
    (hasFDerivAt_heatDuhamelGradientCLM ht.le hr0 hq hH hqb hqholder x)

/-- The scalar Euclidean mild heat solution is genuinely `C²` in space at
every final time strictly after the initial time. -/
theorem contDiff_two_heatMildSpatialND
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ContDiff ℝ 2 (heatMildSpatialND t₀ t u₀ q) := by
  exact (contDiff_two_heatSemigroupND (sub_pos.mpr ht) u₀).add
    (contDiff_two_heatDuhamelND ht.le hr0 hq hH hqb hqholder)

end AnalyticPDE
end RicciFlow
