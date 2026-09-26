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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatInitialValue
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Parabolic second jet of the Euclidean mild heat solution

This file connects the explicit heat-kernel construction to the repository's
coordinate `C^{2+α,1+α/2}` infrastructure.  On the positive-time
cylinder the mild solution has a genuine parabolic second jet: its time
derivative is the spatial Hessian trace plus the source, and its spatial
derivatives are the Frechet gradient and Hessian constructed previously.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- A genuine scalar parabolic second jet on Euclidean time-space.  This
small standalone structure keeps the explicit heat-kernel construction
independently auditable, without importing the much larger optional
Ricci--DeTurck function-space aggregate. -/
structure EuclideanParabolicSecondJetND {n : ℕ}
    (u : ℝ × (Fin n → ℝ) → ℝ)
    (s : Set (ℝ × (Fin n → ℝ))) where
  timeDeriv : ℝ × (Fin n → ℝ) → ℝ
  spaceDeriv : ℝ × (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ
  spaceSecondDeriv : ℝ × (Fin n → ℝ) →
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)
  hasTimeDeriv : ∀ ⦃z⦄, z ∈ s →
    HasDerivWithinAt (fun t : ℝ ↦ u (t, z.2)) (timeDeriv z)
      {t | (t, z.2) ∈ s} z.1
  hasSpaceDeriv : ∀ ⦃z⦄, z ∈ s →
    HasFDerivWithinAt (fun x : Fin n → ℝ ↦ u (z.1, x)) (spaceDeriv z)
      {x | (z.1, x) ∈ s} z.2
  hasSpaceSecondDeriv : ∀ ⦃z⦄, z ∈ s →
    HasFDerivWithinAt (fun x : Fin n → ℝ ↦ spaceDeriv (z.1, x))
      (spaceSecondDeriv z) {x | (z.1, x) ∈ s} z.2

/-- The explicit scalar Euclidean mild solution viewed as a time-space
function. -/
def heatMildSpaceTimeND {n : ℕ} (t₀ : ℝ)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    ℝ × (Fin n → ℝ) → ℝ :=
  fun z ↦ heatMildSpatialND t₀ z.1 u₀ q z.2

/-- The actual time derivative field of the mild heat solution, totalized by
zero outside the positive-time cylinder. -/
def heatMildTimeDerivND {n : ℕ} (t₀ : ℝ)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    ℝ × (Fin n → ℝ) → ℝ :=
  fun z ↦ if t₀ < z.1 then
    heatMildSpatialLaplacianND t₀ z.1 u₀ q z.2 + q z.1 z.2
  else 0

/-- The genuine spatial Hessian field, totalized by zero before the initial
time.  The proof arguments only certify the positive-time integral formula
and do not change its value. -/
def heatMildSpaceHessianND
    {n : ℕ} {r : ℝ} (t₀ : ℝ) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ℝ × (Fin n → ℝ) →
      (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  fun z ↦ if ht : t₀ < z.1 then
    heatMildSpatialHessianCLM ht.le hr0 u₀ hq hH hqb hqholder z.2
  else 0

/-- **The Euclidean mild solution has a genuine parabolic second jet.**
All three derivative witnesses are obtained from actual Frechet/time
derivatives of the heat-kernel formula; the time component satisfies the
inhomogeneous heat equation by construction. -/
def heatMildParabolicSecondJetND
    {n : ℕ} {t₀ r : ℝ} (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    EuclideanParabolicSecondJetND (heatMildSpaceTimeND t₀ u₀ q)
      (Set.Ioi t₀ ×ˢ (Set.univ : Set (Fin n → ℝ))) where
  timeDeriv := heatMildTimeDerivND t₀ u₀ q
  spaceDeriv := fun z ↦ heatMildSpatialGradientCLM t₀ z.1 u₀ q z.2
  spaceSecondDeriv :=
    heatMildSpaceHessianND t₀ hr0 u₀ hq hH hqb hqholder
  hasTimeDeriv := by
    intro z hz
    have hzt : t₀ < z.1 := hz.1
    have hd := hasDerivAt_heatMildSpatialND_time_eq_laplacian_add_source
      hzt hr0 u₀ hq hH hqb hqholder z.2
    simpa [heatMildSpaceTimeND, heatMildTimeDerivND, hzt] using
      hd.hasDerivWithinAt
  hasSpaceDeriv := by
    intro z hz
    have hzt : t₀ < z.1 := hz.1
    have hd := hasFDerivAt_heatMildSpatialND hzt hr0 u₀ hq hH hqb
      hqholder z.2
    simpa [heatMildSpaceTimeND] using hd.hasFDerivWithinAt
  hasSpaceSecondDeriv := by
    intro z hz
    have hzt : t₀ < z.1 := hz.1
    have hd := hasFDerivAt_heatMildSpatialGradientCLM hzt hr0 u₀ hq hH
      hqb hqholder z.2
    simpa [heatMildSpaceHessianND, hzt] using hd

/-- Readout of the jet's time derivative: it is exactly `Δu + q` at every
positive-time point. -/
theorem heatMildParabolicSecondJetND_timeDeriv
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    (heatMildParabolicSecondJetND (t₀ := t₀) hr0 u₀ hq hH hqb hqholder).timeDeriv
        (t, x) =
      heatMildSpatialLaplacianND t₀ t u₀ q x + q t x := by
  simp [heatMildParabolicSecondJetND, heatMildTimeDerivND, ht]

end AnalyticPDE
end RicciFlow
