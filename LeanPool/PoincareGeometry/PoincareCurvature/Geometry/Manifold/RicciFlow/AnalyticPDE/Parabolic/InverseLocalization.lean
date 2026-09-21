/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ParabolicHolder
/-!
# Finite-cover inverse localization

This module composes the finite parabolic-cover globalization theorem with the
reciprocal-difference estimate.  The result is the reusable local-to-global
stability statement needed when inverse metric coefficients are assembled from
parabolic coordinate data.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal BigOperators

namespace RicciFlow
namespace AnalyticPDE
namespace ParabolicC0AlphaOn

variable {X : Type*} [PseudoMetricSpace X]

/-- Finite parabolic-ball localization followed by reciprocal stability.  Local
`C^{0,α}` control for two nonvanishing scalar coefficient families and their
difference globalizes over a finite cover, then produces global control of the
reciprocal difference with the explicit reciprocal estimate. -/
theorem inverse_difference_of_finset_parabolicBall_cover_closedBall
    {𝕜 : Type*} [NormedField 𝕜] {α δ r : ℝ} {K : Set (ℝ × X)}
    (N : Finset (ℝ × X)) (hα : 0 < α) (hr : 0 < r)
    {a b : ℝ × X → 𝕜}
    (hcover : K ⊆ ⋃ y ∈ N, parabolicBall y r)
    (hlocal_a : ∀ y ∈ N, ParabolicC0AlphaOn α a (parabolicClosedBall y (2 * r)))
    (hlocal_b : ∀ y ∈ N, ParabolicC0AlphaOn α b (parabolicClosedBall y (2 * r)))
    (hlocal_diff : ∀ y ∈ N,
      ParabolicC0AlphaOn α (fun z => a z - b z)
        (parabolicClosedBall y (2 * r)))
    (hδpos : 0 < δ)
    (hδa : ∀ ⦃p : ℝ × X⦄, p ∈ K → δ ≤ ‖a p‖)
    (hδb : ∀ ⦃p : ℝ × X⦄, p ∈ K → δ ≤ ‖b p‖) :
    ParabolicC0AlphaOn α (fun z => (a z)⁻¹ - (b z)⁻¹) K := by
  have haK : ParabolicC0AlphaOn α a K :=
    of_finset_parabolicBall_cover_closedBall (u := a) N hα hr hcover hlocal_a
  have hbK : ParabolicC0AlphaOn α b K :=
    of_finset_parabolicBall_cover_closedBall (u := b) N hα hr hcover hlocal_b
  have hdiffK : ParabolicC0AlphaOn α (fun z => a z - b z) K :=
    of_finset_parabolicBall_cover_closedBall (u := fun z => a z - b z)
      N hα hr hcover hlocal_diff
  exact inv_sub_inv haK hbK hdiffK hδpos hδa hδb

end ParabolicC0AlphaOn
end AnalyticPDE
end RicciFlow
