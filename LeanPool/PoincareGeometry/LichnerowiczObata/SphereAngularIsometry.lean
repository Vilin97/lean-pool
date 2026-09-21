/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SphereRadialDifferential
public import LeanPool.PoincareGeometry.LichnerowiczObata.NormPreservingOffZero

/-! # Extending a unit-sphere tangent isometry to a linear isometry -/

@[expose] public noncomputable section
open Metric
open scoped Manifold
namespace LichnerowiczObata
variable {P V : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [Fact (Module.finrank ℝ P = n + 1)]
  [Fact (Module.finrank ℝ V = n + 1)]

/-- A sphere equivalence differentiable and tangent-isometric in both
directions is the restriction of a real linear isometry of the ambient
spaces. No intrinsic-distance or linear-extension assumption is needed. -/
theorem exists_linearIsometryEquiv_of_sphere_tangent_metric
    (A : sphere (0 : P) 1 ≃ sphere (0 : V) 1)
    (hA : MDifferentiable (𝓡 n) (𝓡 n) A)
    (hAi : MDifferentiable (𝓡 n) (𝓡 n) A.symm)
    (hm : PreservesSphereTangentMetric (n := n) A)
    (hmi : PreservesSphereTangentMetric (n := n) A.symm) :
    ∃ L : P ≃ₗᵢ[ℝ] V, ∀ u : sphere (0 : P) 1, L (u : P) = (A u : V) := by
  obtain ⟨L, hL⟩ := exists_linearIsometryEquiv_of_norm_preserving_derivative_off_zero
    (sphereRadialEquiv A) (norm_sphereRadialExtension A)
    (fun x hx => differentiableAt_sphereRadialExtension hA hx)
    (fun x hx => norm_fderiv_sphereRadialExtension_le hA hm hx)
    (fun x hx => differentiableAt_sphereRadialExtension hAi hx)
    (fun x hx => norm_fderiv_sphereRadialExtension_le hAi hmi hx)
  refine ⟨L, fun u => ?_⟩
  rw [hL]
  exact sphereRadialExtension_sphere A u

end LichnerowiczObata
