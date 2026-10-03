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

public import LeanPool.PoincareGeometry.LichnerowiczObata.PolarMetricAssembly

/-! # Unit angular coordinates for the full polar metric -/

@[expose] public noncomputable section
open scoped Manifold Topology

namespace LichnerowiczObata

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- Positive scaling identifies the unit angular sphere with the auxiliary
parameter sphere, with an explicit inverse. -/
def unitSphereScale (R : ℝ) (hR : 0 < R) :
    Metric.sphere (0 : P) 1 ≃ₜ Metric.sphere (0 : P) R where
  toFun u := ⟨R • (u : P), by
    have hu : ‖(u : P)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    rw [mem_sphere_zero_iff_norm]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hR, hu]⟩
  invFun u := ⟨R⁻¹ • (u : P), by
    have hu : ‖(u : P)‖ = R := mem_sphere_zero_iff_norm.mp u.property
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR), hu, inv_mul_cancel₀ hR.ne']⟩
  left_inv u := by
    apply Subtype.ext
    simp [smul_smul, hR.ne']
  right_inv u := by
    apply Subtype.ext
    simp [smul_smul, hR.ne']
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem unitSphereScale_apply (R : ℝ) (hR : 0 < R)
    (u : Metric.sphere (0 : P) 1) :
    (unitSphereScale R hR u : P) = R • (u : P) := rfl

section Metric
open Bundle
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Rescaling only the angular parameter cancels the auxiliary radius in
the full metric and leaves the radial coefficient unchanged. -/
theorem polar_metric_rescale_unit {Γ : P × ℝ → M} {R r B : ℝ}
    (hR : R ≠ 0) {u w v : P} (s t : ℝ)
    (hΓ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Γ (R • u, r))
    (hmetric : inner ℝ
      (mfderiv 𝓘(ℝ, P × ℝ) I Γ (R • u, r) (R • w, s))
      (mfderiv 𝓘(ℝ, P × ℝ) I Γ (R • u, r) (R • v, t)) =
        B * (inner ℝ (R • w) (R • v) / R ^ 2) + s * t) :
    let Φ := fun q : P × ℝ => Γ (R • q.1, q.2)
    inner ℝ (mfderiv 𝓘(ℝ, P × ℝ) I Φ (u, r) (w, s))
      (mfderiv 𝓘(ℝ, P × ℝ) I Φ (u, r) (v, t)) = B * inner ℝ w v + s * t := by
  let L : P × ℝ →L[ℝ] P × ℝ :=
    (R • ContinuousLinearMap.id ℝ P).prodMap (ContinuousLinearMap.id ℝ ℝ)
  have hL : MDifferentiableAt 𝓘(ℝ, P × ℝ) 𝓘(ℝ, P × ℝ) L (u, r) :=
    mdifferentiableAt_iff_differentiableAt.mpr L.differentiableAt
  have hw := mfderiv_comp_apply (f := (L : P × ℝ → P × ℝ)) (g := Γ)
    (u, r) hΓ hL (w, s)
  have hv := mfderiv_comp_apply (f := (L : P × ℝ → P × ℝ)) (g := Γ)
    (u, r) hΓ hL (v, t)
  rw [mfderiv_eq_fderiv, L.fderiv] at hw hv
  change inner ℝ (mfderiv 𝓘(ℝ, P × ℝ) I (Γ ∘ L) (u, r) (w, s))
    (mfderiv 𝓘(ℝ, P × ℝ) I (Γ ∘ L) (u, r) (v, t)) = _
  rw [hw, hv]
  have hi : inner ℝ (R • w) (R • v) / R ^ 2 = inner ℝ w v := by
    simp only [real_inner_smul_left, real_inner_smul_right]
    field_simp
  rw [hi] at hmetric
  exact hmetric

end Metric
end LichnerowiczObata
