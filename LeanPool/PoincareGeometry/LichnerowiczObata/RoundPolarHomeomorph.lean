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

public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundPolarInverse

/-! # Polar homeomorphism of the punctured round sphere -/

@[expose] public noncomputable section

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem roundPolarEquiv_inverse_radius {R : ℝ} (hR : 0 < R) (p : E) (hp : ‖p‖ = 1)
    (x : RoundPuncturedSphere R p) :
    ((roundPolarEquiv hR p hp).symm x).2.1 =
      R * Real.arccos (inner ℝ p (x.1 : E) / R) := by
  obtain ⟨a, rfl⟩ := (roundPolarEquiv hR p hp).surjective x
  rw [Equiv.symm_apply_apply]
  change a.2.1 = R * Real.arccos (inner ℝ p (roundPolarCurve R p a.1.1 a.2.1) / R)
  rw [roundPolarCurve_height R a.2.1 p a.1.1 hp a.1.2.2,
    mul_div_cancel_left₀ _ hR.ne', Real.arccos_cos
      (div_pos a.2.2.1 hR).le ((div_lt_iff₀ hR).mpr a.2.2.2).le]
  field_simp

theorem roundPolarEquiv_inverse_angular {R : ℝ} (hR : 0 < R) (p : E) (hp : ‖p‖ = 1)
    (x : RoundPuncturedSphere R p) :
    ((roundPolarEquiv hR p hp).symm x).1.1 =
      (Real.sin (Real.arccos (inner ℝ p (x.1 : E) / R)))⁻¹ •
        (R⁻¹ • (x.1 : E) - (inner ℝ p (x.1 : E) / R) • p) := by
  obtain ⟨a, rfl⟩ := (roundPolarEquiv hR p hp).surjective x
  rw [Equiv.symm_apply_apply]
  change a.1.1 = (Real.sin (Real.arccos
    (inner ℝ p (roundPolarCurve R p a.1.1 a.2.1) / R)))⁻¹ •
      (R⁻¹ • roundPolarCurve R p a.1.1 a.2.1 -
        (inner ℝ p (roundPolarCurve R p a.1.1 a.2.1) / R) • p)
  rw [roundPolarCurve_height R a.2.1 p a.1.1 hp a.1.2.2,
    mul_div_cancel_left₀ _ hR.ne', Real.arccos_cos
      (div_pos a.2.2.1 hR).le ((div_lt_iff₀ hR).mpr a.2.2.2).le]
  have hsin : Real.sin (a.2.1 / R) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (div_pos a.2.2.1 hR) ((div_lt_iff₀ hR).mpr a.2.2.2)).ne'
  simp only [roundPolarCurve, smul_smul, inv_mul_cancel₀ hR.ne', one_smul,
    add_sub_cancel_left, inv_mul_cancel₀ hsin]

theorem roundPolar_inverse_sine_ne_zero {R : ℝ} (hR : 0 < R) (p : E) (hp : ‖p‖ = 1)
    (x : RoundPuncturedSphere R p) :
    Real.sin (Real.arccos (inner ℝ p (x.1 : E) / R)) ≠ 0 := by
  obtain ⟨a, rfl⟩ := (roundPolarEquiv hR p hp).surjective x
  change Real.sin (Real.arccos (inner ℝ p (roundPolarCurve R p a.1.1 a.2.1) / R)) ≠ 0
  rw [roundPolarCurve_height R a.2.1 p a.1.1 hp a.1.2.2,
    mul_div_cancel_left₀ _ hR.ne', Real.arccos_cos
      (div_pos a.2.2.1 hR).le ((div_lt_iff₀ hR).mpr a.2.2.2).le]
  exact (Real.sin_pos_of_pos_of_lt_pi (div_pos a.2.2.1 hR)
    ((div_lt_iff₀ hR).mpr a.2.2.2)).ne'

/-- The explicit inverse coordinates are continuous away from the poles. -/
theorem continuous_roundPolarEquiv_inverse {R : ℝ} (hR : 0 < R) (p : E) (hp : ‖p‖ = 1) :
    Continuous (roundPolarEquiv hR p hp).symm := by
  have hc : Continuous (fun x : RoundPuncturedSphere R p =>
      Real.sin (Real.arccos (inner ℝ p (x.1 : E) / R))) := by fun_prop
  have hi := hc.inv₀ (roundPolar_inverse_sine_ne_zero hR p hp)
  have hv : Continuous (fun x : RoundPuncturedSphere R p =>
      R⁻¹ • (x.1 : E) - (inner ℝ p (x.1 : E) / R) • p) := by fun_prop
  have hfirst : Continuous (fun x : RoundPuncturedSphere R p =>
      ((roundPolarEquiv hR p hp).symm x).1.1) := by
    simp_rw [roundPolarEquiv_inverse_angular hR p hp]
    exact hi.smul hv
  have hsecond : Continuous (fun x : RoundPuncturedSphere R p =>
      ((roundPolarEquiv hR p hp).symm x).2.1) := by
    simp_rw [roundPolarEquiv_inverse_radius hR p hp]
    fun_prop
  exact (hfirst.subtype_mk _).prodMk (hsecond.subtype_mk _)

/-- The punctured round sphere is homeomorphic to its angular sphere times
the open pole-to-pole radial interval, via the actual polar parametrization. -/
def roundPolarHomeomorph {R : ℝ} (hR : 0 < R) (p : E) (hp : ‖p‖ = 1) :
    (RoundPolarDirections p × Set.Ioo (0 : ℝ) (Real.pi * R)) ≃ₜ RoundPuncturedSphere R p where
  toEquiv := roundPolarEquiv hR p hp
  continuous_toFun := continuous_roundPolarPuncturedMap hR p hp
  continuous_invFun := continuous_roundPolarEquiv_inverse hR p hp

end LichnerowiczObata
