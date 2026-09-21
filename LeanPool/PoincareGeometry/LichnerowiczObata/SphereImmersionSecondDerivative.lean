/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SphereNormalDecomposition

/-! # The Gauss formula for a sphere-valued coordinate immersion

Only the coordinate metric-compatibility and torsion identities are inputs;
the normal second fundamental form is derived from the sphere constraint.
-/

@[expose] public noncomputable section
open scoped Topology ContDiff
namespace LichnerowiczObata
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A]

/-- The ambient acceleration of a spherical immersion is its tangential
connection term minus the induced metric times the radial normal. -/
theorem sphere_immersion_second_derivative
    {F : E → A} {x : E} {R : ℝ} (hR : 0 < R)
    (hF : ContDiffAt ℝ 2 F x) (hn : ∀ᶠ y in 𝓝 x, ‖F y‖ ^ 2 = R ^ 2)
    (hinj : Function.Injective (fderiv ℝ F x))
    (hdim : Module.finrank ℝ A = Module.finrank ℝ E + 1)
    (Γ : E →L[ℝ] E →L[ℝ] E) (hΓ : ∀ v w, Γ v w = Γ w v)
    (hm : ∀ d u w, fderiv ℝ (fun y =>
        inner ℝ (fderiv ℝ F y u) (fderiv ℝ F y w)) x d =
      inner ℝ (fderiv ℝ F x (Γ d u)) (fderiv ℝ F x w) +
        inner ℝ (fderiv ℝ F x u) (fderiv ℝ F x (Γ d w))) (v w : E) :
    fderiv ℝ (fderiv ℝ F) x v w = fderiv ℝ F x (Γ v w) -
      (inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w) / R ^ 2) • F x := by
  let L := fderiv ℝ F x
  let B := fderiv ℝ (fderiv ℝ F) x
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have heval (u : E) : fderiv ℝ (fun y => fderiv ℝ F y u) x = B.flip u := by
    rw [fderiv_clm_apply hD (differentiableAt_const u)]
    simp [B]
  have hm' : ∀ d u w, inner ℝ (B d u) (L w) + inner ℝ (L u) (B d w) =
      inner ℝ (L (Γ d u)) (L w) + inner ℝ (L u) (L (Γ d w)) := by
    intro d u w
    have hh := hm d u w
    rw [fderiv_inner_apply (𝕜 := ℝ) (hD.clm_apply (differentiableAt_const u))
      (hD.clm_apply (differentiableAt_const w)), heval, heval] at hh
    simpa only [ContinuousLinearMap.flip_apply, add_comm] using hh
  have hB : ∀ v w, B v w = B w v := second_fderiv_symmetric_of_contDiffAt_two hF
  have ho : ∀ u, inner ℝ (F x) (L u) = 0 :=
    inner_fderiv_of_locally_constant_norm_sq (hF.differentiableAt (by norm_num)) hn
  have hnorm : ‖F x‖ ^ 2 = R ^ 2 := hn.self_of_nhds
  have hq : F x ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hnorm
    nlinarith [sq_pos_of_pos hR]
  have hnormal : ∀ z, inner ℝ (B v w - L (Γ v w)) (L z) = 0 :=
    second_form_orthogonal_of_metric_compatibility L B Γ hB hΓ hm' v w
  have hrad : inner ℝ (B v w - L (Γ v w)) (F x) = -inner ℝ (L v) (L w) := by
    rw [inner_sub_left, real_inner_comm (F x) (B v w),
      real_inner_comm (F x) (L (Γ v w)), ho, sub_zero]
    exact inner_second_fderiv_of_locally_constant_norm_sq hF hn v w
  have hh := eq_smul_of_orthogonal_tangent L hinj hdim hq ho hnormal
  rw [hrad, hnorm, neg_div, neg_smul] at hh
  change B v w = L (Γ v w) - _
  exact (sub_eq_iff_eq_add.mp hh).trans (by abel)

end LichnerowiczObata
