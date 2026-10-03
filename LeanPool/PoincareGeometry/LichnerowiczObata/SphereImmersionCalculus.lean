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

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Differential identities for maps into a round sphere

The radial first and second derivative identities follow from the actual
constant-norm constraint. They are the extrinsic input to the sphere converse.
-/

@[expose] public noncomputable section
open scoped Topology ContDiff
namespace LichnerowiczObata
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- The derivative of a locally sphere-valued map is orthogonal to its radius. -/
theorem inner_fderiv_of_locally_constant_norm_sq
    {F : E → A} {x : E} {r : ℝ} (hF : DifferentiableAt ℝ F x)
    (hn : ∀ᶠ y in 𝓝 x, ‖F y‖ ^ 2 = r) (v : E) :
    inner ℝ (F x) (fderiv ℝ F x v) = 0 := by
  have he : (fun y => inner ℝ (F y) (F y)) =ᶠ[𝓝 x] fun _ => r := by
    filter_upwards [hn] with y hy
    simpa only [real_inner_self_eq_norm_sq] using hy
  have hd := fderiv_inner_apply (𝕜 := ℝ) hF hF v
  rw [he.fderiv_eq] at hd
  simp only [fderiv_const_apply, zero_apply] at hd
  rw [real_inner_comm (F x) (fderiv ℝ F x v)] at hd
  linarith

/-- Twice differentiating the sphere equation determines the radial
component of the ambient second derivative, without a connection assumption. -/
theorem inner_second_fderiv_of_locally_constant_norm_sq
    {F : E → A} {x : E} {r : ℝ} (hF : ContDiffAt ℝ 2 F x)
    (hn : ∀ᶠ y in 𝓝 x, ‖F y‖ ^ 2 = r) (v w : E) :
    inner ℝ (F x) (fderiv ℝ (fderiv ℝ F) x v w) =
      -inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have he : (fun y => inner ℝ (F y) (fderiv ℝ F y w)) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hF.eventually (by decide), eventually_eventually_nhds.mpr hn] with y hy hn'
    exact inner_fderiv_of_locally_constant_norm_sq (hy.differentiableAt (by norm_num)) hn' w
  have hd := fderiv_inner_apply (𝕜 := ℝ) (hF.differentiableAt (by norm_num))
    (hD.clm_apply (differentiableAt_const w)) v
  rw [he.fderiv_eq, fderiv_clm_apply hD (differentiableAt_const w)] at hd
  simp only [fderiv_const_apply, zero_apply, ContinuousLinearMap.comp_zero,
    zero_add, ContinuousLinearMap.flip_apply] at hd
  linarith

/-- The coordinate second derivative is symmetric on any C2 germ. -/
theorem second_fderiv_symmetric_of_contDiffAt_two
    {F : E → A} {x : E} (hF : ContDiffAt ℝ 2 F x) (v w : E) :
    fderiv ℝ (fderiv ℝ F) x v w = fderiv ℝ (fderiv ℝ F) x w v := by
  apply second_derivative_symmetric_of_eventually
  · filter_upwards [hF.eventually (by decide)] with y hy
    exact (hy.differentiableAt (by norm_num)).hasFDerivAt
  · exact ((hF.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt

/-- A constant ambient linear functional commutes with the coordinate
second derivative. -/
theorem second_fderiv_clm_comp_of_contDiffAt_two
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (ℓ : A →L[ℝ] B) {F : E → A} {x : E} (hF : ContDiffAt ℝ 2 F x) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun y => ℓ (F y))) x u v =
      ℓ (fderiv ℝ (fderiv ℝ F) x u v) := by
  have he : fderiv ℝ (fun y => ℓ (F y)) =ᶠ[𝓝 x] fun y => ℓ.comp (fderiv ℝ F y) := by
    filter_upwards [hF.eventually (by decide)] with y hy
    exact (ℓ.hasFDerivAt.comp y (hy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  rw [he.fderiv_eq, fderiv_clm_comp (differentiableAt_const ℓ) hD]
  simp

end LichnerowiczObata
