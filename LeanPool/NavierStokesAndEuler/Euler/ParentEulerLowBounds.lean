/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerState
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalLowBounds

/-! Low-order source guards can be carried from one actual physical
Euler state to the next. The only update costs are the initial velocity
gradient error and the proved upper pressure bound. -/

@[expose] public section


noncomputable section

namespace EulerPacketPhysicalLowBounds

open InnerProductSpace ContinuousLinearMap EulerSmoothLimit

theorem quadratic_lower_of_norm (M : Matrix) (e : ℝ) (he : ‖M‖ ≤ e) (z : Space) :
    -e*‖z‖^2 ≤ ⟪M z,z⟫_ℝ := by
  have h := (quadratic_le_norm (-M) z).trans
    (mul_le_mul_of_nonneg_right (by simpa only [norm_neg] using he) (sq_nonneg ‖z‖))
  simp only [neg_apply,inner_neg_left] at h
  linarith only [h]

theorem quadratic_lower_of_difference (M N : Matrix) (C e : ℝ)
    (hC : ∀ z, -C * ‖z‖ ^ 2 ≤ ⟪M z, z⟫_ℝ) (he : ‖N - M‖ ≤ e) (z : Space) :
    -(C+e)*‖z‖^2 ≤ ⟪N z,z⟫_ℝ := by
  have h := quadratic_lower_of_norm (N-M) e he z
  simp only [sub_apply,inner_sub_left] at h
  nlinarith only [h,hC z]

end EulerPacketPhysicalLowBounds

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace EulerSmoothLimit EulerMeanHarmonic
  EulerPacketPhysicalLowBounds

variable {A : Parent} (E : Evolution A)

theorem initialStrain_eq (x : Space) :
    A.initialStrain.field x=fderiv ℝ (fun y => E.velocity (0,y)) (A.ell • x) :=
  A.initialStrain_physical (fun t y => E.velocity (t,y))
    (fun t _ => (E.velocity_smooth t).differentiable (by simp) |>.differentiableAt)
    E.velocity_match x

theorem initial_gradient_lower_exterior (H : LowBounds A) (x : Space)
    (hx : H.r ≤ ‖x‖) (z : Space) :
    -H.Be*‖z‖^2 ≤ ⟪fderiv ℝ (fun y => E.velocity (0,y)) x z,z⟫_ℝ := by
  have hx' : H.r ≤ ‖A.ell • (A.ell⁻¹ • x)‖ := by
    simpa only [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul] using hx
  have h := H.exterior_lower (A.ell⁻¹ • x) hx' z
  rw [E.initialStrain_eq] at h
  simpa only [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul] using h

theorem initial_gradient_lower_core (H : LowBounds A) (x : Space)
    (hx : ‖x‖ < H.r) (z : Space) :
    -H.Bc*‖z‖^2 ≤ ⟪fderiv ℝ (fun y => E.velocity (0,y)) x z,z⟫_ℝ := by
  have hx' : ‖A.ell • (A.ell⁻¹ • x)‖ < H.r := by
    simpa only [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul] using hx
  have h := H.core_lower (A.ell⁻¹ • x) hx' z
  rw [E.initialStrain_eq] at h
  simpa only [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul] using h

/-- Low bounds from physical, constructed using `A.lowBoundsOfPhysical`. -/
def lowBoundsFromPhysical (Be Bc L r K : ℝ)
    (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc) (hL : boundaryLocalizationC1 * Bc ≤ L)
    (hr : 0 ≤ r) (hrq : r ≤ 1 / 4) (hK : 0 ≤ K)
    (hexterior : ∀ x, r ≤ ‖x‖ → ∀ z : Space,
      -Be*‖z‖^2 ≤ ⟪fderiv ℝ (fun y => E.velocity (0,y)) x z,z⟫_ℝ)
    (hcore : ∀ x, ‖x‖ < r → ∀ z : Space,
      -Bc*‖z‖^2 ≤ ⟪fderiv ℝ (fun y => E.velocity (0,y)) x z,z⟫_ℝ)
    (hpressure : ∀ t x z, ⟪fderiv ℝ (E.force t) x z,z⟫_ℝ ≤ K*‖z‖^2)
    (hsmall : K*(A.T^2/2)+Be*A.T+boundaryLocalizationC2*Bc*r^3*A.T ≤ 1/2) :
    LowBounds A :=
  A.lowBoundsOfPhysical (fun t y => E.velocity (t,y)) E.force
    (fun t _ => (E.velocity_smooth t).differentiable (by simp) |>.differentiableAt)
    (fun t _ => (E.force_smooth t).differentiable (by simp) |>.differentiableAt)
    E.velocity_match E.acceleration_match Be Bc L r K hBe hBc hL hr hrq hK
    hexterior hcore hpressure hsmall

/-- Update low bounds, constructed using `F.lowBoundsFromPhysical`. -/
def updateLowBounds {N : Parent} (F : Evolution N) (H : LowBounds A)
    (e K : ℝ) (he : 0 ≤ e) (hK : 0 ≤ K)
    (herror : ∀ x, ‖fderiv ℝ (fun y => F.velocity (0, y)) x -
      fderiv ℝ (fun y => E.velocity (0, y)) x‖ ≤ e)
    (hpressure : ∀ t x z, ⟪fderiv ℝ (F.force t) x z, z⟫_ℝ ≤ K * ‖z‖ ^ 2)
    (hsmall : K * (N.T ^ 2 / 2) + (H.Be + e) * N.T +
      boundaryLocalizationC2 * (H.Bc + e) * H.r ^ 3 * N.T ≤ 1 / 2) : LowBounds N :=
  F.lowBoundsFromPhysical (H.Be+e) (H.Bc+e)
    (boundaryLocalizationC1*(H.Bc+e)+1) H.r K
    (add_nonneg H.Be_nonneg he) (add_nonneg H.Bc_nonneg he)
    (by linarith) H.r_nonneg H.r_le_quarter hK
    (fun x hx z => quadratic_lower_of_difference _ _ H.Be e
      (E.initial_gradient_lower_exterior H x hx) (herror x) z)
    (fun x hx z => quadratic_lower_of_difference _ _ H.Bc e
      (E.initial_gradient_lower_core H x hx) (herror x) z)
    hpressure hsmall

end EulerParentPacketFrames.Evolution
