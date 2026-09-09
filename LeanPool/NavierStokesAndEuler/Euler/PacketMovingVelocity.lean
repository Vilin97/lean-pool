/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketMovingRay
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The actual projected primary-velocity ODE in the normalized moving frame. -/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay InnerProductSpace
    ContinuousLinearMap

theorem frameSkew_antisymm (B : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    frameSkew B j i = -frameSkew B i j := by
  fin_cases i <;> fin_cases j <;> simp [frameSkew, Fin.ext_iff]

theorem frameMatrix_adjoint (B : Space →L[ℝ] Space) (p q : Space) (i j : Fin 3) :
    frameMatrix B.adjoint p q i j = frameMatrix B p q j i := by
  unfold frameMatrix
  rw [adjoint_inner_right, real_inner_comm (frame p q j) (B (frame p q i))]

theorem frame_action (M : Space →L[ℝ] Space) (p q x : Space)
    (hp : ⟪p, p⟫_ℝ = 1) (hq : ⟪q, q⟫_ℝ = 1) (hpq : ⟪p, q⟫_ℝ = 0) (i : Fin 3) :
    (∑ j : Fin 3, frameMatrix M p q i j * ⟪frame p q j,x⟫_ℝ) =
      ⟪frame p q i,M x⟫_ℝ := by
  have h := frame_inner_expand p q hp hq hpq (M.adjoint (frame p q i)) x
  have hm (j : Fin 3) : ⟪frame p q j,M.adjoint (frame p q i)⟫_ℝ = frameMatrix M p q i j := by
    rw [adjoint_inner_right, real_inner_comm (frame p q i) (M (frame p q j))]
    rfl
  simp only [hm, adjoint_inner_left] at h
  exact h

theorem frame_norm_sq (p q x : Space)
    (hp : ⟪p, p⟫_ℝ = 1) (hq : ⟪q, q⟫_ℝ = 1) (hpq : ⟪p, q⟫_ℝ = 0) :
    (∑ j : Fin 3, ⟪frame p q j,x⟫_ℝ^2) = ‖x‖^2 := by
  simpa only [pow_two, real_inner_self_eq_norm_sq] using frame_inner_expand p q hp hq hpq x x

theorem frame_flux (M : Space →L[ℝ] Space) (p q r w : Space)
    (hp : ⟪p, p⟫_ℝ = 1) (hq : ⟪q, q⟫_ℝ = 1) (hpq : ⟪p, q⟫_ℝ = 0) :
    (∑ i : Fin 3, ⟪frame p q i,r⟫_ℝ *
      (∑ j : Fin 3, frameMatrix M p q i j * ⟪frame p q j,w⟫_ℝ)) = ⟪r,M w⟫_ℝ := by
  simp_rw [frame_action M p q w hp hq hpq]
  exact frame_inner_expand p q hp hq hpq r (M w)

theorem movingVelocityRate_identity (B M : Space →L[ℝ] Space) (p q w : Space)
    (hp : ⟪p, p⟫_ℝ = 1) (hq : ⟪q, q⟫_ℝ = 1) (hpq : ⟪p, q⟫_ℝ = 0) (i : Fin 3) :
    -⟪frame p q i,M w⟫_ℝ + ⟪frameRate B p q i,w⟫_ℝ =
      -(∑ j : Fin 3, (frameMatrix M p q i j + frameSkew (frameMatrix B p q) i j) *
        ⟪frame p q j,w⟫_ℝ) := by
  have h := movingRayRate_identity B M.adjoint p q w hp hq hpq i
  rw [adjoint_inner_left] at h
  simpa only [frameMatrix_adjoint, frameSkew_antisymm (frameMatrix B p q) i,
    sub_neg_eq_add] using h

/-- Moving velocity, given by `⟪normalizedFrame m v t i,w t⟫_ℝ`. -/
def movingVelocity (m v w : ℝ → Space) (t : ℝ) (i : Fin 3) : ℝ :=
  ⟪normalizedFrame m v t i,w t⟫_ℝ

/-- Moving flux, given by `∑ i : Fin 3, movingRay m v r t i * (∑ j : Fin 3, frameMatrix M (unit
(m t)) (unit (v t)) i j * movingVelocity m v w t j)`. -/
def movingFlux (M : Space →L[ℝ] Space) (m v r w : ℝ → Space) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, movingRay m v r t i *
    (∑ j : Fin 3, frameMatrix M (unit (m t)) (unit (v t)) i j * movingVelocity m v w t j)

/-- Moving denominator, given by `∑ j : Fin 3, (movingRay m v r t j)^2`. -/
def movingDenominator (m v r : ℝ → Space) (t : ℝ) : ℝ :=
  ∑ j : Fin 3, (movingRay m v r t j)^2

theorem movingFlux_eq (M : Space →L[ℝ] Space) (m v r w : ℝ → Space) (t : ℝ)
    (hm : m t ≠ 0) (hv : v t ≠ 0) (hmv : ⟪m t, v t⟫_ℝ = 0) :
    movingFlux M m v r w t = ⟪r t,M (w t)⟫_ℝ :=
  frame_flux M (unit (m t)) (unit (v t)) (r t) (w t)
    (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv)

theorem movingDenominator_eq (m v r : ℝ → Space) (t : ℝ)
    (hm : m t ≠ 0) (hv : v t ≠ 0) (hmv : ⟪m t, v t⟫_ℝ = 0) :
    movingDenominator m v r t = ‖r t‖^2 :=
  frame_norm_sq (unit (m t)) (unit (v t)) (r t)
    (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv)

theorem moving_pairing (m v r w : ℝ → Space) (t : ℝ)
    (hm : m t ≠ 0) (hv : v t ≠ 0) (hmv : ⟪m t, v t⟫_ℝ = 0) :
    (∑ j : Fin 3, movingRay m v r t j * movingVelocity m v w t j) = ⟪r t,w t⟫_ℝ :=
  frame_inner_expand (unit (m t)) (unit (v t))
    (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv) (r t) (w t)

/-- The physical projected ODE becomes the exact `-(M+S)` moving-frame
equation, with its actual scalar pressure flux and denominator. -/
theorem movingVelocity_hasDerivWithinAt (B M : Space →L[ℝ] Space)
    {m v r w : ℝ → Space} {t : ℝ} {S : Set ℝ}
    (hm : HasDerivWithinAt m (-B.adjoint (m t)) S t)
    (hv : HasDerivWithinAt v (-B (v t) + (2 * ⟪m t, B (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) S t)
    (hw : HasDerivWithinAt w (-M (w t) + (2 * ⟪r t, M (w t)⟫_ℝ / ‖r t‖ ^ 2) • r t) S t)
    (hm0 : m t ≠ 0) (hv0 : v t ≠ 0) (hmv : ⟪m t, v t⟫_ℝ = 0) (i : Fin 3) :
    HasDerivWithinAt (fun s => movingVelocity m v w s i)
      (-(∑ j : Fin 3, (frameMatrix M (unit (m t)) (unit (v t)) i j +
        frameSkew (frameMatrix B (unit (m t)) (unit (v t))) i j) * movingVelocity m v w t j) +
        (2*movingFlux M m v r w t / movingDenominator m v r t)*movingRay m v r t i) S t := by
  have h := (normalizedFrame_hasDerivWithinAt B hm hv hm0 hv0 hmv i).inner ℝ hw
  apply h.congr_deriv
  rw [movingFlux_eq M m v r w t hm0 hv0 hmv, movingDenominator_eq m v r t hm0 hv0 hmv]
  have he := movingVelocityRate_identity B M (unit (m t)) (unit (v t)) (w t)
    (unit_inner_self hm0) (unit_inner_self hv0) (unit_inner_zero hmv) i
  simp only [inner_add_right, inner_neg_right, real_inner_smul_right]
  change -⟪frame (unit (m t)) (unit (v t)) i,M (w t)⟫_ℝ +
    (2*⟪r t,M (w t)⟫_ℝ/‖r t‖^2)*movingRay m v r t i +
      ⟪frameRate B (unit (m t)) (unit (v t)) i,w t⟫_ℝ = _
  simp only [movingVelocity, normalizedFrame]
  linarith only [he]

end EulerPacketMovingFrame
