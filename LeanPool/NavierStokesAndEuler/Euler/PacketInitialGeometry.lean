/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity

@[expose] public section

/-! The physical activation data give the scaled initial conditions. -/

noncomputable section


namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketCrossProduct
  EulerPacketRay InnerProductSpace

theorem scaledRay_initial {m v r : ℝ → Space} {s₀ t₀ a ε : ℝ}
    (hs₀ : s₀ ≠ 0) (hm0 : m t₀ ≠ 0) (hv0 : v t₀ ≠ 0) (hmv : ⟪m t₀,v t₀⟫_ℝ = 0)
    (hr : r t₀ = s₀ • cross (unit (m t₀)) (unit (v t₀))) :
    scaledRay m v r s₀ t₀ a ε 0 = ![0,0,1] := by
  have horth := orthonormal_iff_ite.mp (frame_orthonormal (unit (m t₀)) (unit (v t₀))
    (unit_inner_self hm0) (unit_inner_self hv0) (unit_inner_zero hmv))
  have hc (i : Fin 3) : movingRay m v r t₀ i = s₀*(if i = 2 then 1 else 0) := by
    change ⟪frame (unit (m t₀)) (unit (v t₀)) i,r t₀⟫_ℝ = _
    rw [hr]
    change ⟪frame (unit (m t₀)) (unit (v t₀)) i,
      s₀ • frame (unit (m t₀)) (unit (v t₀)) 2⟫_ℝ = _
    rw [real_inner_smul_right, horth]
  funext i
  fin_cases i <;> norm_num [scaledRay, physicalTime, hc, rayScale, Fin.ext_iff, hs₀]

/-- The signed physical `p` component in (26) becomes a nonnegative
scalar initial slope, with the expected factor `ε⁻¹`. -/
theorem activation_scaled_velocity {m v w : ℝ → Space} {t₀ a ε C γ : ℝ}
    (hε : 0 < ε) (hγlo : -C ≤ γ) (hγhi : γ ≤ 0)
    (hp : ⟪unit (m t₀),w t₀⟫_ℝ = γ) (hq : ⟪unit (v t₀),w t₀⟫_ℝ = 1) :
    0 ≤ -γ/ε ∧ -γ/ε ≤ C/ε ∧
      scaledVelocity m v w t₀ a ε 0 0 = -(-γ/ε) ∧
      scaledVelocity m v w t₀ a ε 0 1 = 1 := by
  have hu : scaledVelocity m v w t₀ a ε 0 0 = γ/ε := by
    norm_num [scaledVelocity, movingVelocity, physicalTime, normalizedFrame, frame,
      velocityScale, Fin.ext_iff, hp]
  have hv : scaledVelocity m v w t₀ a ε 0 1 = 1 := by
    norm_num [scaledVelocity, movingVelocity, physicalTime, normalizedFrame, frame,
      velocityScale, Fin.ext_iff, hq]
  refine ⟨div_nonneg (neg_nonneg.mpr hγhi) hε.le,
    div_le_div_of_nonneg_right (by linarith only [hγlo]) hε.le, ?_, hv⟩
  rw [hu]
  ring

theorem activation_tangent_pairing {m v r w : ℝ → Space} {s₀ t₀ : ℝ}
    (hr : r t₀ = s₀ • cross (unit (m t₀)) (unit (v t₀)))
    (hw : ⟪cross (unit (m t₀)) (unit (v t₀)),w t₀⟫_ℝ = 0) :
    ⟪r t₀,w t₀⟫_ℝ = 0 := by
  rw [hr, real_inner_smul_left, hw, mul_zero]

end EulerPacketMovingFrame
