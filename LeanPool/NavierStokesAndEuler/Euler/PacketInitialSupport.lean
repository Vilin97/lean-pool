/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialFields
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalL2Scaling

/-! Common compact support for the two actual initial increments after
the physical spatial dilation. -/

@[expose] public section


noncomputable section

namespace EulerPhysicalL2Scaling

open Set EulerSmoothLimit

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
theorem support_in_ball_of_zero (f : Space → V) (R : ℝ)
    (hz : ∀ x, R < ‖x‖ → f x = 0) : tsupport f ⊆ Metric.closedBall 0 R := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  by_contra h
  exact hx (hz x (lt_of_not_ge h))

theorem scale_support (ell : ℝ) (hell : 0 < ell) (f : Space → V) (R : ℝ)
    (hs : tsupport f ⊆ Metric.closedBall 0 R) :
    tsupport (scale ell f) ⊆ Metric.closedBall 0 (ell*R) := by
  apply support_in_ball_of_zero
  intro x hx
  have hn : ell⁻¹ • x ∉ tsupport f := by
    intro hm
    have hb := hs hm
    rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hell)] at hb
    have h := mul_le_mul_of_nonneg_left hb hell.le
    rw [← mul_assoc,mul_inv_cancel₀ hell.ne',one_mul] at h
    linarith
  exact congrArg (ell • ·) (image_eq_zero_of_notMem_tsupport hn) |>.trans (smul_zero ell)

end EulerPhysicalL2Scaling

namespace EulerPacketInitial

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketCylinderField
    EulerPhysicalL2Scaling

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {N : ℕ}
  {a : ℕ → Profile} {support : Set Space}

theorem high_scaled_support
    (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (κ k : ℝ) (m : Space)
    (ell : ℝ) (hell : 0 < ell) (R : ℝ) (hs : support ⊆ Metric.closedBall 0 R) :
    tsupport (scale ell (fun x => high N κ t a (t,(x,k*inner ℝ m x)))) ⊆
      Metric.closedBall 0 (ell*R) := by
  apply scale_support ell hell
  apply support_in_ball_of_zero
  intro x hx
  apply high_zero_outside G t κ t x _ (k*inner ℝ m x)
  intro hm
  have hb := hs hm
  rw [Metric.mem_closedBall,dist_zero_right] at hb
  linarith

theorem mean_scaled_support (κ k : ℝ) (m : Space) (ell : ℝ) (hell : 0 < ell)
    (a : ℕ → Profile)
    (hs : ∀ i, i ≤ N → ∀ θ, tsupport (fun x => (a i).mean (0, (x, θ))) ⊆
      {x : Space | ‖ell • x‖ ≤ 2}) :
    tsupport (scale ell (fun x => mean N κ 0 a (0,(x,k*inner ℝ m x)))) ⊆
      Metric.closedBall 0 2 := by
  apply support_in_ball_of_zero
  intro x hx
  have hz : mean N κ 0 a (0,(ell⁻¹ • x,k*inner ℝ m (ell⁻¹ • x))) = 0 := by
    apply mean_zero_outside 0 κ 0 a {y : Space | ‖ell • y‖ ≤ 2}
    · intro i hi y hy θ
      exact image_eq_zero_of_notMem_tsupport
        (f := fun x : Space => (a i).mean (0,(x,θ))) (fun hm => hy (hs i hi θ hm))
    · change ¬‖ell • (ell⁻¹ • x)‖ ≤ 2
      rw [smul_smul,mul_inv_cancel₀ hell.ne',one_smul]
      exact not_le.mpr hx
  change ell • mean N κ 0 a (0,(ell⁻¹ • x,k*inner ℝ m (ell⁻¹ • x))) = 0
  rw [hz,smul_zero]

end EulerPacketInitial
