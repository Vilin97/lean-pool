/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketNormalizedPrimary
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketRay
public import LeanPool.NavierStokesAndEuler.Euler.PacketCrossProduct
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
The oriented orthonormal frame built from the actual normalized primary.
Its angular-velocity entries are derived from the physical ODEs and agree
with the `frameSkew` matrix used in the source propagation estimates.
-/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketCrossProduct EulerPacketNormalizedPrimary
  InnerProductSpace ContinuousLinearMap Matrix WithLp

/-- Cross bilinear as an element of `Space →L[ℝ] Space →L[ℝ] Space`. -/
def crossBilinear : Space →L[ℝ] Space →L[ℝ] Space :=
  ({ toFun := crossLeft
     map_add' a b := by
       apply ContinuousLinearMap.ext
       intro x
       simp [crossLeft_apply, cross, map_add]
     map_smul' r a := by
       apply ContinuousLinearMap.ext
       intro x
       simp [crossLeft_apply, cross, map_smul] } : Space →ₗ[ℝ] (Space →L[ℝ] Space)).mkContinuous 1
    (fun a => by
      change ‖crossLeft a‖ ≤ 1*‖a‖
      simpa only [one_mul] using crossLeft_norm_le a)

theorem crossBilinear_apply (a b : Space) : crossBilinear a b = cross a b := rfl

theorem cross_hasDerivAt {p q : ℝ → Space} {p' q' : Space} {t : ℝ}
    (hp : HasDerivAt p p' t) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun s => cross (p s) (q s)) (cross p' (q t) + cross (p t) q') t := by
  have h := (crossBilinear.hasFDerivAt.comp_hasDerivAt t hp).clm_apply hq
  simpa only [Function.comp_def, crossBilinear_apply] using h

theorem cross_hasDerivWithinAt {p q : ℝ → Space} {p' q' : Space} {t : ℝ} {S : Set ℝ}
    (hp : HasDerivWithinAt p p' S t) (hq : HasDerivWithinAt q q' S t) :
    HasDerivWithinAt (fun s => cross (p s) (q s)) (cross p' (q t) + cross (p t) q') S t := by
  have h := (crossBilinear.hasFDerivAt.comp_hasDerivWithinAt t hp).clm_apply hq
  simpa only [Function.comp_def, crossBilinear_apply] using h

theorem inner_cross_first (p q : Space) : ⟪p,cross p q⟫_ℝ = 0 := by
  rw [← dot_eq_inner]
  exact dot_self_cross (ofLp p) (ofLp q)

theorem inner_cross_second (p q : Space) : ⟪q,cross p q⟫_ℝ = 0 := by
  rw [← dot_eq_inner]
  exact dot_cross_self (ofLp p) (ofLp q)

theorem inner_cross_cross (p q r s : Space) :
    ⟪cross p q,cross r s⟫_ℝ = ⟪p,r⟫_ℝ*⟪q,s⟫_ℝ - ⟪p,s⟫_ℝ*⟪q,r⟫_ℝ := by
  simp only [← dot_eq_inner, cross]
  exact cross_dot_cross (ofLp p) (ofLp q) (ofLp r) (ofLp s)

theorem inner_cross_exchange_first (p q r : Space) :
    ⟪p,cross q r⟫_ℝ = -⟪q,cross p r⟫_ℝ := by
  simp only [← dot_eq_inner, cross]
  rw [triple_product_permutation, ← cross_anticomm (ofLp p) (ofLp r), dotProduct_neg]

theorem inner_cross_exchange_last (p q r : Space) :
    ⟪p,cross q r⟫_ℝ = -⟪r,cross q p⟫_ℝ := by
  simp only [← dot_eq_inner, cross]
  rw [triple_product_permutation, triple_product_permutation (ofLp q) (ofLp r) (ofLp p),
    ← cross_anticomm (ofLp q) (ofLp p), dotProduct_neg]

/-- Frame, given by `![p, q, cross p q]`. -/
def frame (p q : Space) : Fin 3 → Space := ![p, q, cross p q]

/-- Frame rate, given by `![rayRate B p, velocityRate B p q, cross (rayRate B p) q + cross p
(velocityRate B p q)]`. -/
def frameRate (B : Space →L[ℝ] Space) (p q : Space) : Fin 3 → Space :=
  ![rayRate B p, velocityRate B p q,
    cross (rayRate B p) q + cross p (velocityRate B p q)]

/-- Frame matrix, given by `⟪frame p q i, B (frame p q j)⟫_ℝ`. -/
def frameMatrix (B : Space →L[ℝ] Space) (p q : Space) (i j : Fin 3) : ℝ :=
  ⟪frame p q i, B (frame p q j)⟫_ℝ

theorem frame_orthonormal (p q : Space)
    (hp : ⟪p, p⟫_ℝ = 1) (hq : ⟪q, q⟫_ℝ = 1) (hpq : ⟪p, q⟫_ℝ = 0) :
    Orthonormal ℝ (frame p q) := by
  have hqp : ⟪q,p⟫_ℝ = 0 := (real_inner_comm _ _).trans hpq
  have hnp : ⟪cross p q,p⟫_ℝ = 0 := (real_inner_comm _ _).trans (inner_cross_first p q)
  have hnq : ⟪cross p q,q⟫_ℝ = 0 := (real_inner_comm _ _).trans (inner_cross_second p q)
  have hnn : ⟪cross p q,cross p q⟫_ℝ = 1 := by
    rw [inner_cross_cross, hp, hq, hpq, hqp]
    norm_num
  apply orthonormal_iff_ite.mpr
  intro i j
  fin_cases i <;> fin_cases j <;> dsimp [frame]
  · exact hp
  · exact hpq
  · exact inner_cross_first p q
  · exact hqp
  · exact hq
  · exact inner_cross_second p q
  · exact hnp
  · exact hnq
  · exact hnn

/-- Frame basis, constructed using `OrthonormalBasis.mk`. -/
def frameBasis (p q : Space)
    (hp : ⟪p, p⟫_ℝ = 1) (hq : ⟪q, q⟫_ℝ = 1) (hpq : ⟪p, q⟫_ℝ = 0) :
    OrthonormalBasis (Fin 3) ℝ Space :=
  OrthonormalBasis.mk (frame_orthonormal p q hp hq hpq)
    ((frame_orthonormal p q hp hq hpq).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simp [Space])).ge

theorem frameBasis_apply (p q : Space)
    (hp : ⟪p, p⟫_ℝ = 1) (hq : ⟪q, q⟫_ℝ = 1) (hpq : ⟪p, q⟫_ℝ = 0) (i : Fin 3) :
    frameBasis p q hp hq hpq i = frame p q i := by
  simp only [frameBasis, OrthonormalBasis.coe_mk]

/-- All nine entries of the actual frame rate, including their signs. -/
theorem frameRate_skew (B : Space →L[ℝ] Space) (p q : Space)
    (hp : ⟪p, p⟫_ℝ = 1) (hq : ⟪q, q⟫_ℝ = 1) (hpq : ⟪p, q⟫_ℝ = 0) :
    ∀ i j, ⟪frame p q i, frameRate B p q j⟫_ℝ =
      EulerPacketRay.frameSkew (frameMatrix B p q) i j := by
  let n := cross p q
  have hqp : ⟪q,p⟫_ℝ = 0 := (real_inner_comm _ _).trans hpq
  have hpn : ⟪p,n⟫_ℝ = 0 := inner_cross_first p q
  have hqn : ⟪q,n⟫_ℝ = 0 := inner_cross_second p q
  have hnp : ⟪n,p⟫_ℝ = 0 := (real_inner_comm _ _).trans hpn
  have hnq : ⟪n,q⟫_ℝ = 0 := (real_inner_comm _ _).trans hqn
  have hpp : ⟪p,rayRate B p⟫_ℝ = 0 := by
    simp only [rayRate, inner_add_right, inner_neg_right, real_inner_smul_right,
      adjoint_inner_right, hp, mul_one]
    rw [real_inner_comm p (B p)]
    ring
  have hqp' : ⟪q,rayRate B p⟫_ℝ = -⟪p,B q⟫_ℝ := by
    simp only [rayRate, inner_add_right, inner_neg_right, real_inner_smul_right,
      adjoint_inner_right, hqp, mul_zero, add_zero]
    rw [real_inner_comm p (B q)]
  have hnp' : ⟪n,rayRate B p⟫_ℝ = -⟪p,B n⟫_ℝ := by
    simp only [rayRate, inner_add_right, inner_neg_right, real_inner_smul_right,
      adjoint_inner_right, hnp, mul_zero, add_zero]
    rw [real_inner_comm p (B n)]
  have hpq' : ⟪p,velocityRate B p q⟫_ℝ = ⟪p,B q⟫_ℝ := by
    simp only [velocityRate, inner_add_right, inner_neg_right, real_inner_smul_right,
      hp, hpq, mul_one, mul_zero, add_zero]
    ring
  have hqq : ⟪q,velocityRate B p q⟫_ℝ = 0 := by
    simp only [velocityRate, inner_add_right, inner_neg_right, real_inner_smul_right,
      hq, hqp, mul_one, mul_zero, add_zero]
    ring
  have hnq' : ⟪n,velocityRate B p q⟫_ℝ = -⟪n,B q⟫_ℝ := by
    simp only [velocityRate, inner_add_right, inner_neg_right, real_inner_smul_right,
      hnp, hnq, mul_zero, add_zero]
  have hpn' : ⟪p,cross (rayRate B p) q + cross p (velocityRate B p q)⟫_ℝ = ⟪p,B n⟫_ℝ := by
    rw [inner_add_right, inner_cross_first, add_zero, inner_cross_exchange_first]
    rw [real_inner_comm n (rayRate B p), hnp', neg_neg]
  have hqn' : ⟪q,cross (rayRate B p) q + cross p (velocityRate B p q)⟫_ℝ = ⟪n,B q⟫_ℝ := by
    rw [inner_add_right, inner_cross_second, zero_add, inner_cross_exchange_last]
    rw [real_inner_comm n (velocityRate B p q), hnq', neg_neg]
  have hnn : ⟪n,cross (rayRate B p) q + cross p (velocityRate B p q)⟫_ℝ = 0 := by
    change ⟪cross p q,cross (rayRate B p) q + cross p (velocityRate B p q)⟫_ℝ = _
    rw [inner_add_right, inner_cross_cross, inner_cross_cross, hpp, hqq, hpq, hqp]
    ring
  intro i j
  fin_cases i <;> fin_cases j <;>
    dsimp [frame, frameRate, frameMatrix, EulerPacketRay.frameSkew]
  · exact hpp
  · exact hpq'
  · exact hpn'
  · exact hqp'
  · exact hqq
  · exact hqn'
  · exact hnp'
  · exact hnq'
  · exact hnn

/-- Normalized frame, given by `frame (unit (m t)) (unit (v t))`. -/
def normalizedFrame (m v : ℝ → Space) (t : ℝ) : Fin 3 → Space := frame (unit (m t)) (unit (v t))

theorem normalizedFrame_hasDerivAt (B : Space →L[ℝ] Space) {m v : ℝ → Space} {t : ℝ}
    (hm : HasDerivAt m (-B.adjoint (m t)) t)
    (hv : HasDerivAt v (-B (v t) + (2 * ⟪m t, B (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) t)
    (hm0 : m t ≠ 0) (hv0 : v t ≠ 0) (hmv : ⟪m t, v t⟫_ℝ = 0) (i : Fin 3) :
    HasDerivAt (fun s => normalizedFrame m v s i)
      (frameRate B (unit (m t)) (unit (v t)) i) t := by
  have hp := normalized_ray_hasDerivAt B hm hm0
  have hq := normalized_velocity_hasDerivAt B hv hv0 hmv
  fin_cases i
  · exact hp
  · exact hq
  · exact cross_hasDerivAt hp hq

theorem normalizedFrame_hasDerivWithinAt (B : Space →L[ℝ] Space)
    {m v : ℝ → Space} {t : ℝ} {S : Set ℝ}
    (hm : HasDerivWithinAt m (-B.adjoint (m t)) S t)
    (hv : HasDerivWithinAt v (-B (v t) + (2 * ⟪m t, B (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) S t)
    (hm0 : m t ≠ 0) (hv0 : v t ≠ 0) (hmv : ⟪m t, v t⟫_ℝ = 0) (i : Fin 3) :
    HasDerivWithinAt (fun s => normalizedFrame m v s i)
      (frameRate B (unit (m t)) (unit (v t)) i) S t := by
  have hp := normalized_ray_hasDerivWithinAt B hm hm0
  have hq := normalized_velocity_hasDerivWithinAt B hv hv0 hmv
  fin_cases i
  · exact hp
  · exact hq
  · exact cross_hasDerivWithinAt hp hq

/-- The source skew matrix is now identified with the derivative of the
actual normalized ray/velocity frame. -/
theorem normalizedFrame_skew (B : Space →L[ℝ] Space) {m v : ℝ → Space} {t : ℝ}
    (hm : HasDerivAt m (-B.adjoint (m t)) t)
    (hv : HasDerivAt v (-B (v t) + (2 * ⟪m t, B (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) t)
    (hm0 : m t ≠ 0) (hv0 : v t ≠ 0) (hmv : ⟪m t, v t⟫_ℝ = 0) (i j : Fin 3) :
    ⟪normalizedFrame m v t i, deriv (fun s => normalizedFrame m v s j) t⟫_ℝ =
      EulerPacketRay.frameSkew (frameMatrix B (unit (m t)) (unit (v t))) i j := by
  rw [(normalizedFrame_hasDerivAt B hm hv hm0 hv0 hmv j).deriv]
  exact frameRate_skew B (unit (m t)) (unit (v t))
    (unit_inner_self hm0) (unit_inner_self hv0) (unit_inner_zero hmv) i j

end EulerPacketMovingFrame
