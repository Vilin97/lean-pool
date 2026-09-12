/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketMovingFrame
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
The physical parent decomposition and moving-frame coefficient bounds in
source (23).  Frame motion and primary shear motion are derived from the
actual homogeneous ray and velocity equations.
-/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketCrossProduct
  EulerPacketRay InnerProductSpace ContinuousLinearMap

theorem abs_inner_map_le (B : Space →L[ℝ] Space) {p q : Space}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) : |⟪p,B q⟫_ℝ| ≤ ‖B‖ := by
  have h := (abs_real_inner_le_norm p (B q)).trans
    (mul_le_mul_of_nonneg_left (B.le_opNorm q) (norm_nonneg p))
  simpa only [hp, hq, mul_one, one_mul] using h

theorem frameMatrix_abs_le (B : Space →L[ℝ] Space) (p q : Space)
    (hp : ⟪p, p⟫_ℝ = 1) (hq : ⟪q, q⟫_ℝ = 1) (hpq : ⟪p, q⟫_ℝ = 0)
    (i j : Fin 3) : |frameMatrix B p q i j| ≤ ‖B‖ :=
  abs_inner_map_le B ((frame_orthonormal p q hp hq hpq).norm_eq_one i)
    ((frame_orthonormal p q hp hq hpq).norm_eq_one j)

/-- The shear is exactly the `(q,p)` entry in the actual orthonormal frame. -/
theorem frameMatrix_parent (B E : Space →L[ℝ] Space) (h : ℝ) (p q : Space)
    (hp : ⟪p, p⟫_ℝ = 1) (hq : ⟪q, q⟫_ℝ = 1) (hpq : ⟪p, q⟫_ℝ = 0) :
    frameMatrix (B + h • rankOne ℝ q p + E) p q =
      parentEntry (frameMatrix B p q) (frameMatrix E p q) h := by
  have horth := orthonormal_iff_ite.mp (frame_orthonormal p q hp hq hpq)
  have hi (i : Fin 3) : ⟪frame p q i,q⟫_ℝ = if i = 1 then 1 else 0 := by
    simpa only [frame, Matrix.cons_val_one, Matrix.cons_val_zero] using horth i 1
  have hj (j : Fin 3) : ⟪p,frame p q j⟫_ℝ = if 0 = j then 1 else 0 := by
    simpa only [frame, Matrix.cons_val_zero] using horth 0 j
  funext i j
  simp only [frameMatrix, add_apply, smul_apply, rankOne_apply, inner_add_right,
    real_inner_smul_right, hi, hj, parentEntry]
  fin_cases i <;> fin_cases j <;> norm_num
  ring

theorem rayRate_norm_le (B : Space →L[ℝ] Space) {p : Space} (hp : ‖p‖ = 1) :
    ‖rayRate B p‖ ≤ 2*‖B‖ := by
  have hB : ‖B.adjoint p‖ ≤ ‖B‖ := by
    simpa only [hp, mul_one, LinearIsometryEquiv.norm_map] using B.adjoint.le_opNorm p
  have hi := abs_inner_map_le B hp hp
  have h := norm_add_le (-B.adjoint p) (⟪p,B p⟫_ℝ • p)
  simp only [norm_neg, norm_smul, Real.norm_eq_abs, hp, mul_one] at h
  exact h.trans (by linarith only [hB, hi])

theorem velocityRate_norm_le (B : Space →L[ℝ] Space) {p q : Space}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) : ‖velocityRate B p q‖ ≤ 4*‖B‖ := by
  have hB : ‖B q‖ ≤ ‖B‖ := by simpa only [hq, mul_one] using B.le_opNorm q
  have hi := abs_inner_map_le B hp hq
  have hj := abs_inner_map_le B hq hq
  have h1 := norm_add_le (-B q) ((2*⟪p,B q⟫_ℝ) • p)
  have h2 := norm_add_le (-B q+(2*⟪p,B q⟫_ℝ) • p) (⟪q,B q⟫_ℝ • q)
  simp only [norm_neg, norm_smul, Real.norm_eq_abs, hp, hq, mul_one, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2)] at h1 h2
  change ‖-B q+(2*⟪p,B q⟫_ℝ) • p+⟪q,B q⟫_ℝ • q‖ ≤ 4*‖B‖
  linarith only [h1, h2, hB, hi, hj]

theorem frameRate_norm_le (B : Space →L[ℝ] Space) (p q : Space)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (i : Fin 3) :
    ‖frameRate B p q i‖ ≤ 6*‖B‖ := by
  have hr := rayRate_norm_le B hp
  have hv := velocityRate_norm_le B hp hq
  fin_cases i
  · change ‖rayRate B p‖ ≤ 6*‖B‖
    linarith only [hr, norm_nonneg B]
  · change ‖velocityRate B p q‖ ≤ 6*‖B‖
    linarith only [hv, norm_nonneg B]
  · change ‖cross (rayRate B p) q+cross p (velocityRate B p q)‖ ≤ 6*‖B‖
    have h := (norm_add_le _ _).trans (add_le_add
      (cross_norm_le (rayRate B p) q) (cross_norm_le p (velocityRate B p q)))
    simp only [hp, hq, mul_one, one_mul] at h
    linarith only [h, hr, hv]

/-- Frame matrix rate, given by `⟪frameRate B p q i,B (frame p q j)⟫_ℝ + ⟪frame p q i,B₁ (frame
p q j)+B (frameRate B p q j)⟫_ℝ`. -/
def frameMatrixRate (B B₁ : Space →L[ℝ] Space) (p q : Space) (i j : Fin 3) : ℝ :=
  ⟪frameRate B p q i,B (frame p q j)⟫_ℝ +
    ⟪frame p q i,B₁ (frame p q j)+B (frameRate B p q j)⟫_ℝ

theorem frameMatrix_hasDerivWithinAt {B : ℝ → Space →L[ℝ] Space}
    {B₁ : Space →L[ℝ] Space} {m v : ℝ → Space} {t : ℝ} {S : Set ℝ}
    (hB : HasDerivWithinAt B B₁ S t)
    (hm : HasDerivWithinAt m (-(B t).adjoint (m t)) S t)
    (hv : HasDerivWithinAt v (-(B t) (v t) +
      (2 * ⟪m t, (B t) (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) S t)
    (hm0 : m t ≠ 0) (hv0 : v t ≠ 0) (hmv : ⟪m t, v t⟫_ℝ = 0) (i j : Fin 3) :
    HasDerivWithinAt (fun s => frameMatrix (B s) (unit (m s)) (unit (v s)) i j)
      (frameMatrixRate (B t) B₁ (unit (m t)) (unit (v t)) i j) S t := by
  have hi := normalizedFrame_hasDerivWithinAt (B t) hm hv hm0 hv0 hmv i
  have hj := normalizedFrame_hasDerivWithinAt (B t) hm hv hm0 hv0 hmv j
  exact (hi.inner ℝ (hB.clm_apply hj)).congr_deriv (add_comm _ _)

theorem frameMatrixRate_abs_le (B B₁ : Space →L[ℝ] Space) (p q : Space)
    (hp : ⟪p, p⟫_ℝ = 1) (hq : ⟪q, q⟫_ℝ = 1) (hpq : ⟪p, q⟫_ℝ = 0)
    (i j : Fin 3) : |frameMatrixRate B B₁ p q i j| ≤ ‖B₁‖+12*‖B‖^2 := by
  have hn := (frame_orthonormal p q hp hq hpq).norm_eq_one
  have hp' : ‖p‖ = 1 := by simpa only [frame, Matrix.cons_val_zero] using hn 0
  have hq' : ‖q‖ = 1 := by
    simpa only [frame, Matrix.cons_val_one, Matrix.cons_val_zero] using hn 1
  have hr := frameRate_norm_le B p q hp' hq' i
  have hs := frameRate_norm_le B p q hp' hq' j
  have hBj : ‖B (frame p q j)‖ ≤ ‖B‖ := by simpa only [hn, mul_one] using B.le_opNorm (frame p q j)
  have hB₁j : ‖B₁ (frame p q j)‖ ≤ ‖B₁‖ := by
      simpa only [hn, mul_one] using B₁.le_opNorm (frame p q j)
  have hBr := B.le_opNorm (frameRate B p q j)
  have h1 := (abs_real_inner_le_norm (frameRate B p q i) (B (frame p q j))).trans
    (mul_le_mul hr hBj (norm_nonneg _) (by positivity : 0 ≤ 6*‖B‖))
  have h2 := abs_real_inner_le_norm (frame p q i) (B₁ (frame p q j)+B (frameRate B p q j))
  rw [hn i, one_mul] at h2
  have h3 := norm_add_le (B₁ (frame p q j)) (B (frameRate B p q j))
  have h4 := mul_le_mul_of_nonneg_left hs (norm_nonneg B)
  have h5 := abs_add_le ⟪frameRate B p q i,B (frame p q j)⟫_ℝ
    ⟪frame p q i,B₁ (frame p q j)+B (frameRate B p q j)⟫_ℝ
  unfold frameMatrixRate
  nlinarith only [h1, h2, h3, h4, h5, hB₁j, hBr]

/-- Primary shear, given by `c*(‖m t‖*‖v t‖)`. -/
def primaryShear (c : ℝ) (m v : ℝ → Space) (t : ℝ) : ℝ := c*(‖m t‖*‖v t‖)

/-- In particular, the logarithmic shear law in source (23) holds for the
actual amplitude `c * ‖m‖ * ‖v‖`. -/
theorem primaryShear_hasDerivWithinAt (B : Space →L[ℝ] Space) (c : ℝ)
    {m v : ℝ → Space} {t : ℝ} {S : Set ℝ}
    (hm : HasDerivWithinAt m (-B.adjoint (m t)) S t)
    (hv : HasDerivWithinAt v (-B (v t) + (2 * ⟪m t, B (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) S t)
    (hm0 : m t ≠ 0) (hv0 : v t ≠ 0) (hmv : ⟪m t, v t⟫_ℝ = 0) :
    HasDerivWithinAt (primaryShear c m v)
      (-(frameMatrix B (unit (m t)) (unit (v t)) 0 0 +
        frameMatrix B (unit (m t)) (unit (v t)) 1 1)*primaryShear c m v t) S t := by
  have hmnorm := norm_ne_zero_iff.mpr hm0
  have hvnorm := norm_ne_zero_iff.mpr hv0
  have hmn : HasDerivWithinAt (fun s => ‖m s‖)
      (-⟪unit (m t),B (unit (m t))⟫_ℝ*‖m t‖) S t := by
    apply (norm_hasDerivWithinAt hm hm0).congr_deriv
    simp only [unit, inner_neg_right, adjoint_inner_right,
      real_inner_comm (B (m t)) (m t), map_smul, real_inner_smul_left, real_inner_smul_right]
    field_simp
  have hvn : HasDerivWithinAt (fun s => ‖v s‖)
      (-⟪unit (v t),B (unit (v t))⟫_ℝ*‖v t‖) S t := by
    have hvm : ⟪v t,m t⟫_ℝ = 0 := (real_inner_comm _ _).trans hmv
    apply (norm_hasDerivWithinAt hv hv0).congr_deriv
    simp only [unit, inner_add_right, inner_neg_right, real_inner_smul_right, hvm,
      mul_zero, add_zero, map_smul, real_inner_smul_left]
    field_simp
  convert! (hmn.mul hvn).const_mul c using 1
  dsimp [primaryShear, frameMatrix, frame]
  ring

theorem primaryShear_rate_bound (B : Space →L[ℝ] Space) (c : ℝ)
    (m v : ℝ → Space) (t : ℝ) (hm0 : m t ≠ 0) (hv0 : v t ≠ 0)
    (hmv : ⟪m t, v t⟫_ℝ = 0) :
    |-(frameMatrix B (unit (m t)) (unit (v t)) 0 0 +
      frameMatrix B (unit (m t)) (unit (v t)) 1 1)*primaryShear c m v t| ≤
        2*‖B‖*|primaryShear c m v t| := by
  have hp := unit_inner_self hm0
  have hq := unit_inner_self hv0
  have hpq := unit_inner_zero hmv
  have h0 := frameMatrix_abs_le B _ _ hp hq hpq 0 0
  have h1 := frameMatrix_abs_le B _ _ hp hq hpq 1 1
  rw [abs_mul, abs_neg]
  have hsum : |frameMatrix B (unit (m t)) (unit (v t)) 0 0 +
      frameMatrix B (unit (m t)) (unit (v t)) 1 1| ≤ 2*‖B‖ := by
    linarith only [abs_add_le (frameMatrix B (unit (m t)) (unit (v t)) 0 0)
      (frameMatrix B (unit (m t)) (unit (v t)) 1 1), h0, h1]
  exact mul_le_mul_of_nonneg_right hsum (abs_nonneg _)

end EulerPacketMovingFrame
