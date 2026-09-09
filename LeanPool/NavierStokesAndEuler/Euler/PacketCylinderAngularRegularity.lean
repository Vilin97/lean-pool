/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientData
import LeanPool.NavierStokesAndEuler.Euler.PeriodicDerivativeMean

/-! Genuine periodicity and zero-mean identities for raw cylinder-path witnesses. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerPacketPointJets
  EulerPacketProfileRecursion EulerPeriodicDerivativeMean
open scoped ContDiff

namespace Field

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} (G : Field P T raw)

include G in
theorem raw_periodic (t : Icc (0 : ℝ) T) (x : Space) :
    Function.Periodic (fun θ => raw (t,(x,θ))) P := by
  intro θ
  change raw (t,(x,θ+P)) = raw (t,(x,θ))
  rw [G.raw_eq,G.raw_eq,AddCircle.coe_add_period]

include G in
theorem raw_angle_continuous (t : Icc (0 : ℝ) T) (x : Space) :
    Continuous (fun θ : ℝ => raw (t,(x,θ))) :=
  (G.raw_smooth t).continuous.comp (continuous_const.prodMk continuous_id)

include G in
theorem raw_angle_hasDerivAt (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    HasDerivAt (fun s => raw (t,(x,s)))
      (fderiv ℝ (fun y => raw (t,y)) (x,θ) (0,1)) θ := by
  have h := ((G.raw_smooth t).differentiable (by simp) (x,θ)).hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_const θ x).prodMk (hasDerivAt_id θ))
  exact h

include G in
theorem raw_angle_derivative_continuous (t : Icc (0 : ℝ) T) (x : Space) :
    Continuous (fun θ => fderiv ℝ (fun y => raw (t,y)) (x,θ) (0,1)) :=
  (((G.raw_smooth t).fderiv_right (m := ∞) (by simp)).continuous.comp
    (continuous_const.prodMk continuous_id)).clm_apply continuous_const

include G in
theorem raw_angle_derivative_integral (t : Icc (0 : ℝ) T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, fderiv ℝ (fun y => raw (t,y)) (x,θ) (0,1)) = 0 :=
  integral_derivative_eq_zero P _ _ (G.raw_angle_hasDerivAt t x)
    (G.raw_angle_derivative_continuous t x) (G.raw_periodic t x)

include G in
theorem subtract_mean_integral (t : Icc (0 : ℝ) T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, (raw-EulerPacketProfileRecursion.angleMean P raw) (t,(x,θ))) = 0 := by
  have hP : P ≠ 0 := ne_of_gt (Fact.out : 0 < P)
  change (∫ θ in (0 : ℝ)..P, raw (t,(x,θ)) -
    P⁻¹ • (∫ s in (0 : ℝ)..P, raw (t,(x,s)))) = 0
  rw [intervalIntegral.integral_sub ((G.raw_angle_continuous t x).intervalIntegrable 0 P)
    intervalIntegrable_const,intervalIntegral.integral_const,sub_zero,smul_smul,
    mul_inv_cancel₀ hP,one_smul,sub_self]

end Field

variable {P T : ℝ} [Fact (0 < P)] {rawB rawA normal : VectorField}

/-- A new angle-independent mean cannot contribute angular mean to its primary interaction. -/
theorem mean_primary_integral_zero (N : VectorCoefficient T normal)
    (A : Field P T rawA) (s : Set ℝ)
    (hB : ∀ (t : Icc (0 : ℝ) T) x θ, rawB (t, (x, θ)) = rawB (t, (x, 0)))
    (t : Icc (0 : ℝ) T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, fastAdvection (normal (t,(x,θ)))
      (slicedJet s rawB (t,(x,θ))) (slicedJet s rawA (t,(x,θ)))) = 0 := by
  have he : (fun θ => fastAdvection (normal (t,(x,θ)))
      (slicedJet s rawB (t,(x,θ))) (slicedJet s rawA (t,(x,θ)))) =
      fun θ => inner ℝ (N.path t x) (rawB (t,(x,0))) •
        fderiv ℝ (fun y => rawA (t,y)) (x,θ) (0,1) := by
    funext θ
    change inner ℝ (normal (t,(x,θ))) (rawB (t,(x,θ))) •
      (slicedJet s rawA (t,(x,θ))).2 angleDirection = _
    rw [N.raw_eq,hB,slicedJet_angle]
  rw [he]
  exact integral_constant_smul_derivative_eq_zero P _ _ _ (A.raw_angle_hasDerivAt t x)
    (A.raw_angle_derivative_continuous t x) (A.raw_periodic t x)

end EulerPacketCylinderField
