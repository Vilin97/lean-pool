/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Measurability.Init

/-!
Differentiating the actual normalized ray and primary velocity.  The rates
are derived from the physical ODEs; no normalized-frame equation is assumed.
-/

@[expose] public section


noncomputable section


namespace EulerPacketNormalizedPrimary

open InnerProductSpace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Unit, given by `‖x‖⁻¹ • x`. -/
def unit (x : E) : E := ‖x‖⁻¹ • x

theorem unit_norm {x : E} (hx : x ≠ 0) : ‖unit x‖ = 1 := by
  rw [unit, norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr hx

theorem unit_inner_self {x : E} (hx : x ≠ 0) : ⟪unit x, unit x⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq, unit_norm hx]
  norm_num

theorem unit_inner_zero {x y : E} (hxy : ⟪x, y⟫_ℝ = 0) : ⟪unit x, unit y⟫_ℝ = 0 := by
  simp only [unit, real_inner_smul_left, real_inner_smul_right, hxy, mul_zero]

theorem norm_hasDerivAt {f : ℝ → E} {f' : E} {t : ℝ}
    (hf : HasDerivAt f f' t) (hft : f t ≠ 0) :
    HasDerivAt (fun s => ‖f s‖) (⟪f t,f'⟫_ℝ / ‖f t‖) t := by
  have hn := norm_ne_zero_iff.mpr hft
  have hh := hf.norm_sq.sqrt (pow_ne_zero 2 hn)
  have he : (fun s => Real.sqrt (‖f s‖^2)) = (fun s => ‖f s‖) := by
    funext s
    exact Real.sqrt_sq (norm_nonneg _)
  rw [he, Real.sqrt_sq (norm_nonneg _)] at hh
  convert hh using 1
  field_simp

theorem unit_hasDerivAt {f : ℝ → E} {f' : E} {t : ℝ}
    (hf : HasDerivAt f f' t) (hft : f t ≠ 0) :
    HasDerivAt (fun s => unit (f s))
      (‖f t‖⁻¹ • f' - (⟪f t,f'⟫_ℝ / ‖f t‖^3) • f t) t := by
  have hn := norm_ne_zero_iff.mpr hft
  have h := ((norm_hasDerivAt hf hft).inv hn).smul hf
  have he : -(⟪f t,f'⟫_ℝ / ‖f t‖) / ‖f t‖^2 = -(⟪f t,f'⟫_ℝ / ‖f t‖^3) := by
    field_simp
  change HasDerivAt (fun s => unit (f s))
    (‖f t‖⁻¹ • f' + (-(⟪f t,f'⟫_ℝ / ‖f t‖) / ‖f t‖^2) • f t) t at h
  rw [he] at h
  simpa only [neg_smul, sub_eq_add_neg, add_comm] using h

theorem norm_hasDerivWithinAt {f : ℝ → E} {f' : E} {t : ℝ} {S : Set ℝ}
    (hf : HasDerivWithinAt f f' S t) (hft : f t ≠ 0) :
    HasDerivWithinAt (fun s => ‖f s‖) (⟪f t,f'⟫_ℝ / ‖f t‖) S t := by
  have hn := norm_ne_zero_iff.mpr hft
  have hh := hf.norm_sq.sqrt (pow_ne_zero 2 hn)
  have he : (fun s => Real.sqrt (‖f s‖^2)) = (fun s => ‖f s‖) := by
    funext s
    exact Real.sqrt_sq (norm_nonneg _)
  rw [he, Real.sqrt_sq (norm_nonneg _)] at hh
  convert hh using 1
  field_simp

theorem unit_hasDerivWithinAt {f : ℝ → E} {f' : E} {t : ℝ} {S : Set ℝ}
    (hf : HasDerivWithinAt f f' S t) (hft : f t ≠ 0) :
    HasDerivWithinAt (fun s => unit (f s))
      (‖f t‖⁻¹ • f' - (⟪f t,f'⟫_ℝ / ‖f t‖^3) • f t) S t := by
  have hn := norm_ne_zero_iff.mpr hft
  have h := ((norm_hasDerivWithinAt hf hft).inv hn).smul hf
  have he : -(⟪f t,f'⟫_ℝ / ‖f t‖) / ‖f t‖^2 = -(⟪f t,f'⟫_ℝ / ‖f t‖^3) := by
    field_simp
  change HasDerivWithinAt (fun s => unit (f s))
    (‖f t‖⁻¹ • f' + (-(⟪f t,f'⟫_ℝ / ‖f t‖) / ‖f t‖^2) • f t) S t at h
  rw [he] at h
  simpa only [neg_smul, sub_eq_add_neg, add_comm] using h

variable [CompleteSpace E]

/-- Ray rate, given by `-B.adjoint p + ⟪p,B p⟫_ℝ • p`. -/
def rayRate (B : E →L[ℝ] E) (p : E) : E := -B.adjoint p + ⟪p,B p⟫_ℝ • p

/-- Velocity rate, given by `-B q + (2*⟪p,B q⟫_ℝ) • p + ⟪q,B q⟫_ℝ • q`. -/
def velocityRate (B : E →L[ℝ] E) (p q : E) : E :=
  -B q + (2*⟪p,B q⟫_ℝ) • p + ⟪q,B q⟫_ℝ • q

theorem normalized_ray_hasDerivAt (B : E →L[ℝ] E) {m : ℝ → E} {t : ℝ}
    (hm : HasDerivAt m (-B.adjoint (m t)) t) (hm0 : m t ≠ 0) :
    HasDerivAt (fun s => unit (m s)) (rayRate B (unit (m t))) t := by
  have h := unit_hasDerivAt hm hm0
  convert h using 1
  unfold rayRate unit
  rw [inner_neg_right, adjoint_inner_right, real_inner_comm (m t) (B (m t))]
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right, smul_smul,
    div_eq_mul_inv, neg_mul, neg_smul, smul_neg]
  module

omit [CompleteSpace E] in
theorem normalized_velocity_hasDerivAt (B : E →L[ℝ] E) {m v : ℝ → E} {t : ℝ}
    (hv : HasDerivAt v (-B (v t) + (2 * ⟪m t, B (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) t)
    (hv0 : v t ≠ 0) (hmv : ⟪m t, v t⟫_ℝ = 0) :
    HasDerivAt (fun s => unit (v s)) (velocityRate B (unit (m t)) (unit (v t))) t := by
  have h := unit_hasDerivAt hv hv0
  have hvm : ⟪v t,m t⟫_ℝ = 0 := (real_inner_comm _ _).trans hmv
  convert h using 1
  unfold velocityRate unit
  simp only [inner_add_right, inner_neg_right, real_inner_smul_right, hvm, mul_zero,
    add_zero, map_smul, real_inner_smul_left, smul_smul, smul_add, div_eq_mul_inv,
    neg_mul, neg_smul, smul_neg]
  module

theorem normalized_ray_hasDerivWithinAt (B : E →L[ℝ] E) {m : ℝ → E} {t : ℝ} {S : Set ℝ}
    (hm : HasDerivWithinAt m (-B.adjoint (m t)) S t) (hm0 : m t ≠ 0) :
    HasDerivWithinAt (fun s => unit (m s)) (rayRate B (unit (m t))) S t := by
  have h := unit_hasDerivWithinAt hm hm0
  convert h using 1
  unfold rayRate unit
  rw [inner_neg_right, adjoint_inner_right, real_inner_comm (m t) (B (m t))]
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right, smul_smul,
    div_eq_mul_inv, neg_mul, neg_smul, smul_neg]
  module

omit [CompleteSpace E] in
theorem normalized_velocity_hasDerivWithinAt (B : E →L[ℝ] E)
    {m v : ℝ → E} {t : ℝ} {S : Set ℝ}
    (hv : HasDerivWithinAt v (-B (v t) + (2 * ⟪m t, B (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) S t)
    (hv0 : v t ≠ 0) (hmv : ⟪m t, v t⟫_ℝ = 0) :
    HasDerivWithinAt (fun s => unit (v s)) (velocityRate B (unit (m t)) (unit (v t))) S t := by
  have h := unit_hasDerivWithinAt hv hv0
  have hvm : ⟪v t,m t⟫_ℝ = 0 := (real_inner_comm _ _).trans hmv
  convert h using 1
  unfold velocityRate unit
  simp only [inner_add_right, inner_neg_right, real_inner_smul_right, hvm, mul_zero,
    add_zero, map_smul, real_inner_smul_left, smul_smul, smul_add, div_eq_mul_inv,
    neg_mul, neg_smul, smul_neg]
  module

end EulerPacketNormalizedPrimary
