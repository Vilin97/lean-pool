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

public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundPolarCurves

/-! # The metric of the explicit round-sphere polar parametrization -/

@[expose] public noncomputable section

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Differentiating the actual polar map in its angular argument. -/
theorem hasFDerivAt_roundPolarCurve_angular (R s : ℝ) (p q : E) :
    HasFDerivAt (fun y => roundPolarCurve R p y s)
      ((R * Real.sin (s / R)) • ContinuousLinearMap.id ℝ E) q := by
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) q).const_smul (Real.sin (s / R))).const_add
    (Real.cos (s / R) • p)
  convert hd.const_smul R using 1
  · ext y
    simp [roundPolarCurve, smul_add, smul_smul]
  · simp [smul_smul]

/-- The angular metric is the spherical sine-square factor times the
metric of angular directions. The derivative is of the explicit map. -/
theorem roundPolarCurve_angular_metric (R s : ℝ) (p q w v : E) :
    inner ℝ
      (fderiv ℝ (fun y => roundPolarCurve R p y s) q w)
      (fderiv ℝ (fun y => roundPolarCurve R p y s) q v) =
        R ^ 2 * Real.sin (s / R) ^ 2 * inner ℝ w v := by
  rw [(hasFDerivAt_roundPolarCurve_angular R s p q).fderiv]
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- Angular tangent directions are orthogonal to the radial velocity. -/
theorem roundPolarCurve_mixed_metric (R s : ℝ) (p q w : E)
    (hpw : inner ℝ p w = 0) (hqw : inner ℝ q w = 0) :
    inner ℝ ((-Real.sin (s / R)) • p + Real.cos (s / R) • q)
      (fderiv ℝ (fun y => roundPolarCurve R p y s) q w) = 0 := by
  rw [(hasFDerivAt_roundPolarCurve_angular R s p q).fderiv]
  simp [inner_add_left, real_inner_smul_left, real_inner_smul_right, hpw, hqw]

/-- The angular variation is tangent to the actual ambient sphere. -/
theorem roundPolarCurve_angular_tangent (R s : ℝ) (p q w : E)
    (hpw : inner ℝ p w = 0) (hqw : inner ℝ q w = 0) :
    inner ℝ (roundPolarCurve R p q s)
      (fderiv ℝ (fun y => roundPolarCurve R p y s) q w) = 0 := by
  rw [(hasFDerivAt_roundPolarCurve_angular R s p q).fderiv]
  simp [roundPolarCurve, inner_add_left, real_inner_smul_left, real_inner_smul_right, hpw, hqw]

/-- The full round polar metric: unit radial coefficient, zero mixed terms,
and the sine-square angular coefficient, evaluated on actual derivatives. -/
theorem roundPolarCurve_full_metric (R s : ℝ) (p q w v : E)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : inner ℝ p q = 0)
    (hpw : inner ℝ p w = 0) (hqw : inner ℝ q w = 0)
    (hpv : inner ℝ p v = 0) (hqv : inner ℝ q v = 0) (a b : ℝ) :
    let V := (-Real.sin (s / R)) • p + Real.cos (s / R) • q
    let D := fderiv ℝ (fun y => roundPolarCurve R p y s) q
    inner ℝ (a • V + D w) (b • V + D v) =
      a * b + R ^ 2 * Real.sin (s / R) ^ 2 * inner ℝ w v := by
  let V := (-Real.sin (s / R)) • p + Real.cos (s / R) • q
  let D := fderiv ℝ (fun y => roundPolarCurve R p y s) q
  have hn : inner ℝ V V = 1 := by
    rw [real_inner_self_eq_norm_sq, roundPolarCurve_velocity_norm p q hp hq hpq R s]
    norm_num
  have hw : inner ℝ V (D w) = 0 := roundPolarCurve_mixed_metric R s p q w hpw hqw
  have hv : inner ℝ V (D v) = 0 := roundPolarCurve_mixed_metric R s p q v hpv hqv
  have hw' : inner ℝ (D w) V = 0 := by rw [real_inner_comm]; exact hw
  have ha := roundPolarCurve_angular_metric R s p q w v
  change inner ℝ (D w) (D v) = _ at ha
  change inner ℝ (a • V + D w) (b • V + D v) = _
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hn, hw', hv, ha, mul_zero, mul_one, add_zero, zero_add]
  ring

end LichnerowiczObata
