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

public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundPoleGraph
public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalChartRadialFlow
public import LeanPool.PoincareGeometry.LichnerowiczObata.IntrinsicRoundInverse
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! # Nonsingular first-order round logarithmic coordinates at the north pole -/

@[expose] public noncomputable section
open Bundle Set Filter Asymptotics
open scoped Topology Manifold ContDiff
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- The radial logarithm of the north hemisphere, expressed in its
equatorial Cartesian projection. The divided slope fills the value at zero. -/
def roundPoleLog (R : ℝ) (z : P) : P :=
  dslope Real.arcsin 0 (‖z‖ / R) • z

@[simp] theorem roundPoleLog_zero (R : ℝ) : roundPoleLog (P := P) R 0 = 0 := by
  simp [roundPoleLog]

/-- Although the norm alone is not differentiable at zero, its scalar
coefficient tends to one, and the radial logarithm has identity derivative. -/
theorem hasFDerivAt_roundPoleLog_zero (R : ℝ) :
    HasFDerivAt (roundPoleLog (P := P) R) (ContinuousLinearMap.id ℝ P) 0 := by
  have hd : HasDerivAt Real.arcsin 1 0 := by
    simpa using Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
  have hc : ContinuousAt (fun z : P => dslope Real.arcsin 0 (‖z‖ / R)) 0 := by
    have hh := (continuousAt_dslope_same.mpr hd.differentiableAt)
    have hn : ContinuousAt (fun z : P => ‖z‖ / R) 0 := by fun_prop
    have hh' : ContinuousAt (dslope Real.arcsin 0) (‖(0 : P)‖ / R) := by
      simpa only [norm_zero, zero_div] using hh
    exact ContinuousAt.comp (f := fun z : P => ‖z‖ / R) (g := dslope Real.arcsin 0) hh' hn
  have hv : dslope Real.arcsin 0 (‖(0 : P)‖ / R) = 1 := by
    simp [dslope_same, hd.deriv]
  have ho : (fun z : P => dslope Real.arcsin 0 (‖z‖ / R) - 1) =o[𝓝 0]
      (fun _ : P => (1 : ℝ)) := by
    apply (isLittleO_one_iff ℝ).mpr
    have hh : ContinuousAt (fun z : P => dslope Real.arcsin 0 (‖z‖ / R) - 1) 0 :=
      hc.sub continuousAt_const
    simpa only [hv, sub_self] using hh.tendsto
  have hh := ho.smul_isBigO (isBigO_refl (fun z : P => z) (𝓝 0))
  rw [hasFDerivAt_iff_isLittleO]
  simpa [roundPoleLog, sub_smul] using hh

/-- The logarithm recovers the geodesic radial vector on the open north
hemisphere; this is an identity of the actual polar curve, not a limit. -/
theorem roundPoleLog_polar_projection {R : ℝ} (hR : 0 < R)
    (u : P) (hu : ‖u‖ = 1) {r : ℝ} (hr : r ∈ Ioo 0 (Real.pi * R / 2)) :
    roundPoleLog R ((WithLp.fstL 2 ℝ P ℝ)
      (roundPolarCurve R roundNorth (roundAngularInclusion u) r)) = r • u := by
  have hrR : 0 < r / R := div_pos hr.1 hR
  have hrhalf : r / R < Real.pi / 2 := (div_lt_iff₀ hR).mpr (by nlinarith [hr.2])
  have hs : 0 < Real.sin (r / R) := Real.sin_pos_of_pos_of_lt_pi hrR
    (lt_trans hrhalf (by linarith [Real.pi_pos]))
  have hproj : (WithLp.fstL 2 ℝ P ℝ)
      (roundPolarCurve R roundNorth (roundAngularInclusion u) r) =
      (R * Real.sin (r / R)) • u := by
    simp [roundPolarCurve, roundNorth, roundAngularInclusion_apply, smul_smul]
  rw [hproj, roundPoleLog]
  have hn : ‖(R * Real.sin (r / R)) • u‖ / R = Real.sin (r / R) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hR hs), hu, mul_one]
    field_simp
  rw [hn, dslope_of_ne _ hs.ne', slope, Real.arcsin_zero, vsub_eq_sub, sub_zero, sub_zero,
    smul_eq_mul, Real.arcsin_sin (by linarith [Real.pi_pos]) hrhalf.le, smul_smul]
  congr 1
  field_simp

end LichnerowiczObata
