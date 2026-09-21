/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/

import LeanPool.DavisKahan.DavisKahan.SpectralTheory.CircleRieszIntegral
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ContinuationContour
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.Transport

/-! # Circle Contour -/

open TauCeti.DavisKahan.Angle


/-!
# The circle as a proof-carrying continuation contour

A separating circle (`CircleSeparatesRealSpectrum`) is upgraded here to the
full quantitative `SpectralSeparatingContour` consumed by the Section 8
continuation stack: the parametrization `t ↦ circleMap c r (2 π t)` is a
single-piece `C¹` closed contour, its normalized winding at every off-circle
real point is the inside indicator (through the scalar Cauchy formula proved
in `RieszCircle`), and a positive contour-to-spectrum margin is produced by
compactness of the circle against the closed spectrum.
-/

open scoped InnerProductSpace unitInterval
open Set

namespace TauCeti
namespace DavisKahan
namespace CircleContour

open DavisKahanExt
open TauCeti.DavisKahan
open DavisKahan.Foundation

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## The circle as a closed path and a piecewise-`C¹` contour -/

/-- The unit-interval parametrization of the circle of center `c` and radius
`r`, one full positive turn. -/
noncomputable def circlePath (c : ℂ) (r : ℝ) :
    Path (circleMap c r 0) (circleMap c r 0) where
  toFun t := circleMap c r (2 * Real.pi * (t : ℝ))
  continuous_toFun :=
    (continuous_circleMap c r).comp (continuous_const.mul continuous_subtype_val)
  source' := by norm_num
  target' := by
    show circleMap c r (2 * Real.pi * ((1 : unitInterval) : ℝ)) = circleMap c r 0
    rw [Set.Icc.coe_one, mul_one,
      show (2 * Real.pi : ℝ) = 0 + 2 * Real.pi by ring]
    exact periodic_circleMap c r 0

/-- The unit-interval circle path is Mathlib's `circleMap` on the rescaled angle. -/
@[simp] theorem circlePath_apply (c : ℂ) (r : ℝ) (t : unitInterval) :
    circlePath c r t = circleMap c r (2 * Real.pi * (t : ℝ)) := rfl

/-- The circle as a single-piece `C¹` closed contour. -/
noncomputable def circleContour (c : ℂ) (r : ℝ) : PiecewiseC1ClosedContour where
  basePoint := circleMap c r 0
  path := circlePath c r
  pieceCount := 1
  pieceCount_pos := one_pos
  breakPoint := ![0, 1]
  breakPoint_zero := rfl
  breakPoint_last := rfl
  breakPoint_strictMono := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    change (0 : ℝ) < 1
    norm_num
  contDiffOn_piece := by
    intro i
    fin_cases i
    change ContDiffOn ℝ 1 (circlePath c r).extend (Set.Icc (0 : ℝ) 1)
    have hglob : ContDiffOn ℝ 1
        (fun t : ℝ => circleMap c r (2 * Real.pi * t)) (Set.Icc (0 : ℝ) 1) :=
      ((contDiff_circleMap c r).comp
        (contDiff_const.mul contDiff_id)).contDiffOn
    exact hglob.congr fun t ht => (circlePath c r).extend_apply ht

/-- On the unit interval, the contour parametrization is the scaled circle
map. -/
theorem circleContour_param_eq (c : ℂ) (r : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (circleContour c r).param t = circleMap c r (2 * Real.pi * t) :=
  (circlePath c r).extend_apply ht

/-- The within-derivative of the circle contour on the unit interval. -/
theorem circleContour_derivWithin (c : ℂ) (r : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    derivWithin (circleContour c r).param (Set.Icc (0 : ℝ) 1) t =
      (2 * Real.pi : ℝ) • (circleMap 0 r (2 * Real.pi * t) * Complex.I) := by
  have hg : HasDerivAt (fun u : ℝ => circleMap c r (2 * Real.pi * u))
      ((2 * Real.pi : ℝ) • (circleMap 0 r (2 * Real.pi * t) * Complex.I)) t := by
    have h1 : HasDerivAt (circleMap c r)
        (circleMap 0 r (2 * Real.pi * t) * Complex.I) (2 * Real.pi * t) :=
      hasDerivAt_circleMap c r (2 * Real.pi * t)
    have h2 : HasDerivAt (fun u : ℝ => 2 * Real.pi * u) (2 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
    exact h1.scomp t h2
  have heq : Set.EqOn (circleContour c r).param
      (fun u : ℝ => circleMap c r (2 * Real.pi * u)) (Set.Icc (0 : ℝ) 1) :=
    fun u hu => (circlePath c r).extend_apply hu
  rw [derivWithin_congr heq ((circlePath c r).extend_apply ht)]
  exact hg.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one t ht)

/-! ## Normalized winding of the circle -/

/-- Off the circle, the normalized winding of the circle contour at a real
point is the inside indicator.  This is the geometric content of the scalar
Cauchy formula. -/
theorem circleContour_normalizedWinding (c x r : ℝ) (hr : 0 < r)
    (hb : |x - c| ≠ r) :
    (circleContour (c : ℂ) r).normalizedWinding (x : ℂ) =
      if |x - c| < r then 1 else 0 := by
  unfold PiecewiseC1ClosedContour.normalizedWinding
  have hstep : (∫ t in (0 : ℝ)..1,
      ((circleContour (c : ℂ) r).param t - (x : ℂ))⁻¹ *
        derivWithin (circleContour (c : ℂ) r).param (Set.Icc (0 : ℝ) 1) t) =
      circleIntegral (fun z : ℂ => (z - (x : ℂ))⁻¹) (c : ℂ) r := by
    have hcongr : (∫ t in (0 : ℝ)..1,
        ((circleContour (c : ℂ) r).param t - (x : ℂ))⁻¹ *
          derivWithin (circleContour (c : ℂ) r).param (Set.Icc (0 : ℝ) 1) t) =
        ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) •
          (deriv (circleMap (c : ℂ) r) (2 * Real.pi * t) •
            (circleMap (c : ℂ) r (2 * Real.pi * t) - (x : ℂ))⁻¹) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      change ((circleContour (c : ℂ) r).param t - (x : ℂ))⁻¹ *
          derivWithin (circleContour (c : ℂ) r).param (Set.Icc (0 : ℝ) 1) t =
        (2 * Real.pi : ℝ) • (deriv (circleMap (c : ℂ) r) (2 * Real.pi * t) •
          (circleMap (c : ℂ) r (2 * Real.pi * t) - (x : ℂ))⁻¹)
      rw [circleContour_param_eq (c : ℂ) r ht,
        circleContour_derivWithin (c : ℂ) r ht, deriv_circleMap]
      rw [mul_smul_comm]
      congr 1
      ring
    rw [hcongr, intervalIntegral.integral_smul]
    have hsub := intervalIntegral.smul_integral_comp_mul_left
      (f := fun u : ℝ => deriv (circleMap (c : ℂ) r) u •
        (circleMap (c : ℂ) r u - (x : ℂ))⁻¹)
      (a := (0 : ℝ)) (b := (1 : ℝ)) (2 * Real.pi)
    rw [mul_zero, mul_one] at hsub
    rw [hsub]
    rfl
  rw [hstep]
  rw [inv_mul_eq_div]
  exact RieszCircle.scalar_circleIntegral_resolvent_indicator x c r hr hb

/-! ## Quantitative margin from compactness -/

/-- A separating circle admits a positive uniform margin to the spectrum. -/
theorem exists_circle_spectralMargin
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {B : Set ℝ} {c r : ℝ}
    (hsep : CircleSeparatesRealSpectrum A hA B c r) :
    ∃ m : ℝ, 0 < m ∧ ∀ t : unitInterval, ∀ lam ∈ realSpectrum A,
      m ≤ ‖(circleContour (c : ℂ) r).path t - (lam : ℂ)‖ := by
  have hpathmem : ∀ t : unitInterval,
      ‖(circleContour (c : ℂ) r).path t - (c : ℂ)‖ = r := by
    intro t
    change ‖circleMap (c : ℂ) r (2 * Real.pi * (t : ℝ)) - (c : ℂ)‖ = r
    simpa [mem_sphere_iff_norm] using
      circleMap_mem_sphere (c : ℂ) hsep.radius_pos.le (2 * Real.pi * (t : ℝ))
  by_cases hσ : (spectrum ℂ A).Nonempty
  · have hKc : IsCompact (Metric.sphere (c : ℂ) r) := isCompact_sphere _ _
    have hKne : (Metric.sphere (c : ℂ) r).Nonempty :=
      NormedSpace.sphere_nonempty.mpr hsep.radius_pos.le
    have hcont : ContinuousOn
        (fun z : ℂ => Metric.infDist z (spectrum ℂ A))
        (Metric.sphere (c : ℂ) r) :=
      (Metric.continuous_infDist_pt _).continuousOn
    obtain ⟨z₀, hz₀K, hz₀min⟩ := hKc.exists_isMinOn hKne hcont
    have hz₀notMem : z₀ ∉ spectrum ℂ A := by
      refine hsep.contour_resolvent z₀ ?_
      rwa [Metric.mem_sphere, dist_eq_norm] at hz₀K
    have hz₀pos : 0 < Metric.infDist z₀ (spectrum ℂ A) :=
      ((spectrum.isClosed A).notMem_iff_infDist_pos hσ).mp hz₀notMem
    refine ⟨Metric.infDist z₀ (spectrum ℂ A), hz₀pos, ?_⟩
    intro t lam hlam
    have htK : (circleContour (c : ℂ) r).path t ∈ Metric.sphere (c : ℂ) r := by
      rw [Metric.mem_sphere, dist_eq_norm]
      exact hpathmem t
    calc Metric.infDist z₀ (spectrum ℂ A) ≤
        Metric.infDist ((circleContour (c : ℂ) r).path t) (spectrum ℂ A) :=
          hz₀min htK
      _ ≤ dist ((circleContour (c : ℂ) r).path t) ((lam : ℝ) : ℂ) :=
          Metric.infDist_le_dist_of_mem hlam
      _ = ‖(circleContour (c : ℂ) r).path t - (lam : ℂ)‖ := dist_eq_norm _ _
  · exact ⟨1, one_pos, fun t lam hlam => absurd ⟨(lam : ℂ), hlam⟩ hσ⟩

/-! ## The separating circle as a full spectral continuation contour -/

omit [CompleteSpace H] in
/-- A real point of the spectrum never lies on a separating circle. -/
theorem abs_sub_ne_radius_of_mem_realSpectrum
    {A : H →L[ℂ] H} {hA : A.IsSymmetric}
    {B : Set ℝ} {c r : ℝ}
    (hsep : CircleSeparatesRealSpectrum A hA B c r)
    {lam : ℝ} (hlam : lam ∈ realSpectrum A) :
    |lam - c| ≠ r := by
  intro habs
  refine hsep.contour_resolvent ((lam : ℝ) : ℂ) ?_ hlam
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact habs

/-- The norm-to-abs translation for real points against a real center. -/
theorem norm_ofReal_sub_ofReal (lam c : ℝ) :
    ‖((lam : ℝ) : ℂ) - ((c : ℝ) : ℂ)‖ = |lam - c| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- Upgrade a separating circle to the quantitative
`SpectralSeparatingContour` consumed by the continuation stack. -/
noncomputable def circleSeparatingContour
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {B : Set ℝ} (hB : MeasurableSet B) {c r : ℝ}
    (hsep : CircleSeparatesRealSpectrum A hA B c r) :
    SpectralSeparatingContour A B where
  geometric := circleContour (c : ℂ) r
  selfAdjoint := hA
  measurable_selected := hB
  spectralMargin := (exists_circle_spectralMargin A hA hsep).choose
  spectralMargin_pos := (exists_circle_spectralMargin A hA hsep).choose_spec.1
  spectrum_separated := fun t lam hlam =>
    (exists_circle_spectralMargin A hA hsep).choose_spec.2 t lam hlam
  winding_selected := by
    intro lam hlam hmem
    have hin : |lam - c| < r := by
      have h := (hsep.inside_iff_mem lam hlam).mpr hmem
      rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    rw [circleContour_normalizedWinding c lam r hsep.radius_pos
      (abs_sub_ne_radius_of_mem_realSpectrum hsep hlam), ite_eq_left hin]
  winding_complement := by
    intro lam hlam hmem
    have hnotin : ¬ |lam - c| < r := by
      intro hlt
      refine hmem ((hsep.inside_iff_mem lam hlam).mp ?_)
      rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [circleContour_normalizedWinding c lam r hsep.radius_pos
      (abs_sub_ne_radius_of_mem_realSpectrum hsep hlam), ite_eq_right hnotin]

/-! ## Contour length and the uniform Neumann margin -/

/-- The circle contour has length `2 π r`. -/
theorem circleContour_contourLength (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (circleContour c r).contourLength = 2 * Real.pi * r := by
  unfold PiecewiseC1ClosedContour.contourLength
    PiecewiseC1ClosedContour.contourSpeed
  have hcongr : (∫ t in (0 : ℝ)..1,
      ‖derivWithin (circleContour c r).path.extend (Set.Icc (0 : ℝ) 1) t‖) =
      ∫ _t in (0 : ℝ)..1, 2 * Real.pi * r := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    change ‖derivWithin (circleContour c r).param (Set.Icc (0 : ℝ) 1) t‖ =
      2 * Real.pi * r
    rw [circleContour_derivWithin c r ht, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), norm_mul,
      Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_nonneg hr]
  rw [hcongr, intervalIntegral.integral_const, sub_zero, one_smul]

/-- A norm bound on the total inverse of the pencil pushes the spectrum a
uniform distance away: the quantitative Neumann-series margin. -/
theorem margin_le_norm_sub_of_inverse_bound
    {T : H →L[ℂ] H} {z : ℂ} {m : ℝ} (hm : 0 < m)
    (hz : z ∉ spectrum ℂ T)
    (hbound : ‖Ring.inverse (z • (1 : H →L[ℂ] H) - T)‖ ≤ m⁻¹)
    {w : ℂ} (hw : w ∈ spectrum ℂ T) : m ≤ ‖z - w‖ := by
  by_contra hlt
  push Not at hlt
  have hu : IsUnit (z • (1 : H →L[ℂ] H) - T) := by
    have h := spectrum.notMem_iff.mp hz
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hRz : (z • (1 : H →L[ℂ] H) - T) *
      Ring.inverse (z • (1 : H →L[ℂ] H) - T) = 1 :=
    Ring.mul_inverse_cancel _ hu
  have hfac : w • (1 : H →L[ℂ] H) - T =
      (z • (1 : H →L[ℂ] H) - T) *
        (1 - (z - w) • Ring.inverse (z • (1 : H →L[ℂ] H) - T)) := by
    rw [mul_sub, mul_one, mul_smul_comm, hRz, sub_smul]
    abel
  have hsmall : ‖(z - w) • Ring.inverse (z • (1 : H →L[ℂ] H) - T)‖ < 1 := by
    rw [norm_smul]
    calc ‖z - w‖ * ‖Ring.inverse (z • (1 : H →L[ℂ] H) - T)‖ ≤
        ‖z - w‖ * m⁻¹ :=
          mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
      _ < m * m⁻¹ := by
          exact mul_lt_mul_of_pos_right hlt (inv_pos.mpr hm)
      _ = 1 := mul_inv_cancel₀ hm.ne'
  have hunit2 : IsUnit
      ((1 : H →L[ℂ] H) - (z - w) • Ring.inverse (z • (1 : H →L[ℂ] H) - T)) :=
    (Units.oneSub _ hsmall).isUnit
  have hwunit : IsUnit (w • (1 : H →L[ℂ] H) - T) := by
    rw [hfac]
    exact hu.mul hunit2
  refine spectrum.notMem_iff.mpr ?_ hw
  rwa [Algebra.algebraMap_eq_smul_one]

/-- The circle separating contour rides on the circle contour. -/
@[simp] theorem circleSeparatingContour_geometric
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {B : Set ℝ} (hB : MeasurableSet B) {c r : ℝ}
    (hsep : CircleSeparatesRealSpectrum A hA B c r) :
    (circleSeparatingContour A hA hB hsep).geometric =
      circleContour (c : ℂ) r := rfl

end CircleContour
end DavisKahan
end TauCeti
