/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.SpectralTheory.CircleRieszProjection
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.BoundedSelfAdjointSpectralProjection
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.CayleySelectorBridge
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Circle Riesz projections for the Section 8 continuation argument

Only circles separating subsets of the real spectrum are exposed here.  This
is the minimum analytic surface required by the Davis--Kahan continuation
stack and intentionally avoids an abstract contour, rectifiability, or winding
number framework.
-/

open scoped InnerProductSpace Topology
open Set Filter

namespace TauCeti
namespace DavisKahan
namespace RieszCircle

open DavisKahanExt
open TauCeti.DavisKahan

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The circle resolvent integrand: the resolvent at the parametrized circle
point, weighted by the derivative of the parametrization, exactly as in
Mathlib's `circleIntegral`. -/
noncomputable def circleResolventIntegrand
    (A : H →L[ℂ] H) (center radius θ : ℝ) : H →L[ℂ] H :=
  deriv (circleMap (center : ℂ) radius) θ •
    Ring.inverse (circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) - A)

/-- The operator-valued circle integral defining the Riesz projection. -/
noncomputable def circleRieszProjectionIntegral
    (A : H →L[ℂ] H) (center radius : ℝ) : H →L[ℂ] H :=
  (2 * Real.pi * Complex.I)⁻¹ •
    ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, circleResolventIntegrand A center radius θ

omit [CompleteSpace H] in
/-- The core definition in `Core` agrees with the explicit operator-valued
circle integral. -/
theorem circleRieszProjection_eq_integral
    (A : H →L[ℂ] H) (center radius : ℝ) :
    circleRieszProjection A center radius =
      circleRieszProjectionIntegral A center radius :=
  rfl

/-- The resolvent integrand is continuous around a separating circle. -/
theorem continuous_circleResolventIntegrand
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (B : Set ℝ) (center radius : ℝ)
    (hsep : CircleSeparatesRealSpectrum A hA B center radius) :
    Continuous (circleResolventIntegrand A center radius) := by
  have hr : (0 : ℝ) ≤ radius := hsep.radius_pos.le
  have hderiv : Continuous fun θ : ℝ => deriv (circleMap (center : ℂ) radius) θ := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 radius).mul continuous_const
  have haff : Continuous fun θ : ℝ =>
      circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) - A :=
    ((continuous_circleMap _ _).smul continuous_const).sub continuous_const
  have hinv : Continuous fun θ : ℝ =>
      Ring.inverse (circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) - A) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hz : circleMap (center : ℂ) radius θ ∉ spectrum ℂ A :=
      hsep.contour_resolvent _ (by
        simpa [mem_sphere_iff_norm] using circleMap_mem_sphere (center : ℂ) hr θ)
    have hu : IsUnit (circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) - A) := by
      have h := spectrum.notMem_iff.mp hz
      rwa [Algebra.algebraMap_eq_smul_one] at h
    have hcont : ContinuousAt Ring.inverse
        (circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) - A) := by
      have h := NormedRing.inverse_continuousAt hu.unit
      rwa [IsUnit.unit_spec] at h
    exact hcont.comp (f := fun θ' : ℝ =>
      circleMap (center : ℂ) radius θ' • (1 : H →L[ℂ] H) - A) haff.continuousAt
  exact hderiv.smul hinv

/-- Cauchy's formula identifies the scalar circle integral with the indicator
of being inside the circle on the real spectrum. -/
theorem scalar_circleIntegral_resolvent_indicator
    (x center radius : ℝ) (hr : 0 < radius)
    (hboundary : |x - center| ≠ radius) :
    (circleIntegral (fun z : ℂ => (z - x)⁻¹) center radius) /
        (2 * Real.pi * Complex.I) =
      if |x - center| < radius then 1 else 0 := by
  split_ifs with hin
  · have hmem : (x : ℂ) ∈ Metric.ball (center : ℂ) radius := by
      rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      exact hin
    rw [circleIntegral.integral_sub_inv_of_mem_ball hmem]
    exact div_self Complex.two_pi_I_ne_zero
  · have hout : (x : ℂ) ∉ Metric.closedBall (center : ℂ) radius := by
      rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      exact not_le.mpr (lt_of_le_of_ne (not_lt.mp hin) (Ne.symm hboundary))
    have hdiff : DiffContOnCl ℂ (fun z : ℂ => (z - (x : ℂ))⁻¹)
        (Metric.ball (center : ℂ) radius) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ hr.ne']
      intro z hz
      have hzx : z - (x : ℂ) ≠ 0 := by
        intro h0
        exact hout (sub_eq_zero.mp h0 ▸ hz)
      have hd : DifferentiableAt ℂ (fun w : ℂ => w - (x : ℂ)) z :=
        differentiableAt_id.sub_const _
      exact (hd.inv hzx).differentiableWithinAt
    rw [DiffContOnCl.circleIntegral_eq_zero hr.le hdiff, zero_div]

/-- Off the spectrum, the total `Ring.inverse` of the pencil is the continuous
functional calculus of the scalar resolvent symbol `(z - ·)⁻¹`. -/
private theorem ringInverse_eq_cfc_of_notMem_spectrum
    (A : H →L[ℂ] H) (hA : A.IsSymmetric) {z : ℂ}
    (hz : z ∉ spectrum ℂ A) :
    Ring.inverse (z • (1 : H →L[ℂ] H) - A) =
      cfc (fun w : ℂ => (z - w)⁻¹) A := by
  have hnormal : IsStarNormal A :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal
  have hne : ∀ w ∈ spectrum ℂ A, z - w ≠ 0 := by
    intro w hw h0
    exact hz (sub_eq_zero.mp h0 ▸ hw)
  have hfcont : ContinuousOn (fun w : ℂ => z - w) (spectrum ℂ A) :=
    (continuous_const.sub continuous_id).continuousOn
  have hgcont : ContinuousOn (fun w : ℂ => (z - w)⁻¹) (spectrum ℂ A) :=
    hfcont.inv₀ hne
  have hshift : cfc (fun w : ℂ => z - w) A = z • (1 : H →L[ℂ] H) - A := by
    rw [cfc_sub (fun _ : ℂ => z) (fun w : ℂ => w) A,
      cfc_id' (R := ℂ) (a := A), cfc_const z A,
      Algebra.algebraMap_eq_smul_one]
  have hright : (z • (1 : H →L[ℂ] H) - A) *
      cfc (fun w : ℂ => (z - w)⁻¹) A = 1 := by
    rw [← hshift, ← cfc_mul _ _ A hfcont hgcont,
      cfc_congr (g := fun _ : ℂ => (1 : ℂ))
        (fun w hw => mul_inv_cancel₀ (hne w hw)),
      cfc_const_one ℂ A]
  have hleft : cfc (fun w : ℂ => (z - w)⁻¹) A *
      (z • (1 : H →L[ℂ] H) - A) = 1 := by
    rw [← hshift, ← cfc_mul _ _ A hgcont hfcont,
      cfc_congr (g := fun _ : ℂ => (1 : ℂ))
        (fun w hw => inv_mul_cancel₀ (hne w hw)),
      cfc_const_one ℂ A]
  let u : (H →L[ℂ] H)ˣ :=
    ⟨z • (1 : H →L[ℂ] H) - A, cfc (fun w : ℂ => (z - w)⁻¹) A, hright, hleft⟩
  exact Ring.inverse_unit u

/-- The circle resolvent integrand as a continuous scalar symbol on the
complex spectrum.  `mkD` keeps the definition total; on a separating circle it
takes the intended value. -/
private noncomputable def circleSpectrumSymbol
    (A : H →L[ℂ] H) (center radius θ : ℝ) : C(spectrum ℂ A, ℂ) :=
  ContinuousMap.mkD
    ((spectrum ℂ A).domRestrict (fun w : ℂ =>
      deriv (circleMap (center : ℂ) radius) θ *
        (circleMap (center : ℂ) radius θ - w)⁻¹)) 0

omit [CompleteSpace H] in
/-- On a separating circle, every contour point avoids the spectrum. -/
private theorem circleMap_notMem_spectrum
    {A : H →L[ℂ] H} {hA : A.IsSymmetric}
    {B : Set ℝ} {center radius : ℝ}
    (hsep : CircleSeparatesRealSpectrum A hA B center radius) (θ : ℝ) :
    circleMap (center : ℂ) radius θ ∉ spectrum ℂ A :=
  hsep.contour_resolvent _ (by
    simpa [mem_sphere_iff_norm] using
      circleMap_mem_sphere (center : ℂ) hsep.radius_pos.le θ)

/-- Applying the bounded continuous functional calculus to the circle symbol
recovers the operator-valued circle integrand. -/
private theorem cfcL_circleSpectrumSymbol
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {B : Set ℝ} {center radius : ℝ}
    (hsep : CircleSeparatesRealSpectrum A hA B center radius) (θ : ℝ) :
    cfcL (a := A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          hA).isStarNormal
        (circleSpectrumSymbol A center radius θ) =
      circleResolventIntegrand A center radius θ := by
  have hnormal : IsStarNormal A :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal
  have hz := circleMap_notMem_spectrum hsep θ
  have hne : ∀ w ∈ spectrum ℂ A,
      circleMap (center : ℂ) radius θ - w ≠ 0 := by
    intro w hw h0
    exact hz (sub_eq_zero.mp h0 ▸ hw)
  have hgcont : ContinuousOn
      (fun w : ℂ => (circleMap (center : ℂ) radius θ - w)⁻¹)
      (spectrum ℂ A) :=
    ((continuous_const.sub continuous_id).continuousOn).inv₀ hne
  unfold circleSpectrumSymbol
  rw [← cfc_eq_cfcL_mkD
    (f := fun w : ℂ => deriv (circleMap (center : ℂ) radius) θ *
      (circleMap (center : ℂ) radius θ - w)⁻¹) (a := A)]
  rw [cfc_const_mul _ _ A hgcont,
    ← ringInverse_eq_cfc_of_notMem_spectrum A hA hz]
  rfl

/-- The circle symbol is interval integrable, by pulling integrability of the
already-continuous operator integrand back through the isometric calculus. -/
private theorem intervalIntegrable_circleSpectrumSymbol
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {B : Set ℝ} {center radius : ℝ}
    (hsep : CircleSeparatesRealSpectrum A hA B center radius) :
    IntervalIntegrable (circleSpectrumSymbol A center radius)
      MeasureTheory.volume 0 (2 * Real.pi) := by
  let hnormal : IsStarNormal A :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal
  let L : C(spectrum ℂ A, ℂ) →L[ℂ] (H →L[ℂ] H) := cfcL (a := A) hnormal
  have hfun : (fun θ => L (circleSpectrumSymbol A center radius θ)) =
      circleResolventIntegrand A center radius := by
    funext θ
    exact cfcL_circleSpectrumSymbol A hA hsep θ
  have hmapped : IntervalIntegrable
      (fun θ => L (circleSpectrumSymbol A center radius θ))
      MeasureTheory.volume 0 (2 * Real.pi) := by
    rw [hfun]
    exact (continuous_circleResolventIntegrand A hA B center radius
      hsep).intervalIntegrable _ _
  have hIso : Isometry L := by
    simpa [L, cfcL] using (isometry_cfcHom A hnormal)
  have hpull {μ : MeasureTheory.Measure ℝ}
      {f : ℝ → C(spectrum ℂ A, ℂ)}
      (hf : MeasureTheory.Integrable (fun t => L (f t)) μ) :
      MeasureTheory.Integrable f μ := by
    have hiff :
        MeasureTheory.Integrable ((fun g : C(spectrum ℂ A, ℂ) => L g) ∘ f) μ ↔
          MeasureTheory.Integrable f μ :=
      MeasureTheory.LipschitzWith.integrable_comp_iff_of_antilipschitz
        (μ := μ) (f := f) (g := fun g : C(spectrum ℂ A, ℂ) => L g)
        hIso.lipschitz hIso.antilipschitz (by simp)
    exact hiff.mp (by simpa only [Function.comp_def] using hf)
  exact ⟨hpull hmapped.1, hpull hmapped.2⟩

/-- The circle Riesz projection equals the genuine measurable spectral
projection selected by the inside of the circle. -/
theorem circleRieszProjection_eq_boundedSelfAdjointSpectralProjection
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (B : Set ℝ) (hB : MeasurableSet B) (center radius : ℝ)
    (hsep : CircleSeparatesRealSpectrum A hA B center radius) :
    circleRieszProjection A center radius =
      boundedSelfAdjointSpectralProjection A hA B hB := by
  classical
  have hnormal : IsStarNormal A :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal
  set g : C(spectrum ℂ A, ℂ) :=
    (2 * Real.pi * Complex.I)⁻¹ •
      ∫ θ in (0 : ℝ)..2 * Real.pi, circleSpectrumSymbol A center radius θ
    with hg
  have hint := intervalIntegrable_circleSpectrumSymbol A hA hsep
  have hproj : circleRieszProjection A center radius =
      cfcL (a := A) hnormal g := by
    have h1 : circleRieszProjection A center radius =
        (2 * Real.pi * Complex.I)⁻¹ •
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            cfcL (a := A) hnormal (circleSpectrumSymbol A center radius θ) := by
      rw [circleRieszProjection_eq_integral]
      unfold circleRieszProjectionIntegral
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      exact (cfcL_circleSpectrumSymbol A hA hsep θ).symm
    rw [h1, cfcL_intervalIntegral A hnormal _ hint, hg, map_smul]
  have hagree : ∀ (lam : ℝ) (hlam : (lam : ℂ) ∈ spectrum ℂ A),
      g ⟨(lam : ℂ), hlam⟩ = spectralSelector B lam := by
    intro lam hlam
    set x : spectrum ℂ A := ⟨(lam : ℂ), hlam⟩ with hx
    have heval : (∫ θ in (0 : ℝ)..2 * Real.pi,
        circleSpectrumSymbol A center radius θ) x =
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          circleSpectrumSymbol A center radius θ x := by
      simpa only [intervalIntegral.integral_of_le Real.two_pi_pos.le] using
        (ContinuousMap.integral_apply hint.1 x)
    have hint_congr : (∫ θ in (0 : ℝ)..2 * Real.pi,
        circleSpectrumSymbol A center radius θ x) =
        circleIntegral (fun z : ℂ => (z - (lam : ℂ))⁻¹) center radius := by
      unfold circleIntegral
      apply intervalIntegral.integral_congr
      intro θ _
      have hz := circleMap_notMem_spectrum hsep θ
      have hne : ∀ w ∈ spectrum ℂ A,
          circleMap (center : ℂ) radius θ - w ≠ 0 := by
        intro w hw h0
        exact hz (sub_eq_zero.mp h0 ▸ hw)
      have hcont : ContinuousOn (fun w : ℂ =>
          deriv (circleMap (center : ℂ) radius) θ *
            (circleMap (center : ℂ) radius θ - w)⁻¹) (spectrum ℂ A) :=
        continuousOn_const.mul
          (((continuous_const.sub continuous_id).continuousOn).inv₀ hne)
      change circleSpectrumSymbol A center radius θ x = _
      unfold circleSpectrumSymbol
      rw [ContinuousMap.mkD_apply_of_continuousOn hcont]
      rfl
    have hnorm : ‖(lam : ℂ) - (center : ℂ)‖ = |lam - center| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hboundary : |lam - center| ≠ radius := by
      intro habs
      exact hsep.contour_resolvent (lam : ℂ) (hnorm.trans habs) hlam
    have hiff : |lam - center| < radius ↔ lam ∈ B := by
      rw [← hnorm]
      exact hsep.inside_iff_mem lam hlam
    calc g x = (2 * Real.pi * Complex.I)⁻¹ *
        ((∫ θ in (0 : ℝ)..2 * Real.pi,
          circleSpectrumSymbol A center radius θ) x) := by
          rw [hg]
          rfl
      _ = (2 * Real.pi * Complex.I)⁻¹ *
          circleIntegral (fun z : ℂ => (z - (lam : ℂ))⁻¹) center radius := by
          rw [heval, hint_congr]
      _ = circleIntegral (fun z : ℂ => (z - (lam : ℂ))⁻¹) center radius /
          (2 * Real.pi * Complex.I) := by
          rw [inv_mul_eq_div]
      _ = (if |lam - center| < radius then 1 else 0) :=
          scalar_circleIntegral_resolvent_indicator lam center radius
            hsep.radius_pos hboundary
      _ = spectralSelector B lam := by
          unfold spectralSelector
          by_cases hmem : lam ∈ B
          · rw [ite_eq_left (hiff.mpr hmem), Set.indicator_of_mem hmem]
          · rw [ite_eq_right (fun h => hmem (hiff.mp h)),
              Set.indicator_of_notMem hmem]
  rw [hproj,
    boundedSelfAdjointSpectralProjection_eq_cfcL_of_selector A hA B hB g hagree]

omit [CompleteSpace H] in
/-- The second resolvent identity for the total `Ring.inverse` at two units. -/
private theorem ringInverse_sub_ringInverse (T T' : H →L[ℂ] H)
    (hT : IsUnit T) (hT' : IsUnit T') :
    Ring.inverse T' - Ring.inverse T =
      Ring.inverse T' * (T - T') * Ring.inverse T := by
  have h1 : T * Ring.inverse T = 1 := Ring.mul_inverse_cancel T hT
  have h2 : Ring.inverse T' * T' = 1 := Ring.inverse_mul_cancel T' hT'
  calc Ring.inverse T' - Ring.inverse T
      = Ring.inverse T' * (T * Ring.inverse T) -
          Ring.inverse T' * T' * Ring.inverse T := by rw [h1, h2, mul_one, one_mul]
    _ = Ring.inverse T' * (T - T') * Ring.inverse T := by noncomm_ring

/-- If a unit with inverse norm at most `margin⁻¹` becomes singular after adding
a perturbation, the perturbation has norm at least `margin` (geometric series). -/
private theorem margin_le_norm_perturbation
    (T Epert : H →L[ℂ] H) {margin : ℝ} (_hmargin : 0 < margin)
    (hT : IsUnit T) (hTnorm : ‖Ring.inverse T‖ ≤ margin⁻¹)
    (hTE : ¬IsUnit (T + Epert)) : margin ≤ ‖Epert‖ := by
  by_contra hlt
  rw [not_le] at hlt
  have : Nontrivial (H →L[ℂ] H) := by
    rcases subsingleton_or_nontrivial (H →L[ℂ] H) with hsub | hn
    · exact absurd (by
        rw [Subsingleton.elim (T + Epert) (1 : H →L[ℂ] H)]
        exact isUnit_one) hTE
    · exact hn
  have hval : ((hT.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = Ring.inverse T :=
    (Ring.inverse_unit hT.unit).symm.trans (congrArg Ring.inverse hT.unit_spec)
  have hpos : (0 : ℝ) < ‖((hT.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖ :=
    Units.norm_pos _
  have hinvnorm : ‖((hT.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖ ≤ margin⁻¹ := by
    rw [hval]; exact hTnorm
  have hmarg : margin ≤ ‖((hT.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖⁻¹ := by
    rw [← inv_inv margin]
    gcongr
  have hu := (hT.unit.add Epert (lt_of_lt_of_le hlt hmarg)).isUnit
  rw [Units.val_add, hT.unit_spec] at hu
  exact hTE hu

/-- A resolvent-type pencil with a uniform norm bound on the circle is circle
integrable: it is continuous on the open set where the pencil is a unit and
identically zero elsewhere, hence a.e. strongly measurable, and it is bounded. -/
private theorem circleIntegrable_ringInverse_pencil
    (A : H →L[ℂ] H) (center radius M : ℝ) (hr : 0 ≤ radius)
    (hbound : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      ‖Ring.inverse (z • (1 : H →L[ℂ] H) - A)‖ ≤ M) :
    CircleIntegrable (fun z : ℂ => Ring.inverse (z • (1 : H →L[ℂ] H) - A))
      center radius := by
  rw [circleIntegrable_def]
  set g : ℝ → H →L[ℂ] H := fun θ =>
    circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) - A with hg
  have hgcont : Continuous g :=
    ((continuous_circleMap _ _).smul continuous_const).sub continuous_const
  have hVopen : IsOpen {θ : ℝ | IsUnit (g θ)} := Units.isOpen.preimage hgcont
  have hcontOn : ContinuousOn (fun θ => Ring.inverse (g θ))
      {θ : ℝ | IsUnit (g θ)} := by
    intro θ hθ
    have hcθ : ContinuousAt Ring.inverse (g θ) := by
      have h := NormedRing.inverse_continuousAt (hθ : IsUnit (g θ)).unit
      rwa [IsUnit.unit_spec] at h
    exact (hcθ.comp (f := g) hgcont.continuousAt).continuousWithinAt
  have heq : (fun θ => Ring.inverse (g θ)) =
      Set.indicator {θ : ℝ | IsUnit (g θ)} (fun θ => Ring.inverse (g θ)) := by
    funext θ
    by_cases hθ : IsUnit (g θ)
    · rw [Set.indicator_of_mem (show θ ∈ {θ : ℝ | IsUnit (g θ)} from hθ)]
    · rw [Set.indicator_of_notMem (show θ ∉ {θ : ℝ | IsUnit (g θ)} from hθ),
        Ring.inverse_non_unit _ hθ]
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => Ring.inverse (g θ))
      MeasureTheory.volume := by
    rw [heq]
    exact (aestronglyMeasurable_indicator_iff hVopen.measurableSet).mpr
      (hcontOn.aestronglyMeasurable hVopen.measurableSet)
  rw [intervalIntegrable_iff, Set.uIoc_of_le Real.two_pi_pos.le]
  refine MeasureTheory.Integrable.mono' (g := fun _ => M)
    (MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne)
    hmeas.restrict ?_
  filter_upwards with θ
  exact hbound _ (by
    simpa [mem_sphere_iff_norm] using circleMap_mem_sphere (center : ℂ) hr θ)

/-- Resolvent-identity norm bound for two circle Riesz projections.

The nonnegative-radius hypothesis is necessary: for negative radius the
resolvent hypotheses quantify over the empty sphere while the right-hand side
is negative and the left-hand side is a norm. -/
theorem norm_circleRieszProjection_sub_le
    (A E : H →L[ℂ] H) (center radius margin : ℝ) (hr : 0 ≤ radius)
    (hmargin : 0 < margin)
    (hAres : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      ‖Ring.inverse (z • (1 : H →L[ℂ] H) - A)‖ ≤ margin⁻¹)
    (hAEres : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      ‖Ring.inverse (z • (1 : H →L[ℂ] H) - (A + E))‖ ≤ margin⁻¹) :
    ‖circleRieszProjection (A + E) center radius -
        circleRieszProjection A center radius‖ ≤
      radius * ‖E‖ / margin ^ 2 := by
  have hint : CircleIntegrable
      (fun z : ℂ => Ring.inverse (z • (1 : H →L[ℂ] H) - A)) center radius :=
    circleIntegrable_ringInverse_pencil A center radius margin⁻¹ hr hAres
  have hint' : CircleIntegrable
      (fun z : ℂ => Ring.inverse (z • (1 : H →L[ℂ] H) - (A + E))) center radius :=
    circleIntegrable_ringInverse_pencil (A + E) center radius margin⁻¹ hr hAEres
  have hpt : ∀ z ∈ Metric.sphere (center : ℂ) radius,
      ‖Ring.inverse (z • (1 : H →L[ℂ] H) - (A + E)) -
        Ring.inverse (z • (1 : H →L[ℂ] H) - A)‖ ≤ ‖E‖ / margin ^ 2 := by
    intro z hz
    have hzn : ‖z - (center : ℂ)‖ = radius := mem_sphere_iff_norm.mp hz
    set T : H →L[ℂ] H := z • (1 : H →L[ℂ] H) - A with hT
    set T' : H →L[ℂ] H := z • (1 : H →L[ℂ] H) - (A + E) with hT'
    have hTsub : T - T' = E := by rw [hT, hT']; abel
    have hbA : ‖Ring.inverse T‖ ≤ margin⁻¹ := hAres z hzn
    have hbAE : ‖Ring.inverse T'‖ ≤ margin⁻¹ := hAEres z hzn
    have hkey : margin ≤ ‖E‖ → margin⁻¹ ≤ ‖E‖ / margin ^ 2 := fun hEm => by
      rw [le_div_iff₀ (by positivity)]
      calc margin⁻¹ * margin ^ 2 = margin := by
            rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hmargin.ne', one_mul]
        _ ≤ ‖E‖ := hEm
    by_cases hTu : IsUnit T <;> by_cases hT'u : IsUnit T'
    · rw [ringInverse_sub_ringInverse T T' hTu hT'u, hTsub]
      calc ‖Ring.inverse T' * E * Ring.inverse T‖
          ≤ ‖Ring.inverse T' * E‖ * ‖Ring.inverse T‖ := norm_mul_le _ _
        _ ≤ ‖Ring.inverse T'‖ * ‖E‖ * ‖Ring.inverse T‖ := by
            gcongr
            exact norm_mul_le _ _
        _ ≤ margin⁻¹ * ‖E‖ * margin⁻¹ := by gcongr
        _ = ‖E‖ / margin ^ 2 := by
            rw [pow_two, div_eq_mul_inv, mul_inv]
            ring
    · rw [Ring.inverse_non_unit T' hT'u, zero_sub, norm_neg]
      have hEm : margin ≤ ‖E‖ := by
        have h := margin_le_norm_perturbation T (-E) hmargin hTu hbA (by
          intro hu
          rw [show T + -E = T' from by rw [hT, hT']; abel] at hu
          exact hT'u hu)
        rwa [norm_neg] at h
      exact hbA.trans (hkey hEm)
    · rw [Ring.inverse_non_unit T hTu, sub_zero]
      have hEm : margin ≤ ‖E‖ :=
        margin_le_norm_perturbation T' E hmargin hT'u hbAE (by
          intro hu
          rw [show T' + E = T from by rw [hT, hT']; abel] at hu
          exact hTu hu)
      exact hbAE.trans (hkey hEm)
    · rw [Ring.inverse_non_unit T hTu, Ring.inverse_non_unit T' hT'u, sub_zero,
        norm_zero]
      positivity
  have hsplit : circleRieszProjection (A + E) center radius -
      circleRieszProjection A center radius =
      (2 * Real.pi * Complex.I)⁻¹ •
        ∮ z in C((center : ℂ), radius),
          (Ring.inverse (z • (1 : H →L[ℂ] H) - (A + E)) -
            Ring.inverse (z • (1 : H →L[ℂ] H) - A)) := by
    rw [circleIntegral.integral_sub hint' hint, smul_sub]
    rfl
  rw [hsplit, mul_div_assoc]
  exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr hpt

/-- Norm continuity of the selected projection along a bounded affine
self-adjoint path.

The nonnegative-radius hypothesis is necessary: for negative radius the
resolvent hypothesis quantifies over the empty sphere, while the conclusion is
false in general. -/
theorem continuous_circleRieszProjection_path
    (A E : H →L[ℂ] H) (center radius : ℝ) (hr : 0 ≤ radius)
    (hres : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
        IsUnit (z • (1 : H →L[ℂ] H) - (A + t • E))) :
    ContinuousOn
      (fun t : ℝ => circleRieszProjection (A + t • E) center radius)
      (Set.Icc 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  set F : Set.Icc (0 : ℝ) 1 → ℝ → (H →L[ℂ] H) := fun t θ =>
    deriv (circleMap (center : ℂ) radius) θ •
      Ring.inverse (circleMap (center : ℂ) radius θ • (1 : H →L[ℂ] H) -
        (A + (t : ℝ) • E)) with hF
  have hpencil : Continuous fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
      circleMap (center : ℂ) radius p.2 • (1 : H →L[ℂ] H) -
        (A + (p.1 : ℝ) • E) :=
    (((continuous_circleMap _ _).comp continuous_snd).smul continuous_const).sub
      (continuous_const.add
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const))
  have hderiv2 : Continuous fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
      deriv (circleMap (center : ℂ) radius) p.2 := by
    have : Continuous fun θ : ℝ => deriv (circleMap (center : ℂ) radius) θ := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 radius).mul continuous_const
    exact this.comp continuous_snd
  have hinv2 : Continuous fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
      Ring.inverse (circleMap (center : ℂ) radius p.2 • (1 : H →L[ℂ] H) -
        (A + (p.1 : ℝ) • E)) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hunit : IsUnit (circleMap (center : ℂ) radius p.2 • (1 : H →L[ℂ] H) -
        (A + (p.1 : ℝ) • E)) :=
      hres p.1 p.1.2 _ (by
        simpa [mem_sphere_iff_norm] using
          circleMap_mem_sphere (center : ℂ) hr p.2)
    have hAt : ContinuousAt Ring.inverse
        (circleMap (center : ℂ) radius p.2 • (1 : H →L[ℂ] H) -
          (A + (p.1 : ℝ) • E)) := by
      have h := NormedRing.inverse_continuousAt hunit.unit
      rwa [IsUnit.unit_spec] at h
    exact hAt.comp (f := fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
      circleMap (center : ℂ) radius p.2 • (1 : H →L[ℂ] H) -
        (A + (p.1 : ℝ) • E)) hpencil.continuousAt
  have hFcont : Continuous (Function.uncurry F) := hderiv2.smul hinv2
  have hcont :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume) (f := F) hFcont 0 (2 * Real.pi)
  exact hcont.const_smul ((2 * Real.pi * Complex.I)⁻¹ : ℂ)

end RieszCircle
end DavisKahan
end TauCeti
