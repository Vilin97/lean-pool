/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Cauchy–Pompeiu identity

For a real-linear map `L` and a direction `v`, the antiholomorphic part of `L` along `v` is `(L
v + I • L (I • v)) / 2`; for the real derivative of a function of one complex variable and `v =
1` this is the Wirtinger derivative `∂f/∂\bar z`. A real-linear map is complex-linear exactly
when all its antiholomorphic parts vanish.

The Cauchy–Pompeiu identity states that for a compactly supported `C¹` function `φ : ℂ → F`, `∫
(∂φ/∂\bar z)(w) / w = -π φ(0)`. The proof passes to polar coordinates: in the direction of the
ray the integrand is the radial derivative, whose integral over each ray is `-φ(0)`, and in the
angular direction it is the angular derivative divided by the radius, whose integral over each
circle vanishes by periodicity. No Green or Stokes theorem is used.

References: [Hörmander][Hormander1973] (1973), Theorem 1.2.1;
[Jakóbczak–Jarnicki][JakobczakJarnicki2021] (2021), Lemma 4.2.4.

## Main definitions

* `dbarAlong`: The antiholomorphic part of a real-linear map along a direction: `(L v + I • L (I •
  v)) / 2`.
* `complexLinearOfDbar`: A real-linear map whose antiholomorphic parts all vanish, as a
  complex-linear map.
* `polarRadialDeriv`: The radial derivative of `φ` at the point with polar coordinates `p`.
* `polarAngularDeriv`: The angular derivative of `φ` at the point with polar coordinates `p`,
  divided by the radius.

## Main results

* `integral_inv_smul_dbarAlong_fderiv`: **The Cauchy–Pompeiu identity.** For a compactly supported
  `C¹` function `φ : ℂ → F`, `∫ w⁻¹ • ∂φ/∂\bar z (w) = -π • φ 0`.

## References

* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public noncomputable section

open Complex MeasureTheory Set Filter
open scoped Real Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

section Dbar

/-- The antiholomorphic part of a real-linear map along a direction: `(L v + I • L (I • v)) / 2`.
For the real derivative of a function of one complex variable at `v = 1` this is `∂/∂\bar z`. -/
@[expose] def dbarAlong (L : E →L[ℝ] F) (v : E) : F := (2 : ℂ)⁻¹ • (L v + I • L (I • v))

/-- The antiholomorphic part along `v` vanishes exactly when `L` commutes with `I` on `v`. -/
theorem dbarAlong_eq_zero_iff (L : E →L[ℝ] F) (v : E) :
    dbarAlong L v = 0 ↔ L (I • v) = I • L v := by
  unfold dbarAlong
  rw [smul_eq_zero, or_iff_right (inv_ne_zero two_ne_zero)]
  constructor
  · intro h
    have h1 : L v = -(I • L (I • v)) := eq_neg_of_add_eq_zero_left h
    calc L (I • v) = -(I • I • L (I • v)) := by
          rw [smul_smul, I_mul_I, neg_one_smul, neg_neg]
      _ = I • L v := by rw [h1, smul_neg]
  · intro h
    rw [h, smul_smul, I_mul_I, neg_one_smul, add_neg_cancel]

/-- The antiholomorphic part of the zero map vanishes. -/
theorem dbarAlong_zero (v : E) : dbarAlong (0 : E →L[ℝ] F) v = 0 := by
  simp [dbarAlong]

/-- The antiholomorphic part is additive in the map. -/
theorem dbarAlong_add (L M : E →L[ℝ] F) (v : E) :
    dbarAlong (L + M) v = dbarAlong L v + dbarAlong M v := by
  simp only [dbarAlong, FunLike.coe_add, Pi.add_apply, smul_add]
  module

/-- The antiholomorphic part respects differences of maps. -/
theorem dbarAlong_sub (L M : E →L[ℝ] F) (v : E) :
    dbarAlong (L - M) v = dbarAlong L v - dbarAlong M v := by
  simp only [dbarAlong, FunLike.coe_sub, Pi.sub_apply, smul_sub]
  module

/-- The antiholomorphic part of a complex-linear map vanishes. -/
theorem dbarAlong_restrictScalars (L : E →L[ℂ] F) (v : E) :
    dbarAlong (L.restrictScalars ℝ) v = 0 := by
  rw [dbarAlong_eq_zero_iff]
  simp

/-- The antiholomorphic part of the composition of a real-linear map with a continuous linear map `T
: E →L[ℝ] F` and a complex-linear evaluation. -/
theorem dbarAlong_comp_clm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (T : F →L[ℂ] G) (L : E →L[ℝ] F) (v : E) :
    dbarAlong ((T.restrictScalars ℝ).comp L) v = T (dbarAlong L v) := by
  simp [dbarAlong, map_add, map_smul]

/-- A real-linear map whose antiholomorphic parts all vanish, as a complex-linear map. -/
@[expose] def complexLinearOfDbar (L : E →L[ℝ] F) (h : ∀ v, dbarAlong L v = 0) : E →L[ℂ] F where
  toFun := L
  map_add' := map_add L
  map_smul' := fun c v => by
    have hI : ∀ v, L (I • v) = I • L v := fun v => (dbarAlong_eq_zero_iff L v).mp (h v)
    simp only [RingHom.id_apply]
    calc L (c • v) = L ((c.re : ℝ) • v + (c.im : ℝ) • (I • v)) := by
          congr 1
          rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
      _ = c • L v := by
          rw [map_add, map_smul, map_smul, hI, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul,
            ← add_smul, Complex.re_add_im]
  cont := L.cont

/-- The complex-linear map built from vanishing antiholomorphic parts has the same underlying
function. -/
@[simp] theorem coe_complexLinearOfDbar (L : E →L[ℝ] F) (h : ∀ v, dbarAlong L v = 0) :
    ⇑(complexLinearOfDbar L h) = ⇑L := rfl

/-- Restricting scalars of `complexLinearOfDbar L h` recovers `L`. -/
theorem restrictScalars_complexLinearOfDbar (L : E →L[ℝ] F) (h : ∀ v, dbarAlong L v = 0) :
    (complexLinearOfDbar L h).restrictScalars ℝ = L := by
  ext v
  rfl

end Dbar

section Polar

/-- The radial derivative of `φ` at the point with polar coordinates `p`. -/
@[expose] def polarRadialDeriv (φ : ℂ → F) (p : ℝ × ℝ) : F :=
  fderiv ℝ φ (p.1 * exp (p.2 * I)) (exp (p.2 * I))

/-- The angular derivative of `φ` at the point with polar coordinates `p`, divided by the radius. -/
@[expose] def polarAngularDeriv (φ : ℂ → F) (p : ℝ × ℝ) : F :=
  fderiv ℝ φ (p.1 * exp (p.2 * I)) (I * exp (p.2 * I))

/-- Rotation identity for a real-linear map on `ℂ`. -/
theorem apply_exp_add_I_smul_apply_I_mul_exp (L : ℂ →L[ℝ] F) (θ : ℝ) :
    L (exp (θ * I)) + I • L (I * exp (θ * I)) = exp (-(θ * I)) • (L 1 + I • L I) := by
  have h1 : exp (θ * I) = (Real.cos θ) • (1 : ℂ) + (Real.sin θ) • I := by
    rw [exp_mul_I]
    simp [Complex.real_smul]
  have h2 : I * exp (θ * I) = (-Real.sin θ) • (1 : ℂ) + (Real.cos θ) • I := by
    rw [exp_mul_I]
    simp only [Complex.real_smul, ofReal_neg]
    ring_nf
    simp [I_sq]
    ring
  have h3 : exp (-(θ * I)) = (cos (θ : ℂ) - sin (θ : ℂ) * I) := by
    rw [← neg_mul, ← ofReal_neg, exp_mul_I]
    simp [Complex.ofReal_neg]
    ring
  rw [h2, h1, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h3]
  simp only [← Complex.coe_smul, ofReal_neg, ofReal_cos, ofReal_sin]
  match_scalars <;> first
    | ring1
    | linear_combination (Complex.sin θ) * I_sq

/-- The polar-coordinate form of the Cauchy–Pompeiu integrand. -/
theorem smul_inv_smul_dbarAlong_polar (φ : ℂ → F) {r θ : ℝ} (hr : 0 < r) :
    r • ((Complex.polarCoord.symm (r, θ))⁻¹ • dbarAlong (fderiv ℝ φ (Complex.polarCoord.symm (r,
      θ))) 1) =
      (2 : ℂ)⁻¹ • (polarRadialDeriv φ (r, θ) + I • polarAngularDeriv φ (r, θ)) := by
  have hw : Complex.polarCoord.symm (r, θ) = r * exp (θ * I) := by
    rw [Complex.polarCoord_symm_apply, exp_mul_I]
    push_cast
    ring
  rw [hw]
  have hinv : ((r : ℂ) * exp (θ * I))⁻¹ = (r : ℂ)⁻¹ * exp (-(θ * I)) := by
    rw [mul_inv, ← exp_neg]
  rw [hinv, polarRadialDeriv, polarAngularDeriv]
  simp only
  rw [apply_exp_add_I_smul_apply_I_mul_exp, dbarAlong]
  simp only [smul_eq_mul, mul_one]
  rw [← Complex.coe_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

/-- The radial derivative of a `C¹` function is continuous in polar coordinates. -/
theorem continuous_polarRadialDeriv {φ : ℂ → F} (hφ : ContDiff ℝ 1 φ) :
    Continuous (polarRadialDeriv φ) := by
  unfold polarRadialDeriv
  exact ((hφ.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply (by fun_prop)

/-- The angular derivative of a `C¹` function is continuous in polar coordinates. -/
theorem continuous_polarAngularDeriv {φ : ℂ → F} (hφ : ContDiff ℝ 1 φ) :
    Continuous (polarAngularDeriv φ) := by
  unfold polarAngularDeriv
  exact ((hφ.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply (by fun_prop)

/-- The real derivative vanishes at points whose modulus exceeds the support radius. -/
theorem fderiv_eq_zero_of_norm_gt {φ : ℂ → F} {R : ℝ} (hR : tsupport φ ⊆ Metric.closedBall 0 R)
    {w : ℂ} (hw : R < ‖w‖) : fderiv ℝ φ w = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have := hR (tsupport_fderiv_subset ℝ h)
  rw [Metric.mem_closedBall, dist_zero_right] at this
  exact absurd this (not_le.mpr hw)

/-- A uniform bound on the derivative bounds the radial derivative. -/
theorem norm_polarRadialDeriv_le {φ : ℂ → F} {C : ℝ} (hC : ∀ w, ‖fderiv ℝ φ w‖ ≤ C) (p : ℝ × ℝ) :
    ‖polarRadialDeriv φ p‖ ≤ C := by
  unfold polarRadialDeriv
  calc ‖fderiv ℝ φ (p.1 * exp (p.2 * I)) (exp (p.2 * I))‖
      ≤ ‖fderiv ℝ φ (p.1 * exp (p.2 * I))‖ * ‖exp (p.2 * I)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C := by rw [norm_exp_ofReal_mul_I, mul_one]; exact hC _

/-- A uniform bound on the derivative bounds the angular derivative. -/
theorem norm_polarAngularDeriv_le {φ : ℂ → F} {C : ℝ} (hC : ∀ w, ‖fderiv ℝ φ w‖ ≤ C) (p : ℝ × ℝ) :
    ‖polarAngularDeriv φ p‖ ≤ C := by
  unfold polarAngularDeriv
  calc ‖fderiv ℝ φ (p.1 * exp (p.2 * I)) (I * exp (p.2 * I))‖
      ≤ ‖fderiv ℝ φ (p.1 * exp (p.2 * I))‖ * ‖I * exp (p.2 * I)‖ := ContinuousLinearMap.le_opNorm
        _ _
    _ ≤ C := by rw [norm_mul, norm_I, norm_exp_ofReal_mul_I, one_mul, mul_one]; exact hC _

/-- The modulus of `r e^{iθ}` is `|r|`. -/
theorem norm_mul_exp_ofReal_mul_I (r θ : ℝ) : ‖(r : ℂ) * exp (θ * I)‖ = |r| := by
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The radial derivative vanishes beyond the support radius. -/
theorem polarRadialDeriv_eq_zero {φ : ℂ → F} {R : ℝ} (hR : tsupport φ ⊆ Metric.closedBall 0 R)
    {p : ℝ × ℝ} (hp : R < |p.1|) : polarRadialDeriv φ p = 0 := by
  unfold polarRadialDeriv
  rw [fderiv_eq_zero_of_norm_gt hR (by rwa [norm_mul_exp_ofReal_mul_I])]
  rfl

/-- The angular derivative vanishes beyond the support radius. -/
theorem polarAngularDeriv_eq_zero {φ : ℂ → F} {R : ℝ} (hR : tsupport φ ⊆ Metric.closedBall 0 R)
    {p : ℝ × ℝ} (hp : R < |p.1|) : polarAngularDeriv φ p = 0 := by
  unfold polarAngularDeriv
  rw [fderiv_eq_zero_of_norm_gt hR (by rwa [norm_mul_exp_ofReal_mul_I])]
  rfl

omit [NormedSpace ℂ F] in
/-- A bounded continuous function on the polar-coordinate rectangle vanishing beyond a radius is
integrable on the polar target. -/
theorem integrableOn_polarCoord_target_of_bound {A : ℝ × ℝ → F} (hA : Continuous A) {C R : ℝ}
    (hC : ∀ p, ‖A p‖ ≤ C) (hzero : ∀ p : ℝ × ℝ, R < |p.1| → A p = 0) :
    IntegrableOn A polarCoord.target := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hg : Integrable ((Icc (0 : ℝ) R ×ˢ Icc (-π) π).indicator fun _ => C) :=
    (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  refine Integrable.mono' hg.integrableOn hA.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem polarCoord.open_target.measurableSet fun p hp => ?_
  rw [polarCoord_target] at hp
  by_cases h : p.1 ≤ R
  · rw [indicator_of_mem (show p ∈ Icc (0 : ℝ) R ×ˢ Icc (-π) π from
      ⟨⟨hp.1.le, h⟩, hp.2.1.le, hp.2.2.le⟩)]
    exact hC p
  · rw [hzero p (by rw [abs_of_pos hp.1]; exact not_le.mp h), norm_zero]
    exact indicator_nonneg (fun _ _ => hC0) p

omit [NormedSpace ℂ F] in
/-- A continuous function on the half-line vanishing beyond a radius is integrable there. -/
theorem integrableOn_Ioi_of_continuous_of_eq_zero {g : ℝ → F} (hg : Continuous g) {R : ℝ}
    (hz : ∀ r, R < r → g r = 0) : IntegrableOn g (Ioi 0) := by
  have h1 : IntegrableOn g (Icc 0 R) := hg.continuousOn.integrableOn_Icc
  have h2 : IntegrableOn g (Ioi R) :=
    ((integrable_zero _ _ _).integrableOn).congr_fun (fun r hr => (hz r hr).symm) measurableSet_Ioi
  refine (h1.union h2).mono_set fun r hr => ?_
  rcases le_or_gt r R with h | h
  · exact Or.inl ⟨le_of_lt hr, h⟩
  · exact Or.inr h

variable [CompleteSpace F]

/-- The radial integral of the radial derivative along a ray is `-φ 0`. -/
theorem integral_Ioi_polarRadialDeriv {φ : ℂ → F} (hφ : ContDiff ℝ 1 φ) {R : ℝ}
    (hR : tsupport φ ⊆ Metric.closedBall 0 R) (θ : ℝ) :
    ∫ r in Ioi (0 : ℝ), polarRadialDeriv φ (r, θ) = -φ 0 := by
  have hderiv : ∀ r ∈ Ici (0 : ℝ),
      HasDerivAt (fun r : ℝ => φ (r * exp (θ * I))) (polarRadialDeriv φ (r, θ)) r := by
    intro r _
    have h1 : HasDerivAt (fun r : ℝ => (r : ℂ) * exp (θ * I)) (exp (θ * I)) r := by
      simpa using (hasDerivAt_id r).ofReal_comp.mul_const (exp (θ * I))
    exact (hφ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt r h1
  have hint : IntegrableOn (fun r : ℝ => polarRadialDeriv φ (r, θ)) (Ioi 0) := by
    refine integrableOn_Ioi_of_continuous_of_eq_zero (R := R)
      ((continuous_polarRadialDeriv hφ).comp (by fun_prop)) fun r hr => ?_
    exact polarRadialDeriv_eq_zero hR (lt_of_lt_of_le hr (le_abs_self r))
  have hlim : Tendsto (fun r : ℝ => φ (r * exp (θ * I))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ((eventually_gt_atTop R).mono fun r hr => ?_)
    symm
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have := hR h
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul_exp_ofReal_mul_I] at this
    exact absurd (lt_of_lt_of_le hr (le_abs_self r)) (not_lt.mpr this)
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  simpa using this

/-- The angular integral of the angular derivative around a circle vanishes. -/
theorem integral_Ioo_polarAngularDeriv {φ : ℂ → F} (hφ : ContDiff ℝ 1 φ) {r : ℝ} (hr : 0 < r) :
    ∫ θ in Ioo (-π) π, polarAngularDeriv φ (r, θ) = 0 := by
  have hderiv : ∀ θ ∈ uIcc (-π) π,
      HasDerivAt (fun θ : ℝ => φ (r * exp (θ * I))) (r • polarAngularDeriv φ (r, θ)) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => (r : ℂ) * exp (θ * I)) ((r : ℂ) * (exp (θ * I) * I)) θ := by
      simpa using ((hasDerivAt_id θ).ofReal_comp.mul_const I).cexp.const_mul (r : ℂ)
    refine ((hφ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt θ h1).congr_deriv ?_
    unfold polarAngularDeriv
    rw [show (r : ℂ) * (exp (θ * I) * I) = r • (I * exp (θ * I)) by
      rw [Complex.real_smul]; ring, map_smul]
  have hcont : IntervalIntegrable (fun θ : ℝ => r • polarAngularDeriv φ (r, θ)) volume (-π) π :=
    (((continuous_polarAngularDeriv hφ).comp (by fun_prop)).const_smul r).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
  have hzero : φ (r * exp (π * I)) - φ (r * exp ((-π : ℝ) * I)) = 0 := by
    rw [show ((-π : ℝ) : ℂ) * I = -(π * I) by push_cast; ring, exp_neg, exp_pi_mul_I]
    simp
  rw [hzero, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo, integral_smul] at hftc
  exact (smul_eq_zero.mp hftc).resolve_left hr.ne'

/-- **The Cauchy–Pompeiu identity.** For a compactly supported `C¹` function `φ : ℂ → F`,
`∫ w⁻¹ • ∂φ/∂\bar z (w) = -π • φ 0`. -/
theorem integral_inv_smul_dbarAlong_fderiv {φ : ℂ → F} (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) :
    ∫ w, w⁻¹ • dbarAlong (fderiv ℝ φ w) 1 = -((π : ℂ) • φ 0) := by
  obtain ⟨R, hR⟩ := hsupp.isBounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := (hsupp.fderiv ℝ).exists_bound_of_continuous (hφ.continuous_fderiv one_ne_zero)
  have hAi : IntegrableOn (polarRadialDeriv φ) polarCoord.target :=
    integrableOn_polarCoord_target_of_bound (continuous_polarRadialDeriv hφ)
      (norm_polarRadialDeriv_le hC) fun p hp => polarRadialDeriv_eq_zero hR hp
  have hBi : IntegrableOn (polarAngularDeriv φ) polarCoord.target :=
    integrableOn_polarCoord_target_of_bound (continuous_polarAngularDeriv hφ)
      (norm_polarAngularDeriv_le hC) fun p hp => polarAngularDeriv_eq_zero hR hp
  rw [← Complex.integral_comp_polarCoord_symm]
  have hpt : EqOn (fun p : ℝ × ℝ => p.1 • ((Complex.polarCoord.symm p)⁻¹ •
      dbarAlong (fderiv ℝ φ (Complex.polarCoord.symm p)) 1))
      (fun p => (2 : ℂ)⁻¹ • (polarRadialDeriv φ p + I • polarAngularDeriv φ p))
      polarCoord.target := by
    rintro ⟨r, θ⟩ hp
    rw [polarCoord_target] at hp
    exact smul_inv_smul_dbarAlong_polar φ hp.1
  have hBi2 : Integrable (fun p => I • polarAngularDeriv φ p) (volume.restrict polarCoord.target) :=
    hBi.smul I
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hpt, integral_smul,
    integral_add hAi hBi2, integral_smul]
  have hA_int : ∫ p in polarCoord.target, polarRadialDeriv φ p = -((2 * π : ℝ) • φ 0) := by
    have hAi' : Integrable (polarRadialDeriv φ)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
      rwa [Measure.prod_restrict, ← Measure.volume_eq_prod, ← polarCoord_target]
    rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
      integral_prod_symm _ hAi']
    simp_rw [integral_Ioi_polarRadialDeriv hφ hR]
    rw [setIntegral_const, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_neg]
    congr 2
    ring
  have hB_int : ∫ p in polarCoord.target, polarAngularDeriv φ p = 0 := by
    have hBi' : Integrable (polarAngularDeriv φ)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
      rwa [Measure.prod_restrict, ← Measure.volume_eq_prod, ← polarCoord_target]
    rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hBi']
    exact setIntegral_eq_zero_of_forall_eq_zero fun r hr => integral_Ioo_polarAngularDeriv hφ hr
  rw [hA_int, hB_int, smul_zero, add_zero, ← Complex.coe_smul, smul_neg, smul_smul]
  congr 2
  push_cast
  field_simp

end Polar

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
