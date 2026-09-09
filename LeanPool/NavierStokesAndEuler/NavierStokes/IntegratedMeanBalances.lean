/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TransportPrimitive
public import LeanPool.NavierStokesAndEuler.NavierStokes.PressureStream
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-!
# Integrated tangential balances from actual radial differential expressions

All moments below are actual Bochner integrals. Compact radial support supplies
the boundary cancellations, and parameter derivatives pass under integrals by
the dominated differentiation theorem in `TransportPrimitive`.
-/

noncomputable section

namespace NavierStokes.IntegratedMeanBalances

open Set Function MeasureTheory Filter
open scoped ContDiff Topology Interval

noncomputable def moment (n : ℕ) (f : ℝ → ℝ) : ℝ := ∫ r, r ^ n * f r

theorem weighted_integrable {f : ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) (n : ℕ) : Integrable (fun r => r ^ n * f r) :=
  ((continuous_id.pow n).mul hf).integrable_of_hasCompactSupport hs.mul_left

theorem moment_add {f g : ℝ → ℝ} (n : ℕ)
    (hf : Integrable (fun r => r ^ n * f r))
    (hg : Integrable (fun r => r ^ n * g r)) :
    moment n (fun r => f r + g r) = moment n f + moment n g := by
  simp only [moment, mul_add]
  exact integral_add hf hg

theorem moment_sub {f g : ℝ → ℝ} (n : ℕ)
    (hf : Integrable (fun r => r ^ n * f r))
    (hg : Integrable (fun r => r ^ n * g r)) :
    moment n (fun r => f r - g r) = moment n f - moment n g := by
  simp only [moment, mul_sub]
  exact integral_sub hf hg

theorem moment_const_mul (n : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    moment n (fun r => c * f r) = c * moment n f := by
  simp only [moment, ← mul_assoc, mul_comm _ c]
  simp only [mul_assoc, integral_const_mul]

theorem moment_mul_const (n : ℕ) (f : ℝ → ℝ) (c : ℝ) :
    moment n (fun r => f r * c) = moment n f * c := by
  simp only [moment, ← mul_assoc, integral_mul_const]

theorem deriv_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (deriv f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem ae_radial_ne_zero : ∀ᵐ r : ℝ, r ≠ 0 := by
  simpa only [mem_singleton_iff] using (countable_singleton (0 : ℝ)).ae_notMem volume

theorem integral_deriv_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : (∫ r, deriv f r) = 0 :=
  integral_eq_zero_of_hasDerivAt_of_integrable
    (fun r => (hf.differentiable (by simp) r).hasDerivAt)
    ((deriv_smooth hf).continuous.integrable_of_hasCompactSupport hs.deriv)
    (hf.continuous.integrable_of_hasCompactSupport hs)

/-- Weighted integration by parts; compact support supplies both endpoint terms. -/
theorem moment_deriv_succ {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (n : ℕ) :
    moment (n + 1) (deriv f) = -((n + 1 : ℕ) : ℝ) * moment n f := by
  have hd : ∀ r : ℝ, HasDerivAt (fun s : ℝ => s ^ (n + 1))
      (((n + 1 : ℕ) : ℝ) * r ^ n) r := by
    intro r
    simpa using (hasDerivAt_id r).fun_pow (n + 1)
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable (fun r _ => hd r)
    (fun r _ => (hf.differentiable (by simp) r).hasDerivAt)
    (weighted_integrable (deriv_smooth hf).continuous hs.deriv (n + 1))
    (by
      change Integrable (fun r => (((n + 1 : ℕ) : ℝ) * r ^ n) * f r)
      simpa only [mul_assoc] using
        (weighted_integrable hf.continuous hs n).const_mul ((n + 1 : ℕ) : ℝ))
    (weighted_integrable hf.continuous hs (n + 1))
  simpa only [moment, Pi.mul_apply, mul_assoc, integral_const_mul, neg_mul] using hi

noncomputable def radialDivergence (c : ℝ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv f r + c / r * f r

noncomputable def angularRadialViscosity (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv f) r + deriv f r / r - f r / r ^ 2

noncomputable def axialRadialViscosity (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv f) r + deriv f r / r

theorem weighted_angular_divergence_ae (f : ℝ → ℝ) :
    (fun r => r ^ 2 * radialDivergence 2 f r) =ᵐ[volume]
      (fun r => r ^ 2 * deriv f r + 2 * (r * f r)) := by
  filter_upwards [ae_radial_ne_zero] with r hr
  unfold radialDivergence
  field_simp [hr]

theorem weighted_axial_divergence_ae (f : ℝ → ℝ) :
    (fun r => r * radialDivergence 1 f r) =ᵐ[volume]
      (fun r => r * deriv f r + f r) := by
  filter_upwards [ae_radial_ne_zero] with r hr
  unfold radialDivergence
  field_simp [hr]

theorem angular_divergence_integrable {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : Integrable (fun r => r ^ 2 * radialDivergence 2 f r) := by
  apply Integrable.congr _ (weighted_angular_divergence_ae f).symm
  have h := (weighted_integrable (deriv_smooth hf).continuous hs.deriv 2).add
    ((weighted_integrable hf.continuous hs 1).const_mul 2)
  simp only [pow_one] at h
  exact h

theorem axial_divergence_integrable {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : Integrable (fun r => r * radialDivergence 1 f r) := by
  apply Integrable.congr _ (weighted_axial_divergence_ae f).symm
  have h := (weighted_integrable (deriv_smooth hf).continuous hs.deriv 1).add
    (hf.continuous.integrable_of_hasCompactSupport hs)
  simp only [pow_one] at h
  exact h

theorem moment_angular_divergence {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : moment 2 (radialDivergence 2 f) = 0 := by
  have hi1 := weighted_integrable (deriv_smooth hf).continuous hs.deriv 2
  have hi2 : Integrable (fun r => 2 * (r * f r)) := by
    simpa only [pow_one] using (weighted_integrable hf.continuous hs 1).const_mul 2
  unfold moment
  rw [integral_congr_ae (weighted_angular_divergence_ae f), integral_add hi1 hi2,
    integral_const_mul]
  have hb := moment_deriv_succ hf hs 1
  norm_num [moment] at hb
  linarith

theorem moment_axial_divergence {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : moment 1 (radialDivergence 1 f) = 0 := by
  have hi1 : Integrable (fun r => r * deriv f r) := by
    simpa only [pow_one] using weighted_integrable (deriv_smooth hf).continuous hs.deriv 1
  have hi2 : Integrable f := hf.continuous.integrable_of_hasCompactSupport hs
  simp only [moment, pow_one]
  rw [integral_congr_ae (weighted_axial_divergence_ae f), integral_add hi1 hi2]
  have hb := moment_deriv_succ hf hs 0
  norm_num [moment] at hb
  linarith

/-- The radial pressure moment follows from the actual derivative equation. -/
theorem pressure_moment {p g : ℝ → ℝ} (hp : ContDiff ℝ ∞ p)
    (hs : HasCompactSupport p) (hd : ∀ r, deriv p r = g r) :
    moment 1 p = -(1 / 2 : ℝ) * moment 2 g := by
  have hb := moment_deriv_succ hp hs 1
  rw [show deriv p = g from funext hd] at hb
  norm_num at hb
  linarith

theorem pressure_moment_reconstructed {p g ρ : ℝ → ℝ} (P : ℝ)
    (hp : ContDiff ℝ ∞ p) (hsp : HasCompactSupport p)
    (hg : Continuous g) (hsg : HasCompactSupport g)
    (hρ : Continuous ρ) (hsρ : HasCompactSupport ρ)
    (hd : ∀ r, deriv p r = g r - ρ r * P) :
    moment 1 p = -(1 / 2 : ℝ) * moment 2 g + (moment 2 ρ / 2) * P := by
  rw [pressure_moment hp hsp hd,
    moment_sub 2 (weighted_integrable hg hsg 2)
      (by simpa only [mul_assoc] using
        (weighted_integrable hρ hsρ 2).mul_const P), moment_mul_const]
  ring

theorem weighted_angular_viscosity_ae (f : ℝ → ℝ) :
    (fun r => r ^ 2 * angularRadialViscosity f r) =ᵐ[volume]
      (fun r => r ^ 2 * deriv (deriv f) r + r * deriv f r - f r) := by
  filter_upwards [ae_radial_ne_zero] with r hr
  unfold angularRadialViscosity
  field_simp [hr]

theorem weighted_axial_viscosity_ae (f : ℝ → ℝ) :
    (fun r => r * axialRadialViscosity f r) =ᵐ[volume]
      (fun r => r * deriv (deriv f) r + deriv f r) := by
  filter_upwards [ae_radial_ne_zero] with r hr
  unfold axialRadialViscosity
  field_simp [hr]

theorem angular_viscosity_integrable {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : Integrable (fun r => r ^ 2 * angularRadialViscosity f r) := by
  apply Integrable.congr _ (weighted_angular_viscosity_ae f).symm
  have h1 : Integrable (fun r => r * deriv f r) := by
    simpa only [pow_one] using weighted_integrable (deriv_smooth hf).continuous hs.deriv 1
  exact ((weighted_integrable (deriv_smooth (deriv_smooth hf)).continuous hs.deriv.deriv 2).add
    h1).sub (hf.continuous.integrable_of_hasCompactSupport hs)

theorem axial_viscosity_integrable {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : Integrable (fun r => r * axialRadialViscosity f r) := by
  apply Integrable.congr _ (weighted_axial_viscosity_ae f).symm
  have h1 : Integrable (fun r => r * deriv (deriv f) r) := by
    simpa only [pow_one] using
      weighted_integrable (deriv_smooth (deriv_smooth hf)).continuous hs.deriv.deriv 1
  exact h1.add ((deriv_smooth hf).continuous.integrable_of_hasCompactSupport hs.deriv)

theorem moment_angular_viscosity {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : moment 2 (angularRadialViscosity f) = 0 := by
  have hi2 := weighted_integrable (deriv_smooth (deriv_smooth hf)).continuous hs.deriv.deriv 2
  have hi1 : Integrable (fun r => r * deriv f r) := by
    simpa only [pow_one] using weighted_integrable (deriv_smooth hf).continuous hs.deriv 1
  have hi0 : Integrable f := hf.continuous.integrable_of_hasCompactSupport hs
  have his : Integrable (fun r => r ^ 2 * deriv (deriv f) r + r * deriv f r) := hi2.add hi1
  unfold moment
  rw [integral_congr_ae (weighted_angular_viscosity_ae f),
    integral_sub his hi0, integral_add hi2 hi1]
  have h2 := moment_deriv_succ (deriv_smooth hf) hs.deriv 1
  have h1 := moment_deriv_succ hf hs 0
  norm_num [moment] at h1 h2
  linarith

theorem moment_axial_viscosity {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : moment 1 (axialRadialViscosity f) = 0 := by
  have hi1 : Integrable (fun r => r * deriv (deriv f) r) := by
    simpa only [pow_one] using
      weighted_integrable (deriv_smooth (deriv_smooth hf)).continuous hs.deriv.deriv 1
  have hi0 : Integrable (deriv f) :=
    (deriv_smooth hf).continuous.integrable_of_hasCompactSupport hs.deriv
  simp only [moment, pow_one]
  rw [integral_congr_ae (weighted_axial_viscosity_ae f), integral_add hi1 hi0]
  have h1 := moment_deriv_succ (deriv_smooth hf) hs.deriv 0
  norm_num [moment] at h1
  linarith

theorem positive_integral_eq_integral {a b : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hs : support f ⊆ Icc a b) : (∫ r in Ioi (0 : ℝ), f r) = ∫ r, f r := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro r hr
  by_contra hf
  exact hr (ha.trans_le (hs hf).1)

/-! ## Smooth compact radial families and their moments -/

section Families

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def radialMoment (n : ℕ) (F : ℝ × P → ℝ) (p : P) : ℝ :=
  moment n (fun r => F (r, p))

noncomputable def parameterPartial (v : P) (F : ℝ × P → ℝ) (x : ℝ × P) : ℝ :=
  fderiv ℝ F x (0, v)

theorem parameterPartial_smooth (v : P) {F : ℝ × P → ℝ}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (parameterPartial v F) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem parameterPartial_supported (v : P) {a b : ℝ} {F : ℝ × P → ℝ}
    (hs : RadialAlias.RadiallySupported a b F) :
    RadialAlias.RadiallySupported a b (parameterPartial v F) :=
  RadialAlias.radialSupport_fderiv_apply hs (0, v)

theorem radial_slice_smooth {F : ℝ × P → ℝ} (hF : ContDiff ℝ ∞ F) (p : P) :
    ContDiff ℝ ∞ (fun r => F (r, p)) :=
  hF.comp (contDiff_id.prodMk contDiff_const)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem radial_slice_compact {a b : ℝ} {F : ℝ × P → ℝ}
    (hs : RadialAlias.RadiallySupported a b F) (p : P) :
    HasCompactSupport (fun r => F (r, p)) :=
  HasCompactSupport.intro isCompact_Icc (fun r hr => by
    by_contra h
    exact hr (hs h))

omit [NormedSpace ℝ P] in
theorem radialMoment_eq_interval {a b : ℝ} {F : ℝ × P → ℝ}
    (hF : Continuous F) (hs : RadialAlias.RadiallySupported a b F) (n : ℕ) (p : P) :
    radialMoment n F p = ∫ r in a..b, r ^ n * F (r, p) := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  have hc : Continuous (fun r => r ^ n * F (r, p)) :=
    (continuous_id.pow n).mul (hF.comp (continuous_id.prodMk continuous_const))
  have hsp : support (fun r => r ^ n * F (r, p)) ⊆ Icc a b := by
    intro r hr
    exact hs (right_ne_zero_of_mul hr)
  have hi : support (fun r => r ^ n * F (r, p)) ⊆ Ioo a b := by
    simpa only [interior_Icc] using hc.isOpen_support.subset_interior_iff.mpr hsp
  exact hi.trans Ioo_subset_Ioc_self

theorem parameterIntegral_fderiv_apply {F : P × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (a b : ℝ) (p v : P) :
    fderiv ℝ (fun q => ∫ r in a..b, F (q, r)) p v =
      ∫ r in a..b, fderiv ℝ F (p, r) (v, 0) := by
  rw [(TransportPrimitive.parameterIntegral_hasFDerivAt (g := F) hF a b p).fderiv,
    ContinuousLinearMap.intervalIntegral_apply]
  · rfl
  · exact ((TransportPrimitive.parameterDerivative_contDiff hF).continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable a b

theorem weighted_swap_smooth {F : ℝ × P → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (fun x : P × ℝ => x.2 ^ n * F (x.2, x.1)) :=
  (contDiff_snd.pow n).mul (hF.comp (contDiff_snd.prodMk contDiff_fst))

theorem radialMoment_smooth {a b : ℝ} {F : ℝ × P → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported a b F) (n : ℕ) :
    ContDiff ℝ ∞ (radialMoment n F) := by
  have he : radialMoment n F = (fun p => ∫ r in a..b, r ^ n * F (r, p)) :=
    funext (radialMoment_eq_interval hF.continuous hs n)
  rw [he]
  exact TransportPrimitive.parameterIntegral_contDiff
    (g := fun x : P × ℝ => x.2 ^ n * F (x.2, x.1)) (weighted_swap_smooth hF n) a b

theorem radialMoment_parameterPartial {a b : ℝ} {F : ℝ × P → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported a b F) (n : ℕ) (p v : P) :
    fderiv ℝ (radialMoment n F) p v = radialMoment n (parameterPartial v F) p := by
  have he : radialMoment n F = (fun q => ∫ r in a..b, r ^ n * F (r, q)) :=
    funext (radialMoment_eq_interval hF.continuous hs n)
  rw [he, parameterIntegral_fderiv_apply (weighted_swap_smooth hF n),
    radialMoment_eq_interval (parameterPartial_smooth v hF).continuous
      (parameterPartial_supported v hs)]
  apply intervalIntegral.integral_congr
  intro r _
  have hslice : HasFDerivAt (fun q : P => r ^ n * F (r, q))
      ((r ^ n) • (fderiv ℝ F (r, p)).comp (ContinuousLinearMap.inr ℝ ℝ P)) p := by
    exact (((hF.differentiable (by simp)) (r, p)).hasFDerivAt.comp p
      (hasFDerivAt_prodMk_right r p)).const_mul (r ^ n)
  have heq := (TransportPrimitive.parameter_hasFDerivAt
    (g := fun x : P × ℝ => x.2 ^ n * F (x.2, x.1))
    (weighted_swap_smooth hF n) p r).unique hslice
  exact congrArg (fun L : P →L[ℝ] ℝ => L v) heq

theorem zero_mass_parameterPartial {a b : ℝ} {F : ℝ × P → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported a b F) (n : ℕ)
    (hm : radialMoment n F = 0) (p v : P) :
    radialMoment n (parameterPartial v F) p = 0 := by
  rw [← radialMoment_parameterPartial hF hs n p v, hm]
  simp

theorem zero_mass_parameterPartial_twice {a b : ℝ} {F : ℝ × P → ℝ} (hF : ContDiff ℝ ∞ F)
    (hs : RadialAlias.RadiallySupported a b F) (n : ℕ)
    (hm : radialMoment n F = 0) (p v w : P) :
    radialMoment n (parameterPartial w (parameterPartial v F)) p = 0 := by
  apply zero_mass_parameterPartial (parameterPartial_smooth v hF)
    (parameterPartial_supported v hs) n _ p w
  funext q
  exact zero_mass_parameterPartial hF hs n hm q v

end Families

/-! ## Actual torus averages annihilate the lift derivatives -/

section Torus

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def torusInner (F : (P × ℝ) × ℝ → ℝ) (q : P × ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, F (q, x)

noncomputable def torusAverage (F : (P × ℝ) × ℝ → ℝ) (p : P) : ℝ :=
  ∫ y in (0 : ℝ)..1, torusInner F (p, y)

noncomputable def fixedPartial (v : (P × ℝ) × ℝ) (F : (P × ℝ) × ℝ → ℝ)
    (q : (P × ℝ) × ℝ) : ℝ := fderiv ℝ F q v

noncomputable def slowPartial (v : P) (F : (P × ℝ) × ℝ → ℝ) : (P × ℝ) × ℝ → ℝ :=
  fixedPartial ((v, 0), 0) F

noncomputable def torusPartial (v : ℝ × ℝ) (F : (P × ℝ) × ℝ → ℝ) : (P × ℝ) × ℝ → ℝ :=
  fixedPartial ((0, v.2), v.1) F

structure TorusPeriodic (F : (P × ℝ) × ℝ → ℝ) : Prop where
  first : ∀ q, F (q + ((0, 0), 1)) = F q
  second : ∀ q, F (q + ((0, 1), 0)) = F q

theorem fixedPartial_smooth (v : (P × ℝ) × ℝ) {F : (P × ℝ) × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (fixedPartial v F) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem fixedPartial_periodic (v : (P × ℝ) × ℝ) {F : (P × ℝ) × ℝ → ℝ}
    (hp : TorusPeriodic F) : TorusPeriodic (fixedPartial v F) := by
  constructor
  · intro q
    have he : (fun x => F (x + ((0, 0), 1))) = F := funext hp.first
    have hd := congrArg (fun f => fderiv ℝ f q) he
    rw [fderiv_comp_add_right] at hd
    exact congrArg (fun L : ((P × ℝ) × ℝ) →L[ℝ] ℝ => L v) hd
  · intro q
    have he : (fun x => F (x + ((0, 1), 0))) = F := funext hp.second
    have hd := congrArg (fun f => fderiv ℝ f q) he
    rw [fderiv_comp_add_right] at hd
    exact congrArg (fun L : ((P × ℝ) × ℝ) →L[ℝ] ℝ => L v) hd

theorem torusInner_smooth {F : (P × ℝ) × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (torusInner F) :=
  TransportPrimitive.parameterIntegral_contDiff (g := F) hF 0 1

theorem torusAverage_smooth {F : (P × ℝ) × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (torusAverage F) :=
  TransportPrimitive.parameterIntegral_contDiff (g := torusInner F) (torusInner_smooth hF) 0 1

/-- Both parameter-integral interchanges are proved from joint smoothness on
the compact torus coordinate square. -/
theorem torusAverage_fderiv {F : (P × ℝ) × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (p v : P) :
    fderiv ℝ (torusAverage F) p v = torusAverage (slowPartial v F) p := by
  rw [show torusAverage F = (fun p => ∫ y in (0 : ℝ)..1, torusInner F (p, y)) from rfl,
    parameterIntegral_fderiv_apply (torusInner_smooth hF) 0 1 p v]
  apply intervalIntegral.integral_congr
  intro y _
  exact parameterIntegral_fderiv_apply hF 0 1 (p, y) (v, 0)

theorem torusAverage_add {F G : (P × ℝ) × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (p : P) :
    torusAverage (fun q => F q + G q) p = torusAverage F p + torusAverage G p := by
  have he : torusInner (fun q => F q + G q) = (fun q => torusInner F q + torusInner G q) := by
    funext q
    exact intervalIntegral.integral_add
      ((hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
      ((hG.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
  unfold torusAverage
  rw [he]
  exact intervalIntegral.integral_add
    (((torusInner_smooth hF).continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
    (((torusInner_smooth hG).continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem torusAverage_coeff_mul (a : P → ℝ) (F : (P × ℝ) × ℝ → ℝ) (p : P) :
    torusAverage (fun q => a q.1.1 * F q) p = a p * torusAverage F p := by
  simp only [torusAverage, torusInner, intervalIntegral.integral_const_mul]

theorem torusAverage_first_zero {F : (P × ℝ) × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hp : TorusPeriodic F) (p : P) :
    torusAverage (fixedPartial ((0, 0), 1) F) p = 0 := by
  have hi : ∀ y, torusInner (fixedPartial ((0, 0), 1) F) (p, y) = 0 := by
    intro y
    have hd : ∀ x, HasDerivAt (fun s => F ((p, y), s))
        (fixedPartial ((0, 0), 1) F ((p, y), x)) x := by
      intro x
      exact ((hF.differentiable (by simp)) ((p, y), x)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_const x (p, y)).prodMk (hasDerivAt_id x))
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (((fixedPartial_smooth ((0, 0), 1) hF).continuous.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
    have he : F ((p, y), 1) = F ((p, y), 0) := by
      simpa only [Prod.add_def, add_zero, zero_add] using hp.first ((p, y), 0)
    rw [he, sub_self] at hftc
    exact hftc
  simp only [torusAverage, hi, intervalIntegral.integral_zero]

theorem torusAverage_second_zero {F : (P × ℝ) × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hp : TorusPeriodic F) (p : P) :
    torusAverage (fixedPartial ((0, 1), 0) F) p = 0 := by
  have hd : ∀ y, HasDerivAt (fun s => torusInner F (p, s))
      (torusInner (fixedPartial ((0, 1), 0) F) (p, y)) y := by
    intro y
    have hh := (((torusInner_smooth hF).differentiable (by simp)) (p,
      y)).hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y p).prodMk (hasDerivAt_id y))
    have he := parameterIntegral_fderiv_apply hF 0 1 (p, y) (0, 1)
    change fderiv ℝ (torusInner F) (p, y) (0, 1) =
      torusInner (fixedPartial ((0, 1), 0) F) (p, y) at he
    rw [he] at hh
    exact hh
  have hc : IntervalIntegrable
      (fun y => torusInner (fixedPartial ((0, 1), 0) F) (p, y)) volume 0 1 :=
    ((torusInner_smooth (fixedPartial_smooth ((0, 1), 0) hF)).continuous.comp
    (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) hc
  have he : torusInner F (p, 1) = torusInner F (p, 0) := by
    apply intervalIntegral.integral_congr
    intro x _
    simpa only [Prod.add_def, add_zero, zero_add] using hp.second ((p, 0), x)
  simpa only [torusAverage, he, sub_self] using hftc

theorem torusPartial_decompose (v : ℝ × ℝ) (F : (P × ℝ) × ℝ → ℝ) :
    torusPartial v F = (fun q => v.1 * fixedPartial ((0, 0), 1) F q +
      v.2 * fixedPartial ((0, 1), 0) F q) := by
  funext q
  have hv : (((0 : P), v.2), v.1) =
      v.1 • (((0 : P), 0), (1 : ℝ)) + v.2 • (((0 : P), 1), (0 : ℝ)) := by
    ext <;> simp
  simp only [torusPartial, fixedPartial, hv, map_add, map_smul, smul_eq_mul]

theorem torusAverage_torusPartial_zero (v : ℝ × ℝ) {F : (P × ℝ) × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hp : TorusPeriodic F) (p : P) :
    torusAverage (torusPartial v F) p = 0 := by
  rw [torusPartial_decompose,
    torusAverage_add (contDiff_const.mul (fixedPartial_smooth _ hF))
      (contDiff_const.mul (fixedPartial_smooth _ hF))]
  rw [torusAverage_coeff_mul (fun _ => v.1), torusAverage_coeff_mul (fun _ => v.2),
    torusAverage_first_zero hF hp, torusAverage_second_zero hF hp]
  simp

noncomputable def graphPartial (a : P → ℝ) (v : P) (w : ℝ × ℝ)
    (F : (P × ℝ) × ℝ → ℝ) (q : (P × ℝ) × ℝ) : ℝ :=
  slowPartial v F q + a q.1.1 * torusPartial w F q

theorem graphPartial_smooth {a : P → ℝ} {F : (P × ℝ) × ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hF : ContDiff ℝ ∞ F) (v : P) (w : ℝ × ℝ) :
    ContDiff ℝ ∞ (graphPartial a v w F) :=
  (fixedPartial_smooth _ hF).add ((ha.comp contDiff_fst.fst).mul (fixedPartial_smooth _ hF))

theorem graphPartial_periodic (a : P → ℝ) (v : P) (w : ℝ × ℝ)
    {F : (P × ℝ) × ℝ → ℝ} (hp : TorusPeriodic F) :
    TorusPeriodic (graphPartial a v w F) := by
  have hs := fixedPartial_periodic ((v, 0), 0) hp
  have ht := fixedPartial_periodic ((0, w.2), w.1) hp
  constructor
  · intro q
    simp only [graphPartial, slowPartial, torusPartial]
    rw [hs.first, ht.first]
    simp only [Prod.add_def, add_zero]
  · intro q
    simp only [graphPartial, slowPartial, torusPartial]
    rw [hs.second, ht.second]
    simp only [Prod.add_def, add_zero]

/-- Graph lift terms integrate to zero; only the genuine slow derivative remains. -/
theorem torusAverage_graphPartial {a : P → ℝ} {F : (P × ℝ) × ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hF : ContDiff ℝ ∞ F) (hp : TorusPeriodic F)
    (v p : P) (w : ℝ × ℝ) :
    torusAverage (graphPartial a v w F) p = fderiv ℝ (torusAverage F) p v := by
  have hs : ContDiff ℝ ∞ (slowPartial v F) := fixedPartial_smooth _ hF
  have ht : ContDiff ℝ ∞ (fun q => a q.1.1 * torusPartial w F q) :=
    (ha.comp contDiff_fst.fst).mul (fixedPartial_smooth _ hF)
  unfold graphPartial
  rw [torusAverage_add hs ht, torusAverage_coeff_mul,
    torusAverage_torusPartial_zero w hF hp, mul_zero, add_zero]
  exact (torusAverage_fderiv hF p v).symm

theorem torusAverage_graphPartial_twice {a : P → ℝ} {F : (P × ℝ) × ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hF : ContDiff ℝ ∞ F) (hp : TorusPeriodic F)
    (v p : P) (w : ℝ × ℝ) :
    torusAverage (graphPartial a v w (graphPartial a v w F)) p =
      fderiv ℝ (fun q => fderiv ℝ (torusAverage F) q v) p v := by
  rw [torusAverage_graphPartial ha (graphPartial_smooth ha hF v w)
    (graphPartial_periodic a v w hp)]
  have he : torusAverage (graphPartial a v w F) =
      (fun q => fderiv ℝ (torusAverage F) q v) :=
    funext (fun q => torusAverage_graphPartial ha hF hp v q w)
  rw [he]

end Torus

/-! ## The averaged chart balances and their exact weighted integrals -/

theorem weighted_integrable_add {n : ℕ} {f g : ℝ → ℝ}
    (hf : Integrable (fun r => r ^ n * f r))
    (hg : Integrable (fun r => r ^ n * g r)) :
    Integrable (fun r => r ^ n * (f r + g r)) := by
  have hh : Integrable (fun r => r ^ n * f r + r ^ n * g r) := hf.add hg
  simpa only [mul_add] using hh

theorem weighted_integrable_sub {n : ℕ} {f g : ℝ → ℝ}
    (hf : Integrable (fun r => r ^ n * f r))
    (hg : Integrable (fun r => r ^ n * g r)) :
    Integrable (fun r => r ^ n * (f r - g r)) := by
  have hh : Integrable (fun r => r ^ n * f r - r ^ n * g r) := hf.sub hg
  simpa only [mul_sub] using hh

theorem weighted_integrable_const_mul {n : ℕ} {f : ℝ → ℝ}
    (hf : Integrable (fun r => r ^ n * f r)) (c : ℝ) :
    Integrable (fun r => r ^ n * (c * f r)) := by
  have hh : Integrable (fun r => c * (r ^ n * f r)) := hf.const_mul c
  simpa only [mul_left_comm] using hh

theorem moment_balance_algebra (n : ℕ) (α β δ : ℝ) (f g h j k l : ℝ → ℝ)
    (hf : Integrable (fun r => r ^ n * f r))
    (hg : Integrable (fun r => r ^ n * g r))
    (hh : Integrable (fun r => r ^ n * h r))
    (hj : Integrable (fun r => r ^ n * j r))
    (hk : Integrable (fun r => r ^ n * k r))
    (hl : Integrable (fun r => r ^ n * l r)) :
    moment n (fun r => α * f r + g r + β * h r - β * (j r + δ * k r) - l r) =
      α * moment n f + moment n g + β * moment n h -
        β * (moment n j + δ * moment n k) - moment n l := by
  have hα := weighted_integrable_const_mul hf α
  have hβ := weighted_integrable_const_mul hh β
  have hδ := weighted_integrable_const_mul hk δ
  have hleft := weighted_integrable_add (weighted_integrable_add hα hg) hβ
  have hright := weighted_integrable_const_mul (weighted_integrable_add hj hδ) β
  rw [moment_sub n (weighted_integrable_sub hleft hright) hl,
    moment_sub n hleft hright, moment_add n (weighted_integrable_add hα hg) hβ,
    moment_add n hα hg, moment_const_mul, moment_const_mul, moment_const_mul,
    moment_add n hj hδ, moment_const_mul]

abbrev MeanParameter := ℝ × ℝ
abbrev MeanPoint := ℝ × MeanParameter
abbrev MeanField := MeanPoint → ℝ

/-- Joint smoothness and a common compact radial shell are genuine input
regularity conditions on the pointwise fields, not conditions on their moments. -/
structure SmoothShell (a b : ℝ) (F : MeanField) : Prop where
  smooth : ContDiff ℝ ∞ F
  supported : RadialAlias.RadiallySupported a b F

theorem SmoothShell.parameterDerivative {a b : ℝ} {F : MeanField} (hF : SmoothShell a b F)
    (v : MeanParameter) : SmoothShell a b (parameterPartial v F) :=
  ⟨parameterPartial_smooth v hF.smooth, parameterPartial_supported v hF.supported⟩

theorem SmoothShell.add {a b : ℝ} {F G : MeanField}
    (hF : SmoothShell a b F) (hG : SmoothShell a b G) :
    SmoothShell a b (fun x => F x + G x) := by
  refine ⟨hF.smooth.add hG.smooth, ?_⟩
  intro x hx
  by_contra hn
  have hFx : F x = 0 := by
    by_contra h
    exact hn (hF.supported h)
  have hGx : G x = 0 := by
    by_contra h
    exact hn (hG.supported h)
  exact hx (by simp [hFx, hGx])

theorem SmoothShell.slice_smooth {a b : ℝ} {F : MeanField} (hF : SmoothShell a b F)
    (p : MeanParameter) : ContDiff ℝ ∞ (fun r => F (r, p)) :=
  radial_slice_smooth hF.smooth p

theorem SmoothShell.slice_compact {a b : ℝ} {F : MeanField} (hF : SmoothShell a b F)
    (p : MeanParameter) : HasCompactSupport (fun r => F (r, p)) :=
  radial_slice_compact hF.supported p

theorem SmoothShell.weighted_integrable {a b : ℝ} {F : MeanField} (hF : SmoothShell a b F)
    (n : ℕ) (p : MeanParameter) : Integrable (fun r => r ^ n * F (r, p)) :=
  IntegratedMeanBalances.weighted_integrable (hF.slice_smooth p).continuous (hF.slice_compact p) n

/-- The angular line of (32), after the actual torus average. Coordinates are
`(R,(T,Z))`; `ε` is constant on a chart. The supplied fluxes are full averages
of the pointwise products in (32), and the last radial divergence is the virtual stress. -/
noncomputable def angularBalance (ε : ℝ) (v radialFlux axialFlux virtualFlux : MeanField)
    (x : MeanPoint) : ℝ :=
  (-ε) * parameterPartial (1, 0) v x +
    radialDivergence 2 (fun r => radialFlux (r, x.2)) x.1 +
    ε * parameterPartial (0, 1) axialFlux x -
    ε * (angularRadialViscosity (fun r => v (r, x.2)) x.1 +
      ε ^ 2 * parameterPartial (0, 1) (parameterPartial (0, 1) v) x) -
    radialDivergence 2 (fun r => virtualFlux (r, x.2)) x.1

/-- The axial line of (32), with pressure retained inside the axial flux. -/
noncomputable def axialBalance (ε : ℝ) (γ radialFlux axialFlux pressure virtualFlux : MeanField)
    (x : MeanPoint) : ℝ :=
  (-ε) * parameterPartial (1, 0) γ x +
    radialDivergence 1 (fun r => radialFlux (r, x.2)) x.1 +
    ε * parameterPartial (0, 1) (fun y => axialFlux y + pressure y) x -
    ε * (axialRadialViscosity (fun r => γ (r, x.2)) x.1 +
      ε ^ 2 * parameterPartial (0, 1) (parameterPartial (0, 1) γ) x) -
    radialDivergence 1 (fun r => virtualFlux (r, x.2)) x.1

/-- The first identity in (34), derived from the pointwise angular balance. -/
theorem integrated_angular_balance {a b : ℝ} (ε : ℝ)
    {v radialFlux axialFlux virtualFlux : MeanField}
    (hv : SmoothShell a b v) (hr : SmoothShell a b radialFlux)
    (hz : SmoothShell a b axialFlux) (hT : SmoothShell a b virtualFlux)
    (hmass : radialMoment 2 v = 0) (p : MeanParameter) :
    radialMoment 2 (angularBalance ε v radialFlux axialFlux virtualFlux) p =
      ε * fderiv ℝ (radialMoment 2 axialFlux) p (0, 1) := by
  have halg := moment_balance_algebra 2 (-ε) ε (ε ^ 2)
    (fun r => parameterPartial (1, 0) v (r, p))
    (radialDivergence 2 (fun r => radialFlux (r, p)))
    (fun r => parameterPartial (0, 1) axialFlux (r, p))
    (angularRadialViscosity (fun r => v (r, p)))
    (fun r => parameterPartial (0, 1) (parameterPartial (0, 1) v) (r, p))
    (radialDivergence 2 (fun r => virtualFlux (r, p)))
    ((hv.parameterDerivative (1, 0)).weighted_integrable 2 p)
    (angular_divergence_integrable (hr.slice_smooth p) (hr.slice_compact p))
    ((hz.parameterDerivative (0, 1)).weighted_integrable 2 p)
    (angular_viscosity_integrable (hv.slice_smooth p) (hv.slice_compact p))
    (((hv.parameterDerivative (0, 1)).parameterDerivative (0, 1)).weighted_integrable 2 p)
    (angular_divergence_integrable (hT.slice_smooth p) (hT.slice_compact p))
  have ht := zero_mass_parameterPartial hv.smooth hv.supported 2 hmass p (1, 0)
  have hzz := zero_mass_parameterPartial_twice hv.smooth hv.supported 2 hmass p (0, 1) (0, 1)
  have hd := radialMoment_parameterPartial hz.smooth hz.supported 2 p (0, 1)
  change moment 2 _ = _
  simp only [angularBalance]
  rw [halg, moment_angular_divergence (hr.slice_smooth p) (hr.slice_compact p),
    moment_angular_divergence (hT.slice_smooth p) (hT.slice_compact p),
    moment_angular_viscosity (hv.slice_smooth p) (hv.slice_compact p)]
  change (-ε) * radialMoment 2 (parameterPartial (1, 0) v) p + 0 +
    ε * radialMoment 2 (parameterPartial (0, 1) axialFlux) p -
    ε * (0 + ε ^ 2 * radialMoment 2 (parameterPartial (0, 1) (parameterPartial (0, 1) v)) p) - 0 = _
  rw [ht, hzz, ← hd]
  ring

/-- The second tangential integral, before eliminating the pressure moment. -/
theorem integrated_axial_balance {a b : ℝ} (ε : ℝ)
    {γ radialFlux axialFlux pressure virtualFlux : MeanField}
    (hγ : SmoothShell a b γ) (hr : SmoothShell a b radialFlux)
    (hz : SmoothShell a b axialFlux) (hp : SmoothShell a b pressure)
    (hT : SmoothShell a b virtualFlux)
    (hmass : radialMoment 1 γ = 0) (p : MeanParameter) :
    radialMoment 1 (axialBalance ε γ radialFlux axialFlux pressure virtualFlux) p =
      ε * fderiv ℝ (radialMoment 1 (fun x => axialFlux x + pressure x)) p (0, 1) := by
  have halg := moment_balance_algebra 1 (-ε) ε (ε ^ 2)
    (fun r => parameterPartial (1, 0) γ (r, p))
    (radialDivergence 1 (fun r => radialFlux (r, p)))
    (fun r => parameterPartial (0, 1) (fun x => axialFlux x + pressure x) (r, p))
    (axialRadialViscosity (fun r => γ (r, p)))
    (fun r => parameterPartial (0, 1) (parameterPartial (0, 1) γ) (r, p))
    (radialDivergence 1 (fun r => virtualFlux (r, p)))
    ((hγ.parameterDerivative (1, 0)).weighted_integrable 1 p)
    (by simpa only [pow_one] using axial_divergence_integrable (hr.slice_smooth p)
      (hr.slice_compact p))
    (((hz.add hp).parameterDerivative (0, 1)).weighted_integrable 1 p)
    (by simpa only [pow_one] using axial_viscosity_integrable (hγ.slice_smooth p) (hγ.slice_compact
      p))
    (((hγ.parameterDerivative (0, 1)).parameterDerivative (0, 1)).weighted_integrable 1 p)
    (by simpa only [pow_one] using axial_divergence_integrable (hT.slice_smooth p)
      (hT.slice_compact p))
  have ht := zero_mass_parameterPartial hγ.smooth hγ.supported 1 hmass p (1, 0)
  have hzz := zero_mass_parameterPartial_twice hγ.smooth hγ.supported 1 hmass p (0, 1) (0, 1)
  have hd := radialMoment_parameterPartial (hz.add hp).smooth (hz.add hp).supported 1 p (0, 1)
  change moment 1 _ = _
  simp only [axialBalance]
  rw [halg, moment_axial_divergence (hr.slice_smooth p) (hr.slice_compact p),
    moment_axial_divergence (hT.slice_smooth p) (hT.slice_compact p),
    moment_axial_viscosity (hγ.slice_smooth p) (hγ.slice_compact p)]
  change (-ε) * radialMoment 1 (parameterPartial (1, 0) γ) p + 0 +
    ε * radialMoment 1 (parameterPartial (0, 1) (fun x => axialFlux x + pressure x)) p -
    ε * (0 + ε ^ 2 * radialMoment 1 (parameterPartial (0, 1) (parameterPartial (0, 1) γ)) p) - 0 = _
  rw [ht, hzz, ← hd]
  ring

noncomputable def pressureTotal (gr : MeanField) : MeanParameter → ℝ := radialMoment 0 gr

noncomputable def pressureCoefficient (ρ : MeanField) (p : MeanParameter) : ℝ :=
  radialMoment 2 ρ p / 2

noncomputable def axialDefect (axialFlux gr : MeanField) (p : MeanParameter) : ℝ :=
  radialMoment 1 axialFlux p - (1 / 2 : ℝ) * radialMoment 2 gr p

theorem flux_pressure_moment {a b : ℝ} {axialFlux pressure gr ρ : MeanField}
    (hz : SmoothShell a b axialFlux) (hp : SmoothShell a b pressure)
    (hg : SmoothShell a b gr) (hρ : SmoothShell a b ρ)
    (hderiv : ∀ r p, deriv (fun s => pressure (s, p)) r =
      gr (r, p) - ρ (r, p) * pressureTotal gr p) :
    radialMoment 1 (fun x => axialFlux x + pressure x) =
      (fun p => axialDefect axialFlux gr p + pressureCoefficient ρ p * pressureTotal gr p) := by
  funext p
  change moment 1 (fun r => axialFlux (r, p) + pressure (r, p)) = _
  rw [moment_add 1 (hz.weighted_integrable 1 p) (hp.weighted_integrable 1 p),
    pressure_moment_reconstructed (pressureTotal gr p) (hp.slice_smooth p) (hp.slice_compact p)
      (hg.slice_smooth p).continuous (hg.slice_compact p)
      (hρ.slice_smooth p).continuous (hρ.slice_compact p) (fun r => hderiv r p)]
  unfold axialDefect pressureCoefficient radialMoment
  ring

/-- The pressure coefficient stays inside the actual axial derivative, exactly
as in (34); it may vary with both slow parameters. -/
theorem integrated_axial_reconstructed {a b : ℝ} (ε : ℝ)
    {γ radialFlux axialFlux pressure virtualFlux gr ρ : MeanField}
    (hγ : SmoothShell a b γ) (hr : SmoothShell a b radialFlux)
    (hz : SmoothShell a b axialFlux) (hp : SmoothShell a b pressure)
    (hT : SmoothShell a b virtualFlux) (hg : SmoothShell a b gr) (hρ : SmoothShell a b ρ)
    (hmass : radialMoment 1 γ = 0)
    (hderiv : ∀ r p, deriv (fun s => pressure (s, p)) r =
      gr (r, p) - ρ (r, p) * pressureTotal gr p) (p : MeanParameter) :
    radialMoment 1 (axialBalance ε γ radialFlux axialFlux pressure virtualFlux) p =
      ε * fderiv ℝ (fun q => axialDefect axialFlux gr q +
        pressureCoefficient ρ q * pressureTotal gr q) p (0, 1) := by
  rw [integrated_axial_balance ε hγ hr hz hp hT hmass,
    flux_pressure_moment hz hp hg hρ hderiv]

/-! ## Restriction to the physical positive radial half-line -/

theorem zero_of_not_mem_interval {a b r : ℝ} {f : ℝ → ℝ}
    (hs : support f ⊆ Icc a b) (hr : r ∉ Icc a b) : f r = 0 := by
  by_contra h
  exact hr (hs h)

theorem deriv_support_interval {a b : ℝ} {f : ℝ → ℝ}
    (hs : support f ⊆ Icc a b) : support (deriv f) ⊆ Icc a b :=
  support_deriv_subset.trans (closure_minimal hs isClosed_Icc)

theorem radialDivergence_supported {a b : ℝ} {f : ℝ → ℝ}
    (hs : support f ⊆ Icc a b) (c : ℝ) :
    support (radialDivergence c f) ⊆ Icc a b := by
  intro r hr
  by_contra hn
  apply hr
  simp [radialDivergence, zero_of_not_mem_interval hs hn,
    zero_of_not_mem_interval (deriv_support_interval hs) hn]

theorem angularViscosity_supported {a b : ℝ} {f : ℝ → ℝ}
    (hs : support f ⊆ Icc a b) : support (angularRadialViscosity f) ⊆ Icc a b := by
  intro r hr
  by_contra hn
  apply hr
  simp [angularRadialViscosity, zero_of_not_mem_interval hs hn,
    zero_of_not_mem_interval (deriv_support_interval hs) hn,
    zero_of_not_mem_interval (deriv_support_interval (deriv_support_interval hs)) hn]

theorem axialViscosity_supported {a b : ℝ} {f : ℝ → ℝ}
    (hs : support f ⊆ Icc a b) : support (axialRadialViscosity f) ⊆ Icc a b := by
  intro r hr
  by_contra hn
  apply hr
  simp [axialRadialViscosity, zero_of_not_mem_interval (deriv_support_interval hs) hn,
    zero_of_not_mem_interval (deriv_support_interval (deriv_support_interval hs)) hn]

theorem SmoothShell.slice_support {a b : ℝ} {F : MeanField} (hF : SmoothShell a b F)
    (p : MeanParameter) : support (fun r => F (r, p)) ⊆ Icc a b :=
  fun _ hr => hF.supported hr

theorem SmoothShell.zero_of_not_mem {a b : ℝ} {F : MeanField} (hF : SmoothShell a b F)
    {x : MeanPoint} (hx : x.1 ∉ Icc a b) : F x = 0 := by
  by_contra h
  exact hx (hF.supported h)

theorem angularBalance_supported {a b : ℝ} (ε : ℝ)
    {v radialFlux axialFlux virtualFlux : MeanField}
    (hv : SmoothShell a b v) (hr : SmoothShell a b radialFlux)
    (hz : SmoothShell a b axialFlux) (hT : SmoothShell a b virtualFlux) :
    RadialAlias.RadiallySupported a b (angularBalance ε v radialFlux axialFlux virtualFlux) := by
  intro x hx
  by_contra hn
  apply hx
  simp [angularBalance,
    (hv.parameterDerivative (1, 0)).zero_of_not_mem hn, (hz.parameterDerivative (0,
      1)).zero_of_not_mem hn,
    ((hv.parameterDerivative (0, 1)).parameterDerivative (0, 1)).zero_of_not_mem hn,
    zero_of_not_mem_interval (radialDivergence_supported (hr.slice_support x.2) 2) hn,
    zero_of_not_mem_interval (radialDivergence_supported (hT.slice_support x.2) 2) hn,
    zero_of_not_mem_interval (angularViscosity_supported (hv.slice_support x.2)) hn]

theorem axialBalance_supported {a b : ℝ} (ε : ℝ)
    {γ radialFlux axialFlux pressure virtualFlux : MeanField}
    (hγ : SmoothShell a b γ) (hr : SmoothShell a b radialFlux)
    (hz : SmoothShell a b axialFlux) (hp : SmoothShell a b pressure)
    (hT : SmoothShell a b virtualFlux) :
    RadialAlias.RadiallySupported a b (axialBalance ε γ radialFlux axialFlux pressure virtualFlux)
      := by
  intro x hx
  by_contra hn
  apply hx
  simp [axialBalance,
    (hγ.parameterDerivative (1, 0)).zero_of_not_mem hn, ((hz.add hp).parameterDerivative (0,
      1)).zero_of_not_mem hn,
    ((hγ.parameterDerivative (0, 1)).parameterDerivative (0, 1)).zero_of_not_mem hn,
    zero_of_not_mem_interval (radialDivergence_supported (hr.slice_support x.2) 1) hn,
    zero_of_not_mem_interval (radialDivergence_supported (hT.slice_support x.2) 1) hn,
    zero_of_not_mem_interval (axialViscosity_supported (hγ.slice_support x.2)) hn]

theorem positive_radialMoment {a b : ℝ} (ha : 0 < a) {F : MeanField}
    (hs : RadialAlias.RadiallySupported a b F) (n : ℕ) (p : MeanParameter) :
    (∫ r in Ioi (0 : ℝ), r ^ n * F (r, p)) = radialMoment n F p := by
  apply positive_integral_eq_integral ha
  intro r hr
  exact hs (right_ne_zero_of_mul hr)

theorem integrated_angular_positive {a b : ℝ} (ha : 0 < a) (ε : ℝ)
    {v radialFlux axialFlux virtualFlux : MeanField}
    (hv : SmoothShell a b v) (hr : SmoothShell a b radialFlux)
    (hz : SmoothShell a b axialFlux) (hT : SmoothShell a b virtualFlux)
    (hmass : radialMoment 2 v = 0) (p : MeanParameter) :
    (∫ r in Ioi (0 : ℝ), r ^ 2 * angularBalance ε v radialFlux axialFlux virtualFlux (r, p)) =
      ε * fderiv ℝ (radialMoment 2 axialFlux) p (0, 1) := by
  rw [positive_radialMoment ha (angularBalance_supported ε hv hr hz hT),
    integrated_angular_balance ε hv hr hz hT hmass]

theorem integrated_axial_positive {a b : ℝ} (ha : 0 < a) (ε : ℝ)
    {γ radialFlux axialFlux pressure virtualFlux gr ρ : MeanField}
    (hγ : SmoothShell a b γ) (hr : SmoothShell a b radialFlux)
    (hz : SmoothShell a b axialFlux) (hp : SmoothShell a b pressure)
    (hT : SmoothShell a b virtualFlux) (hg : SmoothShell a b gr) (hρ : SmoothShell a b ρ)
    (hmass : radialMoment 1 γ = 0)
    (hderiv : ∀ r p, deriv (fun s => pressure (s, p)) r =
      gr (r, p) - ρ (r, p) * pressureTotal gr p) (p : MeanParameter) :
    (∫ r in Ioi (0 : ℝ), r * axialBalance ε γ radialFlux axialFlux pressure virtualFlux (r, p)) =
      ε * fderiv ℝ (fun q => axialDefect axialFlux gr q +
        pressureCoefficient ρ q * pressureTotal gr q) p (0, 1) := by
  simpa only [pow_one] using
    (positive_radialMoment ha (axialBalance_supported ε hγ hr hz hp hT) 1 p).trans
      (integrated_axial_reconstructed ε hγ hr hz hp hT hg hρ hmass hderiv p)

/-! ## The actual pressure primitive (33), without a supplied derivative identity -/

section PressurePrimitive

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Exact moment of the constructed compact pressure, including its normalized
mean correction. The derivative used in the proof is a theorem of the actual
physical transport integral, not an assumption here. -/
theorem constructed_pressure_moment {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : ℝ × ℝ)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (hper : PressureStream.TorusPeriodicLift f)
    (s : S) :
    moment 1 (fun r => PressureStream.torusAverage
      (PressureStream.meanPressure d a b M hab v f) (r, s)) =
      -(1 / 2 : ℝ) * moment 2 (fun r => PressureStream.torusAverage f (r, s)) +
        (moment 2 (PressureStream.rho a b hab) / 2) * PressureStream.pressureMass f s := by
  exact pressure_moment_reconstructed (PressureStream.pressureMass f s)
    (PressureStream.torusAverage_slice_contDiff
      (PressureStream.meanPressure_contDiff ha hab hd v hf hs) s)
    (PressureStream.torusAverage_slice_hasCompactSupport
      (PressureStream.meanPressure_supported ha hab hd v hf hs) s)
    (PressureStream.torusAverage_slice_contDiff hf s).continuous
    (PressureStream.torusAverage_slice_hasCompactSupport hs s)
    (PressureStream.rho_contDiff a b hab).continuous
    (PressureStream.rho_hasCompactSupport a b hab)
    (fun r => (PressureStream.meanPressure_bar_hasDerivAt ha hab hd v hf hs hper s r).deriv)

end PressurePrimitive

noncomputable def reconstructedMeanPressure (d a b M : ℝ) (hab : a < b) (v : ℝ × ℝ)
    (f : PressureStream.Lift MeanParameter → ℝ) : MeanField :=
  PressureStream.torusAverage (PressureStream.meanPressure d a b M hab v f)

noncomputable def averagedRadialSource (f : PressureStream.Lift MeanParameter → ℝ) : MeanField :=
  PressureStream.torusAverage f

noncomputable def normalizedMeanDensity (a b : ℝ) (hab : a < b) (x : MeanPoint) : ℝ :=
  PressureStream.rho a b hab x.1

theorem averagedRadialSource_shell {a b : ℝ} {f : PressureStream.Lift MeanParameter → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) :
    SmoothShell a b (averagedRadialSource f) :=
  ⟨PressureStream.torusAverage_contDiff hf, PressureStream.torusAverage_supported hs⟩

theorem reconstructedMeanPressure_shell {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : ℝ × ℝ)
    {f : PressureStream.Lift MeanParameter → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) :
    SmoothShell a b (reconstructedMeanPressure d a b M hab v f) :=
  ⟨PressureStream.torusAverage_contDiff (PressureStream.meanPressure_contDiff ha hab hd v hf hs),
    PressureStream.torusAverage_supported (PressureStream.meanPressure_supported ha hab hd v hf hs)⟩

theorem normalizedMeanDensity_shell (a b : ℝ) (hab : a < b) :
    SmoothShell a b (normalizedMeanDensity a b hab) := by
  refine ⟨(PressureStream.rho_contDiff a b hab).comp contDiff_fst, ?_⟩
  exact fun _ hx => PressureStream.rho_support a b hab hx

theorem constructed_pressure_deriv {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : ℝ × ℝ)
    {f : PressureStream.Lift MeanParameter → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (hper : PressureStream.TorusPeriodicLift f)
    (r : ℝ) (p : MeanParameter) :
    deriv (fun s => reconstructedMeanPressure d a b M hab v f (s, p)) r =
      averagedRadialSource f (r, p) - normalizedMeanDensity a b hab (r, p) *
        pressureTotal (averagedRadialSource f) p := by
  simpa only [reconstructedMeanPressure, averagedRadialSource, normalizedMeanDensity,
    pressureTotal, radialMoment, moment, pow_zero, one_mul, PressureStream.pressureMass]
    using (PressureStream.meanPressure_bar_hasDerivAt ha hab hd v hf hs hper p r).deriv

/-- The second identity of (34) with pressure supplied by the actual compact
primitive (33). No pressure moment or pressure derivative identity is assumed. -/
theorem integrated_axial_constructed_pressure {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (ε : ℝ) (v : ℝ × ℝ)
    {f : PressureStream.Lift MeanParameter → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (hper : PressureStream.TorusPeriodicLift f)
    {γ radialFlux axialFlux virtualFlux : MeanField}
    (hγ : SmoothShell a b γ) (hr : SmoothShell a b radialFlux)
    (hz : SmoothShell a b axialFlux) (hT : SmoothShell a b virtualFlux)
    (hmass : radialMoment 1 γ = 0) (p : MeanParameter) :
    (∫ r in Ioi (0 : ℝ), r * axialBalance ε γ radialFlux axialFlux
      (reconstructedMeanPressure d a b M hab v f) virtualFlux (r, p)) =
      ε * fderiv ℝ (fun q => axialDefect axialFlux (averagedRadialSource f) q +
        pressureCoefficient (normalizedMeanDensity a b hab) q *
          pressureTotal (averagedRadialSource f) q) p (0, 1) := by
  exact integrated_axial_positive ha ε hγ hr hz
    (reconstructedMeanPressure_shell ha hab hd v hf hs) hT
    (averagedRadialSource_shell hf hs) (normalizedMeanDensity_shell a b hab) hmass
    (constructed_pressure_deriv ha hab hd v hf hs hper) p

end NavierStokes.IntegratedMeanBalances
