/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FourierAlias
public import LeanPool.NavierStokesAndEuler.NavierStokes.RadialPullback
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Pressure and divergence reconstruction with the exact compactification error

The radial primitives are the actual transport integrals. Slow parameters are
retained separately from the two auxiliary torus coordinates. The pressure
correction uses a constructed smooth bump of integral one.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Interval

namespace NavierStokes.PressureStream

open TransportPrimitive

/-- Plane: an abbreviation for `ℝ × ℝ`. -/
abbrev Plane := ℝ × ℝ
/-- Lift: an abbreviation for `ℝ × (S × Plane)`. -/
abbrev Lift (S : Type) := ℝ × (S × Plane)

/-- A concrete bump strictly inside the radial interval. -/
noncomputable def meanBump (a b : ℝ) (hab : a < b) : ContDiffBump ((a + b) / 2) where
  rIn := (b - a) / 8
  rOut := (b - a) / 4
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- The actual radial density has integral one, with no normalization premise. -/
noncomputable def rho (a b : ℝ) (hab : a < b) : ℝ → ℝ :=
  (meanBump a b hab).normed volume

theorem rho_contDiff (a b : ℝ) (hab : a < b) : ContDiff ℝ ∞ (rho a b hab) :=
  (meanBump a b hab).contDiff_normed

theorem rho_integrable (a b : ℝ) (hab : a < b) : Integrable (rho a b hab) :=
  (meanBump a b hab).integrable_normed

theorem rho_integral (a b : ℝ) (hab : a < b) : (∫ r, rho a b hab r) = 1 :=
  (meanBump a b hab).integral_normed

theorem rho_nonneg (a b : ℝ) (hab : a < b) (r : ℝ) : 0 ≤ rho a b hab r :=
  (meanBump a b hab).nonneg_normed r

theorem rho_support (a b : ℝ) (hab : a < b) : support (rho a b hab) ⊆ Icc a b := by
  intro r hr
  rw [rho, ContDiffBump.support_normed_eq] at hr
  change dist r ((a + b) / 2) < (b - a) / 4 at hr
  rw [Real.dist_eq, abs_lt] at hr
  constructor <;> linarith [hr.1, hr.2]

theorem rho_hasCompactSupport (a b : ℝ) (hab : a < b) :
    HasCompactSupport (rho a b hab) :=
  (meanBump a b hab).hasCompactSupport_normed

section Average

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Torus inner, given by `∫ x in (0 : ℝ)..1, f (p.1.1, (p.1.2, (x, p.2)))`. -/
noncomputable def torusInner (f : Lift S → ℝ) (p : (ℝ × S) × ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, f (p.1.1, (p.1.2, (x, p.2)))

/-- The bar averages only the auxiliary torus, preserving every slow parameter. -/
noncomputable def torusAverage (f : Lift S → ℝ) (p : ℝ × S) : ℝ :=
  ∫ y in (0 : ℝ)..1, torusInner f (p, y)

theorem torusInner_contDiff {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (torusInner f) := by
  let g : (((ℝ × S) × ℝ) × ℝ) → ℝ := fun q =>
    f (q.1.1.1, (q.1.1.2, (q.2, q.1.2)))
  have hg : ContDiff ℝ ∞ g := hf.comp ((contDiff_fst.fst.fst).prodMk
    ((contDiff_fst.fst.snd).prodMk (contDiff_snd.prodMk contDiff_fst.snd)))
  exact parameterIntegral_contDiff hg 0 1

theorem torusAverage_contDiff {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (torusAverage f) :=
  parameterIntegral_contDiff (torusInner_contDiff hf) 0 1

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem torusAverage_zero_of_forall {f : Lift S → ℝ} {p : ℝ × S}
    (hzero : ∀ Y : Plane, f (p.1, (p.2, Y)) = 0) : torusAverage f p = 0 := by
  simp [torusAverage, torusInner, hzero]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem torusAverage_supported {a b : ℝ} {f : Lift S → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (torusAverage f) := by
  intro p hp
  by_contra hn
  apply hp
  apply torusAverage_zero_of_forall
  intro Y
  by_contra hne
  exact hn (hs hne)

theorem torusAverage_sub_slow {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (g : ℝ × S → ℝ) (p : ℝ × S) :
    torusAverage (fun q => f q - g (q.1, q.2.1)) p = torusAverage f p - g p := by
  have hx (y : ℝ) : IntervalIntegrable (fun x => f (p.1, (p.2, (x, y)))) volume 0 1 :=
    (hf.continuous.comp (continuous_const.prodMk
      (continuous_const.prodMk (continuous_id.prodMk continuous_const)))).intervalIntegrable 0 1
  have hy : IntervalIntegrable (fun y => torusInner f (p, y)) volume 0 1 :=
    ((torusInner_contDiff hf).continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  have hi (y : ℝ) : torusInner (fun q => f q - g (q.1, q.2.1)) (p, y) =
      torusInner f (p, y) - g p := by
    change (∫ x in (0 : ℝ)..1, f (p.1, (p.2, (x, y))) - g p) = _
    rw [intervalIntegral.integral_sub (hx y) intervalIntegrable_const]
    simp only [torusInner, intervalIntegral.integral_const, sub_zero, one_smul]
  unfold torusAverage
  simp_rw [hi]
  rw [intervalIntegral.integral_sub hy intervalIntegrable_const]
  simp

/-- Pressure mass, given by `∫ r, torusAverage f (r, s)`. -/
noncomputable def pressureMass (f : Lift S → ℝ) (s : S) : ℝ :=
  ∫ r, torusAverage f (r, s)

theorem torusAverage_slice_integrable {a b : ℝ} {f : Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) (s : S) :
    Integrable (fun r => torusAverage f (r, s)) := by
  apply ((torusAverage_contDiff hf).continuous.comp
    (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (fun r hr => torusAverage_supported hs hr)

theorem pressureMass_eq_interval {a b : ℝ} {f : Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) (s : S) :
    pressureMass f s = ∫ r in a..b, torusAverage f (r, s) := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  have hcont : Continuous (fun r => torusAverage f (r, s)) :=
    (torusAverage_contDiff hf).continuous.comp (continuous_id.prodMk continuous_const)
  have hopen : support (fun r => torusAverage f (r, s)) ⊆ Ioo a b := by
    simpa only [interior_Icc] using hcont.isOpen_support.subset_interior_iff.mpr
      (show support (fun r => torusAverage f (r, s)) ⊆ Icc a b from
        fun r hr => torusAverage_supported hs hr)
  exact hopen.trans Ioo_subset_Ioc_self

theorem pressureMass_contDiff {a b : ℝ} {f : Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) :
    ContDiff ℝ ∞ (pressureMass f) := by
  have heq : pressureMass f = fun s => ∫ r in a..b, torusAverage f (r, s) :=
    funext (pressureMass_eq_interval hf hs)
  rw [heq]
  exact parameterIntegral_contDiff
    ((torusAverage_contDiff hf).comp (contDiff_snd.prodMk contDiff_fst)) a b

/-- Pressure source, given by `f p - rho a b hab p.1 * pressureMass f p.2.1`. -/
noncomputable def pressureSource (a b : ℝ) (hab : a < b) (f : Lift S → ℝ)
    (p : Lift S) : ℝ := f p - rho a b hab p.1 * pressureMass f p.2.1

theorem pressureSource_contDiff {a b : ℝ} (hab : a < b) {f : Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) :
    ContDiff ℝ ∞ (pressureSource a b hab f) :=
  hf.sub (((rho_contDiff a b hab).comp contDiff_fst).mul
    ((pressureMass_contDiff hf hs).comp contDiff_snd.fst))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem pressureSource_supported {a b : ℝ} (hab : a < b) {f : Lift S → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (pressureSource a b hab f) := by
  intro p hp
  by_contra hn
  have hf : f p = 0 := by by_contra hne; exact hn (hs hne)
  have hρ : rho a b hab p.1 = 0 := by by_contra hne; exact hn (rho_support a b hab hne)
  exact hp (by simp [pressureSource, hf, hρ])

theorem torusAverage_pressureSource {a b : ℝ} (hab : a < b) {f : Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (p : ℝ × S) :
    torusAverage (pressureSource a b hab f) p =
      torusAverage f p - rho a b hab p.1 * pressureMass f p.2 :=
  torusAverage_sub_slow hf (fun q => rho a b hab q.1 * pressureMass f q.2) p

/-- The corrected pressure source has zero integrated torus mean, derived
from the integral-one bump rather than imposed as a hypothesis. -/
theorem pressureSource_mass_zero {a b : ℝ} (hab : a < b) {f : Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) (s : S) :
    pressureMass (pressureSource a b hab f) s = 0 := by
  unfold pressureMass
  simp_rw [torusAverage_pressureSource hab hf]
  rw [integral_sub (torusAverage_slice_integrable hf hs s)
    ((rho_integrable a b hab).mul_const _), integral_mul_const, rho_integral, one_mul]
  simp [pressureMass]

end Average

section Graph

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial vector, given by `(1, k p.1 • v)`. -/
noncomputable def radialVector (k : ℝ → ℝ) (v : E) (p : ℝ × E) : ℝ × E :=
  (1, k p.1 • v)

/-- The exact radial graph derivative. The directions are fixed; only its
radial speed is allowed to vary with the slow radius. -/
noncomputable def graphDr (k : ℝ → ℝ) (v : E) (f : ℝ × E → ℝ) (p : ℝ × E) : ℝ :=
  fderiv ℝ f p (radialVector k v p)

/-- A fixed axial graph direction may include both slow and torus directions. -/
noncomputable def graphDz (w : E) (f : ℝ × E → ℝ) (p : ℝ × E) : ℝ :=
  fderiv ℝ f p (0, w)

theorem graphDz_contDiff {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) (w : E) :
    ContDiff ℝ ∞ (graphDz w f) := fixedDeriv_contDiff hf (0, w)

theorem graphDr_contDiff {f : ℝ × E → ℝ} {k : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hk : ContDiff ℝ ∞ k) (v : E) :
    ContDiff ℝ ∞ (graphDr k v f) :=
  (hf.fderiv_right (by simp)).clm_apply
    (contDiff_const.prodMk ((hk.comp contDiff_fst).smul contDiff_const))

theorem radialVector_hasFDerivAt {k : ℝ → ℝ} (v : E) {p : ℝ × E}
    (hk : DifferentiableAt ℝ k p.1) :
    HasFDerivAt (radialVector k v)
      ((0 : (ℝ × E) →L[ℝ] ℝ).prod
        (((fderiv ℝ k p.1).comp (ContinuousLinearMap.fst ℝ ℝ E)).smulRight v)) p := by
  exact (hasFDerivAt_const (1 : ℝ) p).prodMk
    ((hk.hasFDerivAt.comp p hasFDerivAt_fst).smul_const v)

theorem radialVector_cross_derivative {k : ℝ → ℝ} (v w : E) {p : ℝ × E}
    (hk : DifferentiableAt ℝ k p.1) :
    fderiv ℝ (radialVector k v) p (0, w) = 0 := by
  rw [(radialVector_hasFDerivAt v hk).fderiv]
  simp

/-- Exact commutation is proved from symmetry of the second derivative and
the vanishing cross derivative of the radial vector field. -/
theorem graphDr_graphDz_comm {f : ℝ × E → ℝ} {k : ℝ → ℝ} (v w : E)
    {p : ℝ × E} (hf : ContDiffAt ℝ 2 f p) (hk : DifferentiableAt ℝ k p.1) :
    graphDr k v (graphDz w f) p = graphDz w (graphDr k v f) p := by
  have hDF := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hV := (radialVector_hasFDerivAt v hk).differentiableAt
  change fderiv ℝ (fun q => fderiv ℝ f q (0, w)) p (radialVector k v p) =
    fderiv ℝ (fun q => fderiv ℝ f q (radialVector k v q)) p (0, w)
  rw [fderiv_clm_apply hDF (differentiableAt_const _), fderiv_clm_apply hDF hV]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, radialVector_cross_derivative v w hk,
    fderiv_fun_const, map_zero, zero_add]
  simpa using (hf.isSymmSndFDerivAt (by norm_num)).eq (radialVector k v p) (0, w)

/-- Divide radius, given by `f p / p.1`. -/
noncomputable def divideRadius (f : ℝ × E → ℝ) (p : ℝ × E) : ℝ := f p / p.1

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem divideRadius_supported {a b : ℝ} {f : ℝ × E → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (divideRadius f) := by
  intro p hp
  apply hs
  intro hf
  exact hp (by simp [divideRadius, hf])

/-- Division by radius is harmless for a smooth field supported away from the axis. -/
theorem divideRadius_contDiff {a b : ℝ} (ha : 0 < a) {f : ℝ × E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f) :
    ContDiff ℝ ∞ (divideRadius f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.1 = 0
  · have hz : divideRadius f =ᶠ[𝓝 p] fun _ => 0 := by
      have hnear : ∀ᶠ q : ℝ × E in 𝓝 p, q.1 < a :=
        continuousAt_fst.eventually (Iio_mem_nhds (by simpa [hp] using ha))
      filter_upwards [hnear] with q hq
      simp [divideRadius, radial_zero_of_lt hs hq]
    exact contDiffAt_const.congr_of_eventuallyEq hz
  · exact hf.contDiffAt.div contDiffAt_fst hp

theorem graphDr_neg {f : ℝ × E → ℝ} {k : ℝ → ℝ} (v : E) {p : ℝ × E}
    (hf : DifferentiableAt ℝ f p) :
    graphDr k v (fun q => -f q) p = -graphDr k v f p := by
  simp only [graphDr, hf.hasFDerivAt.fun_neg.fderiv, _root_.neg_apply]

theorem graphDz_add {f g : ℝ × E → ℝ} (w : E) {p : ℝ × E}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    graphDz w (fun q => f q + g q) p = graphDz w f p + graphDz w g p := by
  simp only [graphDz, fderiv_fun_add hf hg, _root_.add_apply]

theorem divideRadius_hasFDerivAt {f : ℝ × E → ℝ} {p : ℝ × E}
    (hf : DifferentiableAt ℝ f p) (hr : p.1 ≠ 0) :
    HasFDerivAt (divideRadius f)
      (f p • ((-(p.1 ^ 2)⁻¹) • (ContinuousLinearMap.fst ℝ ℝ E)) +
        p.1⁻¹ • fderiv ℝ f p) p := by
  have hi : HasFDerivAt (fun q : ℝ × E => q.1⁻¹)
      ((-(p.1 ^ 2)⁻¹) • ContinuousLinearMap.fst ℝ ℝ E) p :=
    (hasDerivAt_inv hr).comp_hasFDerivAt p hasFDerivAt_fst
  unfold divideRadius
  simpa only [div_eq_mul_inv] using hf.hasFDerivAt.fun_mul hi

theorem graphDz_divideRadius {f : ℝ × E → ℝ} (w : E) {p : ℝ × E}
    (hf : DifferentiableAt ℝ f p) (hr : p.1 ≠ 0) :
    graphDz w (divideRadius f) p = graphDz w f p / p.1 := by
  unfold graphDz
  rw [(divideRadius_hasFDerivAt hf hr).fderiv]
  simp [div_eq_mul_inv, mul_comm]

theorem graphDr_divideRadius {f : ℝ × E → ℝ} (k : ℝ → ℝ) (v : E) {p : ℝ × E}
    (hf : DifferentiableAt ℝ f p) (hr : p.1 ≠ 0) :
    graphDr k v (divideRadius f) p + divideRadius f p / p.1 = graphDr k v f p / p.1 := by
  unfold graphDr
  rw [(divideRadius_hasFDerivAt hf hr).fderiv]
  unfold divideRadius
  simp only [_root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul, radialVector]
  field_simp; ring

/-- Stream beta, defined pointwise by `-graphDz w Ψ p`. -/
noncomputable def streamBeta (w : E) (Ψ : ℝ × E → ℝ) : ℝ × E → ℝ :=
  fun p => -graphDz w Ψ p

/-- Stream gamma, defined pointwise by `graphDr k v Ψ p + divideRadius Ψ p`. -/
noncomputable def streamGamma (k : ℝ → ℝ) (v : E) (Ψ : ℝ × E → ℝ) : ℝ × E → ℝ :=
  fun p => graphDr k v Ψ p + divideRadius Ψ p

/-- Graph divergence, given by `graphDr k v β p + β p / p.1 + graphDz w γ p`. -/
noncomputable def graphDivergence (k : ℝ → ℝ) (v w : E)
    (β γ : ℝ × E → ℝ) (p : ℝ × E) : ℝ :=
  graphDr k v β p + β p / p.1 + graphDz w γ p

/-- The cylindrical divergence of the actual stream realization is exactly zero. -/
theorem stream_divergence_zero {Ψ : ℝ × E → ℝ} {k : ℝ → ℝ} (v w : E)
    {p : ℝ × E} (hΨ : ContDiffAt ℝ 2 Ψ p) (hk : DifferentiableAt ℝ k p.1)
    (hr : p.1 ≠ 0) :
    graphDivergence k v w (streamBeta w Ψ) (streamGamma k v Ψ) p = 0 := by
  have hDΨ := (hΨ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hΨ' := hΨ.differentiableAt (by norm_num)
  have hZ : DifferentiableAt ℝ (graphDz w Ψ) p := hDΨ.clm_apply (differentiableAt_const _)
  have hR : DifferentiableAt ℝ (graphDr k v Ψ) p :=
    hDΨ.clm_apply (radialVector_hasFDerivAt v hk).differentiableAt
  have hQ : DifferentiableAt ℝ (divideRadius Ψ) p :=
    (divideRadius_hasFDerivAt hΨ' hr).differentiableAt
  unfold graphDivergence streamBeta streamGamma
  rw [graphDr_neg v hZ, graphDz_add w hR hQ, graphDz_divideRadius w hΨ' hr,
    graphDr_graphDz_comm v w hΨ hk]
  ring

theorem graphDr_supported {a b : ℝ} {f : ℝ × E → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) (k : ℝ → ℝ) (v : E) :
    RadialAlias.RadiallySupported a b (graphDr k v f) := by
  intro p hp
  apply radialSupport_fderiv hs
  intro hd
  exact hp (by simp [graphDr, hd])

theorem graphDz_supported {a b : ℝ} {f : ℝ × E → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) (w : E) :
    RadialAlias.RadiallySupported a b (graphDz w f) :=
  fixedDeriv_supported hs (0, w)

theorem graphDr_contDiff_of_support {a b : ℝ} (ha : 0 < a)
    {f : ℝ × E → ℝ} {k : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f)
    (hk : ∀ r : ℝ, r ≠ 0 → ContDiffAt ℝ ∞ k r) (v : E) :
    ContDiff ℝ ∞ (graphDr k v f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.1 = 0
  · have hz : graphDr k v f =ᶠ[𝓝 p] fun _ => 0 := by
      have hnear : ∀ᶠ q : ℝ × E in 𝓝 p, q.1 < a :=
        continuousAt_fst.eventually (Iio_mem_nhds (by simpa [hp] using ha))
      filter_upwards [hnear] with q hq
      exact radial_zero_of_lt (graphDr_supported hs k v) hq
    exact contDiffAt_const.congr_of_eventuallyEq hz
  · exact (hf.fderiv_right (by simp)).contDiffAt.clm_apply
      (contDiffAt_const.prodMk (((hk p.1 hp).comp p contDiffAt_fst).smul contDiffAt_const))

/-- Physical speed, given by `RadialPullback.radialJacobian d r * M`. -/
noncomputable def physicalSpeed (d M r : ℝ) : ℝ := RadialPullback.radialJacobian d r * M

theorem physicalSpeed_smooth (d M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (physicalSpeed d M) r :=
  (contDiffAt_const.mul (contDiffAt_id.rpow_const_of_ne hr)).mul contDiffAt_const

theorem graphDr_eq_physical (d M : ℝ) (v : E) (f : ℝ × E → ℝ) (p : ℝ × E) :
    graphDr (physicalSpeed d M) v f p = RadialPullback.physicalGraphDeriv d M v f p := rfl

end Graph

section Pressure

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Formula (33), with the exact physical shifted primitive. -/
noncomputable def meanPressure (d a b M : ℝ) (hab : a < b) (v : Plane)
    (f : Lift S → ℝ) : Lift S → ℝ :=
  RadialPullback.physicalCompact d a b M (0, v) (pressureSource a b hab f)

/-- Pressure alias, given by `RadialPullback.physicalAlias d a b M (0, v) (pressureSource a b
hab f)`. -/
noncomputable def pressureAlias (d a b M : ℝ) (hab : a < b) (v : Plane)
    (f : Lift S → ℝ) : Lift S → ℝ :=
  RadialPullback.physicalAlias d a b M (0, v) (pressureSource a b hab f)

theorem meanPressure_contDiff {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) :
    ContDiff ℝ ∞ (meanPressure d a b M hab v f) :=
  RadialPullback.physicalCompact_contDiff ha hab hd
    (pressureSource_contDiff hab hf hs) (pressureSource_supported hab hs) M (0, v)

theorem meanPressure_supported {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : Plane) {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (meanPressure d a b M hab v f) :=
  RadialPullback.physicalCompact_supported ha hab hd
    (pressureSource_contDiff hab hf hs) (pressureSource_supported hab hs) M (0, v)

/-- The pressure residual retains the entire cutoff alias with its minus sign. -/
theorem meanPressure_radial_residual {d a b M : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (v : Plane) {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (p : Lift S) (hp : a ≤ p.1) :
    graphDr (physicalSpeed d M) (0, v) (meanPressure d a b M hab v f) p - f p =
      -rho a b hab p.1 * pressureMass f p.2.1 - pressureAlias d a b M hab v f p := by
  rw [graphDr_eq_physical, meanPressure,
    RadialPullback.physicalGraphDeriv_physicalCompact ha hab hd
      (pressureSource_contDiff hab hf hs) (pressureSource_supported hab hs) M (0, v) p hp]
  unfold pressureAlias pressureSource
  ring

end Pressure

section Stream

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Weighted source, given by `p.1 * γd p`. -/
noncomputable def weightedSource (γd : ℝ × E → ℝ) (p : ℝ × E) : ℝ := p.1 * γd p

theorem weightedSource_contDiff {γd : ℝ × E → ℝ} (hγ : ContDiff ℝ ∞ γd) :
    ContDiff ℝ ∞ (weightedSource γd) := contDiff_fst.mul hγ

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem weightedSource_supported {a b : ℝ} {γd : ℝ × E → ℝ}
    (hs : RadialAlias.RadiallySupported a b γd) :
    RadialAlias.RadiallySupported a b (weightedSource γd) := by
  intro p hp
  apply hs
  intro hγ
  exact hp (by simp [weightedSource, hγ])

/-- The actual physical stream `r⁻¹ Ic(r γd)`. -/
noncomputable def streamPotential (d a b M : ℝ) (v : E) (γd : ℝ × E → ℝ) : ℝ × E → ℝ :=
  divideRadius (RadialPullback.physicalCompact d a b M v (weightedSource γd))

theorem streamPotential_contDiff {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : E) {γd : ℝ × E → ℝ} (hγ : ContDiff ℝ ∞ γd)
    (hs : RadialAlias.RadiallySupported a b γd) :
    ContDiff ℝ ∞ (streamPotential d a b M v γd) :=
  divideRadius_contDiff ha
    (RadialPullback.physicalCompact_contDiff ha hab hd (weightedSource_contDiff hγ)
      (weightedSource_supported hs) M v)
    (RadialPullback.physicalCompact_supported ha hab hd (weightedSource_contDiff hγ)
      (weightedSource_supported hs) M v)

theorem streamPotential_supported {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : E) {γd : ℝ × E → ℝ} (hγ : ContDiff ℝ ∞ γd)
    (hs : RadialAlias.RadiallySupported a b γd) :
    RadialAlias.RadiallySupported a b (streamPotential d a b M v γd) :=
  divideRadius_supported
    (RadialPullback.physicalCompact_supported ha hab hd (weightedSource_contDiff hγ)
      (weightedSource_supported hs) M v)

theorem streamBeta_contDiff {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v w : E) {γd : ℝ × E → ℝ} (hγ : ContDiff ℝ ∞ γd)
    (hs : RadialAlias.RadiallySupported a b γd) :
    ContDiff ℝ ∞ (streamBeta w (streamPotential d a b M v γd)) :=
  (graphDz_contDiff (streamPotential_contDiff ha hab hd v hγ hs) w).neg

theorem streamGamma_contDiff {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : E) {γd : ℝ × E → ℝ} (hγ : ContDiff ℝ ∞ γd)
    (hs : RadialAlias.RadiallySupported a b γd) :
    ContDiff ℝ ∞ (streamGamma (physicalSpeed d M) v (streamPotential d a b M v γd)) := by
  have hΨ := streamPotential_contDiff (M := M) ha hab hd v hγ hs
  have hΨs := streamPotential_supported (M := M) ha hab hd v hγ hs
  exact (graphDr_contDiff_of_support ha hΨ hΨs (fun _ hr => physicalSpeed_smooth d M hr) v).add
    (divideRadius_contDiff ha hΨ hΨs)

/-- The constructed axial increment is the desired field minus the exact
compactification defect divided by radius. -/
theorem streamGamma_eq_desired_sub_alias {d a b M : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (v : E) {γd : ℝ × E → ℝ} (hγ : ContDiff ℝ ∞ γd)
    (hs : RadialAlias.RadiallySupported a b γd) (p : ℝ × E) (hp : a ≤ p.1) :
    streamGamma (physicalSpeed d M) v (streamPotential d a b M v γd) p =
      γd p - RadialPullback.physicalAlias d a b M v (weightedSource γd) p / p.1 := by
  have hr : p.1 ≠ 0 := (ha.trans_le hp).ne'
  have hH := RadialPullback.physicalCompact_contDiff ha hab hd (weightedSource_contDiff hγ)
    (weightedSource_supported hs) M v
  change graphDr (physicalSpeed d M) v (divideRadius _) p + divideRadius (divideRadius _) p = _
  rw [show divideRadius (divideRadius (RadialPullback.physicalCompact d a b M v
      (weightedSource γd))) p =
      divideRadius (RadialPullback.physicalCompact d a b M v (weightedSource γd)) p / p.1 from rfl]
  rw [graphDr_divideRadius _ _ (hH.differentiable (by simp) p) hr, graphDr_eq_physical,
    RadialPullback.physicalGraphDeriv_physicalCompact ha hab hd (weightedSource_contDiff hγ)
      (weightedSource_supported hs) M v p hp]
  unfold weightedSource
  field_simp

theorem reconstructed_divergence_zero_of_ne {d a b M : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (v w : E) {γd : ℝ × E → ℝ} (hγ : ContDiff ℝ ∞ γd)
    (hs : RadialAlias.RadiallySupported a b γd) (p : ℝ × E) (hp : p.1 ≠ 0) :
    graphDivergence (physicalSpeed d M) v w
      (streamBeta w (streamPotential d a b M v γd))
      (streamGamma (physicalSpeed d M) v (streamPotential d a b M v γd)) p = 0 :=
  stream_divergence_zero v w
    ((streamPotential_contDiff ha hab hd v hγ hs).contDiffAt.of_le
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le)
    ((physicalSpeed_smooth d M hp).differentiableAt (by simp)) hp

end Stream

section BarIdentities

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Torus periodic lift, given by `∀ r : ℝ, ∀ s : S, FourierAlias.TorusPeriodic (fun Y => f (r,
(s, Y)))`. -/
noncomputable def TorusPeriodicLift (f : Lift S → ℝ) : Prop :=
  ∀ r : ℝ, ∀ s : S, FourierAlias.TorusPeriodic (fun Y => f (r, (s, Y)))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem torusAverage_congr_slice {f g : Lift S → ℝ} (p : ℝ × S)
    (h : ∀ Y : Plane, f (p.1, (p.2, Y)) = g (p.1, (p.2, Y))) :
    torusAverage f p = torusAverage g p := by
  unfold torusAverage torusInner
  apply intervalIntegral.integral_congr
  intro y _
  apply intervalIntegral.integral_congr
  intro x _
  exact h (x, y)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem torusAverage_divideRadius (f : Lift S → ℝ) (p : ℝ × S) :
    torusAverage (divideRadius f) p = torusAverage f p / p.1 := by
  change FourierAlias.torusMean (fun Y => f (p.1, (p.2, Y)) / p.1) =
    FourierAlias.torusMean (fun Y => f (p.1, (p.2, Y))) / p.1
  simpa only [smul_eq_mul, mul_comm, div_eq_mul_inv] using
    FourierAlias.torusMean_smul p.1⁻¹ (fun Y => f (p.1, (p.2, Y)))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem torusAverage_weightedSource (f : Lift S → ℝ) (p : ℝ × S) :
    torusAverage (weightedSource f) p = p.1 * torusAverage f p :=
  FourierAlias.torusMean_smul p.1 (fun Y => f (p.1, (p.2, Y)))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem pressureSource_periodic {a b : ℝ} (hab : a < b) {f : Lift S → ℝ}
    (hp : TorusPeriodicLift f) : TorusPeriodicLift (pressureSource a b hab f) := by
  intro r s Y k
  dsimp [pressureSource]
  have he := hp r s Y k
  dsimp at he
  rw [he]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem weightedSource_periodic {f : Lift S → ℝ} (hp : TorusPeriodicLift f) :
    TorusPeriodicLift (weightedSource f) := by
  intro r s Y k
  dsimp [weightedSource]
  have he := hp r s Y k
  dsimp at he
  rw [he]

omit [NormedSpace ℝ S] in
/-- Fubini and translation invariance give the mean of a genuinely shifted
physical radial integral, retaining all slow parameters. -/
theorem torusMean_shifted_integral {a b : ℝ} (hab : a ≤ b)
    {f : Lift S → ℝ} (hf : Continuous f) (hp : TorusPeriodicLift f)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (v : Plane) (s : S) :
    FourierAlias.torusMean (fun Y => ∫ r in a..b, f (r, (s, Y + φ r • v))) =
      ∫ r in a..b, torusAverage f (r, s) := by
  have hg : Continuous (fun q : ℝ × Plane => f (q.1, (s, q.2 + φ q.1 • v))) :=
    hf.comp (continuous_fst.prodMk (continuous_const.prodMk
      (continuous_snd.add ((hφ.comp continuous_fst).smul continuous_const))))
  rw [FourierAlias.torusMean_intervalIntegral hg hab]
  apply intervalIntegral.integral_congr
  intro r _
  exact FourierAlias.torusMean_translate (hp r s) (φ r • v)

theorem physicalAlias_slice_continuous {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane)
    {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (p : ℝ × S) :
    Continuous (fun Y => RadialPullback.physicalAlias d a b M (0, v) f (p.1, (p.2, Y))) := by
  change Continuous (fun Y => (RadialPullback.radialJacobian d p.1 *
    deriv (interiorCutoff (a ^ d) (b ^ d)) (RadialPullback.powerChart d a p.1)) *
    totalIntegral M ((0 : S), v) (RadialPullback.normalizeSource d a f)
      (RadialPullback.powerChart d a p.1, (p.2, Y)))
  exact continuous_const.mul
    ((totalIntegral_contDiff (M := M) (v := ((0 : S), v))
      (RadialPullback.normalizeSource_contDiff ha hd hf)
      (RadialPullback.normalizeSource_supported ha hab hd hs)).continuous.comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id)))

/-- The exact alias mean is the radial mean mass times its cutoff derivative.
The source need not have zero torus mean at each radius. -/
theorem torusAverage_physicalAlias {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane)
    {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (hp : TorusPeriodicLift f) (p : ℝ × S) :
    torusAverage (RadialPullback.physicalAlias d a b M (0, v) f) p =
      (RadialPullback.radialJacobian d p.1 *
        deriv (interiorCutoff (a ^ d) (b ^ d)) (RadialPullback.powerChart d a p.1)) *
          pressureMass f p.2 := by
  let U := RadialPullback.powerChart d a p.1
  let C := RadialPullback.radialJacobian d p.1 * deriv (interiorCutoff (a ^ d) (b ^ d)) U
  change FourierAlias.torusMean (fun Y => C •
    totalIntegral M ((0 : S), v) (RadialPullback.normalizeSource d a f) (U, (p.2, Y))) = _
  rw [FourierAlias.torusMean_smul]
  have heq : (fun Y => totalIntegral M ((0 : S), v)
      (RadialPullback.normalizeSource d a f) (U, (p.2, Y))) =
      (fun Y => ∫ r in a..b, f (r, (p.2, Y + (M * (r ^ d - U)) • v))) := by
    funext Y
    rw [totalIntegral_eq_radialInterval
      (RadialPullback.normalizeSource_contDiff ha hd hf).continuous
      (RadialPullback.normalizeSource_supported ha hab hd hs),
      RadialPullback.normalized_radial_integral ha hd hab.le hf M U ((0 : S), v) (p.2, Y)]
    simp [Prod.add_def, Prod.smul_def]
  rw [heq, torusMean_shifted_integral hab.le hf.continuous hp
    (continuous_const.fun_mul ((Real.continuous_rpow_const hd.le).fun_sub continuous_const)) v p.2,
    ← pressureMass_eq_interval hf hs p.2]
  rfl

theorem pressureAlias_mean_zero {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane)
    {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (hp : TorusPeriodicLift f) (p : ℝ × S) :
    torusAverage (pressureAlias d a b M hab v f) p = 0 := by
  unfold pressureAlias
  rw [torusAverage_physicalAlias ha hab hd v (pressureSource_contDiff hab hf hs)
    (pressureSource_supported hab hs) (pressureSource_periodic hab hp),
    pressureSource_mass_zero hab hf hs, mul_zero]

/-- Taking the torus mean of the physical compact primitive gives the
ordinary radial compact primitive, with its exact mean-mass term. -/
theorem torusAverage_physicalCompact {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane)
    {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (hp : TorusPeriodicLift f) (p : ℝ × S) (hr : a ≤ p.1) :
    torusAverage (RadialPullback.physicalCompact d a b M (0, v) f) p =
      (∫ r in a..p.1, torusAverage f (r, p.2)) -
        interiorCutoff (a ^ d) (b ^ d) (p.1 ^ d) * pressureMass f p.2 := by
  let φ : ℝ → ℝ := fun r => M * (r ^ d - p.1 ^ d)
  have hφ : Continuous φ :=
    continuous_const.fun_mul ((Real.continuous_rpow_const hd.le).fun_sub continuous_const)
  have hg : Continuous (fun q : Plane × ℝ => f (q.2, (p.2, q.1 + φ q.2 • v))) :=
    hf.continuous.comp (continuous_snd.prodMk (continuous_const.prodMk
      (continuous_fst.add ((hφ.comp continuous_snd).smul continuous_const))))
  let A : Plane → ℝ := fun Y => ∫ r in a..p.1, f (r, (p.2, Y + φ r • v))
  let B : Plane → ℝ := fun Y => ∫ r in a..b, f (r, (p.2, Y + φ r • v))
  let C : ℝ := interiorCutoff (a ^ d) (b ^ d) (p.1 ^ d)
  have hA : Continuous A := FourierAlias.continuous_parameter_interval hg hr
  have hB : Continuous B := FourierAlias.continuous_parameter_interval hg hab.le
  have heq : (fun Y => RadialPullback.physicalCompact d a b M ((0 : S), v) f
      (p.1, (p.2, Y))) = fun Y => A Y - C • B Y := by
    funext Y
    simpa [A, B, C, φ, Prod.add_def, Prod.smul_def] using
      RadialPullback.physicalCompact_eq_radialIntegral ha hab hd hf hs M ((0 : S), v)
        (p.1, (p.2, Y)) hr
  change FourierAlias.torusMean (fun Y => RadialPullback.physicalCompact d a b M ((0 : S), v) f
    (p.1, (p.2, Y))) = _
  rw [heq, FourierAlias.torusMean_sub hA (continuous_const.fun_smul hB),
      FourierAlias.torusMean_smul]
  change FourierAlias.torusMean A - C * FourierAlias.torusMean B = _
  rw [torusMean_shifted_integral hr hf.continuous hp hφ v p.2,
    torusMean_shifted_integral hab.le hf.continuous hp hφ v p.2,
    ← pressureMass_eq_interval hf hs p.2]

/-- Zero integrated bar mass removes the compactification term from the bar
exactly. This is an identity on the whole radial line. -/
theorem torusAverage_physicalCompact_of_mass_zero {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane)
    {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (hp : TorusPeriodicLift f) (p : ℝ × S) (hm : pressureMass f p.2 = 0) :
    torusAverage (RadialPullback.physicalCompact d a b M (0, v) f) p =
      ∫ r in a..p.1, torusAverage f (r, p.2) := by
  by_cases hr : a ≤ p.1
  · rw [torusAverage_physicalCompact ha hab hd v hf hs hp p hr, hm, mul_zero, sub_zero]
  · have hlt : p.1 < a := lt_of_not_ge hr
    have hzero : torusAverage (RadialPullback.physicalCompact d a b M ((0 : S), v) f) p = 0 :=
      torusAverage_zero_of_forall fun Y =>
        radial_zero_of_lt (RadialPullback.physicalCompact_supported ha hab hd hf hs M ((0 : S), v))
            hlt
    rw [hzero]
    symm
    have hi : EqOn (fun r => torusAverage f (r, p.2)) (fun _ => 0) (uIcc a p.1) := by
      intro r hr'
      rw [uIcc_of_ge hlt.le] at hr'
      exact radial_zero_of_le (torusAverage_contDiff hf).continuous (torusAverage_supported hs)
          hr'.2
    rw [intervalIntegral.integral_congr hi, intervalIntegral.integral_zero]

theorem meanPressure_bar_eq_integral {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane)
    {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (hp : TorusPeriodicLift f) (p : ℝ × S) :
    torusAverage (meanPressure d a b M hab v f) p =
      ∫ r in a..p.1, torusAverage f (r, p.2) - rho a b hab r * pressureMass f p.2 := by
  rw [meanPressure, torusAverage_physicalCompact_of_mass_zero ha hab hd v
    (pressureSource_contDiff hab hf hs) (pressureSource_supported hab hs)
    (pressureSource_periodic hab hp) p (pressureSource_mass_zero hab hf hs p.2)]
  apply intervalIntegral.integral_congr
  intro r _
  exact torusAverage_pressureSource hab hf (r, p.2)

/-- The derivative of the actual mean pressure, needed for weighted moment
integration. It is derived from the integral reconstruction. -/
theorem meanPressure_bar_hasDerivAt {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane)
    {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (hp : TorusPeriodicLift f) (s : S) (r : ℝ) :
    HasDerivAt (fun R => torusAverage (meanPressure d a b M hab v f) (R, s))
      (torusAverage f (r, s) - rho a b hab r * pressureMass f s) r := by
  have heq : (fun R => torusAverage (meanPressure d a b M hab v f) (R, s)) =
      fun R => ∫ t in a..R, torusAverage f (t, s) - rho a b hab t * pressureMass f s :=
    funext (fun R => meanPressure_bar_eq_integral ha hab hd v hf hs hp (R, s))
  rw [heq]
  have hc : Continuous (fun t => torusAverage f (t, s) - rho a b hab t * pressureMass f s) :=
    ((torusAverage_contDiff hf).continuous.comp (continuous_id.prodMk continuous_const)).sub
      ((rho_contDiff a b hab).continuous.mul continuous_const)
  exact (hc.integral_hasStrictDerivAt a r).hasDerivAt

end BarIdentities

section GlobalStream

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem streamBeta_supported {a b : ℝ} {Ψ : ℝ × E → ℝ}
    (hs : RadialAlias.RadiallySupported a b Ψ) (w : E) :
    RadialAlias.RadiallySupported a b (streamBeta w Ψ) := by
  intro p hp
  apply graphDz_supported hs w
  intro hz
  exact hp (by simp [streamBeta, hz])

theorem streamGamma_supported {a b : ℝ} {Ψ : ℝ × E → ℝ}
    (hs : RadialAlias.RadiallySupported a b Ψ) (k : ℝ → ℝ) (v : E) :
    RadialAlias.RadiallySupported a b (streamGamma k v Ψ) := by
  intro p hp
  by_contra hn
  have hR : graphDr k v Ψ p = 0 := by
    by_contra hne
    exact hn (graphDr_supported hs k v hne)
  have hQ : divideRadius Ψ p = 0 := by
    by_contra hne
    exact hn (divideRadius_supported hs hne)
  exact hp (by simp [streamGamma, hR, hQ])

/-- The support proof handles the axis as well as the positive annulus. -/
theorem reconstructed_divergence_zero {d a b M : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (v w : E) {γd : ℝ × E → ℝ} (hγ : ContDiff ℝ ∞ γd)
    (hs : RadialAlias.RadiallySupported a b γd) (p : ℝ × E) :
    graphDivergence (physicalSpeed d M) v w
      (streamBeta w (streamPotential d a b M v γd))
      (streamGamma (physicalSpeed d M) v (streamPotential d a b M v γd)) p = 0 := by
  by_cases hp : p.1 ≠ 0
  · exact reconstructed_divergence_zero_of_ne ha hab hd v w hγ hs p hp
  · have hp₀ : p.1 = 0 := not_ne_iff.mp hp
    have hpa : p.1 < a := by simpa [hp₀] using ha
    have hΨs := streamPotential_supported (M := M) ha hab hd v hγ hs
    have hβs := streamBeta_supported hΨs w
    have hγs := streamGamma_supported hΨs (physicalSpeed d M) v
    have hβ := radial_zero_of_lt hβs hpa
    have hDβ := radial_zero_of_lt (radialSupport_fderiv hβs) hpa
    have hDγ := radial_zero_of_lt (radialSupport_fderiv hγs) hpa
    simp only [graphDivergence, graphDr, graphDz, hβ, hDβ, hDγ,
      _root_.zero_apply, zero_div, add_zero]

theorem streamGamma_eq_desired_sub_alias_global {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : E)
    {γd : ℝ × E → ℝ} (hγ : ContDiff ℝ ∞ γd) (hs : RadialAlias.RadiallySupported a b γd)
    (p : ℝ × E) :
    streamGamma (physicalSpeed d M) v (streamPotential d a b M v γd) p =
      γd p - RadialPullback.physicalAlias d a b M v (weightedSource γd) p / p.1 := by
  by_cases hp : a ≤ p.1
  · exact streamGamma_eq_desired_sub_alias ha hab hd v hγ hs p hp
  · have hpa : p.1 < a := lt_of_not_ge hp
    have hΨs := streamPotential_supported (M := M) ha hab hd v hγ hs
    rw [radial_zero_of_lt (streamGamma_supported hΨs (physicalSpeed d M) v) hpa,
      radial_zero_of_lt hs hpa,
      radial_zero_of_lt (RadialPullback.physicalAlias_supported ha hab hd M v (weightedSource γd))
          hpa]
    simp

/-- The total physical radial integral, written in normalized transport coordinates. -/
noncomputable def physicalTotal (d a M : ℝ) (v : E) (g : ℝ × E → ℝ) (p : ℝ × E) : ℝ :=
  totalIntegral M v (RadialPullback.normalizeSource d a g)
    (RadialPullback.liftChart (RadialPullback.powerChart d a) p)

theorem physicalTotal_eq_integral {d a b M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v : E) {g : ℝ × E → ℝ} (hg : ContDiff ℝ ∞ g) (hs : RadialAlias.RadiallySupported a b g)
    (p : ℝ × E) (hp : a ≤ p.1) :
    physicalTotal d a M v g p =
      ∫ r in a..b, g (r, p.2 + (M * (r ^ d - p.1 ^ d)) • v) := by
  unfold physicalTotal RadialPullback.liftChart
  rw [RadialPullback.powerChart_eq ha (by linarith) d,
    totalIntegral_eq_radialInterval (RadialPullback.normalizeSource_contDiff ha hd hg).continuous
      (RadialPullback.normalizeSource_supported ha hab hd hs),
    RadialPullback.normalized_radial_integral ha hd hab.le hg]

end GlobalStream

section FinalBar

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem meanPressure_radial_residual_global {d a b M : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (v : Plane) {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (p : Lift S) :
    graphDr (physicalSpeed d M) (0, v) (meanPressure d a b M hab v f) p - f p =
      -rho a b hab p.1 * pressureMass f p.2.1 - pressureAlias d a b M hab v f p := by
  rw [graphDr_eq_physical, meanPressure,
    RadialPullback.physicalGraphDeriv_physicalCompact_global ha hab hd
      (pressureSource_contDiff hab hf hs) (pressureSource_supported hab hs) M (0, v) p]
  unfold pressureAlias pressureSource
  ring

/-- Formula (33), with the physical cutoff derivative and total primitive
fully displayed. No radial-cutoff commutator is discarded. -/
theorem meanPressure_radial_residual_cutoff {d a b M : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (v : Plane) {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (p : Lift S) :
    graphDr (physicalSpeed d M) (0, v) (meanPressure d a b M hab v f) p - f p =
      -rho a b hab p.1 * pressureMass f p.2.1 -
        deriv (RadialPullback.physicalCutoff d a b) p.1 *
          physicalTotal d a M (0, v) (pressureSource a b hab f) p := by
  rw [meanPressure_radial_residual_global ha hab hd v hf hs]
  rw [pressureAlias, RadialPullback.physicalAlias_eq_cutoff_derivative_global ha hab hd]
  rfl

omit [NormedSpace ℝ S] in
theorem torusAverage_sub {f g : Lift S → ℝ} (hf : Continuous f) (hg : Continuous g)
    (p : ℝ × S) : torusAverage (fun q => f q - g q) p = torusAverage f p - torusAverage g p := by
  change FourierAlias.torusMean (fun Y => f (p.1, (p.2, Y)) - g (p.1, (p.2, Y))) =
    FourierAlias.torusMean (fun Y => f (p.1, (p.2, Y))) -
      FourierAlias.torusMean (fun Y => g (p.1, (p.2, Y)))
  exact FourierAlias.torusMean_sub
    (hf.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
    (hg.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))

theorem torusAverage_slice_contDiff {f : Lift S → ℝ} (hf : ContDiff ℝ ∞ f) (s : S) :
    ContDiff ℝ ∞ (fun r => torusAverage f (r, s)) :=
  (torusAverage_contDiff hf).comp (contDiff_id.prodMk contDiff_const)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem torusAverage_slice_hasCompactSupport {a b : ℝ} {f : Lift S → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) (s : S) :
    HasCompactSupport (fun r => torusAverage f (r, s)) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (fun _ hr => torusAverage_supported hs hr)

/-- Zero weighted bar mass yields precisely the prescribed axial bar, although
the full axial field includes the nonzero compactification alias. -/
theorem streamGamma_bar_eq_desired {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane)
    {γd : Lift S → ℝ} (hγ : ContDiff ℝ ∞ γd) (hs : RadialAlias.RadiallySupported a b γd)
    (hp : TorusPeriodicLift γd)
    (hm : ∀ s : S, (∫ r, r * torusAverage γd (r, s)) = 0) (p : ℝ × S) :
    torusAverage (streamGamma (physicalSpeed d M) (0, v)
      (streamPotential d a b M (0, v) γd)) p = torusAverage γd p := by
  have hAs := RadialPullback.physicalAlias_supported ha hab hd M ((0 : S), v) (weightedSource γd)
  have hAc := RadialPullback.physicalAlias_contDiff ha hab hd (weightedSource_contDiff hγ)
    (weightedSource_supported hs) M ((0 : S), v)
  have heq : streamGamma (physicalSpeed d M) (0, v) (streamPotential d a b M (0, v) γd) =
      fun q => γd q - divideRadius (RadialPullback.physicalAlias d a b M (0, v)
        (weightedSource γd)) q :=
    funext (streamGamma_eq_desired_sub_alias_global ha hab hd (0, v) hγ hs)
  rw [heq, torusAverage_sub hγ.continuous (divideRadius_contDiff ha hAc hAs).continuous,
    torusAverage_divideRadius, torusAverage_physicalAlias ha hab hd v
      (weightedSource_contDiff hγ) (weightedSource_supported hs) (weightedSource_periodic hp)]
  have hmass : pressureMass (weightedSource γd) p.2 = 0 := by
    unfold pressureMass
    simp_rw [torusAverage_weightedSource]
    exact hm p.2
  rw [hmass, mul_zero, zero_div, sub_zero]

end FinalBar

end NavierStokes.PressureStream
