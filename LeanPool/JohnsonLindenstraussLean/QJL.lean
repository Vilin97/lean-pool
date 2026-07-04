import JL.Rotation

/-!
# Quantized Johnson–Lindenstrauss (QJL): unbiasedness of the 1-bit estimator

This file formalizes the **unbiasedness theorem** at the heart of QJL / TurboQuant's
one-bit key quantization. It is built in three increasing layers:

1. **Gaussian absolute moment** (`integral_abs_gaussianReal`):
   `E|Z| = √(2/π)` for `Z ~ N(0,1)`.

2. **The asymmetric sign-product identity** (`sign_product_identity`): for a standard
   Gaussian vector `g` in `ℝ^d`, a unit vector `u`, and an arbitrary `v`,
   `E[ sign ⟪u,g⟫ · ⟪v,g⟫ ] = √(2/π) · ⟪u,v⟫`.
   This is the asymmetric one-bit (one-sided, linear) analogue; it is *not* the symmetric
   Grothendieck arcsin identity `E[ sign ⟪u,g⟫ · sign ⟪v,g⟫ ] = (2/π)·arcsin ⟪u,v⟫`.
   The proof decomposes `v = ⟪u,v⟫·u + v⊥` with `v⊥ ⟂ u`, uses that `⟪v⊥,g⟫` is
   *independent* of `⟪u,g⟫` (orthogonal linear functionals of a standard Gaussian are
   independent, via `HasGaussianLaw.indepFun_of_covariance_eq_zero`), and that the cross term
   vanishes because `E⟪v⊥,g⟫ = 0`.

3. **QJL asymmetric estimator unbiasedness** (`qjlEstimator_unbiased`): the 1-bit estimator
   `estimator S key q = √(π/2)·(1/m)·Σᵢ sign ⟪key/‖key‖, sᵢ⟫ · ⟪q, sᵢ⟫`
   over an `m × d` i.i.d. standard-Gaussian sketch is *unbiased* for the normalized inner
   product: `E[estimator] = ⟪key/‖key‖, q⟫`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal RealInnerProductSpace

namespace JL

/-! ## Part 1: the Gaussian absolute moment `E|Z| = √(2/π)` -/

/-- Measurability of the real sign function. -/
theorem measurable_real_sign : Measurable Real.sign := by
  unfold Real.sign
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    measurable_const measurable_const

/-- `Real.sign r * r = |r|`. -/
theorem sign_mul_self (r : ℝ) : Real.sign r * r = |r| := by
  obtain hn | rfl | hp := lt_trichotomy r 0
  · rw [Real.sign_of_neg hn, abs_of_neg hn]; ring
  · simp
  · rw [Real.sign_of_pos hp, abs_of_pos hp]; ring

/-- The half-line first moment: `∫_{x>0} x·exp(-x²/2) dx = 1`. -/
theorem integral_Ioi_mul_exp : ∫ x in Set.Ioi (0 : ℝ), x * rexp (-(1 / 2) * x ^ 2) = 1 := by
  have hcont : ContinuousWithinAt (fun x : ℝ => -rexp (-(1 / 2) * x ^ 2)) (Set.Ici 0) 0 :=
    (by fun_prop : Continuous (fun x : ℝ => -rexp (-(1 / 2) * x ^ 2))).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun x : ℝ => -rexp (-(1 / 2) * x ^ 2)) (x * rexp (-(1 / 2) * x ^ 2)) x := by
    intro x _
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hg : HasDerivAt (fun x : ℝ => -(1 / 2) * x ^ 2) (-(1 / 2) * (2 * x)) x :=
      hsq.const_mul (-(1 / 2))
    have h2 := hg.exp.neg
    rw [show x * rexp (-(1 / 2) * x ^ 2)
        = -(rexp (-(1 / 2) * x ^ 2) * (-(1 / 2) * (2 * x))) from by ring]
    exact h2
  have hf'int : IntegrableOn (fun x : ℝ => x * rexp (-(1 / 2) * x ^ 2)) (Set.Ioi 0) :=
    (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn
  have hinner : Filter.Tendsto (fun x : ℝ => -(1 / 2) * x ^ 2) Filter.atTop Filter.atBot :=
    (Filter.tendsto_pow_atTop (two_ne_zero)).const_mul_atTop_of_neg (by norm_num)
  have htend : Filter.Tendsto (fun x : ℝ => -rexp (-(1 / 2) * x ^ 2)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => rexp (-(1 / 2) * x ^ 2)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hinner
    simpa using h1.neg
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hf'int htend
  rw [hmain]
  simp [Real.exp_zero]

/-- **Gaussian absolute moment.** `E|Z| = √(2/π)` for `Z ~ N(0,1)`. -/
theorem integral_abs_gaussianReal :
    ∫ x, |x| ∂(gaussianReal 0 1) = Real.sqrt (2 / π) := by
  -- `∫ |x| · exp(-x²/2) dx = 2`, via the even-function reduction `∫ f|x| = 2∫_{Ioi 0} f`.
  have hcore : ∫ x : ℝ, |x| * rexp (-(1 / 2) * x ^ 2) = 2 := by
    have e1 : (fun x : ℝ => |x| * rexp (-(1 / 2) * x ^ 2))
        = (fun x : ℝ => (fun t : ℝ => t * rexp (-(1 / 2) * t ^ 2)) |x|) := by
      funext x
      show |x| * rexp (-(1 / 2) * x ^ 2) = |x| * rexp (-(1 / 2) * |x| ^ 2)
      rw [sq_abs]
    calc ∫ x : ℝ, |x| * rexp (-(1 / 2) * x ^ 2)
        = ∫ x : ℝ, (fun t : ℝ => t * rexp (-(1 / 2) * t ^ 2)) |x| := by rw [e1]
      _ = 2 * ∫ x in Set.Ioi (0 : ℝ), (fun t : ℝ => t * rexp (-(1 / 2) * t ^ 2)) x :=
          integral_comp_abs (f := fun t : ℝ => t * rexp (-(1 / 2) * t ^ 2))
      _ = 2 * ∫ x in Set.Ioi (0 : ℝ), x * rexp (-(1 / 2) * x ^ 2) := rfl
      _ = 2 := by rw [integral_Ioi_mul_exp]; norm_num
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have hint : ∀ x : ℝ, gaussianPDFReal 0 1 x • |x|
      = (√(2 * π))⁻¹ * (|x| * rexp (-(1 / 2) * x ^ 2)) := by
    intro x
    rw [stdGaussian_pdf, smul_eq_mul, show (-x ^ 2 / 2 : ℝ) = -(1 / 2) * x ^ 2 from by ring]
    ring
  simp_rw [hint]
  rw [integral_const_mul, hcore]
  -- `(√(2π))⁻¹ · 2 = √(2/π)`.
  have hL : (0 : ℝ) ≤ (√(2 * π))⁻¹ * 2 := by positivity
  have hR : (0 : ℝ) ≤ Real.sqrt (2 / π) := Real.sqrt_nonneg _
  have key : ((√(2 * π))⁻¹ * 2) ^ 2 = (Real.sqrt (2 / π)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity), mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  calc (√(2 * π))⁻¹ * 2
      = Real.sqrt (((√(2 * π))⁻¹ * 2) ^ 2) := (Real.sqrt_sq hL).symm
    _ = Real.sqrt ((Real.sqrt (2 / π)) ^ 2) := by rw [key]
    _ = Real.sqrt (2 / π) := Real.sqrt_sq hR

/-! ## Part 2: the asymmetric sign-product identity -/

/-- Integrability of a Gaussian linear functional `g ↦ ⟪w, g⟫`. -/
theorem integrable_inner_stdGaussian {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪w, g⟫)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hgl : HasGaussianLaw (⇑(innerSL ℝ w))
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    IsGaussian.hasGaussianLaw_id.map (innerSL ℝ w)
  refine hgl.integrable.congr ?_
  filter_upwards with g
  simp [innerSL_apply_apply]

/-- **Asymmetric sign-product identity.** For a standard Gaussian vector `g` in `ℝ^d`,
a unit vector `u` and an arbitrary `v`,
`E[ sign ⟪u,g⟫ · ⟪v,g⟫ ] = √(2/π) · ⟪u,v⟫`.

This is the asymmetric one-bit (one-sided, linear) identity; it is *not* the symmetric
Grothendieck arcsin identity `E[ sign ⟪u,g⟫ · sign ⟪v,g⟫ ] = (2/π)·arcsin ⟪u,v⟫`.

The proof writes `v = ⟪u,v⟫·u + v⊥` with `v⊥ ⟂ u`. The `v⊥` part contributes
`E[ sign ⟪u,g⟫ · ⟪v⊥,g⟫ ] = E[sign ⟪u,g⟫]·E[⟪v⊥,g⟫] = 0` because the two orthogonal linear
functionals are independent (`HasGaussianLaw.indepFun_of_covariance_eq_zero`) and `E⟪v⊥,g⟫ = 0`;
the `u` part contributes `⟪u,v⟫·E|⟪u,g⟫| = ⟪u,v⟫·√(2/π)`. -/
theorem sign_product_identity {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
    ∫ g, Real.sign (⟪u, g⟫) * ⟪v, g⟫ ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))
      = Real.sqrt (2 / π) * ⟪u, v⟫ := by
  classical
  set μ : Measure (EuclideanSpace ℝ (Fin d)) :=
    ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)) with hμ
  set vp : EuclideanSpace ℝ (Fin d) := v - ⟪u, v⟫ • u with hvp
  -- `⟪u, v⊥⟫ = 0`.
  have hperp : ⟪u, vp⟫ = 0 := by
    rw [hvp, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
    ring
  -- pointwise decomposition of the integrand
  have hpt : ∀ g : EuclideanSpace ℝ (Fin d), Real.sign (⟪u, g⟫) * ⟪v, g⟫
      = ⟪u, v⟫ * |⟪u, g⟫| + Real.sign (⟪u, g⟫) * ⟪vp, g⟫ := by
    intro g
    have hvg : ⟪v, g⟫ = ⟪u, v⟫ * ⟪u, g⟫ + ⟪vp, g⟫ := by
      rw [hvp, inner_sub_left, real_inner_smul_left]; ring
    rw [hvg, show Real.sign (⟪u, g⟫) * (⟪u, v⟫ * ⟪u, g⟫ + ⟪vp, g⟫)
        = ⟪u, v⟫ * (Real.sign (⟪u, g⟫) * ⟪u, g⟫) + Real.sign (⟪u, g⟫) * ⟪vp, g⟫ from by ring,
      sign_mul_self]
  -- `E|⟪u,g⟫| = √(2/π)`.
  have habs : ∫ g, |⟪u, g⟫| ∂μ = √(2 / π) := by
      have hns : ‖innerSL ℝ u‖ ^ 2 = 1 := by rw [innerSL_apply_norm, hu]; norm_num
      have hgl : HasGaussianLaw (⇑(innerSL ℝ u))
          (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        IsGaussian.hasGaussianLaw_id.map (innerSL ℝ u)
      have hmap' : μ.map (⇑(innerSL ℝ u)) = gaussianReal 0 1 := by
        rw [hμ, hgl.map_eq_gaussianReal,
          integral_strongDual_stdGaussian (innerSL ℝ u),
          variance_dual_stdGaussian (innerSL ℝ u), hns, Real.toNNReal_one]
      have e2 : ∫ g, |⟪u, g⟫| ∂μ = ∫ g, |(innerSL ℝ u) g| ∂μ := by
        simp only [innerSL_apply_apply]
      rw [e2, ← integral_abs_gaussianReal, ← hmap',
        integral_map (by fun_prop) (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|) _)]
  -- The cross term `E[sign ⟪u,g⟫ · ⟪v⊥,g⟫] = 0`.
  have hWzero : ∫ g, ⟪vp, g⟫ ∂μ = 0 := by
    have h := integral_strongDual_stdGaussian (innerSL ℝ vp)
    rw [hμ]; simpa [innerSL_apply_apply] using h
  have hSignAE : AEStronglyMeasurable (fun g : EuclideanSpace ℝ (Fin d) => Real.sign (⟪u, g⟫)) μ :=
    (measurable_real_sign.comp
      (by fun_prop : Measurable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫))).aestronglyMeasurable
  have hSignInt : Integrable (fun g : EuclideanSpace ℝ (Fin d) => Real.sign (⟪u, g⟫)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hSignAE ?_
    filter_upwards with g
    rcases Real.sign_apply_eq (⟪u, g⟫) with h | h | h <;> rw [h] <;> norm_num
  have hpair : HasGaussianLaw (fun g : EuclideanSpace ℝ (Fin d) => (⟪u, g⟫, ⟪vp, g⟫)) μ := by
    rw [hμ]
    refine (IsGaussian.hasGaussianLaw_id.map ((innerSL ℝ u).prod (innerSL ℝ vp))).congr ?_
    filter_upwards with g
    simp [Function.comp, ContinuousLinearMap.prod_apply, innerSL_apply_apply]
  have hcov : cov[fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫,
      fun g : EuclideanSpace ℝ (Fin d) => ⟪vp, g⟫; μ] = 0 := by
    rw [hμ, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id u vp, covarianceBilin_stdGaussian]
    exact hperp
  have hind : IndepFun (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫)
      (fun g : EuclideanSpace ℝ (Fin d) => ⟪vp, g⟫) μ :=
    hpair.indepFun_of_covariance_eq_zero hcov
  have hindS : IndepFun (fun g : EuclideanSpace ℝ (Fin d) => Real.sign (⟪u, g⟫))
      (fun g : EuclideanSpace ℝ (Fin d) => ⟪vp, g⟫) μ :=
    hind.comp measurable_real_sign measurable_id
  have hcross : ∫ g, Real.sign (⟪u, g⟫) * ⟪vp, g⟫ ∂μ = 0 := by
    rw [hindS.integral_fun_mul_eq_mul_integral hSignAE
        (integrable_inner_stdGaussian vp).aestronglyMeasurable, hWzero, mul_zero]
  -- assemble
  have hI1 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, v⟫ * |⟪u, g⟫|) μ :=
    ((integrable_inner_stdGaussian u).abs).const_mul _
  have hI2 : Integrable (fun g : EuclideanSpace ℝ (Fin d) => Real.sign (⟪u, g⟫) * ⟪vp, g⟫) μ :=
    hindS.integrable_mul hSignInt (integrable_inner_stdGaussian vp)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hI1 hI2,
    integral_const_mul, habs, hcross, add_zero, mul_comm]

/-! ## Part 3: QJL asymmetric 1-bit estimator unbiasedness -/

/-- Integrability of `g ↦ sign ⟪u,g⟫ · ⟪w,g⟫` under a standard Gaussian: the sign factor is
bounded by `1` and `g ↦ ⟪w,g⟫` is integrable. -/
theorem integrable_sign_inner_mul {d : ℕ} (u w : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun g : EuclideanSpace ℝ (Fin d) => Real.sign (⟪u, g⟫) * ⟪w, g⟫)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  refine (integrable_inner_stdGaussian w).bdd_mul (c := 1) ?_ ?_
  · exact (measurable_real_sign.comp
      (by fun_prop : Measurable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫))).aestronglyMeasurable
  · filter_upwards with g
    rcases Real.sign_apply_eq (⟪u, g⟫) with h | h | h <;> rw [h] <;> norm_num

/-- Marginalization: integrating a function of a single coordinate against a product of i.i.d.
probability measures equals the single-coordinate integral. -/
theorem integral_eval_pi {m : ℕ} {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] (i : Fin m) (f : E → ℝ) (hf : AEStronglyMeasurable f P) :
    ∫ S : Fin m → E, f (S i) ∂(Measure.pi (fun _ => P)) = ∫ x, f x ∂P := by
  have hmap : Measure.map (Function.eval i) (Measure.pi (fun _ : Fin m => P)) = P :=
    (measurePreserving_eval (μ := fun _ : Fin m => P) i).map_eq
  have h := integral_map (μ := Measure.pi (fun _ : Fin m => P)) (φ := Function.eval i) (f := f)
    (measurable_pi_apply i).aemeasurable (by rwa [hmap])
  rw [hmap] at h
  exact h.symm

/-- **The QJL asymmetric 1-bit estimator.** Given an `m × d` sketch `S` whose rows `S i` are
i.i.d. standard Gaussian vectors, a `key` and a `query` `q`,
`estimator = √(π/2) · (1/m) · Σᵢ sign ⟪key/‖key‖, sᵢ⟫ · ⟪q, sᵢ⟫`. -/
noncomputable def qjlEstimator {m d : ℕ} (key q : EuclideanSpace ℝ (Fin d))
    (S : Fin m → EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.sqrt (π / 2) *
    ((m : ℝ)⁻¹ * ∑ i, Real.sign (⟪‖key‖⁻¹ • key, S i⟫) * ⟪q, S i⟫)

/-- **QJL unbiasedness.** Over an `m × d` i.i.d. standard-Gaussian sketch, the asymmetric 1-bit
estimator is unbiased for the normalized inner product `⟪key/‖key‖, q⟫`. -/
theorem qjlEstimator_unbiased {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) (hkey : key ≠ 0) :
    ∫ S, qjlEstimator key q S
        ∂(Measure.pi
          (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))
      = ⟪‖key‖⁻¹ • key, q⟫ := by
  have hkne : ‖key‖ ≠ 0 := by simpa [norm_eq_zero] using hkey
  have hu : ‖(‖key‖⁻¹ • key : EuclideanSpace ℝ (Fin d))‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hkne
  -- per-row integrability under the product measure
  have hsummand : ∀ i : Fin m,
      Integrable (fun S : Fin m → EuclideanSpace ℝ (Fin d) =>
        Real.sign (⟪‖key‖⁻¹ • key, S i⟫) * ⟪q, S i⟫)
        (Measure.pi
          (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
    intro i
    have hmap : Measure.map (Function.eval i)
        (Measure.pi
          (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))
        = ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)) :=
      (measurePreserving_eval
        (μ := fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) i).map_eq
    have hI : Integrable (fun g => Real.sign (⟪‖key‖⁻¹ • key, g⟫) * ⟪q, g⟫)
        (Measure.map (Function.eval i)
          (Measure.pi
            (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))) := by
      rw [hmap]; exact integrable_sign_inner_mul (‖key‖⁻¹ • key) q
    exact hI.comp_measurable (measurable_pi_apply i)
  -- per-row expectation is the sign-product identity
  have hrow : ∀ i : Fin m,
      ∫ S : Fin m → EuclideanSpace ℝ (Fin d),
          Real.sign (⟪‖key‖⁻¹ • key, S i⟫) * ⟪q, S i⟫
          ∂(Measure.pi
            (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))
        = Real.sqrt (2 / π) * ⟪‖key‖⁻¹ • key, q⟫ := by
    intro i
    have h := integral_eval_pi
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) i
      (fun g => Real.sign (⟪‖key‖⁻¹ • key, g⟫) * ⟪q, g⟫)
      (integrable_sign_inner_mul (‖key‖⁻¹ • key) q).aestronglyMeasurable
    rw [h]
    exact sign_product_identity (‖key‖⁻¹ • key) q hu
  -- assemble via linearity of the integral
  simp only [qjlEstimator]
  rw [integral_const_mul, integral_const_mul,
    integral_finsetSum Finset.univ (fun i _ => hsummand i)]
  rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hsqrt : Real.sqrt (π / 2) * Real.sqrt (2 / π) = 1 := by
    rw [← Real.sqrt_mul (by positivity), show (π / 2) * (2 / π) = 1 by field_simp, Real.sqrt_one]
  calc Real.sqrt (π / 2) *
          ((m : ℝ)⁻¹ * ((m : ℝ) * (Real.sqrt (2 / π) * ⟪‖key‖⁻¹ • key, q⟫)))
      = (Real.sqrt (π / 2) * Real.sqrt (2 / π)) *
          (((m : ℝ)⁻¹ * (m : ℝ)) * ⟪‖key‖⁻¹ • key, q⟫) := by ring
    _ = 1 * (1 * ⟪‖key‖⁻¹ • key, q⟫) := by rw [hsqrt, inv_mul_cancel₀ hmne]
    _ = ⟪‖key‖⁻¹ • key, q⟫ := by ring

/-- **QJL unbiasedness, un-normalized form.** `‖key‖ · E[estimator] = ⟪key, q⟫`. -/
theorem qjlEstimator_unbiased_inner {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) (hkey : key ≠ 0) :
    ‖key‖ * (∫ S, qjlEstimator key q S
        ∂(Measure.pi
          (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))))
      = ⟪key, q⟫ := by
  have hkne : ‖key‖ ≠ 0 := by simpa [norm_eq_zero] using hkey
  rw [qjlEstimator_unbiased hm key q hkey, real_inner_smul_left, ← mul_assoc,
    mul_inv_cancel₀ hkne, one_mul]

end JL
