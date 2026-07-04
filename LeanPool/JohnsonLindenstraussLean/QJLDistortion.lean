import JL.QJL
import JL.GaussianTail
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.SubGaussian

/-!
# QJL distortion / concentration bound

This file proves the **distortion (concentration) bound** for the QJL asymmetric 1-bit
estimator defined in `JL/QJL.lean`. With `m` sign-bits, the estimator is close to the true
normalized inner product `⟪key/‖key‖, q⟫` with high probability. It is built in three layers:

1. **Per-row variance** (`qjl_perrow_variance_le`): for a single standard-Gaussian `g`, unit `u`
   and arbitrary `q`, `Var[sign ⟪u,g⟫ · ⟪q,g⟫] ≤ ‖q‖²` (and, with the `√(π/2)` scaling, the
   per-row estimator term has variance `≤ (π/2)‖q‖²`).

2. **Estimator variance** (`qjlEstimator_variance_le`): the `m` per-row terms are i.i.d. under the
   product measure, so by additivity of variance over independent summands
   `Var[qjlEstimator] ≤ (π/2)‖q‖² / m`. The cross-row independence is supplied by mathlib's
   `ProbabilityTheory.variance_sum_pi`.

3. **Chebyshev concentration** (`qjlEstimator_concentration`): combining the variance bound with
   Chebyshev's inequality gives
   `P(|qjlEstimator − ⟪key/‖key‖,q⟫| ≥ ε) ≤ (π/2)‖q‖² / (m·ε²)`,
   so `m = O(‖q‖²/(ε²δ))` sign-bits suffice for additive error `ε` with probability `1−δ`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal RealInnerProductSpace

namespace JL

/-! ## Part 1: per-row second moment / variance of the sign-product term -/

/-- Second moment of a Gaussian linear functional: `E⟪q,g⟫² = ‖q‖²`.
This is the variance of the (mean-zero) dual functional `innerSL ℝ q`. -/
theorem integral_inner_sq_stdGaussian {d : ℕ} (q : EuclideanSpace ℝ (Fin d)) :
    ∫ g, ⟪q, g⟫ ^ 2 ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) = ‖q‖ ^ 2 := by
  have hmean := integral_strongDual_stdGaussian (innerSL ℝ q)
  have hvar := variance_dual_stdGaussian (innerSL ℝ q)
  rw [variance_eq_integral
      (IsGaussian.memLp_dual _ (innerSL ℝ q) 2 (by simp)).aemeasurable, hmean] at hvar
  simp only [sub_zero, innerSL_apply_apply, innerSL_apply_norm] at hvar
  exact hvar

/-- The Gaussian linear functional `g ↦ ⟪q,g⟫` is in `L²`. -/
theorem memLp_inner {d : ℕ} (q : EuclideanSpace ℝ (Fin d)) :
    MemLp (fun g : EuclideanSpace ℝ (Fin d) => ⟪q, g⟫) 2
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  refine (IsGaussian.memLp_dual _ (innerSL ℝ q) 2 (by simp)).of_le (by fun_prop) ?_
  filter_upwards with g
  simp [innerSL_apply_apply]

/-- The sign-product term `g ↦ sign ⟪u,g⟫ · ⟪q,g⟫` is in `L²` (dominated by `⟪q,g⟫`). -/
theorem memLp_sign_inner {d : ℕ} (u q : EuclideanSpace ℝ (Fin d)) :
    MemLp (fun g : EuclideanSpace ℝ (Fin d) => Real.sign (⟪u, g⟫) * ⟪q, g⟫) 2
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  refine (memLp_inner q).of_le ?_ ?_
  · exact (measurable_real_sign.comp
      (by fun_prop : Measurable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫))).aestronglyMeasurable.mul
      (by fun_prop)
  · filter_upwards with g
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    have hs : |Real.sign (⟪u, g⟫)| ≤ 1 := by
      rcases Real.sign_apply_eq (⟪u, g⟫) with h | h | h <;> rw [h] <;> norm_num
    nlinarith [hs, abs_nonneg ((⟪q, g⟫ : ℝ))]

/-- **Per-row variance bound.** For a single standard-Gaussian `g`, unit `u` and arbitrary `q`,
`Var[sign ⟪u,g⟫ · ⟪q,g⟫] ≤ ‖q‖²`.

The proof uses `Var X ≤ E[X²]`, bounds `(sign ⟪u,g⟫ · ⟪q,g⟫)² ≤ ⟪q,g⟫²` pointwise (since
`(sign r)² ≤ 1`), and evaluates `E⟪q,g⟫² = ‖q‖²`. -/
theorem qjl_perrow_variance_le {d : ℕ} (u q : EuclideanSpace ℝ (Fin d)) :
    variance (fun g : EuclideanSpace ℝ (Fin d) => Real.sign (⟪u, g⟫) * ⟪q, g⟫)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ ‖q‖ ^ 2 := by
  have hmem := memLp_sign_inner u q
  have hle : (fun g : EuclideanSpace ℝ (Fin d) => (Real.sign (⟪u, g⟫) * ⟪q, g⟫) ^ 2)
      ≤ fun g => ⟪q, g⟫ ^ 2 := by
    intro g
    dsimp only
    rw [mul_pow]
    have hs : (Real.sign (⟪u, g⟫)) ^ 2 ≤ 1 := by
      rcases Real.sign_apply_eq (⟪u, g⟫) with h | h | h <;> rw [h] <;> norm_num
    nlinarith [hs, sq_nonneg ((⟪q, g⟫ : ℝ))]
  calc variance (fun g => Real.sign (⟪u, g⟫) * ⟪q, g⟫)
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))
      ≤ (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))[
          (fun g => Real.sign (⟪u, g⟫) * ⟪q, g⟫) ^ 2] :=
        variance_le_expectation_sq hmem.aestronglyMeasurable
    _ = ∫ g, (Real.sign (⟪u, g⟫) * ⟪q, g⟫) ^ 2
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        simp only [Pi.pow_apply]
    _ ≤ ∫ g, ⟪q, g⟫ ^ 2 ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_mono hmem.integrable_sq (memLp_inner q).integrable_sq hle
    _ = ‖q‖ ^ 2 := integral_inner_sq_stdGaussian q

/-! ## Part 2: variance of the `m`-row estimator via cross-row independence -/

/-- **Estimator variance bound.** Over an `m × d` i.i.d. standard-Gaussian sketch, the variance of
the asymmetric 1-bit estimator is `≤ (π/2)‖q‖² / m`.

The `m` per-row terms are i.i.d. functions of distinct coordinates of the product measure, so
`ProbabilityTheory.variance_sum_pi` gives `Var[Σ row] = Σ Var[row] = m·Var[row]`; pulling out the
`(√(π/2)/m)` scaling and applying the per-row bound finishes it. -/
theorem qjlEstimator_variance_le {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) :
    variance (fun S => qjlEstimator key q S)
        (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))
      ≤ π / 2 * ‖q‖ ^ 2 / m := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  -- present the estimator as a constant times a coordinate-sum of i.i.d. per-row functions
  have heq : (fun S : Fin m → EuclideanSpace ℝ (Fin d) => qjlEstimator key q S)
      = fun S => (Real.sqrt (π / 2) * (m : ℝ)⁻¹) *
          (∑ i, (fun ω : Fin m → EuclideanSpace ℝ (Fin d) =>
            Real.sign (⟪‖key‖⁻¹ • key, ω i⟫) * ⟪q, ω i⟫)) S := by
    funext S
    simp only [qjlEstimator, Finset.sum_apply]
    ring
  rw [heq, variance_const_mul,
    variance_sum_pi (fun _ : Fin m => memLp_sign_inner (‖key‖⁻¹ • key) q),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsq : (Real.sqrt (π / 2)) ^ 2 = π / 2 := Real.sq_sqrt (by positivity)
  have hV := qjl_perrow_variance_le (‖key‖⁻¹ • key) q
  calc (Real.sqrt (π / 2) * (m : ℝ)⁻¹) ^ 2 *
          ((m : ℝ) * variance (fun g => Real.sign (⟪‖key‖⁻¹ • key, g⟫) * ⟪q, g⟫)
            (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))
      ≤ (Real.sqrt (π / 2) * (m : ℝ)⁻¹) ^ 2 * ((m : ℝ) * ‖q‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hV (by positivity)
    _ = π / 2 * ‖q‖ ^ 2 / m := by
        rw [mul_pow, hsq]
        field_simp

/-! ## Part 3: Chebyshev distortion / concentration bound -/

/-- The estimator is in `L²` under the product measure (a constant times a finite sum of i.i.d.
per-row terms, each `L²`). -/
theorem qjlEstimator_memLp {m d : ℕ} (key q : EuclideanSpace ℝ (Fin d)) :
    MemLp (fun S => qjlEstimator key q S) 2
      (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
  have heq : (fun S : Fin m → EuclideanSpace ℝ (Fin d) => qjlEstimator key q S)
      = fun S => (Real.sqrt (π / 2) * (m : ℝ)⁻¹) *
          ∑ i, Real.sign (⟪‖key‖⁻¹ • key, S i⟫) * ⟪q, S i⟫ := by
    funext S
    simp only [qjlEstimator]
    ring
  rw [heq]
  refine MemLp.const_mul ?_ _
  exact memLp_finsetSum Finset.univ (fun i _ =>
    (memLp_sign_inner (‖key‖⁻¹ • key) q).comp_measurePreserving
      (measurePreserving_eval
        (μ := fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) i))

/-- **QJL distortion / concentration bound (Chebyshev).** With `m` sign-bits, the asymmetric 1-bit
estimator deviates from the true normalized inner product `⟪key/‖key‖, q⟫` by at least `ε` with
probability at most `(π/2)‖q‖² / (m·ε²)`. Hence `m = O(‖q‖²/(ε²δ))` sign-bits suffice for additive
error `ε` with probability `1 − δ`. -/
theorem qjlEstimator_concentration {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) (hkey : key ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).real
        {S | ε ≤ |qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫|}
      ≤ π / 2 * ‖q‖ ^ 2 / (m * ε ^ 2) := by
  have hmean : (Measure.pi
      (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))[
        fun S => qjlEstimator key q S] = ⟪‖key‖⁻¹ • key, q⟫ :=
    qjlEstimator_unbiased hm key q hkey
  have hCheb := meas_ge_le_variance_div_sq (qjlEstimator_memLp (m := m) key q) hε
  rw [hmean] at hCheb
  rw [measureReal_def]
  calc (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))
        {S | ε ≤ |qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫|}).toReal
      ≤ (ENNReal.ofReal (variance (fun S => qjlEstimator key q S)
          (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))
            / ε ^ 2)).toReal := ENNReal.toReal_mono (by finiteness) hCheb
    _ = variance (fun S => qjlEstimator key q S)
          (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))
            / ε ^ 2 := ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (by positivity))
    _ ≤ (π / 2 * ‖q‖ ^ 2 / m) / ε ^ 2 :=
        (div_le_div_iff_of_pos_right (by positivity)).mpr (qjlEstimator_variance_le hm key q)
    _ = π / 2 * ‖q‖ ^ 2 / (m * ε ^ 2) := by rw [div_div]

/-! ## Part 4: exponential (sub-Gaussian) distortion bound

The Chebyshev bound above decays only polynomially in `m`. The classical QJL guarantee is an
*exponential* tail, obtained by showing the per-row sign-product term is sub-Gaussian and summing
over the `m` independent rows.

The crux is the per-row sub-Gaussian moment-generating-function bound: bounding
`E[exp(t·(√(π/2)·sign⟪u,g⟫·⟪q,g⟫))]` sharply requires a folded-normal sub-Gaussian estimate for
`|⟪u,g⟫|` (the crude `exp(t|x|) ≤ exp(tx)+exp(-tx)` route loses a factor `2` per row, which is fatal
for `m` rows). That estimate is **not** in mathlib, so we build it from scratch in
`JL/GaussianTail.lean` (`foldedNormal_subgaussian`) and assemble the per-row bound here in
`isPerRowSubgaussian_of_unit` / `isPerRowSubgaussian_normalized`. With this in hand the entire
exponential bound — per-row MGF, coordinate independence under `Measure.pi`, additivity of the
sub-Gaussian parameter over independent rows, the `1/m` rescaling, and the two-sided Chernoff bound —
is proved fully and **unconditionally**. -/

open scoped RealInnerProductSpace in
/-- The centered, `√(π/2)`-scaled per-row sign-product term
`g ↦ √(π/2)·sign⟪u,g⟫·⟪q,g⟫ − ⟪u,q⟫` has a sub-Gaussian moment generating function with variance
proxy `(π/2)·‖q‖²` under the standard Gaussian.

This is proved unconditionally for the normalized key direction by `isPerRowSubgaussian_normalized`
(and for any unit `u` by `isPerRowSubgaussian_of_unit`); the named predicate is kept as a convenient
abbreviation used by the exponential distortion bound below. -/
@[reducible] def IsPerRowSubgaussian {d : ℕ} (u q : EuclideanSpace ℝ (Fin d)) : Prop :=
  HasSubgaussianMGF
    (fun g : EuclideanSpace ℝ (Fin d) =>
      Real.sqrt (π / 2) * Real.sign (⟪u, g⟫) * ⟪q, g⟫ - ⟪u, q⟫)
    ⟨π / 2 * ‖q‖ ^ 2, by positivity⟩
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- The moment generating function of a centered real Gaussian: `∫ exp(r·b) d(N(0,v)) = exp(v·r²/2)`. -/
theorem gaussianReal_mgf_id (r : ℝ) (v : ℝ≥0) :
    ∫ b, rexp (r * b) ∂(gaussianReal 0 v) = rexp ((v : ℝ) * r ^ 2 / 2) := by
  have h := mgf_gaussianReal (X := (id : ℝ → ℝ)) (p := gaussianReal (0 : ℝ) v) Measure.map_id r
  rw [mgf] at h
  simpa using h

open scoped RealInnerProductSpace in
/-- **Per-row sub-Gaussian MGF bound (unit `u`), proved unconditionally.** For a unit vector `u`
and arbitrary `q`, the centered `√(π/2)`-scaled sign-product term
`g ↦ √(π/2)·sign⟪u,g⟫·⟪q,g⟫ − ⟪u,q⟫` is sub-Gaussian with variance proxy `(π/2)·‖q‖²` under the
standard Gaussian.

The proof decomposes `q = ⟪u,q⟫·u + w` with `w ⟂ u`. Under the standard Gaussian, `a := ⟪u,g⟫`
and `b := ⟪w,g⟫` are independent, with `a ~ N(0,1)` and `b ~ N(0,‖w‖²)`. Pushing forward to the
product law `N(0,1) ⊗ N(0,‖w‖²)` and integrating in `b` first (Gaussian MGF) leaves a folded-normal
integral in `a`, controlled by `foldedNormal_subgaussian`. The two variance proxies combine to
`(π/2)(⟪u,q⟫² + ‖w‖²) = (π/2)‖q‖²` by Pythagoras. -/
theorem isPerRowSubgaussian_of_unit {d : ℕ} (u q : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
    IsPerRowSubgaussian u q := by
  classical
  set μ : Measure (EuclideanSpace ℝ (Fin d)) :=
    ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)) with hμ
  haveI hμprob : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  set s0 : ℝ := Real.sqrt (π / 2) with hs0
  have hs0nn : (0 : ℝ) ≤ s0 := Real.sqrt_nonneg _
  have hs0sq : s0 ^ 2 = π / 2 := Real.sq_sqrt (by positivity)
  have hs0cc : s0 * Real.sqrt (2 / π) = 1 := by
    rw [hs0, ← Real.sqrt_mul (by positivity), show (π / 2) * (2 / π) = 1 by field_simp, Real.sqrt_one]
  -- orthogonal decomposition `q = ⟪u,q⟫ • u + w`
  set w : EuclideanSpace ℝ (Fin d) := q - ⟪u, q⟫ • u with hw
  have hperp : ⟪u, w⟫ = 0 := by
    rw [hw, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]; ring
  have hqg : ∀ g : EuclideanSpace ℝ (Fin d), ⟪q, g⟫ = ⟪u, q⟫ * ⟪u, g⟫ + ⟪w, g⟫ := by
    intro g; rw [hw, inner_sub_left, real_inner_smul_left]; ring
  have hnw : ‖w‖ ^ 2 = ‖q‖ ^ 2 - ⟪u, q⟫ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hw]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu, real_inner_comm q u, norm_smul, Real.norm_eq_abs, mul_one,
      sq_abs]
    ring
  have hnq : ‖q‖ ^ 2 = ⟪u, q⟫ ^ 2 + ‖w‖ ^ 2 := by rw [hnw]; ring
  -- the variance proxy of `b = ⟪w,g⟫`
  set vw : ℝ≥0 := Real.toNNReal (‖w‖ ^ 2) with hvw
  have hvwc : (vw : ℝ) = ‖w‖ ^ 2 := Real.coe_toNNReal _ (by positivity)
  -- marginal laws of `a = ⟪u,g⟫` and `b = ⟪w,g⟫`
  have hmapu : μ.map (fun g => ⟪u, g⟫) = gaussianReal 0 1 := by
    have e : (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫) = ⇑(innerSL ℝ u) := by
      funext g; rw [innerSL_apply_apply]
    rw [e]
    have hns : ‖innerSL ℝ u‖ ^ 2 = 1 := by rw [innerSL_apply_norm, hu]; norm_num
    have hgl : HasGaussianLaw (⇑(innerSL ℝ u))
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      IsGaussian.hasGaussianLaw_id.map (innerSL ℝ u)
    rw [hμ, hgl.map_eq_gaussianReal, integral_strongDual_stdGaussian (innerSL ℝ u),
      variance_dual_stdGaussian (innerSL ℝ u), hns, Real.toNNReal_one]
  have hmapw : μ.map (fun g => ⟪w, g⟫) = gaussianReal 0 vw := by
    have e : (fun g : EuclideanSpace ℝ (Fin d) => ⟪w, g⟫) = ⇑(innerSL ℝ w) := by
      funext g; rw [innerSL_apply_apply]
    rw [e]
    have hns : ‖innerSL ℝ w‖ ^ 2 = ‖w‖ ^ 2 := by rw [innerSL_apply_norm]
    have hgl : HasGaussianLaw (⇑(innerSL ℝ w))
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) :=
      IsGaussian.hasGaussianLaw_id.map (innerSL ℝ w)
    rw [hμ, hgl.map_eq_gaussianReal, integral_strongDual_stdGaussian (innerSL ℝ w),
      variance_dual_stdGaussian (innerSL ℝ w), hns, hvw]
  -- independence of `a` and `b` (orthogonal Gaussian functionals)
  have haem_u : AEMeasurable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫) μ :=
    (by fun_prop : Measurable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫)).aemeasurable
  have haem_w : AEMeasurable (fun g : EuclideanSpace ℝ (Fin d) => ⟪w, g⟫) μ :=
    (by fun_prop : Measurable (fun g : EuclideanSpace ℝ (Fin d) => ⟪w, g⟫)).aemeasurable
  have hpair : HasGaussianLaw (fun g : EuclideanSpace ℝ (Fin d) => (⟪u, g⟫, ⟪w, g⟫)) μ := by
    rw [hμ]
    refine (IsGaussian.hasGaussianLaw_id.map ((innerSL ℝ u).prod (innerSL ℝ w))).congr ?_
    filter_upwards with g
    simp [Function.comp, ContinuousLinearMap.prod_apply, innerSL_apply_apply]
  have hcov : cov[fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫,
      fun g : EuclideanSpace ℝ (Fin d) => ⟪w, g⟫; μ] = 0 := by
    rw [hμ, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id u w, covarianceBilin_stdGaussian]
    exact hperp
  have hindep : IndepFun (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫)
      (fun g : EuclideanSpace ℝ (Fin d) => ⟪w, g⟫) μ :=
    hpair.indepFun_of_covariance_eq_zero hcov
  have hjoint : μ.map (fun g : EuclideanSpace ℝ (Fin d) => (⟪u, g⟫, ⟪w, g⟫))
      = (gaussianReal 0 1).prod (gaussianReal 0 vw) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map haem_u haem_w).mp hindep, hmapu, hmapw]
  have hΦaem : AEMeasurable (fun g : EuclideanSpace ℝ (Fin d) => (⟪u, g⟫, ⟪w, g⟫)) μ :=
    (by fun_prop :
      Measurable (fun g : EuclideanSpace ℝ (Fin d) => (⟪u, g⟫, ⟪w, g⟫))).aemeasurable
  -- the pushed-forward integrand on the product law
  set G : ℝ × ℝ → ℝ := fun p => s0 * Real.sign p.1 * (⟪u, q⟫ * p.1 + p.2) - ⟪u, q⟫ with hG
  have hGval : ∀ a b : ℝ, G (a, b) = s0 * Real.sign a * (⟪u, q⟫ * a + b) - ⟪u, q⟫ := fun _ _ => rfl
  have hGmeas : Measurable G := by
    refine Measurable.sub (Measurable.mul ?_ ?_) measurable_const
    · exact measurable_const.mul (measurable_real_sign.comp measurable_fst)
    · exact (measurable_const.mul measurable_fst).add measurable_snd
  -- integrability of `exp(t·G)` on the product law, by a product domination
  have hIntProd : ∀ t : ℝ, Integrable (fun p : ℝ × ℝ => rexp (t * G p))
      ((gaussianReal 0 1).prod (gaussianReal 0 vw)) := by
    intro t
    set k : ℝ := |t| * s0 * |⟪u, q⟫| with hk
    set k' : ℝ := |t| * s0 with hk'
    have hdom : Integrable (fun p : ℝ × ℝ =>
        (rexp (|t| * |⟪u, q⟫|) * (rexp (k * p.1) + rexp (-k * p.1)))
          * (rexp (k' * p.2) + rexp (-k' * p.2)))
        ((gaussianReal 0 1).prod (gaussianReal 0 vw)) :=
      Integrable.mul_prod
        (f := fun a : ℝ => rexp (|t| * |⟪u, q⟫|) * (rexp (k * a) + rexp (-k * a)))
        (g := fun b : ℝ => rexp (k' * b) + rexp (-k' * b))
        (((integrable_exp_mul_gaussianReal k).add
          (integrable_exp_mul_gaussianReal (-k))).const_mul _)
        ((integrable_exp_mul_gaussianReal k').add (integrable_exp_mul_gaussianReal (-k')))
    refine hdom.mono' (hGmeas.const_mul t |>.exp.aestronglyMeasurable) ?_
    filter_upwards with p
    obtain ⟨a, b⟩ := p
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    have hsign : |Real.sign a| ≤ 1 := by
      rcases Real.sign_apply_eq a with h | h | h <;> rw [h] <;> norm_num
    have hsplit : t * G (a, b)
        = t * s0 * Real.sign a * ⟪u, q⟫ * a + t * s0 * Real.sign a * b + (-(t * ⟪u, q⟫)) := by
      rw [hGval a b]; ring
    rw [hsplit, Real.exp_add, Real.exp_add]
    have hA : rexp (t * s0 * Real.sign a * ⟪u, q⟫ * a) ≤ rexp (k * a) + rexp (-k * a) := by
      have hbnd : t * s0 * Real.sign a * ⟪u, q⟫ * a ≤ k * |a| := by
        calc t * s0 * Real.sign a * ⟪u, q⟫ * a
            ≤ |t * s0 * Real.sign a * ⟪u, q⟫ * a| := le_abs_self _
          _ = |t| * s0 * |Real.sign a| * |⟪u, q⟫| * |a| := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hs0nn]
          _ ≤ |t| * s0 * 1 * |⟪u, q⟫| * |a| := by gcongr
          _ = k * |a| := by rw [hk]; ring
      rcases le_or_gt 0 a with ha | ha
      · rw [abs_of_nonneg ha] at hbnd
        linarith [Real.exp_le_exp.mpr hbnd, (Real.exp_pos (-k * a)).le]
      · rw [abs_of_neg ha] at hbnd
        have hbnd' : t * s0 * Real.sign a * ⟪u, q⟫ * a ≤ -k * a := by rw [neg_mul]; linarith
        linarith [Real.exp_le_exp.mpr hbnd', (Real.exp_pos (k * a)).le]
    have hB : rexp (t * s0 * Real.sign a * b) ≤ rexp (k' * b) + rexp (-k' * b) := by
      have hbnd : t * s0 * Real.sign a * b ≤ k' * |b| := by
        calc t * s0 * Real.sign a * b
            ≤ |t * s0 * Real.sign a * b| := le_abs_self _
          _ = |t| * s0 * |Real.sign a| * |b| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs0nn]
          _ ≤ |t| * s0 * 1 * |b| := by gcongr
          _ = k' * |b| := by rw [hk']; ring
      rcases le_or_gt 0 b with hb | hb
      · rw [abs_of_nonneg hb] at hbnd
        linarith [Real.exp_le_exp.mpr hbnd, (Real.exp_pos (-k' * b)).le]
      · rw [abs_of_neg hb] at hbnd
        have hbnd' : t * s0 * Real.sign a * b ≤ -k' * b := by rw [neg_mul]; linarith
        linarith [Real.exp_le_exp.mpr hbnd', (Real.exp_pos (k' * b)).le]
    have hC : rexp (-(t * ⟪u, q⟫)) ≤ rexp (|t| * |⟪u, q⟫|) := by
      apply Real.exp_le_exp.mpr
      calc -(t * ⟪u, q⟫) ≤ |t * ⟪u, q⟫| := neg_le_abs _
        _ = |t| * |⟪u, q⟫| := abs_mul _ _
    calc rexp (t * s0 * Real.sign a * ⟪u, q⟫ * a) * rexp (t * s0 * Real.sign a * b)
            * rexp (-(t * ⟪u, q⟫))
        ≤ (rexp (k * a) + rexp (-k * a)) * (rexp (k' * b) + rexp (-k' * b))
            * rexp (|t| * |⟪u, q⟫|) := by gcongr
      _ = rexp (|t| * |⟪u, q⟫|) * (rexp (k * a) + rexp (-k * a))
            * (rexp (k' * b) + rexp (-k' * b)) := by ring
  -- the sub-Gaussian bound on the product law
  have hGsub : HasSubgaussianMGF G ⟨π / 2 * ‖q‖ ^ 2, by positivity⟩
      ((gaussianReal 0 1).prod (gaussianReal 0 vw)) := by
    refine ⟨hIntProd, fun t => ?_⟩
    show mgf G _ t ≤ rexp (π / 2 * ‖q‖ ^ 2 * t ^ 2 / 2)
    rw [mgf, integral_prod _ (hIntProd t)]
    -- integrate in `b` first
    have hinner : ∀ a : ℝ, ∫ b, rexp (t * G (a, b)) ∂(gaussianReal 0 vw)
        = rexp (t * s0 * ⟪u, q⟫ * (|a| - Real.sqrt (2 / π)))
          * rexp ((vw : ℝ) * (t * s0 * Real.sign a) ^ 2 / 2) := by
      intro a
      have e : ∀ b : ℝ, rexp (t * G (a, b))
          = rexp (t * s0 * ⟪u, q⟫ * (|a| - Real.sqrt (2 / π)))
            * rexp ((t * s0 * Real.sign a) * b) := by
        intro b
        rw [hGval a b, ← Real.exp_add]
        congr 1
        rw [← sign_mul_self a]
        linear_combination (t * ⟪u, q⟫) * hs0cc
      simp_rw [e]
      rw [integral_const_mul, gaussianReal_mgf_id]
    simp_rw [hinner]
    set K : ℝ := rexp ((vw : ℝ) * (t * s0) ^ 2 / 2) with hK
    have hpt : ∀ a : ℝ,
        rexp (t * s0 * ⟪u, q⟫ * (|a| - Real.sqrt (2 / π)))
            * rexp ((vw : ℝ) * (t * s0 * Real.sign a) ^ 2 / 2)
          ≤ rexp (t * s0 * ⟪u, q⟫ * (|a| - Real.sqrt (2 / π))) * K := by
      intro a
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Real.exp_le_exp.mpr
      have hsq1 : (Real.sign a) ^ 2 ≤ 1 := by
        rcases Real.sign_apply_eq a with h | h | h <;> rw [h] <;> norm_num
      have hvwnn : (0 : ℝ) ≤ (vw : ℝ) := vw.coe_nonneg
      have heq : (t * s0 * Real.sign a) ^ 2 = (t * s0) ^ 2 * (Real.sign a) ^ 2 := by ring
      rw [heq]
      have hkey := mul_le_mul_of_nonneg_left hsq1 (mul_nonneg hvwnn (sq_nonneg (t * s0)))
      nlinarith [hkey]
    have hI2 : Integrable (fun a => rexp (t * s0 * ⟪u, q⟫ * (|a| - Real.sqrt (2 / π))) * K)
        (gaussianReal 0 1) :=
      (foldedNormal_subgaussian.integrable_exp_mul (t * s0 * ⟪u, q⟫)).mul_const K
    have hI1 : Integrable (fun a => rexp (t * s0 * ⟪u, q⟫ * (|a| - Real.sqrt (2 / π)))
        * rexp ((vw : ℝ) * (t * s0 * Real.sign a) ^ 2 / 2)) (gaussianReal 0 1) := by
      refine hI2.mono' ?_ ?_
      · refine (Measurable.mul ?_ ?_).aestronglyMeasurable
        · exact measurable_exp.comp (by fun_prop)
        · exact measurable_exp.comp
            ((((measurable_const.mul measurable_real_sign).pow_const 2).const_mul (vw : ℝ)).div_const 2)
      · filter_upwards with a
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hpt a
    calc ∫ a, rexp (t * s0 * ⟪u, q⟫ * (|a| - Real.sqrt (2 / π)))
            * rexp ((vw : ℝ) * (t * s0 * Real.sign a) ^ 2 / 2) ∂(gaussianReal 0 1)
        ≤ ∫ a, rexp (t * s0 * ⟪u, q⟫ * (|a| - Real.sqrt (2 / π))) * K ∂(gaussianReal 0 1) :=
          integral_mono hI1 hI2 hpt
      _ = (∫ a, rexp (t * s0 * ⟪u, q⟫ * (|a| - Real.sqrt (2 / π))) ∂(gaussianReal 0 1)) * K := by
          rw [integral_mul_const]
      _ ≤ rexp ((t * s0 * ⟪u, q⟫) ^ 2 / 2) * K := by
          have hfold : (∫ a, rexp (t * s0 * ⟪u, q⟫ * (|a| - Real.sqrt (2 / π)))
              ∂(gaussianReal 0 1)) ≤ rexp ((t * s0 * ⟪u, q⟫) ^ 2 / 2) := by
            have h := foldedNormal_subgaussian.mgf_le (t * s0 * ⟪u, q⟫)
            rw [mgf] at h
            calc ∫ a, rexp (t * s0 * ⟪u, q⟫ * (|a| - Real.sqrt (2 / π))) ∂(gaussianReal 0 1)
                ≤ rexp (1 * (t * s0 * ⟪u, q⟫) ^ 2 / 2) := h
              _ = rexp ((t * s0 * ⟪u, q⟫) ^ 2 / 2) := by rw [one_mul]
          have hKnn : (0 : ℝ) ≤ K := (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right hfold hKnn
      _ = rexp (π / 2 * ‖q‖ ^ 2 * t ^ 2 / 2) := by
          rw [hK, ← Real.exp_add]
          congr 1
          rw [hvwc, hnq]
          linear_combination ((⟪u, q⟫ ^ 2 + ‖w‖ ^ 2) * t ^ 2 / 2) * hs0sq
  -- transport back to `g ↦ √(π/2)·sign⟪u,g⟫·⟪q,g⟫ − ⟪u,q⟫`
  have hofmap : HasSubgaussianMGF
      (G ∘ (fun g : EuclideanSpace ℝ (Fin d) => (⟪u, g⟫, ⟪w, g⟫)))
      ⟨π / 2 * ‖q‖ ^ 2, by positivity⟩ μ := by
    apply HasSubgaussianMGF.of_map hΦaem
    rw [hjoint]; exact hGsub
  have htarget : (G ∘ (fun g : EuclideanSpace ℝ (Fin d) => (⟪u, g⟫, ⟪w, g⟫)))
      = fun g => Real.sqrt (π / 2) * Real.sign (⟪u, g⟫) * ⟪q, g⟫ - ⟪u, q⟫ := by
    funext g
    simp only [Function.comp_apply, hGval]
    rw [← hqg g, hs0]
  rw [htarget] at hofmap
  exact hofmap

open scoped RealInnerProductSpace in
/-- **Per-row sub-Gaussian MGF bound for the normalized key, proved unconditionally.** For any
`key` and `q`, the normalized direction `‖key‖⁻¹ • key` satisfies `IsPerRowSubgaussian`. When
`key ≠ 0` this is the unit case `isPerRowSubgaussian_of_unit`; when `key = 0` the normalized
direction is `0`, the per-row term is identically `0`, and the bound is trivial. -/
theorem isPerRowSubgaussian_normalized {d : ℕ} (key q : EuclideanSpace ℝ (Fin d)) :
    IsPerRowSubgaussian (‖key‖⁻¹ • key) q := by
  rcases eq_or_ne key 0 with hkey | hkey
  · subst hkey
    rw [smul_zero]
    refine HasSubgaussianMGF.congr (X := fun _ => (0 : ℝ)) ?_ ?_
    · refine ⟨fun t => by simp, fun t => ?_⟩
      have hmgf : mgf (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ))
          (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) t = 1 := by
        rw [mgf]; simp
      rw [hmgf]
      exact Real.one_le_exp (by positivity)
    · filter_upwards with g
      simp [inner_zero_left, Real.sign_zero]
  · have hkne : ‖key‖ ≠ 0 := by simpa [norm_eq_zero] using hkey
    have hu : ‖(‖key‖⁻¹ • key : EuclideanSpace ℝ (Fin d))‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ hkne
    exact isPerRowSubgaussian_of_unit _ q hu

/-- **Centered estimator is sub-Gaussian.** The centered estimator `qjlEstimator − ⟪key/‖key‖, q⟫`
is sub-Gaussian with variance proxy `(π/2)·‖q‖² / m` under the `m`-fold product Gaussian, by summing
the `m` i.i.d. per-row terms (independent coordinates of `Measure.pi`) and rescaling by `1/m`. The
per-row sub-Gaussian bound is supplied unconditionally by `isPerRowSubgaussian_normalized`. -/
theorem qjlEstimator_centered_hasSubgaussianMGF {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) :
    HasSubgaussianMGF (fun S => qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫)
      ⟨π / 2 * ‖q‖ ^ 2 / m, by positivity⟩
      (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
  set u : EuclideanSpace ℝ (Fin d) := ‖key‖⁻¹ • key with hu_def
  set G : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun g => Real.sqrt (π / 2) * Real.sign (⟪u, g⟫) * ⟪q, g⟫ - ⟪u, q⟫ with hG_def
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hGmeas : Measurable G := by
    refine Measurable.sub ?_ measurable_const
    refine Measurable.mul ?_ (by fun_prop)
    exact measurable_const.mul (measurable_real_sign.comp (by fun_prop))
  -- each coordinate is sub-Gaussian, transported from the single-Gaussian hypothesis
  have hcoord : ∀ i : Fin m,
      HasSubgaussianMGF (fun S : Fin m → EuclideanSpace ℝ (Fin d) => G (S i))
        (⟨π / 2 * ‖q‖ ^ 2, by positivity⟩ : ℝ≥0)
        (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
    intro i
    have hmap : (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).map
          (fun f : Fin m → EuclideanSpace ℝ (Fin d) => f i)
        = ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)) :=
      (measurePreserving_eval
        (μ := fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) i).map_eq
    have h2 : HasSubgaussianMGF G (⟨π / 2 * ‖q‖ ^ 2, by positivity⟩ : ℝ≥0)
        ((Measure.pi
          (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).map
            (fun f : Fin m → EuclideanSpace ℝ (Fin d) => f i)) := by
      rw [hmap]; exact isPerRowSubgaussian_normalized key q
    exact HasSubgaussianMGF.of_map (X := G)
      (Y := fun f : Fin m → EuclideanSpace ℝ (Fin d) => f i)
      (measurable_pi_apply i).aemeasurable h2
  -- coordinates of a product measure are independent
  have hindep : iIndepFun (fun (i : Fin m) (S : Fin m → EuclideanSpace ℝ (Fin d)) => G (S i))
      (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))) :=
    iIndepFun_pi (fun _ => hGmeas.aemeasurable)
  -- sum the m independent rows
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindep
    (fun i (_ : i ∈ Finset.univ) => hcoord i)
  -- rescale by 1/m
  have hscale := hsum.const_mul ((m : ℝ)⁻¹)
  -- the rescaled coordinate-sum equals the centered estimator
  have hDeq : (fun S : Fin m → EuclideanSpace ℝ (Fin d) => (m : ℝ)⁻¹ * ∑ i, G (S i))
      = fun S => qjlEstimator key q S - ⟪u, q⟫ := by
    funext S
    simp only [hG_def, qjlEstimator, ← hu_def]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      show (∑ i, Real.sqrt (π / 2) * Real.sign (⟪u, S i⟫) * ⟪q, S i⟫)
          = Real.sqrt (π / 2) * ∑ i, Real.sign (⟪u, S i⟫) * ⟪q, S i⟫ by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
    field_simp
  rw [hDeq] at hscale
  -- reconcile the variance proxy
  convert hscale using 2
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_sum]
  show π / 2 * ‖q‖ ^ 2 / (m : ℝ)
      = ((m : ℝ)⁻¹) ^ 2 * ∑ _i : Fin m, (π / 2 * ‖q‖ ^ 2)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

open scoped RealInnerProductSpace in
/-- **QJL exponential distortion bound (sub-Gaussian / Chernoff).** The asymmetric 1-bit estimator
deviates from the true normalized inner product `⟪key/‖key‖, q⟫` by at least `ε` with probability at
most
`2 · exp(-m·ε² / (π·‖q‖²))`, an exponential (rather than polynomial) improvement over the Chebyshev
bound `qjlEstimator_concentration`. Hence `m = O(‖q‖²·log(1/δ)/ε²)` sign-bits suffice for additive
error `ε` with probability `1 − δ`. -/
theorem qjlEstimator_concentration_exp {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).real
        {S | ε ≤ |qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫|}
      ≤ 2 * Real.exp (-((m : ℝ) * ε ^ 2) / (π * ‖q‖ ^ 2)) := by
  have hDsub := qjlEstimator_centered_hasSubgaussianMGF hm key q
  -- the Chernoff exponent simplifies to the clean constant (`↑⟨a,_⟩` is defeq `a`)
  have hcoe : -ε ^ 2 / (2 * (π / 2 * ‖q‖ ^ 2 / (m : ℝ)))
      = -((m : ℝ) * ε ^ 2) / (π * ‖q‖ ^ 2) := by
    rw [show (2 : ℝ) * (π / 2 * ‖q‖ ^ 2 / m) = π * ‖q‖ ^ 2 / m by ring, div_div_eq_mul_div]
    ring
  -- right tail (`↑⟨a,_⟩` is defeq `a`, so `change` rewrites the exponent denominator)
  have hR := hDsub.measure_ge_le hε.le
  change _ ≤ Real.exp (-ε ^ 2 / (2 * (π / 2 * ‖q‖ ^ 2 / (m : ℝ)))) at hR
  rw [hcoe] at hR
  -- left tail
  have hL := hDsub.neg.measure_ge_le hε.le
  simp only [Pi.neg_apply] at hL
  change _ ≤ Real.exp (-ε ^ 2 / (2 * (π / 2 * ‖q‖ ^ 2 / (m : ℝ)))) at hL
  rw [hcoe] at hL
  -- split the absolute-value event into the two one-sided events
  have hset : {S : Fin m → EuclideanSpace ℝ (Fin d) |
        ε ≤ |qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫|}
      = {S | ε ≤ qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫}
        ∪ {S | ε ≤ -(qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫)} := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [hset]
  refine (measureReal_union_le _ _).trans ?_
  calc (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).real
          {S | ε ≤ qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫}
        + (Measure.pi
            (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).real
          {S | ε ≤ -(qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫)}
      ≤ Real.exp (-((m : ℝ) * ε ^ 2) / (π * ‖q‖ ^ 2))
          + Real.exp (-((m : ℝ) * ε ^ 2) / (π * ‖q‖ ^ 2)) := add_le_add hR hL
    _ = 2 * Real.exp (-((m : ℝ) * ε ^ 2) / (π * ‖q‖ ^ 2)) := by ring

end JL
