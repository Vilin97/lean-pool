/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import LeanPool.ZetaZeros.Hilbert.AlphaExpansion
public import LeanPool.ZetaZeros.MontgomeryTaylor.Basic
public import LeanPool.ZetaZeros.Zeta.Asymptotics
public import LeanPool.ZetaZeros.Defs
public import LeanPool.ZetaZeros.Zeta.Cutoff
public import LeanPool.ZetaZeros.Zeta.Finite
public import LeanPool.ZetaZeros.Zeta.Mass

/-!
# Construction of the pair-correlation kernel

The cutoff construction packages the unweighted pair sum, proves that the normalized cutoff is
admissible, and develops the analytic identities needed to apply pair correlation.
-/

@[expose] public section

namespace ZetaZeros

open MeasureTheory

/-- Compact support makes the defining complex-frequency Fourier integrand integrable. -/
private lemma integrable_fourierC_integrand {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (z : ℂ) :
    Integrable (fun x : ℝ => (f x : ℂ) *
      Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * z * (x : ℂ))) := by
  have hc : HasCompactSupport (fun x : ℝ => (f x : ℂ)) := by
    change HasCompactSupport ((fun x : ℝ => (x : ℂ)) ∘ f)
    exact hfc.comp_left (g := fun x : ℝ => (x : ℂ)) (by norm_num)
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · exact hc.mul_right


/-- Integration by parts for the complex-frequency Fourier transform. -/
private lemma fourierC_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (z : ℂ) :
    fourierC (deriv f) z = (2 * (Real.pi : ℂ) * Complex.I * z) * fourierC f z := by
  let c : ℂ := -(2 * (Real.pi : ℂ)) * Complex.I * z
  let e : ℝ → ℂ := fun x => Complex.exp (c * (x : ℂ))
  let e' : ℝ → ℂ := fun x => e x * c
  let fc : ℝ → ℂ := fun x => (f x : ℂ)
  let dfc : ℝ → ℂ := fun x => ((deriv f x : ℝ) : ℂ)
  have he : ∀ x : ℝ, HasDerivAt e (e' x) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
      simpa only [mul_one] using!
        ((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal
    exact hlin.cexp
  have hfc_deriv : ∀ x : ℝ, HasDerivAt fc (dfc x) x := by
    intro x
    exact ((hf.differentiable (by simp)) x).hasDerivAt.ofReal_comp
  have hcont_e : Continuous e := by
    unfold e
    fun_prop
  have hcont_e' : Continuous e' := by
    unfold e'
    fun_prop
  have hcont_fc : Continuous fc := by
    unfold fc
    fun_prop
  have hcont_dfc : Continuous dfc := by
    unfold dfc
    exact Complex.continuous_ofReal.comp (hf.continuous_deriv (by simp))
  have hcompact_fc : HasCompactSupport fc := by
    change HasCompactSupport ((fun x : ℝ => (x : ℂ)) ∘ f)
    exact hfc.comp_left (g := fun x : ℝ => (x : ℂ)) (by norm_num)
  have hcompact_dfc : HasCompactSupport dfc := by
    change HasCompactSupport ((fun x : ℝ => (x : ℂ)) ∘ deriv f)
    exact hfc.deriv.comp_left (g := fun x : ℝ => (x : ℂ)) (by norm_num)
  have hed : Integrable (e * dfc) :=
    (hcont_e.mul hcont_dfc).integrable_of_hasCompactSupport hcompact_dfc.mul_left
  have he'f : Integrable (e' * fc) :=
    (hcont_e'.mul hcont_fc).integrable_of_hasCompactSupport hcompact_fc.mul_left
  have hef : Integrable (e * fc) :=
    (hcont_e.mul hcont_fc).integrable_of_hasCompactSupport hcompact_fc.mul_left
  have hibp : ∫ x : ℝ, e x * dfc x = -∫ x : ℝ, e' x * fc x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => he x)
      (fun x _ => hfc_deriv x) hed he'f hef
  unfold fourierC
  change (∫ x : ℝ, dfc x * e x) =
    (2 * (Real.pi : ℂ) * Complex.I * z) * ∫ x : ℝ, fc x * e x
  calc
    ∫ x : ℝ, dfc x * e x = ∫ x : ℝ, e x * dfc x := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = -∫ x : ℝ, e' x * fc x := hibp
    _ = -c * ∫ x : ℝ, fc x * e x := by
      rw [← integral_const_mul, ← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      unfold e'
      ring
    _ = (2 * (Real.pi : ℂ) * Complex.I * z) * ∫ x : ℝ, fc x * e x := by
      unfold c
      ring

/-- The unweighted second moment of the test kernel over ordered pairs of zeta zeros. -/
noncomputable def unweightedKernelSum (eta : ℝ → ℝ) (T : ℝ) : ℂ :=
  ∑ᶠ ρ ∈ nontrivialZeros T, ∑ᶠ ρ' ∈ nontrivialZeros T,
    ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
      testKernel eta (rescaledDiff T ρ ρ') ^ 2


/-- The cutoff-weighted extremal density is integrable. -/
private lemma integrable_cutoffWeight {delta : ℝ} {psi : ℝ → ℝ}
    (hpsi : IsCutoff delta psi) : Integrable (fun x => psi x ^ 2 * extremalTest x) := by
  have hzero : ∀ x ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
      psi x ^ 2 * extremalTest x = 0 := by
    intro x hx
    have h : 1 / 2 ≤ |x| := by
      by_contra hlt
      exact hx (Set.mem_Icc.mpr (abs_le.mp (le_of_lt (not_le.mp hlt))))
    rw [hpsi.support x h]
    ring
  have hcont : ContinuousOn (fun x => psi x ^ 2 * extremalTest x)
      (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) := by
    have hG : Continuous fun x : ℝ => psi x ^ 2 *
        (Real.cos (Real.sqrt 2 * x) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))) :=
      (hpsi.smooth.continuous.pow 2).mul
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).div_const _)
    refine hG.continuousOn.congr ?_
    intro x hx
    have hx' : |x| ≤ 1 / 2 := abs_le.mpr (Set.mem_Icc.mp hx)
    change psi x ^ 2 * extremalTest x = psi x ^ 2 *
      (Real.cos (Real.sqrt 2 * x) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)))
    rw [extremalTest, ite_eq_left hx']
  exact hcont.integrableOn_Icc.integrable_of_forall_notMem_eq_zero hzero

/-- The square of the normalized cutoff is integrable. -/
lemma integrable_cutoffTestSq {delta : ℝ} (hd : 0 < delta) (hd4 : delta < 1 / 4)
    {psi : ℝ → ℝ} (hpsi : IsCutoff delta psi) : Integrable (cutoffTestSq psi) := by
  have hdiv : Integrable (fun x => psi x ^ 2 * extremalTest x / cutoffNormaliser psi) :=
    (integrable_cutoffWeight hpsi).div_const _
  exact hdiv.congr (Filter.Eventually.of_forall fun x => (cutoffTestSq_eq hd hd4 hpsi x).symm)


/-- The self-convolution is integrable. -/
lemma integrable_cutoffSelfConv {delta : ℝ} (hd : 0 < delta) (hd4 : delta < 1 / 4)
    {psi : ℝ → ℝ} (hpsi : IsCutoff delta psi) : Integrable (cutoffSelfConv psi) := by
  change Integrable
    (convolution (cutoffTestSq psi) (cutoffTestSq psi)
      (ContinuousLinearMap.mul ℝ ℝ) volume)
  exact (integrable_cutoffTestSq hd hd4 hpsi).integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) (integrable_cutoffTestSq hd hd4 hpsi)


/-- The second derivative of the self-convolution has compact support. -/
lemma hasCompactSupport_iteratedDeriv_two_cutoffSelfConv {delta : ℝ} {psi : ℝ → ℝ}
    (hpsi : IsCutoff delta psi) :
    HasCompactSupport (iteratedDeriv 2 (cutoffSelfConv psi)) := by
  rw [iteratedDeriv_eq_iterate]
  simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
    (hasCompactSupport_cutoffSelfConv hpsi).deriv.deriv

/-- The second derivative of the self-convolution is integrable. -/
lemma integrable_iteratedDeriv_two_cutoffSelfConv {delta : ℝ}
    {psi : ℝ → ℝ} (hpsi : IsCutoff delta psi) :
    Integrable (iteratedDeriv 2 (cutoffSelfConv psi)) :=
  ((contDiff_iteratedDeriv_two_cutoffSelfConv hpsi).continuous)
    |>.integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv_two_cutoffSelfConv hpsi)

/-- The complex-frequency Fourier transform of the second derivative has the expected
quadratic multiplier. -/
@[zz_tag "lem_Q_psi_second_hat"]
lemma fourierC_iteratedDeriv_two_cutoffSelfConv {delta : ℝ}
    {psi : ℝ → ℝ} (hpsi : IsCutoff delta psi) (z : ℂ) :
    fourierC (iteratedDeriv 2 (cutoffSelfConv psi)) z =
      -4 * (Real.pi : ℂ) ^ 2 * z ^ 2 * testKernel (cutoffTest psi) z ^ 2 := by
  have hQ := contDiff_cutoffSelfConv hpsi
  have hQ' : ContDiff ℝ (⊤ : ℕ∞) (deriv (cutoffSelfConv psi)) := by
    simpa only [Function.iterate_one] using hQ.iterate_deriv 1
  rw [iteratedDeriv_eq_iterate]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [fourierC_deriv hQ' (hasCompactSupport_cutoffSelfConv hpsi).deriv,
    fourierC_deriv hQ (hasCompactSupport_cutoffSelfConv hpsi),
    fourierC_cutoffSelfConv hpsi]
  ring_nf
  rw [show Complex.I ^ 2 = -(1 : ℂ) by norm_num]
  ring

/-- Fourier transform of the corrected pair-correlation test function. -/
@[zz_tag "lem_r_psi_hat"]
lemma fourierC_correctedTest {delta : ℝ}
    {psi : ℝ → ℝ} (hpsi : IsCutoff delta psi) {T : ℝ} (hT : 1 < T) (z : ℂ) :
    fourierC (correctedTest psi T) z =
      (1 + (Real.pi : ℂ) ^ 2 * z ^ 2 / (Real.log T : ℂ) ^ 2) *
        testKernel (cutoffTest psi) z ^ 2 := by
  have hlog : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT)
  have hden : (4 * Real.log T ^ 2 : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hlog)
  have hQint := integrable_fourierC_integrand
    (contDiff_cutoffSelfConv hpsi).continuous
    (hasCompactSupport_cutoffSelfConv hpsi) z
  have hQ2int := integrable_fourierC_integrand
    (contDiff_iteratedDeriv_two_cutoffSelfConv hpsi).continuous
    (hasCompactSupport_iteratedDeriv_two_cutoffSelfConv hpsi) z
  unfold correctedTest fourierC
  rw [show (fun x : ℝ =>
      ((cutoffSelfConv psi x -
        iteratedDeriv 2 (cutoffSelfConv psi) x / (4 * Real.log T ^ 2) : ℝ) : ℂ) *
          Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * z * (x : ℂ))) =
      (fun x : ℝ => (cutoffSelfConv psi x : ℂ) *
          Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * z * (x : ℂ)) -
          ((iteratedDeriv 2 (cutoffSelfConv psi) x : ℝ) : ℂ) *
            Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * z * (x : ℂ)) /
              ((4 * Real.log T ^ 2 : ℝ) : ℂ)) by
        funext x
        push_cast
        ring]
  rw [integral_sub hQint (hQ2int.div_const _), integral_div]
  change fourierC (cutoffSelfConv psi) z -
      fourierC (iteratedDeriv 2 (cutoffSelfConv psi)) z /
        ((4 * Real.log T ^ 2 : ℝ) : ℂ) = _
  rw [fourierC_cutoffSelfConv hpsi,
    fourierC_iteratedDeriv_two_cutoffSelfConv hpsi]
  push_cast
  field_simp
  ring

/-- At a rescaled pair of zeros, the correction factor cancels the unconditional
pair-correlation weight. -/
@[zz_tag "lem_r_at_z_rho"]
lemma correctedTest_weight_cancel {delta : ℝ}
    {psi : ℝ → ℝ} (hpsi : IsCutoff delta psi) {T : ℝ} (hT : 1 < T)
    {rho rho' : ℂ} (hrho0 : 0 < rho.re) (hrho1 : rho.re < 1)
    (hrho0' : 0 < rho'.re) (hrho1' : rho'.re < 1) :
    fourierC (correctedTest psi T) (rescaledDiff T rho rho') * pairWeight (rho - rho') =
      testKernel (cutoffTest psi) (rescaledDiff T rho rho') ^ 2 := by
  let d : ℂ := rho - rho'
  have hdre0 : -1 < d.re := by
    dsimp [d]
    linarith
  have hdre1 : d.re < 1 := by
    dsimp [d]
    linarith
  have hdne_two : d ≠ (2 : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hdne_neg_two : d ≠ -(2 : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hden : 4 - d ^ 2 ≠ 0 := by
    rw [show 4 - d ^ 2 = -(d - 2) * (d + 2) by ring]
    exact mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr hdne_two)) (by
      intro h
      apply hdne_neg_two
      linear_combination h)
  have hlog : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT)
  have hfactor :
      1 + (Real.pi : ℂ) ^ 2 * (rescaledDiff T rho rho') ^ 2 /
          (Real.log T : ℂ) ^ 2 = (4 - d ^ 2) / 4 := by
    unfold rescaledDiff
    dsimp [d]
    push_cast
    field_simp [hlog, Real.pi_ne_zero]
    ring_nf
    rw [show Complex.I ^ 2 = -(1 : ℂ) by norm_num]
    ring
  rw [fourierC_correctedTest hpsi hT, hfactor]
  unfold pairWeight
  change ((4 - d ^ 2) / 4 * testKernel (cutoffTest psi) (rescaledDiff T rho rho') ^ 2) *
      (4 / (4 - d ^ 2)) = _
  field_simp [hden]


/-- The self-convolution is an admissible pair-correlation test function. -/
lemma cutoffSelfConv_isPairTestFunction {delta : ℝ} (hd : 0 < delta)
    (hd4 : delta < 1 / 4) {psi : ℝ → ℝ} (hpsi : IsCutoff delta psi) :
    IsPairTestFunction (cutoffSelfConv psi) := by
  refine ⟨cutoffSelfConv_neg hpsi, integrable_cutoffSelfConv hd hd4 hpsi,
    fun x hx => cutoffSelfConv_eq_zero_of_one_le_abs hpsi hx.le, ?_⟩
  obtain ⟨C, hC⟩ := (contDiff_cutoffSelfConv hpsi).lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_cutoffSelfConv hpsi) (by simp)
  refine ⟨C, fun x => ?_⟩
  simpa only [Real.norm_eq_abs, sub_zero] using hC.norm_sub_le x 0

/-- The second derivative of the self-convolution is an admissible pair-correlation test
function. -/
lemma iteratedDeriv_two_cutoffSelfConv_isPairTestFunction {delta : ℝ}
    {psi : ℝ → ℝ} (hpsi : IsCutoff delta psi) :
    IsPairTestFunction (iteratedDeriv 2 (cutoffSelfConv psi)) := by
  refine ⟨iteratedDeriv_two_cutoffSelfConv_neg hpsi,
    integrable_iteratedDeriv_two_cutoffSelfConv hpsi,
    fun x hx => iteratedDeriv_two_cutoffSelfConv_eq_zero hpsi hx, ?_⟩
  obtain ⟨C, hC⟩ :=
    (contDiff_iteratedDeriv_two_cutoffSelfConv hpsi).lipschitzWith_of_hasCompactSupport
      (hasCompactSupport_iteratedDeriv_two_cutoffSelfConv hpsi) (by simp)
  refine ⟨C, fun x => ?_⟩
  simpa only [Real.norm_eq_abs, sub_zero] using hC.norm_sub_le x 0

/-- The unweighted kernel sum is the difference of the two pair-correlation sums supplied by
the corrected test function, expanded linearly. -/
@[zz_tag "lem_sum_expansion"]
lemma unweightedKernelSum_cutoffTest_eq_pairCorrelationSum {delta : ℝ}
    {psi : ℝ → ℝ} (hpsi : IsCutoff delta psi)
    {T : ℝ} (hT : 1 < T) :
    unweightedKernelSum (cutoffTest psi) T =
      pairCorrelationSum (cutoffSelfConv psi) T -
        pairCorrelationSum (iteratedDeriv 2 (cutoffSelfConv psi)) T /
          (((4 * Real.log T ^ 2 : ℝ) : ℂ)) := by
  let s := (nontrivialZeros_finite T).toFinset
  have hlog : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT)
  have hlinear (z : ℂ) :
      fourierC (correctedTest psi T) z =
        fourierC (cutoffSelfConv psi) z -
          fourierC (iteratedDeriv 2 (cutoffSelfConv psi)) z /
            (((4 * Real.log T ^ 2 : ℝ) : ℂ)) := by
    rw [fourierC_correctedTest hpsi hT,
      fourierC_cutoffSelfConv hpsi,
      fourierC_iteratedDeriv_two_cutoffSelfConv hpsi]
    push_cast
    field_simp [hlog]
    ring
  rw [unweightedKernelSum, pairCorrelationSum, pairCorrelationSum]
  rw [finsum_mem_eq_finite_toFinset_sum _ (nontrivialZeros_finite T)]
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ (nontrivialZeros_finite T)]
  change (∑ rho ∈ s, ∑ rho' ∈ s,
      ((zeroMultiplicity rho * zeroMultiplicity rho' : ℕ) : ℂ) *
        testKernel (cutoffTest psi) (rescaledDiff T rho rho') ^ 2) =
    (∑ rho ∈ s, ∑ rho' ∈ s,
      ((zeroMultiplicity rho * zeroMultiplicity rho' : ℕ) : ℂ) *
        fourierC (cutoffSelfConv psi) (rescaledDiff T rho rho') * pairWeight (rho - rho')) -
      (∑ rho ∈ s, ∑ rho' ∈ s,
        ((zeroMultiplicity rho * zeroMultiplicity rho' : ℕ) : ℂ) *
          fourierC (iteratedDeriv 2 (cutoffSelfConv psi)) (rescaledDiff T rho rho') *
            pairWeight (rho - rho')) / (((4 * Real.log T ^ 2 : ℝ) : ℂ))
  rw [Finset.sum_div]
  simp_rw [Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro rho' hrho'
  have hrho_mem : rho ∈ nontrivialZeros T := by
    simpa [s] using hrho
  have hrho'_mem : rho' ∈ nontrivialZeros T := by
    simpa [s] using hrho'
  have hcancel := correctedTest_weight_cancel hpsi hT
    hrho_mem.2.1 hrho_mem.2.2.1 hrho'_mem.2.1 hrho'_mem.2.2.1
  rw [← hcancel, hlinear]
  ring

/-- The quantitative pair-correlation hypothesis implies convergence to its stated main term. -/
lemma PairCorrelation.tendsto (hPC : PairCorrelation) {f : ℝ → ℝ}
    (hf : IsPairTestFunction f) :
    Filter.Tendsto
      (fun T => pairCorrelationSum f T / ((zeroScale T : ℝ) : ℂ))
      Filter.atTop (nhds ((pairMainTerm f : ℝ) : ℂ)) := by
  obtain ⟨C, hC, T0, hbound⟩ := hPC f hf
  have hsqrtlog : Filter.Tendsto (fun T : ℝ => Real.sqrt (Real.log T))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hinv : Filter.Tendsto (fun T : ℝ => (Real.sqrt (Real.log T))⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hsqrtlog
  have herror_bound : Filter.Tendsto (fun T : ℝ => C / Real.sqrt (Real.log T))
      Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinv : Filter.Tendsto
        (fun T : ℝ => C * (Real.sqrt (Real.log T))⁻¹) Filter.atTop (nhds (C * 0)))
  have herror : Filter.Tendsto
      (fun T => pairCorrelationSum f T / ((zeroScale T : ℝ) : ℂ) -
        ((pairMainTerm f : ℝ) : ℂ)) Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [Filter.eventually_ge_atTop T0] with T hT
      simpa only [zeroScale] using hbound T hT
    · exact herror_bound
  have hconst : Filter.Tendsto (fun _ : ℝ => ((pairMainTerm f : ℝ) : ℂ))
      Filter.atTop (nhds ((pairMainTerm f : ℝ) : ℂ)) := tendsto_const_nhds
  convert hconst.add herror using 1
  · funext T
    ring
  · simp

/-- The normalized unweighted cutoff-kernel sum converges to the pair-correlation functional of
the self-convolution. The second-derivative correction vanishes because of its `log T` squared
denominator. -/
lemma unweightedKernelSum_cutoffTest_tendsto (hPC : PairCorrelation) {delta : ℝ}
    (hd : 0 < delta) (hd4 : delta < 1 / 4) {psi : ℝ → ℝ} (hpsi : IsCutoff delta psi) :
    Filter.Tendsto
      (fun T => unweightedKernelSum (cutoffTest psi) T / ((zeroScale T : ℝ) : ℂ))
      Filter.atTop (nhds ((pairMainTerm (cutoffSelfConv psi) : ℝ) : ℂ)) := by
  have hQ := hPC.tendsto (cutoffSelfConv_isPairTestFunction hd hd4 hpsi)
  have hQ2 := hPC.tendsto
    (iteratedDeriv_two_cutoffSelfConv_isPairTestFunction hpsi)
  have hlog_sq : Filter.Tendsto (fun T : ℝ => Real.log T ^ 2)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)).comp
      Real.tendsto_log_atTop
  have hden : Filter.Tendsto (fun T : ℝ => 4 * Real.log T ^ 2)
      Filter.atTop Filter.atTop := hlog_sq.const_mul_atTop' (by norm_num)
  have hinv_real : Filter.Tendsto (fun T : ℝ => (4 * Real.log T ^ 2)⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hden
  have hinv_complex : Filter.Tendsto
      (fun T : ℝ => ((((4 * Real.log T ^ 2 : ℝ) : ℂ)))⁻¹)
      Filter.atTop (nhds 0) := by
    convert (Complex.continuous_ofReal.tendsto 0).comp hinv_real using 1
    · funext T
      exact (Complex.ofReal_inv _).symm
    · rfl
  have hQ2_small : Filter.Tendsto
      (fun T =>
        (pairCorrelationSum (iteratedDeriv 2 (cutoffSelfConv psi)) T /
          ((zeroScale T : ℝ) : ℂ)) / (((4 * Real.log T ^ 2 : ℝ) : ℂ)))
      Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hQ2.mul hinv_complex
  have hdiff : Filter.Tendsto
      (fun T =>
        pairCorrelationSum (cutoffSelfConv psi) T / ((zeroScale T : ℝ) : ℂ) -
          (pairCorrelationSum (iteratedDeriv 2 (cutoffSelfConv psi)) T /
            ((zeroScale T : ℝ) : ℂ)) / (((4 * Real.log T ^ 2 : ℝ) : ℂ)))
      Filter.atTop (nhds ((pairMainTerm (cutoffSelfConv psi) : ℝ) : ℂ)) := by
    simpa only [sub_zero] using hQ.sub hQ2_small
  apply hdiff.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with T hT
  rw [unweightedKernelSum_cutoffTest_eq_pairCorrelationSum hpsi hT]
  have hlog : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT)
  have hdenR : (4 * Real.log T ^ 2 : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hlog)
  have hdenC : (((4 * Real.log T ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hdenR
  have hscaleR : zeroScale T ≠ 0 := by
    unfold zeroScale
    exact mul_ne_zero
      (div_ne_zero (ne_of_gt (lt_trans zero_lt_one hT))
        (mul_ne_zero (by norm_num) Real.pi_ne_zero)) hlog
  have hscaleC : ((zeroScale T : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hscaleR
  field_simp [hdenC, hscaleC]

/-! ## Removing the cutoff

The last step of the construction. We choose a
cutoff at scale `1 / (n + 5)`, use dominated convergence first for its normalising constant and
then for the two convolution integrals, and finally pass to the pair-correlation functional.
-/

/-- The extremal density is integrable on the real line. -/
private lemma integrable_extremalTest : Integrable extremalTest := by
  have hzero : ∀ x ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2), extremalTest x = 0 := by
    intro x hx
    rw [extremalTest, ite_eq_right]
    intro habs
    exact hx (Set.mem_Icc.mpr (abs_le.mp habs))
  have hcont : ContinuousOn extremalTest (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) := by
    have hG : Continuous fun x : ℝ =>
        Real.cos (Real.sqrt 2 * x) /
          (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).div_const _
    refine hG.continuousOn.congr ?_
    intro x hx
    rw [extremalTest, ite_eq_left (abs_le.mpr (Set.mem_Icc.mp hx))]
  exact hcont.integrableOn_Icc.integrable_of_forall_notMem_eq_zero hzero

/-- A fixed pointwise upper bound for the extremal density. -/
private noncomputable def extremalBound : ℝ :=
  1 / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))

private lemma extremalBound_pos : 0 < extremalBound := by
  unfold extremalBound
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsin : 0 < Real.sin (1 / Real.sqrt 2) := sin_inv_sqrt_two_pos
  exact one_div_pos.mpr (mul_pos hsqrt hsin)

private lemma extremalTest_le_bound (x : ℝ) : extremalTest x ≤ extremalBound := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsin : 0 < Real.sin (1 / Real.sqrt 2) := sin_inv_sqrt_two_pos
  have hden : 0 < Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) := mul_pos hsqrt hsin
  unfold extremalBound extremalTest
  split_ifs with hx
  · apply (div_le_div_iff_of_pos_right hden).2
    exact (le_abs_self _).trans (Real.abs_cos_le_one _)
  · exact (one_div_pos.mpr hden).le

/-- A concrete sequence of cutoff widths tending to zero. -/
private noncomputable def cutoffDelta (n : ℕ) : ℝ := 1 / ((n : ℝ) + 5)

private lemma cutoffDelta_pos (n : ℕ) : 0 < cutoffDelta n := by
  unfold cutoffDelta
  positivity

private lemma cutoffDelta_lt_quarter (n : ℕ) : cutoffDelta n < 1 / 4 := by
  unfold cutoffDelta
  rw [div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 5)]
  have hn : 0 ≤ (n : ℝ) := by positivity
  linarith

private lemma cutoffDelta_tendsto_zero :
    Filter.Tendsto cutoffDelta Filter.atTop (nhds 0) := by
  have h := (tendsto_mul_add_inv_atTop_nhds_zero (1 : ℝ) 5 (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  convert h using 1
  funext n
  simp only [cutoffDelta, Function.comp_apply, one_mul, one_div]

/-- One cutoff at every width in `cutoffDelta`. -/
private noncomputable def cutoffFamily (n : ℕ) : ℝ → ℝ :=
  Classical.choose (exists_isCutoff (cutoffDelta_pos n) (cutoffDelta_lt_quarter n))

private lemma cutoffFamily_isCutoff (n : ℕ) :
    IsCutoff (cutoffDelta n) (cutoffFamily n) :=
  Classical.choose_spec (exists_isCutoff (cutoffDelta_pos n) (cutoffDelta_lt_quarter n))

private lemma cutoffFamily_tendsto_one {x : ℝ} (hx : |x| < 1 / 2) :
    Filter.Tendsto (fun n => cutoffFamily n x) Filter.atTop (nhds 1) := by
  have hgap : 0 < 1 / 2 - |x| := by linarith
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, cutoffDelta n < 1 / 2 - |x| :=
    (tendsto_order.1 cutoffDelta_tendsto_zero).2 _ hgap
  have heq : (fun n => cutoffFamily n x) =ᶠ[Filter.atTop] (fun _ : ℕ => 1) := by
    filter_upwards [hevent] with n hn
    apply (cutoffFamily_isCutoff n).eq_one
    linarith
  exact tendsto_const_nhds.congr' heq.symm

private lemma ae_cutoffWeight_tendsto : ∀ᵐ x : ℝ,
    Filter.Tendsto (fun n => cutoffFamily n x ^ 2 * extremalTest x)
      Filter.atTop (nhds (extremalTest x)) := by
  have hboundary : ∀ᵐ x : ℝ, |x| ≠ 1 / 2 := by
    rw [ae_iff]
    have hset : {x : ℝ | ¬|x| ≠ 1 / 2} = {-(1 / 2), 1 / 2} := by
      ext x
      simp only [Set.mem_ofPred_eq, not_not, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hx
        rcases abs_eq (show (0 : ℝ) ≤ 1 / 2 by norm_num) |>.mp hx with hx | hx
        · exact Or.inr hx
        · exact Or.inl hx
      · rintro (hx | hx) <;> subst x <;> norm_num
    rw [hset]
    exact ((Set.finite_singleton (1 / 2 : ℝ)).insert (-(1 / 2))).countable.measure_zero volume
  filter_upwards [hboundary] with x hx
  rcases lt_or_gt_of_ne hx with hinside | houtside
  · simpa only [one_pow, one_mul] using
      (cutoffFamily_tendsto_one hinside).pow 2 |>.mul
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => extremalTest x)
          Filter.atTop (nhds (extremalTest x)))
  · have hf0 : extremalTest x = 0 := by
      rw [extremalTest, ite_eq_right]
      exact not_le.mpr houtside
    simp only [hf0, mul_zero]
    exact tendsto_const_nhds

/-- The normalisers of the shrinking cutoffs converge to the total extremal mass, namely one. -/
private lemma cutoffNormaliser_tendsto_one :
    Filter.Tendsto (fun n => cutoffNormaliser (cutoffFamily n))
      Filter.atTop (nhds 1) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x => cutoffFamily n x ^ 2 * extremalTest x) volume := fun n =>
    (integrable_cutoffWeight (cutoffFamily_isCutoff n)).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ x : ℝ,
      ‖cutoffFamily n x ^ 2 * extremalTest x‖ ≤ extremalTest x := by
    intro n
    filter_upwards with x
    have hpsi0 := (cutoffFamily_isCutoff n).nonneg x
    have hpsi1 := (cutoffFamily_isCutoff n).le_one x
    have hs0 : 0 ≤ cutoffFamily n x ^ 2 := sq_nonneg _
    have hs1 : cutoffFamily n x ^ 2 ≤ 1 := by nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs0 (extremalTest_nonneg x))]
    exact mul_le_of_le_one_left (extremalTest_nonneg x) hs1
  have hlim := MeasureTheory.tendsto_integral_of_dominated_convergence extremalTest
    hmeas integrable_extremalTest hbound ae_cutoffWeight_tendsto
  simpa only [cutoffNormaliser, integral_extremalTest] using hlim

private lemma cutoffNormaliser_eventually_gt_half :
    ∀ᶠ n : ℕ in Filter.atTop, 1 / 2 < cutoffNormaliser (cutoffFamily n) :=
  (tendsto_order.1 cutoffNormaliser_tendsto_one).1 _ (by norm_num)

/-- Away from the two endpoints, the normalised cutoff densities converge to the extremal
density.  Since the endpoints form a null set, this is exactly the almost-everywhere convergence
needed below. -/
private lemma ae_cutoffTestSq_tendsto : ∀ᵐ x : ℝ,
    Filter.Tendsto (fun n => cutoffTestSq (cutoffFamily n) x)
      Filter.atTop (nhds (extremalTest x)) := by
  filter_upwards [ae_cutoffWeight_tendsto] with x hx
  have hdiv := hx.div cutoffNormaliser_tendsto_one (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (fun n =>
      cutoffFamily n x ^ 2 * extremalTest x / cutoffNormaliser (cutoffFamily n))
      =ᶠ[Filter.atTop] (fun n => cutoffTestSq (cutoffFamily n) x) := by
    filter_upwards with n
    exact (cutoffTestSq_eq (cutoffDelta_pos n) (cutoffDelta_lt_quarter n)
      (cutoffFamily_isCutoff n) x).symm
  simpa using hdiv.congr' heq

/-- Eventually every normalised cutoff density is non-negative and bounded by twice the extremal
density. -/
private lemma cutoffTestSq_eventually_bounds : ∀ᶠ n : ℕ in Filter.atTop,
    ∀ x : ℝ, 0 ≤ cutoffTestSq (cutoffFamily n) x ∧
      cutoffTestSq (cutoffFamily n) x ≤ 2 * extremalTest x := by
  filter_upwards [cutoffNormaliser_eventually_gt_half] with n hA
  intro x
  have hApos : 0 < cutoffNormaliser (cutoffFamily n) := by linarith
  have hpsi0 := (cutoffFamily_isCutoff n).nonneg x
  have hpsi1 := (cutoffFamily_isCutoff n).le_one x
  have hs1 : cutoffFamily n x ^ 2 ≤ 1 := by nlinarith
  have hf0 := extremalTest_nonneg x
  rw [cutoffTestSq_eq (cutoffDelta_pos n) (cutoffDelta_lt_quarter n)
    (cutoffFamily_isCutoff n) x]
  constructor
  · exact div_nonneg (mul_nonneg (sq_nonneg _) hf0) hApos.le
  · apply (div_le_iff₀ hApos).2
    calc
      cutoffFamily n x ^ 2 * extremalTest x ≤ extremalTest x :=
        mul_le_of_le_one_left hf0 hs1
      _ = (2 * extremalTest x) * (1 / 2) := by ring
      _ ≤ (2 * extremalTest x) * cutoffNormaliser (cutoffFamily n) :=
        mul_le_mul_of_nonneg_left (le_of_lt hA) (mul_nonneg (by norm_num) hf0)

private lemma integrable_extremalDominating :
    Integrable (fun x : ℝ => 4 * extremalBound * extremalTest x) := by
  exact integrable_extremalTest.const_mul (4 * extremalBound)

/-- The self-convolutions of the normalised cutoff densities converge pointwise to the extremal
self-convolution. -/
private lemma cutoffSelfConv_tendsto (x : ℝ) :
    Filter.Tendsto (fun n => cutoffSelfConv (cutoffFamily n) x)
      Filter.atTop (nhds (extremalSelfConv x)) := by
  have hmeas : ∀ᶠ n : ℕ in Filter.atTop, AEStronglyMeasurable
      (fun t : ℝ => cutoffTestSq (cutoffFamily n) t *
        cutoffTestSq (cutoffFamily n) (x - t)) volume := by
    filter_upwards with n
    have hcont := (cutoffTestSq_contDiff (cutoffFamily_isCutoff n)).continuous
    exact (hcont.mul (hcont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hbound : ∀ᶠ n : ℕ in Filter.atTop, ∀ᵐ t : ℝ,
      ‖cutoffTestSq (cutoffFamily n) t *
          cutoffTestSq (cutoffFamily n) (x - t)‖ ≤
        4 * extremalBound * extremalTest t := by
    filter_upwards [cutoffTestSq_eventually_bounds] with n hn
    filter_upwards with t
    rcases hn t with ⟨ht0, ht1⟩
    rcases hn (x - t) with ⟨hxt0, hxt1⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 hxt0)]
    calc
      cutoffTestSq (cutoffFamily n) t * cutoffTestSq (cutoffFamily n) (x - t)
          ≤ (2 * extremalTest t) * (2 * extremalTest (x - t)) :=
        mul_le_mul ht1 hxt1 hxt0 (mul_nonneg (by norm_num) (extremalTest_nonneg t))
      _ ≤ (2 * extremalTest t) * (2 * extremalBound) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left (extremalTest_le_bound (x - t)) (by norm_num)
        · exact mul_nonneg (by norm_num) (extremalTest_nonneg t)
      _ = 4 * extremalBound * extremalTest t := by ring
  have hlim_left := ae_cutoffTestSq_tendsto
  have hlim_right := (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae
    ae_cutoffTestSq_tendsto
  have hlim : ∀ᵐ t : ℝ, Filter.Tendsto
      (fun n => cutoffTestSq (cutoffFamily n) t *
        cutoffTestSq (cutoffFamily n) (x - t)) Filter.atTop
      (nhds (extremalTest t * extremalTest (x - t))) := by
    filter_upwards [hlim_left, hlim_right] with t ht hxt
    exact ht.mul hxt
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => 4 * extremalBound * extremalTest t)
    hmeas hbound integrable_extremalDominating hlim
  simpa only [cutoffSelfConv, extremalSelfConv] using h

/-- The same dominating function gives a uniform bound for all sufficiently small-cutoff
self-convolutions. -/
private lemma cutoffSelfConv_eventually_bounds : ∀ᶠ n : ℕ in Filter.atTop,
    ∀ x : ℝ, 0 ≤ cutoffSelfConv (cutoffFamily n) x ∧
      cutoffSelfConv (cutoffFamily n) x ≤ 4 * extremalBound := by
  filter_upwards [cutoffTestSq_eventually_bounds] with n hn
  intro x
  have hcont := (cutoffTestSq_contDiff (cutoffFamily_isCutoff n)).continuous
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => cutoffTestSq (cutoffFamily n) t *
        cutoffTestSq (cutoffFamily n) (x - t)) volume :=
    (hcont.mul (hcont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hnonneg : ∀ t : ℝ, 0 ≤ cutoffTestSq (cutoffFamily n) t *
      cutoffTestSq (cutoffFamily n) (x - t) := fun t => mul_nonneg (hn t).1 (hn (x - t)).1
  have hpoint : ∀ t : ℝ,
      cutoffTestSq (cutoffFamily n) t * cutoffTestSq (cutoffFamily n) (x - t) ≤
        4 * extremalBound * extremalTest t := by
    intro t
    calc
      cutoffTestSq (cutoffFamily n) t * cutoffTestSq (cutoffFamily n) (x - t)
          ≤ (2 * extremalTest t) * (2 * extremalTest (x - t)) :=
        mul_le_mul (hn t).2 (hn (x - t)).2 (hn (x - t)).1
          (mul_nonneg (by norm_num) (extremalTest_nonneg t))
      _ ≤ (2 * extremalTest t) * (2 * extremalBound) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left (extremalTest_le_bound (x - t)) (by norm_num)
        · exact mul_nonneg (by norm_num) (extremalTest_nonneg t)
      _ = 4 * extremalBound * extremalTest t := by ring
  have hnorm : ∀ᵐ t : ℝ,
      ‖cutoffTestSq (cutoffFamily n) t * cutoffTestSq (cutoffFamily n) (x - t)‖ ≤
        4 * extremalBound * extremalTest t := by
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t)]
    exact hpoint t
  have hint : Integrable (fun t : ℝ => cutoffTestSq (cutoffFamily n) t *
      cutoffTestSq (cutoffFamily n) (x - t)) :=
    integrable_extremalDominating.mono' hmeas hnorm
  constructor
  · unfold cutoffSelfConv
    exact MeasureTheory.integral_nonneg hnonneg
  · unfold cutoffSelfConv
    calc
      (∫ t : ℝ, cutoffTestSq (cutoffFamily n) t *
          cutoffTestSq (cutoffFamily n) (x - t))
          ≤ ∫ t : ℝ, 4 * extremalBound * extremalTest t :=
        MeasureTheory.integral_mono_ae hint integrable_extremalDominating
          (Filter.Eventually.of_forall hpoint)
      _ = 4 * extremalBound := by
        rw [MeasureTheory.integral_const_mul, integral_extremalTest, mul_one]

private lemma cutoffSelfConv_interval_tendsto :
    Filter.Tendsto
      (fun n => ∫ α in (0 : ℝ)..1, α * cutoffSelfConv (cutoffFamily n) α)
      Filter.atTop
      (nhds (∫ α in (0 : ℝ)..1, α * extremalSelfConv α)) := by
  have hmeas : ∀ᶠ n : ℕ in Filter.atTop, AEStronglyMeasurable
      (fun α : ℝ => α * cutoffSelfConv (cutoffFamily n) α)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards with n
    have hcont := (contDiff_cutoffSelfConv (cutoffFamily_isCutoff n)).continuous
    exact (continuous_id.mul hcont).aestronglyMeasurable
  have hbound : ∀ᶠ n : ℕ in Filter.atTop, ∀ᵐ α : ℝ,
      α ∈ Set.uIoc (0 : ℝ) 1 →
        ‖α * cutoffSelfConv (cutoffFamily n) α‖ ≤ 4 * extremalBound := by
    filter_upwards [cutoffSelfConv_eventually_bounds] with n hn
    filter_upwards with α
    intro hα
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hα
    have hα0 : 0 ≤ α := le_of_lt hα.1
    rcases hn α with ⟨hQ0, hQ1⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hα0 hQ0)]
    calc
      α * cutoffSelfConv (cutoffFamily n) α
          ≤ 1 * cutoffSelfConv (cutoffFamily n) α :=
        mul_le_mul_of_nonneg_right hα.2 hQ0
      _ ≤ 4 * extremalBound := by simpa using hQ1
  have hlim : ∀ᵐ α : ℝ, α ∈ Set.uIoc (0 : ℝ) 1 → Filter.Tendsto
      (fun n => α * cutoffSelfConv (cutoffFamily n) α) Filter.atTop
      (nhds (α * extremalSelfConv α)) := by
    filter_upwards with α
    intro _
    exact tendsto_const_nhds.mul (cutoffSelfConv_tendsto α)
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (F := fun n α => α * cutoffSelfConv (cutoffFamily n) α)
    (f := fun α => α * extremalSelfConv α)
    (fun _ : ℝ => 4 * extremalBound) hmeas hbound intervalIntegrable_const hlim

private lemma cutoffPairMainTerm_tendsto :
    Filter.Tendsto (fun n => pairMainTerm (cutoffSelfConv (cutoffFamily n)))
      Filter.atTop (nhds (pairMainTerm extremalSelfConv)) := by
  simpa only [pairMainTerm] using
    (cutoffSelfConv_tendsto 0).add (cutoffSelfConv_interval_tendsto.const_mul 2)

/-- **The cutoff constants converge to the Montgomery--Taylor constant**
(`lem_C_delta_limit`). -/
@[zz_tag "lem_C_delta_limit"]
theorem exists_cutoff_pairMainTerm_close (ε : ℝ) (hε : 0 < ε) :
    ∃ delta : ℝ, ∃ psi : ℝ → ℝ,
      0 < delta ∧ delta < 1 / 4 ∧ IsCutoff delta psi ∧
        |pairMainTerm (cutoffSelfConv psi) - montgomeryTaylorConst| < ε := by
  have hMT : pairMainTerm extremalSelfConv = montgomeryTaylorConst := by
    unfold pairMainTerm
    exact montgomeryTaylor
  have hlim : Filter.Tendsto (fun n => pairMainTerm (cutoffSelfConv (cutoffFamily n)))
      Filter.atTop (nhds montgomeryTaylorConst) := by
    rw [← hMT]
    exact cutoffPairMainTerm_tendsto
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) ε hε
  refine ⟨cutoffDelta N, cutoffFamily N, cutoffDelta_pos N,
    cutoffDelta_lt_quarter N, cutoffFamily_isCutoff N, ?_⟩
  simpa only [Real.dist_eq] using hN N le_rfl

/-- **Kernel construction** (`lem_kernel_construction`).  The cutoff test is admissible, its
pair-correlation constant is arbitrarily close to the Montgomery--Taylor constant, and the
normalized unweighted kernel sum converges to that constant. -/
@[zz_tag "lem_kernel_construction"]
theorem kernelConstruction (hPC : PairCorrelation) (ε : ℝ) (hε : 0 < ε) :
    ∃ eta C,
      IsAdmissible (1 / 2) eta ∧
      |C - montgomeryTaylorConst| < ε ∧
      Filter.Tendsto
        (fun T => (unweightedKernelSum eta T).re / zeroScale T)
        Filter.atTop (nhds C) := by
  obtain ⟨delta, psi, hd, hd4, hpsi, hclose⟩ := exists_cutoff_pairMainTerm_close ε hε
  refine ⟨cutoffTest psi, pairMainTerm (cutoffSelfConv psi),
    isAdmissible_cutoffTest hd hd4 hpsi, hclose, ?_⟩
  have hreal : Filter.Tendsto
      (Complex.re ∘ fun T =>
        unweightedKernelSum (cutoffTest psi) T / ((zeroScale T : ℝ) : ℂ))
      Filter.atTop (nhds (pairMainTerm (cutoffSelfConv psi))) :=
    (Complex.continuous_re.tendsto
      ((pairMainTerm (cutoffSelfConv psi) : ℝ) : ℂ)).comp
        (unweightedKernelSum_cutoffTest_tendsto hPC hd hd4 hpsi)
  convert hreal using 1
  funext T
  exact (Complex.div_ofReal_re _ _).symm

end ZetaZeros
