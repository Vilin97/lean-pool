/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.SingleIntegral.Series

/-! # The unit-interval representation and node analyticity -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- The affine segment from `1` to a point in Carlson's right-half-plane domain remains in
that domain. -/
lemma affineSegment_mem_rightHalfPlane
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    {u : ℝ} (hu : u ∈ Set.Icc 0 1) (i : ι) :
    (1 - u : ℂ) + (u : ℂ) * z i ∈ carlsonRightHalfPlane := by
  have hzi : 0 < (z i).re := hz i
  by_cases hu0 : u = 0
  · subst u
    simp [carlsonRightHalfPlane]
  have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have hmul : 0 < u * (z i).re := mul_pos hupos hzi
  have hone : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  dsimp only [carlsonRightHalfPlane, Set.mem_ofPred_eq]
  simp only [add_re, sub_re, one_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero]
  exact add_pos_of_nonneg_of_pos hone hmul

/-- The product kernel in Carlson's single-integral formula. -/
def singleIntegralKernel (b z : ι → ℂ) (u : ℝ) : ℂ :=
  ∏ i, ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i)

/-- The Fréchet derivative of the product kernel with respect to the Carlson variables. -/
private def singleIntegralKernelFDeriv (b z : ι → ℂ) (u : ℝ) :
    (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i, (∏ j ∈ Finset.univ.erase i,
      ((1 - u : ℂ) + (u : ℂ) * z j) ^ (-b j)) •
    ((-b i * ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i - 1)) •
      ((u : ℂ) • (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)))

/-- The displayed derivative is the derivative of the single-integral product kernel. -/
private lemma hasFDerivAt_singleIntegralKernel
    (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain)
    {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    HasFDerivAt (fun y => singleIntegralKernel b y u)
      (singleIntegralKernelFDeriv b z u) z := by
  classical
  let p : ι → ((ι → ℂ) →L[ℂ] ℂ) := fun i => ContinuousLinearMap.proj i
  have hq (i : ι) : HasFDerivAt
      (fun y : ι → ℂ => (1 - u : ℂ) + (u : ℂ) * y i) ((u : ℂ) • p i) z := by
    simpa [p] using (((p i).hasFDerivAt.const_mul (u : ℂ)).const_add (1 - u : ℂ))
  have hpow (i : ι) : HasFDerivAt
      (fun y : ι → ℂ => ((1 - u : ℂ) + (u : ℂ) * y i) ^ (-b i))
      ((-b i * ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i - 1)) •
        ((u : ℂ) • p i)) z := by
    have h := (hq i).cpow (hasFDerivAt_const (x := z) (-b i))
      (carlsonRSegment_mem_slitPlane hz hu i)
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro v
    simp [p, neg_mul, smul_smul]
  exact HasFDerivAt.finsetProd (u := (Finset.univ : Finset ι))
    (fun i hi => hpow i)

/-- The kernel derivative is continuous jointly in its variables away from the branch cut. -/
private lemma continuousOn_singleIntegralKernelFDeriv
    (b : ι → ℂ) {S : Set ((ι → ℂ) × ℝ)}
    (hS : ∀ p ∈ S, ∀ i,
      (1 - p.2 : ℂ) + (p.2 : ℂ) * p.1 i ∈ slitPlane) :
    ContinuousOn (fun p => singleIntegralKernelFDeriv b p.1 p.2) S := by
  classical
  have hq (i : ι) : Continuous
      (fun p : (ι → ℂ) × ℝ => (1 - p.2 : ℂ) + (p.2 : ℂ) * p.1 i) := by
    fun_prop
  have hpow (e : ι → ℂ) (i : ι) : ContinuousOn
      (fun p : (ι → ℂ) × ℝ =>
        ((1 - p.2 : ℂ) + (p.2 : ℂ) * p.1 i) ^ e i) S :=
    (hq i).continuousOn.cpow continuousOn_const (fun p hp => hS p hp i)
  unfold singleIntegralKernelFDeriv
  apply continuousOn_finsetSum
  intro i hi
  have hout : ContinuousOn (fun p : (ι → ℂ) × ℝ =>
      ∏ j ∈ Finset.univ.erase i,
        ((1 - p.2 : ℂ) + (p.2 : ℂ) * p.1 j) ^ (-b j)) S := by
    apply continuousOn_finsetProd
    intro j hj
    exact hpow (fun j => -b j) j
  have hscalar : ContinuousOn (fun p : (ι → ℂ) × ℝ =>
      -b i * ((1 - p.2 : ℂ) + (p.2 : ℂ) * p.1 i) ^ (-b i - 1)) S :=
    continuousOn_const.mul (hpow (fun j => -b j - 1) i)
  have hproj : Continuous (fun p : (ι → ℂ) × ℝ =>
      (p.2 : ℂ) • (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)) := by
    fun_prop
  exact hout.smul (hscalar.smul hproj.continuousOn)

/-- At fixed Carlson variables in the slit plane, the product kernel is continuous on
the closed unit interval. -/
lemma continuousOn_singleIntegralKernel_fixed
    (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    ContinuousOn (singleIntegralKernel b z) (Set.Icc 0 1) := by
  classical
  unfold singleIntegralKernel
  apply continuousOn_finsetProd
  intro i hi
  have hq : Continuous
      (fun u : ℝ => (1 - u : ℂ) + (u : ℂ) * z i) := by fun_prop
  exact hq.continuousOn.cpow continuousOn_const (fun u hu =>
    carlsonRSegment_mem_slitPlane hz hu i)

/-- At fixed Carlson variables in the slit plane, the kernel derivative is continuous
on the closed unit interval. -/
private lemma continuousOn_singleIntegralKernelFDeriv_fixed
    (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    ContinuousOn (singleIntegralKernelFDeriv b z) (Set.Icc 0 1) := by
  classical
  have hq (i : ι) : Continuous
      (fun u : ℝ => (1 - u : ℂ) + (u : ℂ) * z i) := by fun_prop
  have hpow (e : ι → ℂ) (i : ι) : ContinuousOn
      (fun u : ℝ => ((1 - u : ℂ) + (u : ℂ) * z i) ^ e i) (Set.Icc 0 1) :=
    (hq i).continuousOn.cpow continuousOn_const (fun u hu =>
      carlsonRSegment_mem_slitPlane hz hu i)
  unfold singleIntegralKernelFDeriv
  apply continuousOn_finsetSum
  intro i hi
  have hout : ContinuousOn (fun u : ℝ =>
      ∏ j ∈ Finset.univ.erase i,
        ((1 - u : ℂ) + (u : ℂ) * z j) ^ (-b j)) (Set.Icc 0 1) := by
    apply continuousOn_finsetProd
    intro j hj
    exact hpow (fun j => -b j) j
  have hscalar : ContinuousOn (fun u : ℝ =>
      -b i * ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i - 1)) (Set.Icc 0 1) :=
    continuousOn_const.mul (hpow (fun j => -b j - 1) i)
  have hproj : Continuous (fun u : ℝ =>
      (u : ℂ) • (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)) := by fun_prop
  exact hout.smul (hscalar.smul hproj.continuousOn)
/-- For positive beta exponents, the unit-interval integral is analytic in all Carlson
variables throughout the full product slit plane (Carlson's Theorem 6.8-1). -/
theorem analyticOnNhd_carlsonRUnitIntervalIntegral_slit
    (a a' : ℂ) (b : ι → ℂ) (ha : 0 < a.re) (ha' : 0 < a'.re) :
    AnalyticOnNhd ℂ (carlsonRUnitIntervalIntegral a a' b)
      carlsonRSlitDomain := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 1)
  let W : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1)
  let F : (ι → ℂ) → ℝ → ℂ := fun z u => W u * singleIntegralKernel b z u
  let F' : (ι → ℂ) → ℝ → ((ι → ℂ) →L[ℂ] ℂ) := fun z u =>
    W u • singleIntegralKernelFDeriv b z u
  have hWint : Integrable W μ := by
    change IntegrableOn (fun u : ℝ =>
      (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1)) (Set.Ioo 0 1) volume
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (betaIntegral_convergent ha ha')
  have hU := isOpen_carlsonRSlitDomain (ι := ι)
  have hanalytic : AnalyticOnNhd ℂ (fun z => ∫ u, F z u ∂μ)
      carlsonRSlitDomain := by
    refine analyticOnNhd_integral_of_dominated_of_fderiv_le hU ?_
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
    let r : ℝ := ε / 2
    have hr : 0 < r := half_pos hε
    let Kset : Set ((ι → ℂ) × ℝ) := Metric.closedBall z r ×ˢ Set.Icc 0 1
    have hclosed_mem : Metric.closedBall z r ∈ nhds z := Metric.closedBall_mem_nhds z hr
    have hclosed_domain : Metric.closedBall z r ⊆ carlsonRSlitDomain := by
      intro y hy
      apply hball
      rw [Metric.mem_closedBall] at hy
      exact Metric.mem_ball.mpr (hy.trans_lt (half_lt_self hε))
    have hslit : ∀ p ∈ Kset, ∀ i,
        (1 - p.2 : ℂ) + (p.2 : ℂ) * p.1 i ∈ slitPlane := by
      intro p hp i
      exact carlsonRSegment_mem_slitPlane (hclosed_domain hp.1) hp.2 i
    have hDcont : ContinuousOn
        (fun p => singleIntegralKernelFDeriv b p.1 p.2) Kset :=
      continuousOn_singleIntegralKernelFDeriv b hslit
    have hKcompact : IsCompact Kset := (isCompact_closedBall z r).prod isCompact_Icc
    obtain ⟨C₀, hC₀⟩ := bddAbove_def.mp (hKcompact.bddAbove_image hDcont.norm)
    let C : ℝ := max C₀ 0
    have hC : ∀ p ∈ Kset, ‖singleIntegralKernelFDeriv b p.1 p.2‖ ≤ C := by
      intro p hp
      exact (hC₀ _ ⟨p, hp, rfl⟩).trans (le_max_left _ _)
    let bound : ℝ → ℝ := fun u => C * ‖W u‖
    have hFint (y : ι → ℂ) (hy : y ∈ Metric.closedBall z r) : Integrable (F y) μ := by
      have hinterval := (betaIntegral_convergent ha ha').mul_continuousOn
        (by simpa [Set.uIcc_of_le zero_le_one] using
          continuousOn_singleIntegralKernel_fixed b (hclosed_domain hy))
      change IntegrableOn (fun u => W u * singleIntegralKernel b y u)
        (Set.Ioo 0 1) volume
      exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hinterval
    refine ⟨Metric.closedBall z r, bound, F', hclosed_mem, ?_, hFint z
      (Metric.mem_closedBall_self hr.le), ?_, ?_, ?_, ?_⟩
    · filter_upwards [hclosed_mem] with y hy
      exact (hFint y hy).aestronglyMeasurable
    · have hinterval := (betaIntegral_convergent ha ha').smul_continuousOn
          (by simpa [Set.uIcc_of_le zero_le_one] using
            continuousOn_singleIntegralKernelFDeriv_fixed b hz)
      exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hinterval).1
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
      intro y hy
      simp only [F', bound, norm_smul]
      calc
        ‖W u‖ * ‖singleIntegralKernelFDeriv b y u‖ ≤ ‖W u‖ * C := by
          gcongr
          exact hC (y, u) ⟨hy, hu.1.le, hu.2.le⟩
        _ = C * ‖W u‖ := mul_comm _ _
    · exact hWint.norm.const_mul C
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
      intro y hy
      have hyDomain := hclosed_domain hy
      have hder := (hasFDerivAt_singleIntegralKernel b hyDomain
        ⟨hu.1.le, hu.2.le⟩).const_mul (W u)
      simpa [F, F'] using hder
  change AnalyticOnNhd ℂ (fun z => ∫ u, F z u ∂μ) carlsonRSlitDomain
  exact hanalytic

/-- The right-half-plane restriction of the slit-plane analyticity theorem. -/
theorem analyticOnNhd_carlsonRUnitIntervalIntegral
    (a a' : ℂ) (b : ι → ℂ) (ha : 0 < a.re) (ha' : 0 < a'.re) :
    AnalyticOnNhd ℂ (carlsonRUnitIntervalIntegral a a' b)
      carlsonRVariableDomain :=
  (analyticOnNhd_carlsonRUnitIntervalIntegral_slit a a' b ha ha').mono
    carlsonRVariableDomain_subset_slitDomain

/-- Carlson's Theorem 6.8-1 in unit-interval form.  The homogeneity relation
`a + a' = ∑ i, b i` supplies the exponent at the endpoint `u = 1`. -/
theorem carlsonRUnitIntervalIntegral_eq
    {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i)
    (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    carlsonRUnitIntervalIntegral a a' b z =
      betaIntegral a a' * carlsonRIntegral (-a) b z := by
  let one : ι → ℂ := fun _ => 1
  have hone : one ∈ carlsonRVariableDomain := by
    intro i
    simp [one, carlsonRightHalfPlane]
  have hconv : Convex ℝ (carlsonRVariableDomain : Set (ι → ℂ)) := by
    rw [show carlsonRVariableDomain (ι := ι) =
        Set.pi Set.univ (fun _ => carlsonRightHalfPlane) by
      ext w
      simp [carlsonRVariableDomain]]
    exact convex_pi (fun _ _ => convex_carlsonRightHalfPlane)
  have hleft := analyticOnNhd_carlsonRUnitIntervalIntegral a a' b ha ha'
  have hright : AnalyticOnNhd ℂ
      (fun w => betaIntegral a a' * carlsonRIntegral (-a) b w)
      carlsonRVariableDomain :=
    analyticOnNhd_const.mul (analyticOnNhd_carlsonRIntegral (-a) hb)
  have hevent : (carlsonRUnitIntervalIntegral a a' b) =ᶠ[nhds one]
      (fun w => betaIntegral a a' * carlsonRIntegral (-a) b w) := by
    filter_upwards [Metric.ball_mem_nhds one zero_lt_one] with w hw
    apply carlsonRUnitIntervalIntegral_eq_of_norm_one_sub_lt_one ha ha' hsum hb
    intro i
    calc
      ‖1 - w i‖ = ‖(w - one) i‖ := by
        change ‖(1 : ℂ) - w i‖ = ‖w i - 1‖
        exact norm_sub_rev _ _
      _ ≤ ‖w - one‖ := norm_le_pi_norm (w - one) i
      _ = dist w one := by rw [dist_eq_norm]
      _ < 1 := Metric.mem_ball.mp hw
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconv.isPreconnected hone hevent hz

end DirichletTransform
