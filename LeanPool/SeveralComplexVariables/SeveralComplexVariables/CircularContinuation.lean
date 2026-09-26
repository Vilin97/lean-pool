/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.CPolynomial
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Circular
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.IdentityPrinciple
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LocallyUniform
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.RemovableSingularity.Cauchy

/-!
# Homogeneous expansion and continuation on circular domains

The terms are diagonals of Mathlib continuous multilinear Taylor coefficients, hence homogeneous
polynomials. Convergence is grouped by total degree, not by individual coordinate monomials.
Cauchy projections identify the terms on circular domains, and geometric majorants give locally
uniform convergence on the balanced hull. Reference: [Scheidemann][Scheidemann2005] (2005),
Theorem 2.1.8. Banach-valued targets are allowed.

## Main results

`homogeneousTerm` is the degree-`k` diagonal of a multilinear Taylor series.
`IsCircular.hasSumLocallyUniformlyOn_homogeneousTerm_balancedHull` is locally uniform convergence of
the homogeneous expansion on the balanced hull. `exists_extension_balancedHull` is continuation from
a circular domain to its balanced hull.

## References

* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The homogeneous term of degree `k` of a multilinear power series centered at zero. -/
@[expose] def homogeneousTerm (p : FormalMultilinearSeries ℂ E F) (k : ℕ) (z : E) : F :=
  p k (fun _ => z)

omit [FiniteDimensional ℂ E] [CompleteSpace F] in
/-- A homogeneous term is the corresponding multilinear map on the constant tuple. -/
theorem homogeneousTerm_apply (p : FormalMultilinearSeries ℂ E F) (k : ℕ) (z : E) :
    homogeneousTerm p k z = p k (fun _ => z) := rfl

omit [FiniteDimensional ℂ E] [CompleteSpace F] in
/-- The degree is expressed by the usual scalar homogeneity identity. -/
theorem homogeneousTerm_smul (p : FormalMultilinearSeries ℂ E F) (k : ℕ) (c : ℂ) (z : E) :
    homogeneousTerm p k (c • z) = c ^ k • homogeneousTerm p k z := by
  simpa [homogeneousTerm] using (p k).map_smul_univ (fun _ => c) (fun _ => z)

omit [FiniteDimensional ℂ E] [CompleteSpace F] in
/-- A homogeneous Taylor term is analytic on the whole ambient space. -/
theorem analyticOnNhd_homogeneousTerm (p : FormalMultilinearSeries ℂ E F) (k : ℕ)
    (S : Set E) : AnalyticOnNhd ℂ (homogeneousTerm p k) S := by
  intro z _
  exact (p k).analyticAt.comp (analyticAt_pi_iff.mpr fun _ => analyticAt_id)

/-- On a circular domain, the homogeneous Taylor terms are the Cauchy projections under simultaneous
rotation of all coordinates. -/
theorem homogeneousTerm_eq_circleIntegral {U : Set E} (ho : IsOpen U)
    (hc : IsPreconnected U) (hrot : IsCircular U) (hzero : (0 : E) ∈ U)
    {f : E → F} (hf : AnalyticOnNhd ℂ f U) {p : FormalMultilinearSeries ℂ E F}
    (hp : HasFPowerSeriesAt f p 0) (k : ℕ) :
    EqOn (homogeneousTerm p k)
      (fun z => (2 * Real.pi * I : ℂ)⁻¹ •
        ∮ w in C(0, 1), w⁻¹ ^ k • w⁻¹ • f (w • z)) U := by
  let H : E × ℂ → F := fun q => q.2⁻¹ ^ k • q.2⁻¹ • f (q.2 • q.1)
  have hH : AnalyticOnNhd ℂ H {q | q.2 ≠ 0 ∧ q.2 • q.1 ∈ U} := by
    intro q hq
    exact ((analyticAt_snd.inv hq.1).pow k).smul
      ((analyticAt_snd.inv hq.1).smul
        ((hf _ hq.2).comp_of_eq (analyticAt_snd.smul analyticAt_fst) rfl))
  have hproj := (analyticOnNhd_circleIntegral_kernel (c := 0) ho hH
    (by norm_num : (0 : ℝ) ≤ 1)
    (fun z hz w hw => by
      have hw' : ‖w‖ = 1 := by simpa using hw
      exact ⟨norm_ne_zero_iff.mp (by rw [hw']; norm_num),
        hrot.smul_mem hz hw'⟩)).const_smul
        (c := (2 * Real.pi * I : ℂ)⁻¹)
  apply DifferentiableOn.eqOn_of_preconnected_of_eventuallyEq ho hc
    (analyticOnNhd_homogeneousTerm p k U).differentiableOn hproj.differentiableOn hzero
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ho 0 hzero
  filter_upwards [ball_mem_nhds (0 : E) hr] with z hz
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight z
  have hline : HasFPowerSeriesAt (fun w : ℂ => f (w • z))
      (p.compContinuousLinearMap L) 0 := by
    have hp' : HasFPowerSeriesAt f p (L 0) := by simpa [L] using hp
    exact hp'.compContinuousLinearMap
  have hd : DifferentiableOn ℂ (fun w : ℂ => f (w • z)) (closedBall 0 1) := by
    intro w hw
    apply ((hf _ (hball ?_)).differentiableAt.comp w L.differentiableAt).differentiableWithinAt
    change w • z ∈ ball 0 r
    rw [mem_ball_zero_iff, norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg z) (mem_closedBall_zero_iff.mp hw)).trans_lt
      (mem_ball_zero_iff.mp hz)
  have he := hline.eq_formalMultilinearSeries
    (hd.hasFPowerSeriesOnBall (R := 1) (by norm_num)).hasFPowerSeriesAt
  have he' := congrArg (fun q : FormalMultilinearSeries ℂ ℂ F => q k (fun _ => 1)) he
  simpa only [FormalMultilinearSeries.compContinuousLinearMap_apply, L,
    Function.comp_def, Pi.smul_apply, NNReal.coe_one,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul,
    homogeneousTerm, cauchyPowerSeries_apply, sub_zero, one_div, H] using he'

omit [FiniteDimensional ℂ E] in
/-- Openness lets every point of a balanced hull be represented by a strict, nonzero contraction of
a point of the original set. -/
private theorem exists_strict_contraction {U : Set E} (ho : IsOpen U)
    (hzero : (0 : E) ∈ U) {x : E} (hx : x ∈ balancedHull ℂ U) :
    ∃ (c : ℂ) (z : E), c ≠ 0 ∧ ‖c‖ < 1 ∧ z ∈ U ∧ c • z = x := by
  obtain ⟨d, hd, y, hy, rfl⟩ := mem_balancedHull_iff.mp hx
  by_cases hd0 : d = 0
  · exact ⟨1 / 2, 0, by norm_num, by norm_num, hzero, by simp [hd0]⟩
  have hn : {t : ℝ | (t : ℂ) • y ∈ U} ∈ 𝓝 1 := by
    exact (continuous_ofReal.smul continuous_const).continuousAt.preimage_mem_nhds
      (ho.mem_nhds (by simpa using hy))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hn
  let t : ℝ := 1 + ε / 2
  have ht : 1 < t := by dsimp [t]; linarith
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hty : (t : ℂ) • y ∈ U := hsub (by
    simp only [mem_ball, Real.dist_eq, t, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    exact half_lt_self hε)
  refine ⟨d / t, (t : ℂ) • y, div_ne_zero hd0 (ofReal_ne_zero.mpr ht0.ne'), ?_, hty, ?_⟩
  · rw [norm_div, Complex.norm_of_nonneg ht0.le]
    exact (div_lt_one ht0).mpr (hd.trans_lt ht)
  · rw [smul_smul, div_mul_cancel₀ _ (ofReal_ne_zero.mpr ht0.ne')]

/-- Cauchy projections give a locally summable geometric majorant throughout the balanced hull of a
circular domain. -/
private theorem hasSumLocallyUniformlyOn_homogeneousTerm {U : Set E} (ho : IsOpen U)
    (hc : IsPreconnected U) (hrot : IsCircular U) (hzero : (0 : E) ∈ U)
    {f : E → F} (hf : AnalyticOnNhd ℂ f U) {p : FormalMultilinearSeries ℂ E F}
    (hp : HasFPowerSeriesAt f p 0) :
    HasSumLocallyUniformlyOn (homogeneousTerm p) (fun z => ∑' k, homogeneousTerm p k z)
      (balancedHull ℂ U) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro x hx
  obtain ⟨c, z, hc0, hc1, hz, rfl⟩ := exists_strict_contraction ho hzero hx
  have hn : ∀ᶠ y in 𝓝 z, ∀ w ∈ sphere (0 : ℂ) 1, w • y ∈ U := by
    apply (isCompact_sphere (0 : ℂ) 1).eventually_forall_of_forall_eventually
    intro w hw
    apply (continuous_snd.smul continuous_fst).continuousAt.preimage_mem_nhds
    exact ho.mem_nhds (hrot.smul_mem hz (by simpa using hw))
  obtain ⟨δ, hδ, hball⟩ := nhds_basis_closedBall.mem_iff.mp hn
  let K := (fun q : E × ℂ => q.2 • q.1) '' (closedBall z δ ×ˢ sphere 0 1)
  have hK : IsCompact K := ((isCompact_closedBall z δ).prod (isCompact_sphere 0 1)).image
    (continuous_snd.smul continuous_fst)
  have hKU : K ⊆ U := by
    rintro _ ⟨⟨y, w⟩, ⟨hy, hw⟩, rfl⟩
    exact hball hy w hw
  obtain ⟨M, hM⟩ := hK.bddAbove_image (hf.continuousOn.mono hKU).norm
  let C := max M 0
  have hbound (y : E) (hy : y ∈ closedBall z δ) (k : ℕ) : ‖homogeneousTerm p k y‖ ≤ C := by
    have hyU : y ∈ U := by simpa using hball hy 1 (by simp)
    rw [homogeneousTerm_eq_circleIntegral ho hc hrot hzero hf hp k hyU]
    apply (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (by norm_num : (0 : ℝ) ≤ 1) ?_).trans_eq (one_mul C)
    intro w hw
    have hw' : ‖w‖ = 1 := by simpa using hw
    simp only [norm_smul, norm_pow, norm_inv, hw', inv_one, one_pow, one_mul]
    exact (hM ⟨w • y, ⟨(y, w), ⟨hy, hw⟩, rfl⟩, rfl⟩).trans (le_max_left _ _)
  let N := {y : E | c⁻¹ • y ∈ ball z δ}
  have hN : N ∈ 𝓝 (c • z) := by
    apply (continuous_const.smul continuous_id).continuousAt.preimage_mem_nhds
    simpa [hc0] using ball_mem_nhds z hδ
  have hterm (k : ℕ) (y : E) (hy : y ∈ N) :
      ‖homogeneousTerm p k y‖ ≤ C * ‖c‖ ^ k := by
    have he : y = c • (c⁻¹ • y) := by simp [hc0]
    calc
      ‖homogeneousTerm p k y‖ = ‖c‖ ^ k * ‖homogeneousTerm p k (c⁻¹ • y)‖ := by
        conv_lhs => rw [he, homogeneousTerm_smul]
        rw [norm_smul, norm_pow]
      _ ≤ ‖c‖ ^ k * C := mul_le_mul_of_nonneg_left
        (hbound _ (ball_subset_closedBall hy) k) (by positivity)
      _ = C * ‖c‖ ^ k := mul_comm _ _
  refine ⟨N, mem_nhdsWithin_of_mem_nhds hN, ?_⟩
  exact hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
    (tendstoUniformlyOn_tsum ((summable_geometric_of_lt_one (norm_nonneg c) hc1).mul_left C)
      hterm)

/-- Homogeneous Taylor expansion on a circular domain extends to its balanced hull. Cauchy
projections under common rotations and compact majorants on radial contractions give
convergence; analytic uniqueness identifies the sum with the original function. The chosen
Taylor series is supplied explicitly. -/
theorem IsCircular.hasSumLocallyUniformlyOn_homogeneousTerm_balancedHull {U : Set E} (ho : IsOpen U)
    (hc : IsPreconnected U) (hrot : IsCircular U) (hzero : (0 : E) ∈ U)
    {f : E → F} (hf : AnalyticOnNhd ℂ f U) {p : FormalMultilinearSeries ℂ E F}
    (hp : HasFPowerSeriesAt f p 0) :
    HasSumLocallyUniformlyOn (homogeneousTerm p) f U ∧
      HasSumLocallyUniformlyOn (homogeneousTerm p) (fun z => ∑' k, homogeneousTerm p k z)
        (balancedHull ℂ U) ∧
      AnalyticOnNhd ℂ (fun z => ∑' k, homogeneousTerm p k z) (balancedHull ℂ U) := by
  have hs := hasSumLocallyUniformlyOn_homogeneousTerm ho hc hrot hzero hf hp
  have ha : AnalyticOnNhd ℂ (fun z => ∑' k, homogeneousTerm p k z) (balancedHull ℂ U) := by
    apply hs.analyticOnNhd_of_finiteDimensional _ (ho.balancedHull hzero)
    filter_upwards with s
    exact Finset.analyticOnNhd_fun_sum s fun k _ =>
      analyticOnNhd_homogeneousTerm p k _
  have he : EqOn (fun z => ∑' k, homogeneousTerm p k z) f U := by
    apply DifferentiableOn.eqOn_of_preconnected_of_eventuallyEq ho hc
      (ha.mono (subset_balancedHull ℂ)).differentiableOn hf.differentiableOn hzero
    filter_upwards [hp.eventually_hasSum] with z hz
    simpa only [homogeneousTerm, zero_add] using hz.tsum_eq
  exact ⟨(hs.mono (subset_balancedHull ℂ)).congr_right (fun z hz => he hz), hs, ha⟩

/-- A holomorphic function on a circular domain containing zero extends to its balanced hull.
Depends on homogeneous expansion. -/
theorem exists_extension_balancedHull {U : Set E} (ho : IsOpen U)
    (hc : IsPreconnected U) (hrot : IsCircular U) (hzero : (0 : E) ∈ U)
    {f : E → F} (hf : AnalyticOnNhd ℂ f U) :
    ∃ g, AnalyticOnNhd ℂ g (balancedHull ℂ U) ∧ EqOn g f U := by
  obtain ⟨p, hp⟩ := hf 0 hzero
  obtain ⟨hs, _, ha⟩
    := IsCircular.hasSumLocallyUniformlyOn_homogeneousTerm_balancedHull ho hc hrot hzero hf hp
  exact ⟨_, ha, fun z hz => (hs.hasSum hz).tsum_eq⟩

/-- Extensions to the balanced hull are unique by the identity theorem and geometry. -/
theorem eqOn_balancedHull_of_eqOn {U : Set E} (ho : IsOpen U) (hzero : (0 : E) ∈ U)
    {f g : E → F} (hf : AnalyticOnNhd ℂ f (balancedHull ℂ U))
    (hg : AnalyticOnNhd ℂ g (balancedHull ℂ U)) (he : EqOn f g U) :
    EqOn f g (balancedHull ℂ U) :=
  DifferentiableOn.eqOn_of_preconnected_of_eqOn (ho.balancedHull hzero)
    (isPathConnected_balancedHull ⟨0, hzero⟩).isConnected.isPreconnected
    hf.differentiableOn hg.differentiableOn ho ⟨0, hzero⟩ (subset_balancedHull ℂ) he

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
