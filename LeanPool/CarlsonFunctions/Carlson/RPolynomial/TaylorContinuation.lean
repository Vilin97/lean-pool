/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.PowerSeries
public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.SharpEstimates
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Continuation
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.LocallyUniform
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Carlson's continued Taylor representation

The R-polynomial expansion gives the entire regularized continuation in the
Dirichlet parameters on the full scalar Taylor disk (Carlson, Theorem 6.3-1).
The sharp estimate from Section 6.2 supplies locally uniform convergence.
-/

open Complex Set
open scoped Topology NNReal ENNReal
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

private lemma affine_sub_center (A : ℂ) (z : ι → ℂ) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    carlsonAffineForm z u - A = carlsonAffineForm (fun i => z i - A) u := by
  simpa [sub_eq_add_neg] using (carlsonAffineForm_affine (z := z) hu (a := 1) (t := -A)).symm

/-- A geometric coefficient bound yields a continued Taylor average. This internal
criterion is discharged automatically by `isRegCarlsonContinuation_taylor`. -/
theorem isRegCarlsonContinuation_taylor_of_geometric_bound
    (A : ℂ) (a : ℕ → ℂ) (z : ι → ℂ) (f : ℂ → ℂ)
    {C q : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hqr : q * ‖fun i => z i - A‖ < 1) (ha : ∀ n, ‖a n‖ ≤ C * q ^ n)
    (hsum : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      HasSum (fun n => a n * (carlsonAffineForm z u - A) ^ n) (f (carlsonAffineForm z u))) :
    IsRegCarlsonContinuation f z (regCarlsonTaylorSeries A a z) := by
  have hmajor (K : Set (ι → ℂ)) (hK : IsCompact K) :=
    exists_summable_norm_carlsonTaylor_bounded_variables hK hC hq
      (norm_nonneg (fun i => z i - A)) hqr ha
  refine ⟨?_, ?_⟩
  · apply analyticOnNhd_tsum_of_summable_norm_on_compactsCarlson isOpen_univ
    · intro n
      exact analyticOnNhd_const.mul (analyticOnNhd_regCarlsonR n _)
    · intro K _ hK
      obtain ⟨M, hM, hbound⟩ := hmajor K hK
      exact ⟨M, hM, fun n b hb => hbound n b hb _ (norm_le_pi_norm _)⟩
  · intro b hb
    apply HasSum.tsum_eq
    apply hasSum_regCarlsonR_of_powerSeries hb A a z f
      (fun n => C * (q * ‖fun i => z i - A‖) ^ n)
      ((summable_geometric_of_lt_one (mul_nonneg hq (norm_nonneg _)) hqr).mul_left C)
    · intro n u hu
      rw [norm_mul, norm_pow, affine_sub_center A z hu]
      calc
        _ ≤ (C * q ^ n) * ‖fun i => z i - A‖ ^ n :=
          mul_le_mul (ha n)
            (pow_le_pow_left₀ (norm_nonneg _) (norm_carlsonAffineForm_le_pi_norm _ hu) n)
            (by positivity) (by positivity)
        _ = _ := by rw [mul_pow]; ring
    · exact hsum

/-- Scalar power-series data suffice for Carlson's continuation on the full disk;
no separate domination hypothesis is needed. -/
theorem isRegCarlsonContinuation_of_hasFPowerSeriesOnBall
    {A : ℂ} {a : ℕ → ℂ} {f : ℂ → ℂ} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) A R)
    {z : ι → ℂ} (hz : ‖fun i => z i - A‖ < R) :
    IsRegCarlsonContinuation f z (regCarlsonTaylorSeries A a z) := by
  obtain ⟨ρ, hρz, hρR⟩ := exists_between hz
  have hρ : 0 < ρ := (norm_nonneg _).trans_lt hρz
  let ρ' : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hρrad : (ρ' : ℝ≥0∞) < (FormalMultilinearSeries.ofScalars ℂ a).radius :=
    (show (ρ' : ℝ≥0∞) < R by exact_mod_cast hρR).trans_le hf.r_le
  obtain ⟨C, hC, hbound⟩ := FormalMultilinearSeries.norm_le_div_pow_of_pos_of_lt_radius
    (FormalMultilinearSeries.ofScalars ℂ a) (show 0 < ρ' from hρ) hρrad
  have ha (n : ℕ) : ‖a n‖ ≤ C * (ρ⁻¹) ^ n := by
    have hn := hbound n
    rw [FormalMultilinearSeries.ofScalars_norm] at hn
    change ‖a n‖ ≤ C / ρ ^ n at hn
    simpa only [div_eq_mul_inv, inv_pow] using hn
  refine isRegCarlsonContinuation_taylor_of_geometric_bound A a z f hC.le
    (inv_nonneg.mpr hρ.le) ?_ ha ?_
  · simpa [div_eq_mul_inv, mul_comm] using (div_lt_one hρ).mpr hρz
  · intro u hu
    have hnorm : ‖carlsonAffineForm z u - A‖ < R := by
      rw [affine_sub_center A z hu]
      exact (norm_carlsonAffineForm_le_pi_norm _ hu).trans_lt hz
    have hm : carlsonAffineForm z u - A ∈ Metric.eball (0 : ℂ) R := by
      rw [Metric.eball_coe]
      simpa using hnorm
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
      add_sub_cancel] using hf.hasSum hm

/-- Carlson's Theorem 6.3-1, entire in the parameters on the full holomorphy disk.
The coefficients are the usual scalar Taylor coefficients `f⁽ⁿ⁾(A) / n!`. -/
theorem isRegCarlsonContinuation_taylor {A : ℂ} {R : ℝ}
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball A R))
    {z : ι → ℂ} (hz : ‖fun i => z i - A‖ < R) :
    IsRegCarlsonContinuation f z
      (regCarlsonTaylorSeries A (fun n => iteratedDeriv n f A / n.factorial) z) := by
  obtain ⟨r, hzr, hrR⟩ := exists_between hz
  have hr : 0 < r := (norm_nonneg _).trans_lt hzr
  let r' : ℝ≥0 := ⟨r, hr.le⟩
  have hfull := DifferentiableOn.hasFPowerSeriesOnBall (R := r')
    (hf.differentiableOn.mono (Metric.closedBall_subset_ball hrR)) (show 0 < r' from hr)
  have hlocal := (hf A (by simp only [Metric.mem_ball, dist_self]; exact (norm_nonneg _).trans_lt hz)).hasFPowerSeriesAt
  have heq := hfull.hasFPowerSeriesAt.eq_formalMultilinearSeries hlocal
  rw [heq] at hfull
  exact isRegCarlsonContinuation_of_hasFPowerSeriesOnBall hfull hzr

/-- Every entire continuation agrees with the Taylor construction wherever the
nodes lie in a disk of holomorphy of the scalar function. -/
theorem IsRegCarlsonContinuation.eq_taylor {A : ℂ} {R : ℝ}
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball A R))
    {z : ι → ℂ} (hz : ‖fun i => z i - A‖ < R)
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f z G) :
    G = regCarlsonTaylorSeries A (fun n => iteratedDeriv n f A / n.factorial) z :=
  hG.eq (isRegCarlsonContinuation_taylor hf hz)

private lemma exists_taylor_geometric_bound {A : ℂ} {R r : ℝ}
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball A R))
    (hr : 0 ≤ r) (hrR : r < R) :
    ∃ C q : ℝ, 0 ≤ C ∧ 0 ≤ q ∧ q * r < 1 ∧
      ∀ n, ‖iteratedDeriv n f A / n.factorial‖ ≤ C * q ^ n := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  have hs : 0 < s := hr.trans_lt hrs
  let s' : ℝ≥0 := ⟨s, hs.le⟩
  have hfull := DifferentiableOn.hasFPowerSeriesOnBall (R := s')
    (hf.differentiableOn.mono (Metric.closedBall_subset_ball hsR)) (show 0 < s' from hs)
  have hlocal := (hf A (by simp only [Metric.mem_ball, dist_self]; exact hr.trans_lt hrR)).hasFPowerSeriesAt
  rw [hfull.hasFPowerSeriesAt.eq_formalMultilinearSeries hlocal] at hfull
  obtain ⟨ρ, hrρ, hρs⟩ := exists_between hrs
  have hρ : 0 < ρ := hr.trans_lt hrρ
  let ρ' : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hρrad : (ρ' : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ (fun n => iteratedDeriv n f A / n.factorial)).radius :=
    (show (ρ' : ℝ≥0∞) < s' by exact_mod_cast hρs).trans_le hfull.r_le
  obtain ⟨C, hC, hbound⟩ := FormalMultilinearSeries.norm_le_div_pow_of_pos_of_lt_radius
    (FormalMultilinearSeries.ofScalars ℂ (fun n => iteratedDeriv n f A / n.factorial))
    (show 0 < ρ' from hρ) hρrad
  refine ⟨C, ρ⁻¹, hC.le, inv_nonneg.mpr hρ.le, ?_, ?_⟩
  · simpa [div_eq_mul_inv, mul_comm] using (div_lt_one hρ).mpr hrρ
  · intro n
    have hn := hbound n
    rw [FormalMultilinearSeries.ofScalars_norm] at hn
    change ‖iteratedDeriv n f A / n.factorial‖ ≤ C / ρ ^ n at hn
    simpa only [div_eq_mul_inv, inv_pow] using hn

/-- Absolute convergence of the continued Taylor expansion at every complex
parameter vector and throughout the full node disk. -/
theorem summable_norm_regCarlsonTaylorSeries {A : ℂ} {R : ℝ}
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball A R))
    {z : ι → ℂ} (hz : ‖fun i => z i - A‖ < R) (b : ι → ℂ) :
    Summable (fun n => ‖(iteratedDeriv n f A / n.factorial) *
      regCarlsonR n (fun i => z i - A) b‖) := by
  obtain ⟨C, q, hC, hq, hqr, ha⟩ := exists_taylor_geometric_bound hf (norm_nonneg _) hz
  obtain ⟨M, hM, hbound⟩ := exists_summable_norm_carlsonTaylor_bounded_variables
    (isCompact_singleton (x := b)) hC hq (norm_nonneg _) hqr ha
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => hbound n b (mem_singleton b) _ (norm_le_pi_norm _)) hM

/-- The convergent R-polynomial Taylor series represents every continued average,
including at exceptional total parameters. -/
theorem IsRegCarlsonContinuation.hasSum_taylor {A : ℂ} {R : ℝ}
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball A R))
    {z : ι → ℂ} (hz : ‖fun i => z i - A‖ < R)
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f z G) (b : ι → ℂ) :
    HasSum (fun n => (iteratedDeriv n f A / n.factorial) *
      regCarlsonR n (fun i => z i - A) b) (G b) := by
  rw [hG.eq_taylor hf hz]
  exact (summable_norm_regCarlsonTaylorSeries hf hz b).of_norm.hasSum

/-- The Taylor series converges locally uniformly jointly in parameters and nodes
on the full scalar holomorphy disk. The two coordinate blocks are encoded by `Sum`. -/
theorem hasSumLocallyUniformlyOn_regCarlsonTaylorSeries_joint {A : ℂ} {R : ℝ}
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball A R)) :
    HasSumLocallyUniformlyOn
      (fun (n : ℕ) (p : Sum ι ι → ℂ) => (iteratedDeriv n f A / n.factorial) *
        regCarlsonR n (fun i => p (.inr i) - A) (fun i => p (.inl i)))
      (fun p => regCarlsonTaylorSeries A (fun n => iteratedDeriv n f A / n.factorial)
        (fun i => p (.inr i)) (fun i => p (.inl i)))
      {p : Sum ι ι → ℂ | ‖fun i => p (.inr i) - A‖ < R} := by
  have hnorm : Continuous (fun p : Sum ι ι → ℂ => ‖fun i => p (.inr i) - A‖) := by fun_prop
  have hs : SummableLocallyUniformlyOn
      (fun (n : ℕ) (p : Sum ι ι → ℂ) => (iteratedDeriv n f A / n.factorial) *
        regCarlsonR n (fun i => p (.inr i) - A) (fun i => p (.inl i)))
      {p : Sum ι ι → ℂ | ‖fun i => p (.inr i) - A‖ < R} := by
    apply SummableLocallyUniformlyOn_of_locally_bounded (isOpen_lt hnorm continuous_const)
    intro K hKU hK
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, summable_zero, by simp⟩
    obtain ⟨p₀, hp₀, hmax⟩ := hK.exists_isMaxOn hne hnorm.continuousOn
    obtain ⟨C, q, hC, hq, hqr, ha⟩ :=
      exists_taylor_geometric_bound hf (norm_nonneg _) (hKU hp₀)
    have hp : Continuous (fun p : Sum ι ι → ℂ => fun i => p (.inl i)) := by fun_prop
    obtain ⟨M, hM, hbound⟩ := exists_summable_norm_carlsonTaylor_bounded_variables
      (hK.image hp) hC hq (norm_nonneg _) hqr ha
    refine ⟨M, hM, fun n p hpk => hbound n _ (mem_image_of_mem _ hpk) _ (fun i => ?_)⟩
    exact (norm_le_pi_norm (fun j => p (.inr j) - A) i).trans (hmax hpk)
  exact hs.hasSumLocallyUniformlyOn

/-- The joint holomorphy conclusion of Carlson's Theorem 6.3-1. There are no
Dirichlet-parameter exclusions, and the node domain is the full product of disks. -/
theorem analyticOnNhd_regCarlsonTaylorSeries_joint {A : ℂ} {R : ℝ}
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball A R)) :
    AnalyticOnNhd ℂ
      (fun p : Sum ι ι → ℂ => regCarlsonTaylorSeries A
        (fun n => iteratedDeriv n f A / n.factorial)
        (fun i => p (.inr i)) (fun i => p (.inl i)))
      {p : Sum ι ι → ℂ | ‖fun i => p (.inr i) - A‖ < R} := by
  apply (hasSumLocallyUniformlyOn_regCarlsonTaylorSeries_joint hf).analyticOnNhd_piCarlson
  · intro n p _
    exact analyticAt_const.mul (analyticAt_regCarlsonR_comp
      (b := fun p : Sum ι ι → ℂ => fun i => p (.inl i))
      (z := fun p : Sum ι ι → ℂ => fun i => p (.inr i) - A) (x := p)
      (fun i => (ContinuousLinearMap.proj (R := ℂ) (.inl i)).analyticAt p)
      (fun i => ((ContinuousLinearMap.proj (R := ℂ) (.inr i)).analyticAt p).sub analyticAt_const) n)
  · apply isOpen_lt _ continuous_const
    fun_prop

end DirichletTransform
end
