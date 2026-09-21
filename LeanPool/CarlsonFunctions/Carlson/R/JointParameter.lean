/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.Exponent
public import LeanPool.CarlsonFunctions.Carlson.R.Relations
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.LocallyBounded

/-!
# Joint dependence on the exponent and Dirichlet parameters

The exponent occupies the `none` coordinate, and the Dirichlet parameters the `some`
coordinates. Native joint analyticity follows from separate analyticity and a local
integrable majorant. Parameter-raising relations transport it to the entire continuation.
-/

open Complex ProbabilityTheory MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform

open CarlsonFunctions.SeveralComplexVariables
variable {ι : Type*} [Fintype ι]

private theorem locallyBounded_regCarlsonRIntegral_exponent_parameters
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (p : Option ι → ℂ)
    (hp : (fun i => p (some i)) ∈ mvBetaConvergent) :
    ∃ M : ℝ, ∀ᶠ q in 𝓝 p,
      ‖regCarlsonRIntegral (q none) (fun i => q (some i)) z‖ ≤ M := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    let _ := hι
    exact ⟨0, Eventually.of_forall (fun q => by
      simp [regCarlsonRIntegral, regCarlsonDirichletAverage, regDirichletIntegral,
        stdSimplexMeasure_empty])⟩
  | inr hι =>
    let _ := hι
    let K := Convexity.StdSimplex.coordinateSet ℝ ι
    let μ := stdSimplexMeasure.restrict K
    have hpow : ContinuousOn (fun v : ℂ × (ι → ℝ) => carlsonAffineForm z v.2 ^ v.1)
        (Metric.closedBall (p none) 1 ×ˢ K) :=
      ((continuous_carlsonAffineForm z).comp continuous_snd).continuousOn.cpow
        continuous_fst.continuousOn (fun v hv => carlsonAffineForm_mem_slitPlane hz hv.2)
    obtain ⟨C, hC⟩ := ((isCompact_closedBall (p none) 1).prod
      (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)).bddAbove_image hpow.norm
    let a : ι → ℂ := fun i => ((p (some i)).re / 2 : ℝ)
    have ha : a ∈ mvBetaConvergent := fun i => by simpa [a] using half_pos (hp i)
    have hevent : ∀ᶠ q in 𝓝 p,
        (∀ i, (a i).re < (q (some i)).re) ∧ dist (q none) (p none) < 1 := by
      apply Eventually.and
      · apply eventually_all.mpr
        intro i
        apply (isOpen_lt continuous_const
          (Complex.continuous_re.comp (continuous_apply (some i)))).eventually_mem
        simpa [a] using half_lt_self (hp i)
      · have hcoord : Continuous (fun q : Option ι → ℂ => q none) := continuous_apply none
        have hdist : ContinuousAt (fun q : Option ι → ℂ => dist (q none) (p none)) p :=
          (hcoord.dist continuous_const).continuousAt
        exact hdist.eventually_lt_const (by simp)
    let F := fun (q : Option ι → ℂ) (u : ι → ℝ) =>
      (∏ i, (u i : ℂ) ^ (q (some i) - 1)) * carlsonAffineForm z u ^ q none
    let D : ℝ := ∫ u, ‖∏ i, (u i : ℂ) ^ (a i - 1)‖ * max C 0 ∂μ
    have hD : ∀ᶠ q in 𝓝 p, ‖∫ u, F q u ∂μ‖ ≤ D := by
      filter_upwards [hevent] with q hq
      apply norm_integral_le_of_norm_le ((integrableOn_mvBetaMonomial a ha).norm.mul_const _)
      filter_upwards [self_mem_ae_restrict (μ := stdSimplexMeasure)
        (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet,
          ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hupos
      have hm : ‖∏ i, (u i : ℂ) ^ (q (some i) - 1)‖ ≤ ‖∏ i, (u i : ℂ) ^ (a i - 1)‖ := by
        simp only [norm_prod]
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i _
        rw [norm_cpow_eq_rpow_re_of_pos (hupos i), norm_cpow_eq_rpow_re_of_pos (hupos i)]
        apply Real.rpow_le_rpow_of_exponent_ge (hupos i)
          ((Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)).trans_eq hu.2)
        simpa only [sub_re, one_re] using sub_le_sub_right (hq.1 i).le 1
      have hf : ‖carlsonAffineForm z u ^ q none‖ ≤ max C 0 :=
        (hC (mem_image_of_mem _ (show (q none, u) ∈
          Metric.closedBall (p none) 1 ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι from
            ⟨Metric.mem_closedBall.mpr hq.2.le, hu⟩))).trans (le_max_left _ _)
      exact (norm_mul _ _).trans_le (mul_le_mul hm hf (norm_nonneg _) (norm_nonneg _))
    let B : ℝ := ‖∏ i, (Gamma (p (some i)))⁻¹‖ + 1
    have hproj : ContinuousAt (fun q : Option ι → ℂ => fun i => q (some i)) p :=
      continuousAt_pi.mpr fun i => (continuous_apply (some i)).continuousAt
    have hB := ((analyticOnNhd_prod_invGamma _ (mem_univ _)).continuousAt.comp
      hproj).norm.eventually_lt_const
      (lt_add_one ‖∏ i, (Gamma (p (some i)))⁻¹‖)
    refine ⟨B * max D 0, ?_⟩
    filter_upwards [hB, hD] with q hq hqD
    rw [regCarlsonRIntegral, regCarlsonDirichletAverage,
      regDirichletIntegral_eq_prod_invGamma_mul, norm_mul]
    exact mul_le_mul hq.le (hqD.trans (le_max_left _ _)) (norm_nonneg _) (by dsimp [B]; positivity)

open scoped Classical in
/-- Joint analyticity of the native regularized integral in its exponent and parameters. -/
theorem analyticOnNhd_regCarlsonRIntegral_exponent_parameters {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (fun p : Option ι → ℂ =>
      regCarlsonRIntegral (p none) (fun i => p (some i)) z)
      {p | (fun i => p (some i)) ∈ mvBetaConvergent} := by
  apply analyticOnNhd_of_separately_analytic_locally_bounded
    (isOpen_mvBetaConvergent.preimage (by fun_prop))
  · intro p hp k
    cases k with
    | none =>
      have H := analyticOnNhd_regCarlsonRIntegral_exponent hp hz (p none) (mem_univ _)
      simpa only [Function.update_self, Function.update_of_ne (Option.some_ne_none _)] using H
    | some i =>
      have hcont : ContinuousOn (fun u => carlsonAffineForm z u ^ p none)
        (Convexity.StdSimplex.coordinateSet ℝ ι) :=
        (continuous_carlsonAffineForm z).continuousOn.cpow_const
          (fun _ hu => carlsonAffineForm_mem_slitPlane hz hu)
      have H := (isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp
        (regDirichletIntegral_analyticOn hcont)).analyticAt_updateCarlson hp i
      change AnalyticAt ℂ (fun w => regCarlsonRIntegral (p none)
        (Function.update (fun j => p (some j)) i w) z) (p (some i)) at H
      have hup (v : ι → ℂ) (w : ℂ) : Function.update v i w = fun j => if j = i then w else v j := by
        ext j
        simp only [Function.update_apply]
      simpa only [hup, Function.update_apply, Option.some.injEq, reduceCtorEq, ite_false] using! H
  · exact fun p hp => locallyBounded_regCarlsonRIntegral_exponent_parameters hz p hp

private theorem analyticAt_regCarlsonRContinued_comp_of_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {b : E → ι → ℂ} {p : E} {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) (hf : AnalyticAt ℂ f p) (hb : AnalyticAt ℂ b p)
    (hpos : b p ∈ mvBetaConvergent) :
    AnalyticAt ℂ (fun w => regCarlsonRContinued (f w) z hz (b w)) p := by
  let g : E → Option ι → ℂ := fun w i => i.elim (f w) (b w)
  have hg : AnalyticAt ℂ g p := by
    apply analyticAt_pi_iff.mpr
    intro i
    cases i with
    | none => exact hf
    | some i => exact (analyticAt_pi_iff.mp hb) i
  have H := (analyticOnNhd_regCarlsonRIntegral_exponent_parameters hz (g p) hpos).comp hg
  have hevent := hb.continuousAt.tendsto.eventually (isOpen_mvBetaConvergent.mem_nhds hpos)
  apply H.congr
  filter_upwards [hevent] with w hw
  exact (regCarlsonRContinued_eq_integral (f w) hz hw).symm

open scoped Classical in
/-- The continued R-function remains analytic when the exponent and all parameters vary
analytically together. Parameter raising removes every native convergence restriction. -/
theorem analyticAt_regCarlsonRContinued_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {b : E → ι → ℂ} {p : E} {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) (hf : AnalyticAt ℂ f p) (hb : AnalyticAt ℂ b p) :
    AnalyticAt ℂ (fun w => regCarlsonRContinued (f w) z hz (b w)) p := by
  have lower (n : ι → ℕ) : ∀ (f : E → ℂ) (b : E → ι → ℂ),
      AnalyticAt ℂ f p → AnalyticAt ℂ b p →
      (fun i => b p i + n i) ∈ mvBetaConvergent →
      AnalyticAt ℂ (fun w => regCarlsonRContinued (f w) z hz (b w)) p := by
    induction n using (measure (fun n : ι → ℕ => ∑ i, n i)).wf.induction with
    | h n ih =>
      intro f b hf hb hpos
      by_cases hn : n = 0
      · exact analyticAt_regCarlsonRContinued_comp_of_pos hz hf hb (by simpa [hn] using hpos)
      obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
        simpa only [funext_iff, Pi.zero_apply, not_forall] using hn
      let n' := Function.update n i (n i - 1)
      have hlt : (∑ j, n' j) < ∑ j, n j := by
        apply Finset.sum_lt_sum
        · intro j _
          by_cases hji : j = i <;> simp [n', hji]
        · exact ⟨i, Finset.mem_univ _, by simp [n']; omega⟩
      let b' : E → ι → ℂ := fun w => addDirichletUnit (b w) i
      have hb' : AnalyticAt ℂ b' p := by
        apply analyticAt_pi_iff.mpr
        intro j
        by_cases hji : j = i
        · subst j
          simp only [addDirichletUnit, Function.update_self]
          exact ((analyticAt_pi_iff.mp hb) i).add analyticAt_const
        · simpa only [b', addDirichletUnit, Function.update_of_ne hji] using (analyticAt_pi_iff.mp
          hb) j
      have hpos' : (fun j => b' p j + n' j) ∈ mvBetaConvergent := by
        have heq : (fun j => b' p j + (n' j : ℂ)) = (fun j => b p j + (n j : ℂ)) := by
          ext j
          by_cases hji : j = i
          · subst j
            simp only [b', addDirichletUnit, n', Function.update_self]
            rw [Nat.cast_sub (by omega : 1 ≤ n i)]
            push_cast
            ring
          · simp [b', addDirichletUnit, n', hji]
        rwa [heq]
      have h₀ := ih n' hlt f b' hf hb' hpos'
      have h₁ := ih n' hlt (fun w => f w - 1) b' (hf.sub analyticAt_const) hb' hpos'
      have hsum : AnalyticAt ℂ (fun w => ∑ j, b w j) p :=
        Finset.analyticAt_fun_sum _ (fun j _ => (analyticAt_pi_iff.mp hb) j)
      have heq : (fun w => regCarlsonRContinued (f w) z hz (b w)) =
          (fun w => ((∑ j, b w j) + f w) * regCarlsonRContinued (f w) z hz (b' w) -
            f w * z i * regCarlsonRContinued (f w - 1) z hz (b' w)) :=
        funext fun w => regCarlsonRContinued_eq_addDirichletUnit (f w) (b w) hz i
      rw [heq]
      exact ((hsum.add hf).mul h₀).sub ((hf.mul analyticAt_const).mul h₁)
  choose n hn using fun i => exists_nat_gt (-(b p i).re)
  apply lower n f b hf hb
  intro i
  change 0 < (b p i + (n i : ℂ)).re
  simp only [add_re, natCast_re]
  linarith [hn i]

/-- Joint entireness of the regularized continuation in the exponent and all parameters. -/
theorem analyticOnNhd_regCarlsonRContinued_exponent_parameters {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    AnalyticOnNhd ℂ (fun p : Option ι → ℂ =>
      regCarlsonRContinued (p none) z hz (fun i => p (some i))) Set.univ := by
  intro p _
  apply analyticAt_regCarlsonRContinued_comp hz
  · exact (ContinuousLinearMap.proj none : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt p
  · exact analyticAt_pi_iff.mpr fun i =>
      (ContinuousLinearMap.proj (some i) : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt p

end DirichletTransform
end
