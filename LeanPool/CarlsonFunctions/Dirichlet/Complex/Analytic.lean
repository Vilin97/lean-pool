/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Complex
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Basic
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Analytic dependence of convergent Dirichlet integrals

This module proves parameter analyticity on the domain of absolute convergence.
Continuation beyond that domain is developed separately in `Dirichlet.Transform`.
-/

open Complex Fintype Filter MeasureTheory MeasureTheory.Measure
open scoped Topology

@[expose] public noncomputable section

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- The product of reciprocal Gamma factors used to regularize a Dirichlet integral is entire
in the parameter vector. -/
theorem analyticOnNhd_prod_invGamma :
    AnalyticOnNhd ℂ (fun b : ι → ℂ ↦ ∏ i, (Gamma (b i))⁻¹) Set.univ := by
  apply DifferentiableOn.analyticOnNhd_piCarlson _ isOpen_univ
  intro b _
  apply DifferentiableAt.differentiableWithinAt
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      have hi := Complex.differentiable_one_div_Gamma.differentiableAt.comp b
        (ContinuousLinearMap.proj i).differentiableAt
      change DifferentiableAt ℂ (fun b : ι → ℂ ↦ (Gamma (b i))⁻¹) b at hi
      rw [show (fun b : ι → ℂ ↦ ∏ j ∈ insert i s, (Gamma (b j))⁻¹) =
          (fun b ↦ (Gamma (b i))⁻¹) * (fun b ↦ ∏ j ∈ s, (Gamma (b j))⁻¹) by
        funext x
        exact Finset.prod_insert his]
      exact hi.mul ih

/-- The Dirichlet monomial `∏ i, (u i) ^ (b i - 1)` is entire in the parameter vector at
every interior simplex point. -/
theorem hasFDerivAt_mvBetaMonomial {u : ι → ℝ} (hu : ∀ i, 0 < u i) (b : ι → ℂ) :
    HasFDerivAt (fun c : ι → ℂ ↦ ∏ i, (u i : ℂ) ^ (c i - 1))
      (∑ i, ((Complex.log (u i : ℂ) * ∏ j, (u j : ℂ) ^ (b j - 1)) •
        (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ))) b := by
  classical
  let p : ι → ((ι → ℂ) →L[ℂ] ℂ) :=
    fun i ↦ (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)
  let g : ι → (ι → ℂ) → ℂ := fun i c ↦ (u i : ℂ) ^ (c i - 1)
  let g' : ι → (ι → ℂ) →L[ℂ] ℂ := fun i ↦
    ((u i : ℂ) ^ (b i - 1) * Complex.log (u i : ℂ)) • p i
  have hg i : HasFDerivAt (g i) (g' i) b := by
    have hproj : HasFDerivAt (fun c : ι → ℂ ↦ c i) (p i) b := (p i).hasFDerivAt
    have hsub : HasFDerivAt (fun c : ι → ℂ ↦ c i - 1) (p i) b := hproj.sub_const 1
    have h0 : (u i : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hu i).ne'
    simpa [g, g', mul_comm] using hsub.const_cpow (Or.inl h0)
  have hprod :=
    HasFDerivAt.finsetProd (u := (Finset.univ : Finset ι)) (fun i _ ↦ hg i)
  refine hprod.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp only [g, g', p, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hprod_erase :
      (∏ j, (u j : ℂ) ^ (b j - 1)) =
        (u i : ℂ) ^ (b i - 1) *
          ∏ j ∈ Finset.univ.erase i, (u j : ℂ) ^ (b j - 1) :=
    (Finset.mul_prod_erase Finset.univ (fun j ↦ (u j : ℂ) ^ (b j - 1))
      (Finset.mem_univ i)).symm
  rw [hprod_erase]
  ring

/-- If `f` is continuous on the closed standard simplex, then
`b ↦ regDirichletIntegral b f` is analytic on the domain of absolute convergence. -/
theorem regDirichletIntegral_analyticOn {f : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    AnalyticOn ℂ (fun b ↦ regDirichletIntegral b f) mvBetaConvergent := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      have hconst : (fun b : ι → ℂ ↦ regDirichletIntegral b f) = fun _ ↦ 0 := by
        funext b
        simp [regDirichletIntegral, stdSimplexMeasure_empty]
      rw [hconst]
      exact analyticOn_const
  | inr hι =>
    let _ := hι
    have hH : AnalyticOnNhd ℂ (fun b : ι → ℂ ↦ ∏ i, (Gamma (b i))⁻¹) Set.univ :=
      analyticOnNhd_prod_invGamma
    let μ := stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)
    let G : (ι → ℂ) → ℂ := fun b ↦
      ∫ u, (∏ i, (u i : ℂ) ^ (b i - 1)) * f u ∂μ
    have hG : AnalyticOnNhd ℂ G mvBetaConvergent := by
      refine analyticOnNhd_integral_of_dominated_of_fderiv_leCarlson
        (μ := μ) (U := mvBetaConvergent) (F := fun b u ↦
          (∏ i, (u i : ℂ) ^ (b i - 1)) * f u)
        Complex.isOpen_mvBetaConvergent ?_
      intro b hb
      let α : ι → ℝ := fun i ↦ (b i).re / 2
      have hα i : 0 < α i := half_pos (hb i)
      let s : Set (ι → ℂ) := {c | ∀ i, α i < (c i).re}
      have hsopen : IsOpen s := by
        rw [show s = ⋂ i, {c : ι → ℂ | α i < (c i).re} by ext c; simp [s]]
        exact isOpen_iInter_of_finite fun i ↦
          isOpen_lt continuous_const
            (Complex.continuous_re.comp (continuous_apply i))
      have hsb : b ∈ s := fun i ↦ half_lt_self (hb i)
      have hs_nhds : s ∈ 𝓝 b := hsopen.mem_nhds hsb
      let a : ι → ℂ := fun i ↦ (α i : ℂ)
      have ha : a ∈ mvBetaConvergent := fun i ↦ by simpa [a] using hα i
      obtain ⟨Cf, hCf⟩ := bddAbove_def.mp
        ((Convexity.StdSimplex.isCompact_coordinateSet ℝ ι).bddAbove_image hf.norm)
      let C : ℝ := max Cf 0
      have hC0 : 0 ≤ C := le_max_right _ _
      have hf_le : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι, ‖f u‖ ≤ C := fun u hu ↦
        (hCf _ ⟨u, hu, rfl⟩).trans (le_max_left _ _)
      let bound : (ι → ℝ) → ℝ := fun u ↦
        C * ∑ i, ‖(∏ j, (u j : ℂ) ^ (a j - 1)) * Complex.log (u i : ℂ)‖
      let p : ι → ((ι → ℂ) →L[ℂ] ℂ) :=
        fun i ↦ (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)
      let F' : (ι → ℂ) → (ι → ℝ) → (ι → ℂ) →L[ℂ] ℂ := fun c u ↦
        ∑ i, ((Complex.log (u i : ℂ) * (∏ j, (u j : ℂ) ^ (c j - 1)) * f u) • p i)
      refine ⟨s, bound, F', hs_nhds, ?meas, ?int, ?F'meas, ?bd, ?bdint, ?diff⟩
      · filter_upwards [hs_nhds] with c hc
        have hc' : c ∈ mvBetaConvergent := fun i ↦ (hα i).trans (hc i)
        exact ((integrableOn_mvBetaMonomial c hc').mul_continuousOn hf
          (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)).1
      · change IntegrableOn (fun u ↦ (∏ i, (u i : ℂ) ^ (b i - 1)) * f u)
            (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure
        exact (integrableOn_mvBetaMonomial b hb).mul_continuousOn hf
          (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
      · apply Finset.aestronglyMeasurable_fun_sum
        intro i _
        have hmono := (integrableOn_mvBetaMonomial_mul_log b hb i).aestronglyMeasurable
        have hfmeas :=
          hf.aestronglyMeasurable (μ := stdSimplexMeasure)
            (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
        have hscal : AEStronglyMeasurable
            (fun u ↦ Complex.log (u i : ℂ) * (∏ j, (u j : ℂ) ^ (b j - 1)) * f u) μ :=
          (hmono.mul hfmeas).congr <| Eventually.of_forall fun u ↦ by
            simp [mul_comm]
        exact hscal.smul_const _
      · filter_upwards [self_mem_ae_restrict (Convexity.StdSimplex.isClosed_coordinateSet ℝ
        ι).measurableSet,
            ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hupos
        intro c hc
        have hui i : 0 < u i := hupos i
        have hui1 i : u i ≤ 1 :=
          (hu.2.symm ▸ Finset.single_le_sum (fun j _ ↦ hu.1 j) (Finset.mem_univ i))
        have hmon : ‖∏ j, (u j : ℂ) ^ (c j - 1)‖ ≤
            ‖∏ j, (u j : ℂ) ^ (a j - 1)‖ := by
          simp only [norm_prod]
          refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun j _ ↦ ?_
          have hjpos : 0 < u j := hui j
          rw [norm_cpow_eq_rpow_re_of_pos hjpos, norm_cpow_eq_rpow_re_of_pos hjpos]
          simp only [sub_re, one_re]
          exact Real.rpow_le_rpow_of_exponent_ge hjpos (hui1 j)
            (sub_le_sub_right (le_of_lt (hc j)) 1)
        have hproj (i : ι) : ‖p i‖ ≤ 1 :=
          (p i).opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1) fun v ↦ by
            simpa [p] using (norm_le_pi_norm v i)
        have hsum : ‖F' c u‖ ≤
            ∑ i, ‖Complex.log (u i : ℂ)‖ *
              ‖∏ j, (u j : ℂ) ^ (c j - 1)‖ * ‖f u‖ := by
          refine (norm_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [norm_smul, norm_mul, norm_mul]
          refine mul_le_mul_of_nonneg_left (hproj i) (by positivity) |>.trans_eq ?_
          ring
        refine hsum.trans ?_
        calc
          ∑ i, ‖Complex.log (u i : ℂ)‖ *
              ‖∏ j, (u j : ℂ) ^ (c j - 1)‖ * ‖f u‖ ≤
            ∑ i, ‖Complex.log (u i : ℂ)‖ *
              ‖∏ j, (u j : ℂ) ^ (a j - 1)‖ * C := by
            gcongr <;> first | exact hmon | exact hf_le u hu
          _ = C * ∑ i, ‖(∏ j, (u j : ℂ) ^ (a j - 1)) * Complex.log (u i : ℂ)‖ := by
            simp [mul_comm, mul_left_comm, Finset.mul_sum]
          _ = bound u := rfl
      · have hterm i := (integrableOn_mvBetaMonomial_mul_log a ha i).norm
        have hsum := integrable_finsetSum (s := Finset.univ) fun i _ ↦ hterm i
        simpa [bound] using hsum.const_mul C
      · filter_upwards [self_mem_ae_restrict (Convexity.StdSimplex.isClosed_coordinateSet ℝ
        ι).measurableSet,
            ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hupos
        intro c hc
        have hmon := hasFDerivAt_mvBetaMonomial hupos c
        have hfconst : HasFDerivAt (fun _ : ι → ℂ ↦ f u)
            (0 : (ι → ℂ) →L[ℂ] ℂ) c := hasFDerivAt_const (f u) c
        have hmul := hmon.mul hfconst
        have hF'eq :
            f u • ∑ i, (Complex.log (u i : ℂ) *
                ∏ j, (u j : ℂ) ^ (c j - 1)) • p i =
              F' c u := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [smul_smul]
          simp [p, mul_comm]
        refine hmul.congr_fderiv ?_
        have hz : ((∏ i, (u i : ℂ) ^ (c i - 1)) • (0 : (ι → ℂ) →L[ℂ] ℂ)) = 0 := by
          ext v; simp
        rw [hz, zero_add]
        simpa [p] using hF'eq
    have hEq : (fun b ↦ regDirichletIntegral b f) =
        fun b ↦ (∏ i, (Gamma (b i))⁻¹) * G b := by
      funext b
      exact regDirichletIntegral_eq_prod_invGamma_mul b f
    rw [hEq]
    exact ((hH.mono (Set.subset_univ _)).mul hG).analyticOn

end ProbabilityTheory

end
