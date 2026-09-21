/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Associated.Deriv
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.LocallyBounded

/-! # Node and joint analyticity of native Dirichlet averages -/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- **Carlson 5.3-3, node-variable part.** On a convex domain of holomorphy, a regularized
Carlson average is analytic in all node variables throughout the corresponding product domain. -/
theorem analyticOnNhd_regCarlsonDirichletAverage_nodes
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    AnalyticOnNhd ℂ (fun z => regCarlsonDirichletAverage b z f)
      {z : ι → ℂ | Set.range z ⊆ Ω} := by
  classical
  let U : Set (ι → ℂ) := {z | Set.range z ⊆ Ω}
  have hU : IsOpen U := by
    rw [show U = Set.pi Set.univ (fun _ => Ω) by
      ext z
      simp [U, Set.range_subset_iff]]
    exact isOpen_set_pi Set.finite_univ fun _ _ => hΩopen
  let μ := (MeasureTheory.Measure.stdSimplexMeasure (ι := ι)).restrict (Convexity.StdSimplex.coordinateSet ℝ ι)
  let F : (ι → ℂ) → (ι → ℝ) → ℂ := fun z u =>
    regDirichletDensity b u * f (carlsonAffineForm z u)
  let L : (ι → ℝ) → ((ι → ℂ) →L[ℂ] ℂ) := carlsonAffineFormCLM
  refine analyticOnNhd_integral_of_dominated_of_fderiv_le
    (μ := μ) (U := U) (F := F) hU ?_
  intro z hz
  let K : Set ℂ := convexHull ℝ (Set.range z)
  have hKcompact : IsCompact K := (Set.finite_range z).isCompact_convexHull ℝ
  have hKΩ : K ⊆ Ω := convexHull_min hz hΩconv
  obtain ⟨δ, hδ, hδΩ, C, hCnonneg, hC⟩ :=
    hf.exists_cthickening_deriv_bound hΩopen hKcompact hKΩ
  have hderivCont : ContinuousOn (deriv f) Ω := hf.deriv.continuousOn
  let s : Set (ι → ℂ) := Metric.ball z δ
  have hs : s ∈ nhds z := Metric.ball_mem_nhds z hδ
  let bound : (ι → ℝ) → ℝ := fun u => C * ‖regDirichletDensity b u‖
  let F' : (ι → ℂ) → (ι → ℝ) → ((ι → ℂ) →L[ℂ] ℂ) := fun y u =>
    regDirichletDensity b u • ((deriv f (carlsonAffineForm y u)) • L u)
  have hdens : Integrable (fun u => regDirichletDensity b u) μ := by
    change IntegrableOn (fun u => regDirichletDensity b u)
      (Convexity.StdSimplex.coordinateSet ℝ ι) MeasureTheory.Measure.stdSimplexMeasure
    simpa only [mul_one] using integrableOn_regDirichletDensity_mul b hb
      (continuousOn_const : ContinuousOn (fun _ : ι → ℝ => (1 : ℂ)) (Convexity.StdSimplex.coordinateSet ℝ ι))
  refine ⟨s, bound, F', hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hs] with y hy
    have hyU : Set.range y ⊆ Ω := by
      intro q hq
      obtain ⟨i, rfl⟩ := hq
      have hiK : z i ∈ K := by
        apply subset_convexHull ℝ
        exact Set.mem_range_self i
      have hy' : dist y z < δ := by simpa [s, Metric.mem_ball, dist_comm] using hy
      apply hδΩ
      exact Metric.mem_cthickening_of_dist_le (y i) (z i) δ K hiK
        ((dist_le_pi_dist y z i).trans (le_of_lt hy'))
    have hcont : ContinuousOn (fun u => f (carlsonAffineForm y u)) (Convexity.StdSimplex.coordinateSet ℝ ι) :=
      hf.continuousOn.comp (continuous_carlsonAffineForm y).continuousOn fun u hu =>
        (convexHull_min hyU hΩconv) (carlsonAffineForm_mem_convexHull y hu)
    exact (integrableOn_regDirichletDensity_mul b hb hcont).aestronglyMeasurable
  · change IntegrableOn (fun u => regDirichletDensity b u * f (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι) MeasureTheory.Measure.stdSimplexMeasure
    exact integrableOn_regDirichletDensity_mul b hb
      (hf.continuousOn.comp (continuous_carlsonAffineForm z).continuousOn fun u hu =>
        hKΩ (carlsonAffineForm_mem_convexHull z hu))
  · have hcomp : ContinuousOn (fun u => deriv f (carlsonAffineForm z u))
        (Convexity.StdSimplex.coordinateSet ℝ ι) :=
      hderivCont.comp (continuous_carlsonAffineForm z).continuousOn fun u hu =>
        hKΩ (carlsonAffineForm_mem_convexHull z hu)
    have hL : Continuous (fun u : ι → ℝ => L u) := by
      dsimp only [L, carlsonAffineFormCLM]
      fun_prop
    have hcont : ContinuousOn (fun u =>
        (deriv f (carlsonAffineForm z u)) • L u) (Convexity.StdSimplex.coordinateSet ℝ ι) :=
      hcomp.smul hL.continuousOn
    exact hdens.aestronglyMeasurable.smul
      (hcont.aestronglyMeasurable (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet)
  · filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    intro y hy
    have hy' : dist y z < δ := by simpa [s, Metric.mem_ball, dist_comm] using hy
    have hbase : carlsonAffineForm z u ∈ K := carlsonAffineForm_mem_convexHull z hu
    have hnear : carlsonAffineForm y u ∈ Metric.cthickening δ K :=
      Metric.mem_cthickening_of_dist_le _ _ δ K hbase
        ((dist_carlsonAffineForm_le_norm_sub z y hu).trans (by
          simpa [dist_eq_norm] using le_of_lt hy'))
    dsimp only [F', bound]
    rw [norm_smul, norm_smul]
    calc
      ‖regDirichletDensity b u‖ *
          (‖deriv f (carlsonAffineForm y u)‖ * ‖L u‖) ≤
          ‖regDirichletDensity b u‖ * (C * 1) := by
            gcongr
            · exact hC _ hnear
            · exact norm_carlsonAffineFormCLM_le_one hu
      _ = C * ‖regDirichletDensity b u‖ := by ring
  · exact hdens.norm.const_mul C
  · filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    intro y hy
    have hy' : dist y z < δ := by simpa [s, Metric.mem_ball, dist_comm] using hy
    have hbase : carlsonAffineForm z u ∈ K := carlsonAffineForm_mem_convexHull z hu
    have hnear : carlsonAffineForm y u ∈ Metric.cthickening δ K :=
      Metric.mem_cthickening_of_dist_le _ _ δ K hbase
        ((dist_carlsonAffineForm_le_norm_sub z y hu).trans (by
          simpa [dist_eq_norm] using le_of_lt hy'))
    have hf' : HasDerivAt f (deriv f (carlsonAffineForm y u))
        (carlsonAffineForm y u) :=
      (hf _ (hδΩ hnear)).differentiableAt.hasDerivAt
    have hfL : HasDerivAt f (deriv f (carlsonAffineForm y u)) (L u y) := by
      simpa only [L, carlsonAffineFormCLM_apply] using hf'
    have hcomp := hfL.comp_hasFDerivAt y (L u).hasFDerivAt
    have hmul := hcomp.const_mul (regDirichletDensity b u)
    simpa only [F, F', L, Function.comp_apply, carlsonAffineFormCLM_apply,
      smul_eq_mul] using hmul

/-- A common integrable Dirichlet majorant bounds the average near each parameter and
node vector. No continuity of the density at the simplex boundary is required. -/
theorem locallyBounded_regCarlsonDirichletAverage_parameters_nodes
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : ContinuousOn f Ω) {p : (ι → ℂ) × (ι → ℂ)}
    (hb : p.1 ∈ mvBetaConvergent) (hz : Set.range p.2 ⊆ Ω) :
    ∃ M : ℝ, ∀ᶠ q : (ι → ℂ) × (ι → ℂ) in nhds p,
      ‖regCarlsonDirichletAverage q.1 q.2 f‖ ≤ M := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · let := hι
    exact ⟨0, Filter.Eventually.of_forall (fun q => by
      simp [regCarlsonDirichletAverage, regDirichletIntegral, stdSimplexMeasure_empty])⟩
  let := hι
  let μ := (MeasureTheory.Measure.stdSimplexMeasure (ι := ι)).restrict (Convexity.StdSimplex.coordinateSet ℝ ι)
  let K := convexHull ℝ (Set.range p.2)
  have hK : IsCompact K := (Set.finite_range p.2).isCompact_convexHull ℝ
  have hKΩ : K ⊆ Ω := convexHull_min hz hΩconv
  obtain ⟨δ₁, hδ₁, hc₁⟩ := hK.exists_isCompact_cthickening
  obtain ⟨δ₂, hδ₂, hc₂⟩ := hK.exists_cthickening_subset_open hΩopen hKΩ
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hc : IsCompact (Metric.cthickening δ K) := hc₁.of_isClosed_subset
    Metric.isClosed_cthickening (Metric.cthickening_mono (min_le_left _ _) K)
  have hsub : Metric.cthickening δ K ⊆ Ω :=
    (Metric.cthickening_mono (min_le_right _ _) K).trans hc₂
  obtain ⟨C, hC⟩ := hc.bddAbove_image (hf.mono hsub).norm
  let a : ι → ℂ := fun i => ((p.1 i).re / 2 : ℝ)
  have ha : a ∈ mvBetaConvergent := fun i => by simpa [a] using half_pos (hb i)
  have hevent : ∀ᶠ q : (ι → ℂ) × (ι → ℂ) in nhds p,
      (∀ i, (a i).re < (q.1 i).re) ∧ dist q.2 p.2 < δ := by
    apply Filter.Eventually.and
    · apply Filter.eventually_all.mpr
      intro i
      apply (isOpen_lt continuous_const
        (Complex.continuous_re.comp ((continuous_apply i).comp continuous_fst))).eventually_mem
      simpa [a] using half_lt_self (hb i)
    · exact (continuous_snd.continuousAt.dist continuousAt_const).eventually_lt_const
        (by simpa using hδ)
  have hnear {q : (ι → ℂ) × (ι → ℂ)} (hq : dist q.2 p.2 < δ)
      {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
      carlsonAffineForm q.2 u ∈ Metric.cthickening δ K :=
    Metric.mem_cthickening_of_dist_le _ _ δ K (carlsonAffineForm_mem_convexHull p.2 hu)
      ((dist_carlsonAffineForm_le_norm_sub p.2 q.2 hu).trans (by simpa [dist_eq_norm] using hq.le))
  let F := fun (q : (ι → ℂ) × (ι → ℂ)) (u : ι → ℝ) =>
    (∏ i, (u i : ℂ) ^ (q.1 i - 1)) * f (carlsonAffineForm q.2 u)
  let D : ℝ := ∫ u, ‖∏ i, (u i : ℂ) ^ (a i - 1)‖ * max C 0 ∂μ
  have hD : ∀ᶠ q in nhds p, ‖∫ u, F q u ∂μ‖ ≤ D := by
    filter_upwards [hevent] with q hq
    apply norm_integral_le_of_norm_le ((integrableOn_mvBetaMonomial a ha).norm.mul_const _)
    filter_upwards [self_mem_ae_restrict (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet, ae_zero_lt_of_mem_stdSimplex (ι := ι)] with u hu hupos
    have hm : ‖∏ i, (u i : ℂ) ^ (q.1 i - 1)‖ ≤ ‖∏ i, (u i : ℂ) ^ (a i - 1)‖ := by
      simp only [norm_prod]
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      rw [norm_cpow_eq_rpow_re_of_pos (hupos i), norm_cpow_eq_rpow_re_of_pos (hupos i)]
      apply Real.rpow_le_rpow_of_exponent_ge (hupos i)
        ((Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)).trans_eq hu.2)
      simpa only [sub_re, one_re] using sub_le_sub_right (hq.1 i).le 1
    have hfu : ‖f (carlsonAffineForm q.2 u)‖ ≤ max C 0 :=
      (hC (Set.mem_image_of_mem _ (hnear hq.2 hu))).trans (le_max_left _ _)
    exact (norm_mul _ _).trans_le (mul_le_mul hm hfu (norm_nonneg _) (norm_nonneg _))
  let B : ℝ := ‖∏ i, (Gamma (p.1 i))⁻¹‖ + 1
  have hB := ((analyticOnNhd_prod_invGamma p.1 (Set.mem_univ _)).continuousAt.comp
    (continuous_fst.continuousAt (x := p))).norm.eventually_lt_const
      (lt_add_one ‖∏ i, (Gamma (p.1 i))⁻¹‖)
  refine ⟨B * max D 0, ?_⟩
  filter_upwards [hB, hD] with q hq hqD
  rw [regCarlsonDirichletAverage, regDirichletIntegral_eq_prod_invGamma_mul, norm_mul]
  exact mul_le_mul hq.le (hqD.trans (le_max_left _ _)) (norm_nonneg _)
    (by dsimp [B]; positivity)

/-- **Carlson 5.3-3, joint form.** Separate analyticity and a local integral bound give
joint analyticity by the locally bounded Osgood theorem. -/
theorem analyticOnNhd_regCarlsonDirichletAverage_parameters_nodes
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) :
    AnalyticOnNhd ℂ
      (fun p : (ι → ℂ) × (ι → ℂ) => regCarlsonDirichletAverage p.1 p.2 f)
      {p | p.1 ∈ mvBetaConvergent ∧ Set.range p.2 ⊆ Ω} := by
  classical
  let L := ContinuousLinearEquiv.sumPiEquivProdPi ℂ ι ι (fun _ => ℂ)
  have hLapply (q : (ι ⊕ ι) → ℂ) : L q = ((fun i => q (.inl i)), (fun i => q (.inr i))) := rfl
  let U : Set ((ι ⊕ ι) → ℂ) := {q | (L q).1 ∈ mvBetaConvergent ∧ Set.range (L q).2 ⊆ Ω}
  let G : ((ι ⊕ ι) → ℂ) → ℂ := fun q => regCarlsonDirichletAverage (L q).1 (L q).2 f
  have hU : IsOpen U := by
    have hzopen : IsOpen {z : ι → ℂ | Set.range z ⊆ Ω} := by
      simp only [Set.range_subset_iff, Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i => hΩopen.preimage (continuous_apply i)
    exact (isOpen_mvBetaConvergent.preimage (continuous_fst.comp L.continuous)).inter
      (hzopen.preimage (continuous_snd.comp L.continuous))
  have hG : AnalyticOnNhd ℂ G U := by
    apply SeveralComplexVariables.analyticOnNhd_of_separately_analytic_locally_bounded hU
    · intro q hq k
      have hupdate (v : ι → ℂ) (i : ι) (w : ℂ) :
          Function.update v i w = fun j => if j = i then w else v j := by
        funext j
        simp only [Function.update_apply]
      cases k with
      | inl i =>
        have hcont : ContinuousOn (fun u => f (carlsonAffineForm (L q).2 u)) (Convexity.StdSimplex.coordinateSet ℝ ι) :=
          hf.continuousOn.comp (continuous_carlsonAffineForm _).continuousOn
            (fun u hu => convexHull_min hq.2 hΩconv (carlsonAffineForm_mem_convexHull _ hu))
        have H := (isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp
          (regDirichletIntegral_analyticOn hcont)).analyticAt_update hq.1 i
        change AnalyticAt ℂ (fun w => regCarlsonDirichletAverage
          (Function.update (fun j => q (.inl j)) i w) (fun j => q (.inr j)) f) (q (.inl i)) at H
        dsimp only [G]
        simp only [hLapply]
        simpa only [hupdate, Function.update_apply, Sum.inl.injEq, reduceCtorEq, ite_false] using! H
      | inr i =>
        have H := (analyticOnNhd_regCarlsonDirichletAverage_nodes hΩopen hΩconv hf hq.1).analyticAt_update
          hq.2 i
        change AnalyticAt ℂ (fun w => regCarlsonDirichletAverage
          (fun j => q (.inl j)) (Function.update (fun j => q (.inr j)) i w) f) (q (.inr i)) at H
        dsimp only [G]
        simp only [hLapply]
        simpa only [hupdate, Function.update_apply, Sum.inr.injEq, reduceCtorEq, ite_false] using! H
    · intro q hq
      obtain ⟨M, hM⟩ := locallyBounded_regCarlsonDirichletAverage_parameters_nodes
        hΩopen hΩconv hf.continuousOn hq.1 hq.2
      exact ⟨M, L.continuous.continuousAt.tendsto.eventually hM⟩
  intro p hp
  have hmem : L.symm p ∈ U := by simpa [U] using hp
  have H := (hG _ hmem).comp_of_eq (L.symm.analyticAt p) rfl
  simpa [G] using! H

end DirichletTransform
