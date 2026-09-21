/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Associated.Relations
public import LeanPool.CarlsonFunctions.Dirichlet.Average.DifferentialOperators
public import LeanPool.CarlsonFunctions.Dirichlet.Complex.Analytic
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.ParametricIntegral

/-! # Differentiation of associated Dirichlet averages -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- Differentiation under a regularized Carlson average under a local uniform bound for the
derivative on the affine combinations met by the simplex. -/
theorem hasDerivAt_regCarlsonDirichletAverage_update_of_bound
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (i : ι)
    {f f' : ℂ → ℂ} {s : Set ℂ} (hs : s ∈ nhds (z i))
    (hf : ∀ w ∈ s, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      HasDerivAt f (f' (carlsonAffineForm (Function.update z i w) u))
        (carlsonAffineForm (Function.update z i w) u))
    (hf'_continuous : ∀ w ∈ s, ContinuousOn f'
      (carlsonAffineForm (Function.update z i w) '' Convexity.StdSimplex.coordinateSet ℝ ι)) {C : ℝ}
    (hf'_bound : ∀ w ∈ s, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      ‖f' (carlsonAffineForm (Function.update z i w) u)‖ ≤ C) :
    HasDerivAt
      (fun w ↦ regCarlsonDirichletAverage b (Function.update z i w) f)
      (regDirichletIntegral b
        (fun u ↦ (u i : ℂ) * f' (carlsonAffineForm z u)))
      (z i) := by
  let μ : Measure (ι → ℝ) :=
    (MeasureTheory.Measure.stdSimplexMeasure (ι := ι)).restrict
      (Convexity.StdSimplex.coordinateSet ℝ ι)
  let F : ℂ → (ι → ℝ) → ℂ := fun w u ↦
    regDirichletDensity b u * f (carlsonAffineForm (Function.update z i w) u)
  let F' : ℂ → (ι → ℝ) → ℂ := fun w u ↦
    regDirichletDensity b u * ((u i : ℂ) * f' (carlsonAffineForm
      (Function.update z i w) u))
  let bound : (ι → ℝ) → ℝ := fun u ↦ C * ‖regDirichletDensity b u‖
  have hzi : z i ∈ s := mem_of_mem_nhds hs
  have hf_comp (w : ℂ) (hw : w ∈ s) :
      ContinuousOn (fun u : ι → ℝ ↦
        f (carlsonAffineForm (Function.update z i w) u)) (Convexity.StdSimplex.coordinateSet ℝ ι)
          := by
    have hfon : ContinuousOn f
        (carlsonAffineForm (Function.update z i w) '' Convexity.StdSimplex.coordinateSet ℝ ι) := by
      intro y hy
      obtain ⟨u, hu, rfl⟩ := hy
      exact (hf w hw u hu).continuousAt.continuousWithinAt
    exact hfon.comp (continuous_carlsonAffineForm _).continuousOn
      (fun u hu ↦ ⟨u, hu, rfl⟩)
  have hF_meas : ∀ᶠ w in nhds (z i), AEStronglyMeasurable (F w) μ := by
    filter_upwards [hs] with w hw
    exact (integrableOn_regDirichletDensity_mul b hb
      (hf_comp w hw)).1
  have hF_int : Integrable (F (z i)) μ := by
    dsimp only [F, μ]
    rw [Function.update_eq_self]
    change IntegrableOn (fun u ↦ regDirichletDensity b u * f (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι) MeasureTheory.Measure.stdSimplexMeasure
    simpa using integrableOn_regDirichletDensity_mul b hb
      (by simpa using hf_comp (z i) hzi)
  have hF'_meas : AEStronglyMeasurable (F' (z i)) μ := by
    have hf'_comp : ContinuousOn (fun u : ι → ℝ ↦
        f' (carlsonAffineForm z u)) (Convexity.StdSimplex.coordinateSet ℝ ι) := by
      change ContinuousOn (f' ∘ carlsonAffineForm z) (Convexity.StdSimplex.coordinateSet ℝ ι)
      exact (hf'_continuous (z i) hzi).comp
        (continuous_carlsonAffineForm z).continuousOn
          (fun u hu ↦ ⟨u, hu, by rw [Function.update_eq_self]⟩)
    have hcont : ContinuousOn (fun u : ι → ℝ ↦
        (u i : ℂ) * f' (carlsonAffineForm z u)) (Convexity.StdSimplex.coordinateSet ℝ ι) :=
      (Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn.mul hf'_comp
    simpa [F', μ] using
      (integrableOn_regDirichletDensity_mul b hb hcont).1
  have hbound_int : Integrable bound μ := by
    have hdens : Integrable (fun u ↦ regDirichletDensity b u) μ := by
      change IntegrableOn (fun u ↦ regDirichletDensity b u)
        (Convexity.StdSimplex.coordinateSet ℝ ι) MeasureTheory.Measure.stdSimplexMeasure
      simpa only [mul_one] using integrableOn_regDirichletDensity_mul b hb
        (continuousOn_const : ContinuousOn (fun _ : ι → ℝ ↦ (1 : ℂ))
          (Convexity.StdSimplex.coordinateSet ℝ ι))
    exact hdens.norm.const_mul C
  have hbound : ∀ᵐ u ∂μ, ∀ w ∈ s, ‖F' w u‖ ≤ bound u := by
    filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    intro w hw
    simp only [F', bound, norm_mul]
    calc
      ‖regDirichletDensity b u‖ *
          (‖(u i : ℂ)‖ * ‖f' (carlsonAffineForm (Function.update z i w) u)‖)
          ≤ ‖regDirichletDensity b u‖ * (1 * C) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            apply mul_le_mul
            · simpa [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)] using
                (show u i ≤ 1 by
                  calc
                    u i ≤ ∑ j, u j := Finset.single_le_sum
                      (fun j _ ↦ hu.1 j) (Finset.mem_univ i)
                    _ = 1 := hu.2)
            · exact hf'_bound w hw u hu
            · exact norm_nonneg _
            · norm_num
      _ = C * ‖regDirichletDensity b u‖ := by ring
  have hdiff : ∀ᵐ u ∂μ, ∀ w ∈ s, HasDerivAt (F · u) (F' w u) w := by
    filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu w hw
    dsimp only [F, F']
    simpa [F, F'] using (HasDerivAt.comp_carlsonAffineForm_update i
      (hf w hw u hu)).const_mul
        (regDirichletDensity b u)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := s) (x₀ := z i) hs hF_meas hF_int hF'_meas
      hbound hbound_int hdiff |>.2
  simpa [regCarlsonDirichletAverage, regDirichletIntegral, F, F', μ] using h

open scoped Classical in
/-- Differentiation under a regularized Carlson average when the derivative of the
univariate function is globally bounded. -/
theorem hasDerivAt_regCarlsonDirichletAverage_update
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (i : ι)
    {f f' : ℂ → ℂ} (hf : ∀ w, HasDerivAt f (f' w) w)
    (hf'_continuous : Continuous f') {C : ℝ}
    (hf'_bound : ∀ w, ‖f' w‖ ≤ C) :
    HasDerivAt
      (fun w ↦ regCarlsonDirichletAverage b (Function.update z i w) f)
      (regDirichletIntegral b
        (fun u ↦ (u i : ℂ) * f' (carlsonAffineForm z u)))
      (z i) := by
  apply hasDerivAt_regCarlsonDirichletAverage_update_of_bound hb i Filter.univ_mem
    (fun w hw u hu ↦ hf _) (fun w hw ↦ hf'_continuous.continuousOn)
  intro w hw u hu
  exact hf'_bound _
open scoped Classical in
/-- Differentiation under a regularized Carlson average when the averaged function is
holomorphic on a convex neighborhood of all the nodes. -/
theorem hasDerivAt_regCarlsonDirichletAverage_update_of_analyticOnNhd
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω)
    (i : ι) :
    HasDerivAt
      (fun w => regCarlsonDirichletAverage b (Function.update z i w) f)
      (regDirichletIntegral b
        (fun u => (u i : ℂ) * deriv f (carlsonAffineForm z u)))
      (z i) := by
  let K : Set ℂ := convexHull ℝ (Set.range z)
  have hKcompact : IsCompact K := (Set.finite_range z).isCompact_convexHull ℝ
  have hKΩ : K ⊆ Ω := convexHull_min hz hΩconv
  obtain ⟨δ, hδ, hδΩ, C, hCnonneg, hC⟩ :=
    hf.exists_cthickening_deriv_boundCarlson hΩopen hKcompact hKΩ
  have hderivCont : ContinuousOn (deriv f) Ω := hf.deriv.continuousOn
  let s : Set ℂ := Metric.ball (z i) δ
  have hs : s ∈ nhds (z i) := Metric.ball_mem_nhds _ hδ
  have hnear {w : ℂ} (hw : w ∈ s) {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
      carlsonAffineForm (Function.update z i w) u ∈ Metric.cthickening δ K := by
    have hbase : carlsonAffineForm z u ∈ K := carlsonAffineForm_mem_convexHull z hu
    apply Metric.mem_cthickening_of_dist_le _ _ δ K hbase
    have hwi : ‖w - z i‖ < δ := by
      simpa [s, Metric.mem_ball, dist_eq_norm] using hw
    rw [carlsonAffineForm_update, dist_eq_norm]
    simp only [add_sub_cancel_left]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (Convexity.StdSimplex.mem_Icc_of_mem_coordinateSet hu i).2).trans hwi.le
  apply hasDerivAt_regCarlsonDirichletAverage_update_of_bound hb i hs
  · intro w hw u hu
    exact (hf _ (hδΩ (hnear hw hu))).differentiableAt.hasDerivAt
  · intro w hw
    exact hderivCont.mono fun q hq => by
      obtain ⟨u, hu, rfl⟩ := hq
      exact hδΩ (hnear hw hu)
  · intro w hw u hu
    exact hC _ (hnear hw hu)

open scoped Classical in
/-- **Carlson 5.3-2, first-order form.** For a function holomorphic on a convex node domain,
differentiation with respect to node `i` raises the corresponding Dirichlet parameter. -/
theorem carlsonPartialDeriv_regCarlsonDirichletAverage_of_analyticOnNhd
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω)
    (i : ι) :
    carlsonPartialDeriv i (fun w => regCarlsonDirichletAverage b w f) z =
      b i * regCarlsonDirichletAverage (addDirichletUnit b i) z (deriv f) := by
  rw [carlsonPartialDeriv,
    (hasDerivAt_regCarlsonDirichletAverage_update_of_analyticOnNhd
      hΩopen hΩconv hf hb hz i).deriv]
  exact (mul_regDirichletIntegral_addDirichletUnit hb i
    (fun u => deriv f (carlsonAffineForm z u))).symm

open scoped Classical in
/-- Regularized form of Carlson's relation 5.6-1(5): differentiating with respect to `z i`
produces the associated average with parameter `b i` increased by one. -/
theorem carlsonPartialDeriv_regCarlsonDirichletAverage
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (i : ι)
    {f f' : ℂ → ℂ} (hf : ∀ w, HasDerivAt f (f' w) w)
    (hf'_continuous : Continuous f') {C : ℝ}
    (hf'_bound : ∀ w, ‖f' w‖ ≤ C) :
    carlsonPartialDeriv i (fun z ↦ regCarlsonDirichletAverage b z f) z =
      b i * regCarlsonDirichletAverage (addDirichletUnit b i) z f' := by
  rw [carlsonPartialDeriv]
  rw [(hasDerivAt_regCarlsonDirichletAverage_update hb i hf
    hf'_continuous hf'_bound).deriv]
  exact (mul_regDirichletIntegral_addDirichletUnit hb i
    (fun u ↦ f' (carlsonAffineForm z u))).symm

/-- Iteration of `addDirichletUnit` in the order matching
`carlsonIteratedPartialDeriv`. -/
private def iteratedAddDirichletUnit : List ι → (ι → ℂ) → (ι → ℂ)
  | [], b => b
  | i :: is, b => addDirichletUnit (iteratedAddDirichletUnit is b) i

/-- The product of the successive Dirichlet parameters introduced by repeated parameter
shifts. -/
private def iteratedDirichletShiftCoeff : List ι → (ι → ℂ) → ℂ
  | [], _ => 1
  | i :: is, b =>
      iteratedDirichletShiftCoeff is b * iteratedAddDirichletUnit is b i

omit [Fintype ι] in
/-- Iterated positive unit shifts preserve the native Dirichlet convergence region. -/
private lemma iteratedAddDirichletUnit_mem {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (is : List ι) :
    iteratedAddDirichletUnit is b ∈ mvBetaConvergent := by
  induction is with
  | nil => exact hb
  | cons i is ih => exact addDirichletUnit_mem_mvBetaConvergent ih i

/-- Repeated density shifts convert a product of simplex coordinates into successive
positive unit shifts of the Dirichlet parameters. -/
private lemma iteratedDirichletShiftCoeff_mul_regDirichletIntegral
    (is : List ι) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (g : (ι → ℝ) → ℂ) :
    iteratedDirichletShiftCoeff is b *
        regDirichletIntegral (iteratedAddDirichletUnit is b) g =
      regDirichletIntegral b (fun u =>
        (is.map fun i => (u i : ℂ)).prod * g u) := by
  induction is generalizing g with
  | nil => simp [iteratedDirichletShiftCoeff, iteratedAddDirichletUnit]
  | cons i is ih =>
      rw [iteratedDirichletShiftCoeff, iteratedAddDirichletUnit, mul_assoc,
        mul_regDirichletIntegral_addDirichletUnit
          (iteratedAddDirichletUnit_mem hb is) i,
        ih (g := fun u => (u i : ℂ) * g u)]
      apply regDirichletIntegral_congr
      intro u hu
      simp only [List.map_cons, List.prod_cons]
      ring

omit [Fintype ι] in
open scoped Classical in
/-- Updating one node to another point of the node domain preserves containment of the node
range in that domain. -/
private lemma range_update_subset {Ω : Set ℂ} {z : ι → ℂ}
    (hz : Set.range z ⊆ Ω) {i : ι} {w : ℂ} (hw : w ∈ Ω) :
    Set.range (Function.update z i w) ⊆ Ω := by
  intro q hq
  obtain ⟨j, rfl⟩ := hq
  by_cases hji : j = i
  · subst j
    simpa using hw
  · simpa [hji] using hz (Set.mem_range_self j)
open scoped Classical in
/-- An iterated node derivative is an average with successively shifted parameters and the
corresponding iterated derivative of the averaged function. -/
private lemma carlsonIteratedPartialDeriv_eq_iteratedShift
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω)
    (is : List ι) :
    carlsonIteratedPartialDeriv is
        (fun w => regCarlsonDirichletAverage b w f) z =
      iteratedDirichletShiftCoeff is b *
        regCarlsonDirichletAverage (iteratedAddDirichletUnit is b) z
          (iteratedDeriv is.length f) := by
  induction is generalizing z with
  | nil => simp [carlsonIteratedPartialDeriv, iteratedDirichletShiftCoeff,
      iteratedAddDirichletUnit]
  | cons i is ih =>
      rw [carlsonIteratedPartialDeriv]
      unfold carlsonPartialDeriv
      have hzi : z i ∈ Ω := hz (Set.mem_range_self i)
      have heq :
          (fun w => carlsonIteratedPartialDeriv is
            (fun y => regCarlsonDirichletAverage b y f) (Function.update z i w)) =ᶠ[nhds (z i)]
          (fun w => iteratedDirichletShiftCoeff is b *
            regCarlsonDirichletAverage (iteratedAddDirichletUnit is b)
              (Function.update z i w) (iteratedDeriv is.length f)) := by
        filter_upwards [hΩopen.mem_nhds hzi] with w hw
        exact ih (range_update_subset hz hw)
      rw [heq.deriv_eq]
      have hfiter : AnalyticOnNhd ℂ (iteratedDeriv is.length f) Ω := by
        simpa [iteratedDeriv_eq_iterate] using hf.iterated_deriv is.length
      have hder := hasDerivAt_regCarlsonDirichletAverage_update_of_analyticOnNhd
        hΩopen hΩconv hfiter (iteratedAddDirichletUnit_mem hb is) hz i
      rw [(hder.const_mul (iteratedDirichletShiftCoeff is b)).deriv]
      rw [← mul_regDirichletIntegral_addDirichletUnit
        (iteratedAddDirichletUnit_mem hb is) i]
      simp only [List.length_cons, iteratedDirichletShiftCoeff,
        iteratedAddDirichletUnit, iteratedDeriv_succ]
      rw [regCarlsonDirichletAverage]
      ring

/-- **Carlson 5.3-2, regularized complex form.** Successive partial differentiation may be
taken under a Carlson average when the nodes lie in a convex domain of holomorphy. -/
theorem carlsonIteratedPartialDeriv_regCarlsonDirichletAverage
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω)
    (is : List ι) :
    carlsonIteratedPartialDeriv is
        (fun w => regCarlsonDirichletAverage b w f) z =
      regDirichletIntegral b (fun u =>
        (is.map fun i => (u i : ℂ)).prod *
          iteratedDeriv is.length f (carlsonAffineForm z u)) := by
  rw [carlsonIteratedPartialDeriv_eq_iteratedShift hΩopen hΩconv hf hb hz]
  exact iteratedDirichletShiftCoeff_mul_regDirichletIntegral is hb
    (fun u => iteratedDeriv is.length f (carlsonAffineForm z u))

open scoped Classical in
/-- The unregularized coordinate derivative on a convex domain of holomorphy.
Unlike the globally bounded derivative specialization, this applies to general holomorphic
kernels, including exponentials and powers on their branch domains. -/
theorem carlsonPartialDeriv_carlsonDirichletAverage_of_analyticOnNhd
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω) (i : ι) :
    carlsonPartialDeriv i (fun z => carlsonDirichletAverage b z f) z =
      (b i / ∑ j, b j) *
        carlsonDirichletAverage (addDirichletUnit b i) z (deriv f) := by
  let : Nonempty ι := ⟨i⟩
  have hcpos : 0 < (∑ j, b j).re := by
    simpa using Finset.sum_pos (fun j _ => hb j) Finset.univ_nonempty
  have hc : (∑ j, b j) ≠ 0 := ne_zero_of_re_pos hcpos
  have hder := hasDerivAt_regCarlsonDirichletAverage_update_of_analyticOnNhd
    hΩopen hΩconv hf hb hz i
  unfold carlsonPartialDeriv carlsonDirichletAverage
  rw [deriv_const_mul _ hder.differentiableAt, hder.deriv,
    ← mul_regDirichletIntegral_addDirichletUnit hb i
      (fun u => deriv f (carlsonAffineForm z u))]
  rw [sum_addDirichletUnit, Gamma_add_one _ hc]
  change Gamma (∑ j, b j) *
      (b i * regCarlsonDirichletAverage (addDirichletUnit b i) z (deriv f)) =
    (b i / ∑ j, b j) *
      ((∑ j, b j) * Gamma (∑ j, b j) *
        regCarlsonDirichletAverage (addDirichletUnit b i) z (deriv f))
  field_simp [hc]

open scoped Classical in
/-- Carlson's relation 5.6-1(5) in its original normalization.  The coefficient is the
weight `b i / ∑ j, b j`. -/
theorem carlsonPartialDeriv_carlsonDirichletAverage [Nonempty ι]
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (i : ι)
    {f f' : ℂ → ℂ} (hf : ∀ w, HasDerivAt f (f' w) w)
    (hf'_continuous : Continuous f') {C : ℝ}
    (hf'_bound : ∀ w, ‖f' w‖ ≤ C) :
    carlsonPartialDeriv i (fun z ↦ carlsonDirichletAverage b z f) z =
      (b i / ∑ j, b j) * carlsonDirichletAverage (addDirichletUnit b i) z f' := by
  let c : ℂ := ∑ j, b j
  have hcpos : 0 < c.re := by
    simpa [c] using Finset.sum_pos (fun j _ ↦ hb j) Finset.univ_nonempty
  have hc : c ≠ 0 := ne_zero_of_re_pos hcpos
  have hsum : ∑ j, addDirichletUnit b i j = c + 1 := sum_addDirichletUnit b i
  have hder := hasDerivAt_regCarlsonDirichletAverage_update (z := z) hb i hf
    hf'_continuous hf'_bound
  unfold carlsonPartialDeriv carlsonDirichletAverage
  rw [deriv_const_mul _ hder.differentiableAt, hder.deriv]
  rw [← mul_regDirichletIntegral_addDirichletUnit hb i
    (fun u ↦ f' (carlsonAffineForm z u))]
  rw [hsum, Gamma_add_one c hc]
  change Gamma c * (b i * regCarlsonDirichletAverage (addDirichletUnit b i) z f') =
    (b i / c) * (c * Gamma c * regCarlsonDirichletAverage (addDirichletUnit b i) z f')
  field_simp [hc]

end DirichletTransform
