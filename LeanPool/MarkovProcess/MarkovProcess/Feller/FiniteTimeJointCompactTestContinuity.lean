/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Feller.FiniteTimeCompactTestContinuity


/-!
# Joint continuity of finite-time compact-test integrals

Finite-time integrals of compactly supported continuous tests vary continuously when both the
ordered observation times and the starting point vary. The empty coordinate family is included;
in that case the integral is constant, and no constant-one `C₀` function is introduced.

This is finite-dimensional analytic infrastructure; no statement about path space is proved
here.  The continuous-path process is built in `Trajectory/`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

omit [MeasurableSpace alpha] [BorelSpace alpha] [LocallyCompactSpace alpha]
  [T2Space alpha] in
private theorem tendsto_c0_apply_of_tendsto
    {X : Type*} {l : Filter X} {f : X → C₀(alpha, ℝ)} {f₀ : C₀(alpha, ℝ)}
    {x : X → alpha} {x₀ : alpha} (hf : Tendsto f l (nhds f₀))
    (hx : Tendsto x l (nhds x₀)) :
    Tendsto (fun a ↦ f a (x a)) l (nhds (f₀ x₀)) := by
  rw [Metric.tendsto_nhds] at hf ⊢
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hpoint : Tendsto (fun a ↦ f₀ (x a)) l (nhds (f₀ x₀)) :=
    f₀.continuous.continuousAt.tendsto.comp hx
  rw [Metric.tendsto_nhds] at hpoint
  filter_upwards [hf (epsilon / 2) hhalf, hpoint (epsilon / 2) hhalf] with a ha hxa
  calc
    dist (f a (x a)) (f₀ x₀) ≤
        dist (f a (x a)) (f₀ (x a)) + dist (f₀ (x a)) (f₀ x₀) :=
      dist_triangle _ _ _
    _ ≤ dist (f a) f₀ + dist (f₀ (x a)) (f₀ x₀) := by
      have hdist : dist (f a (x a)) (f₀ (x a)) ≤
          dist (f a).toBCF f₀.toBCF :=
        BoundedContinuousFunction.dist_coe_le_dist
          (f := (f a).toBCF) (g := f₀.toBCF) (x a)
      rw [ZeroAtInftyContinuousMap.dist_toBCF_eq_dist] at hdist
      exact add_le_add_left hdist _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add ha hxa
    _ = epsilon := add_halves epsilon

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem integrable_coordinateProductTerm_joint
    {n : ℕ} (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha)
    (mu : Measure (Fin n → alpha)) [IsFiniteMeasure mu] :
    Integrable term.toContinuousMap mu := by
  have hprod : StronglyMeasurable (fun path : Fin n → alpha ↦
      (term.factors.map fun p ↦ p.2 (path p.1)).prod) := by
    induction term.factors with
    | nil => exact stronglyMeasurable_const
    | cons p factors ih =>
        simp only [List.map_cons, List.prod_cons]
        exact ((p.2.measurable.comp (measurable_pi_apply p.1)).stronglyMeasurable).mul ih
  rw [show (term.toContinuousMap : (Fin n → alpha) → ℝ) = fun path ↦
      term.coefficient * (term.factors.map fun p ↦ p.2 (path p.1)).prod by
    funext path
    exact PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply term path]
  refine Integrable.of_bound (hprod.const_mul term.coefficient).aestronglyMeasurable
    (‖term.coefficient‖ * (term.factors.map fun p ↦ ‖p.2‖).prod) ?_
  filter_upwards [] with path
  rw [norm_mul, List.norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  induction term.factors with
  | nil =>
      simp only [List.map_nil, List.prod_nil]
      exact le_rfl
  | cons p factors ih =>
      simp only [List.map_cons, List.prod_cons]
      have all_nonneg : ∀ fs : List (Fin n × C₀(alpha, ℝ)),
          0 ≤ (fs.map fun q ↦ ‖q.2 (path q.1)‖).prod := by
        intro fs
        induction fs with
        | nil => simp only [List.map_nil, List.prod_nil, zero_le_one]
        | cons q fs ihFactors =>
            simp only [List.map_cons, List.prod_cons]
            exact mul_nonneg (norm_nonneg _) ihFactors
      have hnonneg : 0 ≤
          ((factors.map fun p ↦ p.2 (path p.1)).map norm).prod := by
        simpa only [List.map_map, Function.comp_apply] using! all_nonneg factors
      apply mul_le_mul (p.2.toBCF.norm_coe_le_norm (path p.1)) ih
      · exact hnonneg
      · exact norm_nonneg _

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem integrable_coordinatePolynomial_joint
    {n : ℕ} (terms : List (PiContinuousMap.CoordinateProductTerm (Fin n) alpha))
    (mu : Measure (Fin n → alpha)) [IsFiniteMeasure mu] :
    Integrable (PiContinuousMap.coordinatePolynomial terms) mu := by
  induction terms with
  | nil =>
      simp only [PiContinuousMap.coordinatePolynomial_nil]
      change Integrable (fun _ : Fin n → alpha ↦ (0 : ℝ)) mu
      refine Integrable.of_bound stronglyMeasurable_const.aestronglyMeasurable 0 ?_
      exact ae_of_all _ fun _ ↦ by
        simpa only [norm_zero] using (le_refl (0 : ℝ))
  | cons term terms ih =>
      rw [PiContinuousMap.coordinatePolynomial_cons]
      exact (integrable_coordinateProductTerm_joint term mu).add ih

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem stronglyMeasurable_coordinatePolynomial_joint
    {n : ℕ} (terms : List (PiContinuousMap.CoordinateProductTerm (Fin n) alpha)) :
    StronglyMeasurable (PiContinuousMap.coordinatePolynomial terms) := by
  induction terms with
  | nil =>
      simp only [PiContinuousMap.coordinatePolynomial_nil]
      exact stronglyMeasurable_const
  | cons term terms ih =>
      rw [PiContinuousMap.coordinatePolynomial_cons]
      apply StronglyMeasurable.add _ ih
      have hprod : StronglyMeasurable (fun path : Fin n → alpha ↦
          (term.factors.map fun p ↦ p.2 (path p.1)).prod) := by
        induction term.factors with
        | nil => exact stronglyMeasurable_const
        | cons p factors ihFactors =>
            simp only [List.map_cons, List.prod_cons]
            exact ((p.2.measurable.comp (measurable_pi_apply p.1)).stronglyMeasurable).mul
              ihFactors
      rw [show (term.toContinuousMap : (Fin n → alpha) → ℝ) = fun path ↦
          term.coefficient * (term.factors.map fun p ↦ p.2 (path p.1)).prod by
        funext path
        exact PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply term path]
      exact hprod.const_mul term.coefficient

private theorem stronglyMeasurable_compactlySupported_fin_joint
    {n : ℕ} (f : C_c(Fin n → alpha, ℝ)) : StronglyMeasurable f := by
  have hexists (m : ℕ) :
      ∃ terms : List (PiContinuousMap.CoordinateProductTerm (Fin n) alpha),
        ∀ x, ‖PiContinuousMap.coordinatePolynomial terms x - f x‖ <
          1 / ((m : ℝ) + 1) := by
    have hpositive : 0 < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨terms, hterms⟩ :=
      PiContinuousMap.exists_coordinateProductTerms_near_compactlySupported f hpositive
    exact ⟨terms, fun x ↦ by
      rw [PiContinuousMap.coordinatePolynomial_apply]
      exact hterms x⟩
  choose terms hterms using hexists
  apply stronglyMeasurable_of_tendsto atTop
    (fun m ↦ stronglyMeasurable_coordinatePolynomial_joint (terms m))
  rw [tendsto_pi_nhds]
  intro x
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hscalar : Tendsto (fun m : ℕ ↦ (1 : ℝ) / ((m : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Metric.tendsto_nhds] at hscalar
  filter_upwards [hscalar epsilon hepsilon] with m hm
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at hm
  exact (hterms m x).trans_le hm.le

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem tendsto_integral_coordinateProductTerm_joint
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes n} {times₀ : FiniteOrderedTimes n}
    {x : X → alpha} {x₀ : alpha}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times₀ i)))
    (hx : Tendsto x l (nhds x₀))
    (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha) :
    Tendsto (fun a ↦ ∫ path, term.toContinuousMap path
        ∂finiteTimeKernel P (times a) (x a)) l
      (nhds (∫ path, term.toContinuousMap path ∂finiteTimeKernel P times₀ x₀)) := by
  let A := PiContinuousMap.activeCoordinates term.factors
  by_cases hA : A.card = 0
  · have hActive : PiContinuousMap.activeCoordinates term.factors = ∅ :=
      Finset.card_eq_zero.mp hA
    have hTerm (path : Fin n → alpha) : term.toContinuousMap path = term.coefficient := by
      rw [PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply_active]
      simp only [PiContinuousMap.CoordinateProductTerm.activeEvaluation, hActive,
        Finset.card_empty, Finset.prod_fin_eq_prod_range, Finset.prod_range_zero, mul_one]
    have hIntegral (u : FiniteOrderedTimes n) (y : alpha) :
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel P u y = term.coefficient := by
      let : IsProbabilityMeasure (finiteTimeKernel P u y) :=
        hP.isProbabilityMeasure_finiteTimeLaw P u y
      rw [integral_congr_ae (ae_of_all _ hTerm)]
      simp only [integral_const, probReal_univ, one_smul]
    simp_rw [hIntegral]
    exact tendsto_const_nhds
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hA
    let e := PiContinuousMap.activeOrderEmbedding term.factors
    let ec : Fin (k + 1) ↪o Fin n :=
      (Fin.castOrderIso hk.symm).toOrderEmbedding.trans e
    let factors : Fin (k + 1) → C₀(alpha, ℝ) := fun j ↦
      PiContinuousMap.activeNormalizedFactor term.factors (Fin.cast hk.symm j)
    have htimes : ∀ i, Tendsto (fun a ↦ (times a).restrict ec i) l
        (nhds (times₀.restrict ec i)) := fun i ↦ ht (ec i)
    have hIntegral (u : FiniteOrderedTimes n) (y : alpha) :
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel P u y =
          term.coefficient * hFeller.backwardC0 (u.restrict ec) factors y := by
      let g : (Fin (k + 1) → alpha) → ℝ :=
        fun path ↦ ∏ i, factors i (path i)
      have hg : StronglyMeasurable g :=
        Finset.stronglyMeasurable_fun_prod Finset.univ fun i _ ↦
          ((factors i).measurable.comp (measurable_pi_apply i)).stronglyMeasurable
      have hpoint : ∀ path : Fin n → alpha,
          term.toContinuousMap path =
            term.coefficient * g (FiniteOrderedTimes.restrictPath ec path) := by
        intro path
        rw [PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply_active]
        simp only [PiContinuousMap.CoordinateProductTerm.activeEvaluation, g,
          factors, FiniteOrderedTimes.restrictPath, ec, e,
          RelEmbedding.coe_trans, Function.comp_apply, OrderIso.coe_toOrderEmbedding]
        congr 1
        exact ((Fin.castOrderIso hk.symm).toEquiv.prod_comp
          (fun j ↦ PiContinuousMap.activeNormalizedFactor term.factors j
            (path (PiContinuousMap.activeOrderEmbedding term.factors j)))).symm
      calc
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel P u y =
            ∫ path, term.coefficient *
              g (FiniteOrderedTimes.restrictPath ec path) ∂finiteTimeKernel P u y := by
          exact integral_congr_ae (ae_of_all _ hpoint)
        _ = term.coefficient * ∫ path,
              g (FiniteOrderedTimes.restrictPath ec path) ∂finiteTimeKernel P u y := by
          rw [integral_const_mul]
        _ = term.coefficient * ∫ path, g path ∂
              (finiteTimeKernel P u).map (FiniteOrderedTimes.restrictPath ec) y := by
          rw [Kernel.map_apply _ (FiniteOrderedTimes.measurable_restrictPath ec),
            integral_map (FiniteOrderedTimes.measurable_restrictPath ec).aemeasurable
              hg.aestronglyMeasurable]
        _ = term.coefficient * ∫ path, g path ∂
              finiteTimeKernel P (u.restrict ec) y := by
          rw [hP.finiteTimeKernel_map_restrictPath P u ec]
        _ = term.coefficient * hFeller.backwardC0 (u.restrict ec) factors y := by
          rw [hFeller.backwardC0_apply_eq_integral_finiteTimeKernel]
    simp_rw [hIntegral]
    apply tendsto_const_nhds.mul
    exact tendsto_c0_apply_of_tendsto
      (hFeller.tendsto_backwardC0 htimes factors) hx

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem tendsto_integral_coordinatePolynomial_joint
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes n} {times₀ : FiniteOrderedTimes n}
    {x : X → alpha} {x₀ : alpha}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times₀ i)))
    (hx : Tendsto x l (nhds x₀))
    (terms : List (PiContinuousMap.CoordinateProductTerm (Fin n) alpha)) :
    Tendsto (fun a ↦ ∫ path, PiContinuousMap.coordinatePolynomial terms path
        ∂finiteTimeKernel P (times a) (x a)) l
      (nhds (∫ path, PiContinuousMap.coordinatePolynomial terms path
        ∂finiteTimeKernel P times₀ x₀)) := by
  induction terms with
  | nil =>
      simp only [PiContinuousMap.coordinatePolynomial_nil, ContinuousMap.zero_apply,
        integral_zero]
      exact tendsto_const_nhds
  | cons term terms ih =>
      have hIntegral (u : FiniteOrderedTimes n) (y : alpha) :
          ∫ path, PiContinuousMap.coordinatePolynomial (term :: terms) path
              ∂finiteTimeKernel P u y =
            (∫ path, term.toContinuousMap path ∂finiteTimeKernel P u y) +
              ∫ path, PiContinuousMap.coordinatePolynomial terms path
                ∂finiteTimeKernel P u y := by
        let : IsProbabilityMeasure (finiteTimeKernel P u y) :=
          hP.isProbabilityMeasure_finiteTimeLaw P u y
        rw [PiContinuousMap.coordinatePolynomial_cons]
        exact integral_add (integrable_coordinateProductTerm_joint term _)
          (integrable_coordinatePolynomial_joint terms _)
      simp_rw [hIntegral]
      exact (tendsto_integral_coordinateProductTerm_joint hFeller hP ht hx term).add ih

/-- Finite-time compact-test integrals vary continuously when both the ordered observation
times and the starting point vary. This includes the empty coordinate family. -/
theorem IsFellerKernelSemigroup.tendsto_integral_compactlySupported_finiteTimeKernel_of_tendsto
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes n} {times₀ : FiniteOrderedTimes n}
    {x : X → alpha} {x₀ : alpha}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times₀ i)))
    (hx : Tendsto x l (nhds x₀)) (f : C_c(Fin n → alpha, ℝ)) :
    Tendsto (fun a ↦ ∫ path, f path ∂finiteTimeKernel P (times a) (x a)) l
      (nhds (∫ path, f path ∂finiteTimeKernel P times₀ x₀)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  obtain ⟨terms, hterms⟩ :=
    PiContinuousMap.exists_coordinateProductTerms_near_compactlySupported f
      (div_pos hepsilon (by norm_num : (0 : ℝ) < 3))
  let polynomial := PiContinuousMap.coordinatePolynomial terms
  have hnear (path : Fin n → alpha) : ‖polynomial path - f path‖ < epsilon / 3 := by
    rw [PiContinuousMap.coordinatePolynomial_apply]
    exact hterms path
  have hApprox (u : FiniteOrderedTimes n) (y : alpha) :
      dist (∫ path, polynomial path ∂finiteTimeKernel P u y)
          (∫ path, f path ∂finiteTimeKernel P u y) ≤ epsilon / 3 := by
    let : IsProbabilityMeasure (finiteTimeKernel P u y) :=
      hP.isProbabilityMeasure_finiteTimeLaw P u y
    have hdiff : Integrable (fun path ↦ polynomial path - f path)
        (finiteTimeKernel P u y) := by
      apply Integrable.of_bound (C := epsilon / 3)
      · exact (stronglyMeasurable_coordinatePolynomial_joint terms).sub
          (stronglyMeasurable_compactlySupported_fin_joint f) |>.aestronglyMeasurable
      · exact ae_of_all _ fun path ↦ (hnear path).le
    have hp : Integrable polynomial (finiteTimeKernel P u y) :=
      integrable_coordinatePolynomial_joint terms _
    have hf : Integrable f (finiteTimeKernel P u y) := by
      have hsub := hp.sub hdiff
      apply hsub.congr
      exact ae_of_all _ fun path ↦ by simp only [Pi.sub_apply, sub_sub_cancel]
    rw [Real.dist_eq, ← MeasureTheory.integral_sub hp hf]
    calc
      ‖∫ path, polynomial path - f path ∂finiteTimeKernel P u y‖ ≤
          (epsilon / 3) * (finiteTimeKernel P u y).real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const
          (ae_of_all _ fun path ↦ (hnear path).le)
      _ = epsilon / 3 := by
        simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]
  have hPolynomial := tendsto_integral_coordinatePolynomial_joint
    hFeller hP ht hx terms
  rw [Metric.tendsto_nhds] at hPolynomial
  filter_upwards [hPolynomial (epsilon / 3)
    (div_pos hepsilon (by norm_num : (0 : ℝ) < 3))] with a ha
  calc
    dist (∫ path, f path ∂finiteTimeKernel P (times a) (x a))
        (∫ path, f path ∂finiteTimeKernel P times₀ x₀) ≤
      dist (∫ path, f path ∂finiteTimeKernel P (times a) (x a))
          (∫ path, polynomial path ∂finiteTimeKernel P (times a) (x a)) +
        dist (∫ path, polynomial path ∂finiteTimeKernel P (times a) (x a))
          (∫ path, f path ∂finiteTimeKernel P times₀ x₀) :=
      dist_triangle _ _ _
    _ ≤ dist (∫ path, f path ∂finiteTimeKernel P (times a) (x a))
          (∫ path, polynomial path ∂finiteTimeKernel P (times a) (x a)) +
        (dist (∫ path, polynomial path ∂finiteTimeKernel P (times a) (x a))
            (∫ path, polynomial path ∂finiteTimeKernel P times₀ x₀) +
          dist (∫ path, polynomial path ∂finiteTimeKernel P times₀ x₀)
            (∫ path, f path ∂finiteTimeKernel P times₀ x₀)) := by
      apply add_le_add_right
      exact dist_triangle _ _ _
    _ < epsilon := by
      have hleft := hApprox (times a) (x a)
      rw [dist_comm] at hleft
      have hright := hApprox times₀ x₀
      linarith only [hleft, ha, hright]

/-- At fixed ordered observation times, a finite-time compact-test integral is continuous in the
starting point. The statement also covers the empty observation family. -/
theorem IsFellerKernelSemigroup.continuous_integral_compactlySupported_finiteTimeKernel
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {n : ℕ} (times : FiniteOrderedTimes n)
    (f : C_c(Fin n → alpha, ℝ)) :
    Continuous fun x ↦ ∫ path, f path ∂finiteTimeKernel P times x := by
  rw [continuous_iff_continuousAt]
  intro x
  exact hFeller.tendsto_integral_compactlySupported_finiteTimeKernel_of_tendsto hP
    (times := fun _ : alpha ↦ times) (times₀ := times) (x := fun y ↦ y) (x₀ := x)
    (fun _ ↦ tendsto_const_nhds) tendsto_id f

end MarkovProcess.SubMarkovKernelSemigroup
