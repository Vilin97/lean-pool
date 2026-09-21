/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Feller.BackwardC0Convergence
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.CoordinateProductActiveReduction
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.FiniteProductCoordinateNormalForm
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.KernelRestriction
import Mathlib.MeasureTheory.Integral.CompactlySupported

/-!
# Convergence of finite-time laws along a family of Feller semigroups

Let `P i` be conservative Feller kernel semigroups whose `C₀` semigroups converge strongly to
that of a conservative Feller kernel semigroup `Q`.  Then, at every fixed finite ordered family
of observation times, the finite-time laws converge, uniformly in the starting point:

* for a coordinate-product term, by reduction to the coordinates carrying a factor and the
  backward `C₀` recursion (`Feller/BackwardC0Convergence.lean`); a term with no active
  coordinate integrates to its coefficient because the finite-time law is a probability measure;
* for a finite coordinate polynomial, by linearity;
* for an arbitrary compactly supported continuous test, by uniform approximation with coordinate
  polynomials (`FiniteTime/FiniteProductCoordinateNormalForm.lean`), the approximation error
  being uniform because the laws are probability measures.

Main results: `tendstoUniformly_integral_coordinateProductTerm_finiteTimeKernel`,
`tendstoUniformly_integral_coordinatePolynomial_finiteTimeKernel`,
`tendstoUniformly_integral_compactlySupported_finiteTimeKernel`.

The observation times are fixed throughout; nothing is asserted for test functions that are only
bounded and continuous, which needs the tightness of the limiting law and is therefore not
uniform in the starting point.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported

namespace MarkovProcess

section UniformAlgebra

variable {beta : Type*} {iota : Type*} {l : Filter iota}

/-- A family of constants converges uniformly to that constant. -/
theorem tendstoUniformly_const (c : ℝ) :
    TendstoUniformly (fun (_ : iota) (_ : beta) ↦ c) (fun _ ↦ c) l :=
  tendstoUniformlyOn_univ.mp (tendsto_const_nhds.tendstoUniformlyOn_const Set.univ)

/-- Uniform convergence is preserved by multiplication with a fixed scalar. -/
theorem tendstoUniformly_const_mul {F : iota → beta → ℝ} {f : beta → ℝ}
    (h : TendstoUniformly F f l) (c : ℝ) :
    TendstoUniformly (fun i x ↦ c * F i x) (fun x ↦ c * f x) l :=
  (uniformContinuous_const_smul c).comp_tendstoUniformly h

/-- Uniform convergence is preserved by addition. -/
theorem tendstoUniformly_add {F G : iota → beta → ℝ} {f g : beta → ℝ}
    (hf : TendstoUniformly F f l) (hg : TendstoUniformly G g l) :
    TendstoUniformly (fun i x ↦ F i x + G i x) (fun x ↦ f x + g x) l :=
  hf.add hg

end UniformAlgebra

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}

section Integrability

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem integrable_coordinateProductTerm
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
  have hfun : (term.toContinuousMap : (Fin n → alpha) → ℝ) = fun path ↦
      term.coefficient * (term.factors.map fun p ↦ p.2 (path p.1)).prod := by
    funext path
    exact PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply term path
  rw [hfun]
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
        | cons q fs ih_nonneg =>
            simp only [List.map_cons, List.prod_cons]
            exact mul_nonneg (norm_nonneg _) ih_nonneg
      have hnonneg : 0 ≤ ((factors.map fun p ↦ p.2 (path p.1)).map norm).prod := by
        simpa only [List.map_map, Function.comp_apply] using! all_nonneg factors
      exact mul_le_mul (p.2.toBCF.norm_coe_le_norm (path p.1)) ih hnonneg (norm_nonneg _)

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem integrable_coordinatePolynomial
    {n : ℕ} (terms : List (PiContinuousMap.CoordinateProductTerm (Fin n) alpha))
    (mu : Measure (Fin n → alpha)) [IsFiniteMeasure mu] :
    Integrable (PiContinuousMap.coordinatePolynomial terms) mu := by
  induction terms with
  | nil =>
      simp only [PiContinuousMap.coordinatePolynomial_nil]
      change Integrable (fun _ : Fin n → alpha ↦ (0 : ℝ)) mu
      exact integrable_zero _ _ _
  | cons term terms ih =>
      rw [PiContinuousMap.coordinatePolynomial_cons]
      exact (integrable_coordinateProductTerm term mu).add ih

end Integrability

section ActiveReduction

/-- The increasing enumeration of the active coordinates of a coordinate-product term, read at a
positive cardinality of the active set. -/
private def activeEmbedding {n k : ℕ} (factors : List (Fin n × C₀(alpha, ℝ)))
    (hk : (PiContinuousMap.activeCoordinates factors).card = k + 1) : Fin (k + 1) ↪o Fin n :=
  (Fin.castOrderIso hk.symm).toOrderEmbedding.trans
    (PiContinuousMap.activeOrderEmbedding factors)

/-- The normalized `C₀` factors at the active coordinates, indexed in increasing order. -/
private def activeFactor {n k : ℕ} (factors : List (Fin n × C₀(alpha, ℝ)))
    (hk : (PiContinuousMap.activeCoordinates factors).card = k + 1) :
    Fin (k + 1) → C₀(alpha, ℝ) :=
  fun j ↦ PiContinuousMap.activeNormalizedFactor factors (Fin.cast hk.symm j)

omit [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha] in
/-- A coordinate-product term with no active coordinate integrates to its coefficient. -/
private theorem integral_coordinateProductTerm_eq_coefficient
    {Q : SubMarkovKernelSemigroup alpha} (hQc : Q.IsConservative) {n : ℕ}
    (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha)
    (hA : PiContinuousMap.activeCoordinates term.factors = ∅)
    (u : FiniteOrderedTimes n) (x : alpha) :
    ∫ path, term.toContinuousMap path ∂finiteTimeKernel Q u x = term.coefficient := by
  let : IsProbabilityMeasure (finiteTimeKernel Q u x) :=
    hQc.isProbabilityMeasure_finiteTimeLaw Q u x
  have hTerm : ∀ path : Fin n → alpha, term.toContinuousMap path = term.coefficient := by
    intro path
    rw [PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply_active]
    simp only [PiContinuousMap.CoordinateProductTerm.activeEvaluation, hA,
      Finset.card_empty, Finset.prod_fin_eq_prod_range, Finset.prod_range_zero, mul_one]
  rw [integral_congr_ae (ae_of_all _ hTerm)]
  simp only [integral_const, probReal_univ, one_smul]

/-- A coordinate-product term with active coordinates integrates to its coefficient times the
backward `C₀` recursion at the active times. -/
private theorem integral_coordinateProductTerm_eq_backwardC0
    {Q : SubMarkovKernelSemigroup alpha} (hQ : Q.IsFellerKernelSemigroup)
    (hQc : Q.IsConservative) {n k : ℕ}
    (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha)
    (hk : (PiContinuousMap.activeCoordinates term.factors).card = k + 1)
    (u : FiniteOrderedTimes n) (x : alpha) :
    ∫ path, term.toContinuousMap path ∂finiteTimeKernel Q u x =
      term.coefficient * hQ.backwardC0 (u.restrict (activeEmbedding term.factors hk))
        (activeFactor term.factors hk) x := by
  have hg : StronglyMeasurable
      (fun path : Fin (k + 1) → alpha ↦ ∏ i, activeFactor term.factors hk i (path i)) :=
    Finset.stronglyMeasurable_fun_prod Finset.univ fun i _ ↦
      (((activeFactor term.factors hk i).measurable.comp
        (measurable_pi_apply i)).stronglyMeasurable)
  have hpoint : ∀ path : Fin n → alpha, term.toContinuousMap path =
      term.coefficient * ∏ i, activeFactor term.factors hk i
        (FiniteOrderedTimes.restrictPath (activeEmbedding term.factors hk) path i) := by
    intro path
    rw [PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply_active]
    simp only [PiContinuousMap.CoordinateProductTerm.activeEvaluation, activeFactor,
      activeEmbedding, FiniteOrderedTimes.restrictPath, RelEmbedding.coe_trans,
      Function.comp_apply, OrderIso.coe_toOrderEmbedding]
    congr 1
    exact ((Fin.castOrderIso hk.symm).toEquiv.prod_comp
      (fun j ↦ PiContinuousMap.activeNormalizedFactor term.factors j
        (path (PiContinuousMap.activeOrderEmbedding term.factors j)))).symm
  calc
    ∫ path, term.toContinuousMap path ∂finiteTimeKernel Q u x =
        ∫ path, term.coefficient * ∏ i, activeFactor term.factors hk i
          (FiniteOrderedTimes.restrictPath (activeEmbedding term.factors hk) path i)
            ∂finiteTimeKernel Q u x :=
      integral_congr_ae (ae_of_all _ hpoint)
    _ = term.coefficient * ∫ path, (fun p : Fin (k + 1) → alpha ↦
          ∏ i, activeFactor term.factors hk i (p i))
          (FiniteOrderedTimes.restrictPath (activeEmbedding term.factors hk) path)
            ∂finiteTimeKernel Q u x := by
      rw [integral_const_mul]
    _ = term.coefficient * ∫ path, ∏ i, activeFactor term.factors hk i (path i)
          ∂(finiteTimeKernel Q u).map
            (FiniteOrderedTimes.restrictPath (activeEmbedding term.factors hk)) x := by
      rw [Kernel.map_apply _
        (FiniteOrderedTimes.measurable_restrictPath (activeEmbedding term.factors hk))]
      rw [integral_map (FiniteOrderedTimes.measurable_restrictPath
        (activeEmbedding term.factors hk)).aemeasurable hg.aestronglyMeasurable]
    _ = term.coefficient * ∫ path, ∏ i, activeFactor term.factors hk i (path i)
          ∂finiteTimeKernel Q (u.restrict (activeEmbedding term.factors hk)) x := by
      rw [hQc.finiteTimeKernel_map_restrictPath Q u (activeEmbedding term.factors hk)]
    _ = term.coefficient * hQ.backwardC0 (u.restrict (activeEmbedding term.factors hk))
          (activeFactor term.factors hk) x := by
      rw [hQ.backwardC0_apply_eq_integral_finiteTimeKernel]

end ActiveReduction

variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}

/-- **Uniform convergence of the finite-time integral of a coordinate-product term.** -/
theorem tendstoUniformly_integral_coordinateProductTerm_finiteTimeKernel
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    {n : ℕ} (times : FiniteOrderedTimes n)
    (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha) :
    TendstoUniformly
      (fun i x ↦ ∫ path, term.toContinuousMap path ∂finiteTimeKernel (P i) times x)
      (fun x ↦ ∫ path, term.toContinuousMap path ∂finiteTimeKernel Q times x) l := by
  by_cases hA : (PiContinuousMap.activeCoordinates term.factors).card = 0
  · have hAe : PiContinuousMap.activeCoordinates term.factors = ∅ := Finset.card_eq_zero.mp hA
    have hcoefP : ∀ (i : iota) (y : alpha),
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel (P i) times y = term.coefficient :=
      fun i y ↦ integral_coordinateProductTerm_eq_coefficient (hPc i) term hAe times y
    have hcoefQ : ∀ y : alpha,
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel Q times y = term.coefficient :=
      fun y ↦ integral_coordinateProductTerm_eq_coefficient hQc term hAe times y
    simp only [hcoefP, hcoefQ]
    exact tendstoUniformly_const term.coefficient
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hA
    have hbackP : ∀ (i : iota) (y : alpha),
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel (P i) times y =
          term.coefficient * (hP i).backwardC0
            (times.restrict (activeEmbedding term.factors hk))
            (activeFactor term.factors hk) y :=
      fun i y ↦ integral_coordinateProductTerm_eq_backwardC0 (hP i) (hPc i) term hk times y
    have hbackQ : ∀ y : alpha,
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel Q times y =
          term.coefficient * hQ.backwardC0
            (times.restrict (activeEmbedding term.factors hk))
            (activeFactor term.factors hk) y :=
      fun y ↦ integral_coordinateProductTerm_eq_backwardC0 hQ hQc term hk times y
    simp only [hbackP, hbackQ]
    exact tendstoUniformly_const_mul (tendstoUniformly_apply_of_tendsto
      (tendsto_backwardC0_of_tendsto_c0Semigroup hP hQ hconv
        (times.restrict (activeEmbedding term.factors hk))
        (activeFactor term.factors hk))) term.coefficient

/-- **Uniform convergence of the finite-time integral of a coordinate polynomial.** -/
theorem tendstoUniformly_integral_coordinatePolynomial_finiteTimeKernel
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    {n : ℕ} (times : FiniteOrderedTimes n)
    (terms : List (PiContinuousMap.CoordinateProductTerm (Fin n) alpha)) :
    TendstoUniformly
      (fun i x ↦ ∫ path, PiContinuousMap.coordinatePolynomial terms path
        ∂finiteTimeKernel (P i) times x)
      (fun x ↦ ∫ path, PiContinuousMap.coordinatePolynomial terms path
        ∂finiteTimeKernel Q times x) l := by
  induction terms with
  | nil =>
      simp only [PiContinuousMap.coordinatePolynomial_nil, ContinuousMap.zero_apply,
        integral_zero]
      exact tendstoUniformly_const 0
  | cons term terms ih =>
      have hsplit : ∀ (R : SubMarkovKernelSemigroup alpha), R.IsConservative → ∀ y : alpha,
          ∫ path, PiContinuousMap.coordinatePolynomial (term :: terms) path
              ∂finiteTimeKernel R times y =
            (∫ path, term.toContinuousMap path ∂finiteTimeKernel R times y) +
              ∫ path, PiContinuousMap.coordinatePolynomial terms path
                ∂finiteTimeKernel R times y := by
        intro R hRc y
        let : IsProbabilityMeasure (finiteTimeKernel R times y) :=
          hRc.isProbabilityMeasure_finiteTimeLaw R times y
        rw [PiContinuousMap.coordinatePolynomial_cons]
        exact integral_add (integrable_coordinateProductTerm term _)
          (integrable_coordinatePolynomial terms _)
      have hsplitP : ∀ (i : iota) (y : alpha),
          ∫ path, PiContinuousMap.coordinatePolynomial (term :: terms) path
              ∂finiteTimeKernel (P i) times y =
            (∫ path, term.toContinuousMap path ∂finiteTimeKernel (P i) times y) +
              ∫ path, PiContinuousMap.coordinatePolynomial terms path
                ∂finiteTimeKernel (P i) times y :=
        fun i y ↦ hsplit (P i) (hPc i) y
      have hsplitQ : ∀ y : alpha,
          ∫ path, PiContinuousMap.coordinatePolynomial (term :: terms) path
              ∂finiteTimeKernel Q times y =
            (∫ path, term.toContinuousMap path ∂finiteTimeKernel Q times y) +
              ∫ path, PiContinuousMap.coordinatePolynomial terms path
                ∂finiteTimeKernel Q times y :=
        fun y ↦ hsplit Q hQc y
      simp only [hsplitP, hsplitQ]
      exact tendstoUniformly_add
        (tendstoUniformly_integral_coordinateProductTerm_finiteTimeKernel hP hPc hQ hQc
          hconv times term) ih

section CompactTest

variable [SecondCountableTopology alpha]

/-- **Uniform convergence of the finite-time integral of a compactly supported test.** -/
theorem tendstoUniformly_integral_compactlySupported_finiteTimeKernel
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    {n : ℕ} (times : FiniteOrderedTimes n) (f : C_c(Fin n → alpha, ℝ)) :
    TendstoUniformly (fun i x ↦ ∫ path, f path ∂finiteTimeKernel (P i) times x)
      (fun x ↦ ∫ path, f path ∂finiteTimeKernel Q times x) l := by
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  have heps3 : (0 : ℝ) < eps / 3 := by positivity
  obtain ⟨terms, hterms⟩ :=
    PiContinuousMap.exists_coordinateProductTerms_near_compactlySupported f heps3
  have hnear : ∀ path : Fin n → alpha,
      ‖PiContinuousMap.coordinatePolynomial terms path - f path‖ < eps / 3 := by
    intro path
    rw [PiContinuousMap.coordinatePolynomial_apply]
    exact hterms path
  have hApprox : ∀ (R : SubMarkovKernelSemigroup alpha), R.IsConservative → ∀ y : alpha,
      dist (∫ path, PiContinuousMap.coordinatePolynomial terms path ∂finiteTimeKernel R times y)
        (∫ path, f path ∂finiteTimeKernel R times y) ≤ eps / 3 := by
    intro R hRc y
    let : IsProbabilityMeasure (finiteTimeKernel R times y) :=
      hRc.isProbabilityMeasure_finiteTimeLaw R times y
    have hp : Integrable (PiContinuousMap.coordinatePolynomial terms)
        (finiteTimeKernel R times y) := integrable_coordinatePolynomial terms _
    have hf : Integrable (f : (Fin n → alpha) → ℝ) (finiteTimeKernel R times y) :=
      (map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport
    rw [Real.dist_eq, ← MeasureTheory.integral_sub hp hf]
    calc
      |∫ path, (PiContinuousMap.coordinatePolynomial terms path - f path)
          ∂finiteTimeKernel R times y| ≤ (eps / 3) * (finiteTimeKernel R times y).real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const
          (ae_of_all _ fun path ↦ (hnear path).le)
      _ = eps / 3 := by
        simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]
  have hpoly := tendstoUniformly_integral_coordinatePolynomial_finiteTimeKernel hP hPc hQ hQc
    hconv times terms
  rw [Metric.tendstoUniformly_iff] at hpoly
  filter_upwards [hpoly (eps / 3) heps3] with i hi x
  have hleft := hApprox Q hQc x
  have hright := hApprox (P i) (hPc i) x
  have hix := hi x
  have htri : dist (∫ path, f path ∂finiteTimeKernel Q times x)
      (∫ path, f path ∂finiteTimeKernel (P i) times x) ≤
      dist (∫ path, f path ∂finiteTimeKernel Q times x)
        (∫ path, PiContinuousMap.coordinatePolynomial terms path
          ∂finiteTimeKernel Q times x) +
      dist (∫ path, PiContinuousMap.coordinatePolynomial terms path
          ∂finiteTimeKernel Q times x)
        (∫ path, PiContinuousMap.coordinatePolynomial terms path
          ∂finiteTimeKernel (P i) times x) +
      dist (∫ path, PiContinuousMap.coordinatePolynomial terms path
          ∂finiteTimeKernel (P i) times x)
        (∫ path, f path ∂finiteTimeKernel (P i) times x) := dist_triangle4 _ _ _ _
  rw [dist_comm] at hleft
  linarith

end CompactTest

end SubMarkovKernelSemigroup

end MarkovProcess
