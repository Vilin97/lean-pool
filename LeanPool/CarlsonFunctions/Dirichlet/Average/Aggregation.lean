/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Continuation
public import LeanPool.CarlsonFunctions.Dirichlet.Moments

/-!
# Aggregation of continued Dirichlet averages

Carlson's equal-node aggregation theorem holds for all complex parameters after
regularization. The probability aggregation theorem supplies the identity on positive
real parameters; analytic uniqueness extends it to the whole complex parameter space.
The partition is surjective, so no empty blocks are inserted.
-/

open Complex MeasureTheory ProbabilityTheory Set
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

open scoped Classical in
/-- Fiber summation preserves the total parameter. -/
theorem sum_aggregate_dirichletParameters (q : ι → κ) (b : ι → ℂ) :
    ∑ k, stdSimplexAggregate q b k = ∑ i, b i := by
  simp only [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
  exact Finset.sum_fiberwise Finset.univ q b

open scoped Classical in
/-- The affine form factors through aggregation when nodes are constant on blocks. -/
theorem carlsonAffineForm_aggregate (q : ι → κ) (z : κ → ℂ) (u : ι → ℝ) :
    carlsonAffineForm z (stdSimplexAggregate q u) = carlsonAffineForm (z ∘ q) u := by
  unfold carlsonAffineForm
  simp only [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
  push_cast
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ k, ∑ i ∈ Finset.univ with q i = k, (u i : ℂ) * z (q i) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise Finset.univ q _

open scoped Classical in
private lemma aggregate_ofReal (q : ι → κ) (b : ι → ℝ) :
    stdSimplexAggregate q (fun i => (b i : ℂ)) =
      fun k => ((stdSimplexAggregate (R := ℝ) q b k : ℝ) : ℂ) := by
  ext k
  simp [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]

/-- Real Dirichlet averages respect any surjective grouping of equal nodes. -/
theorem realCarlsonDirichletAverage_aggregate {q : ι → κ} (hq : Function.Surjective q)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (z : κ → ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn (fun u => f (carlsonAffineForm z u)) (Convexity.StdSimplex.coordinateSet ℝ κ)) :
    realCarlsonDirichletAverage b (z ∘ q) f =
      realCarlsonDirichletAverage (stdSimplexAggregate q b) z f := by
  have hmap := (measurePreserving_stdSimplexAggregate_dirichletMeasure hq hb).map_eq
  have hm : AEStronglyMeasurable (fun u => f (carlsonAffineForm z u))
      (dirichletMeasure (stdSimplexAggregate q b)) := by
    rw [← dirichletMeasure_restrict]
    exact hf.aestronglyMeasurable (Convexity.StdSimplex.isClosed_coordinateSet ℝ κ).measurableSet
  unfold realCarlsonDirichletAverage
  rw [← hmap, integral_map (_root_.continuous_stdSimplexAggregate q).measurable.aemeasurable
    (by rwa [hmap])]
  simp only [carlsonAffineForm_aggregate]

/-- Entire-parameter form of Carlson's Theorem 5.2-4. Equal nodes are merged and
their parameters added, including zero and negative parameters. -/
theorem IsRegCarlsonContinuation.aggregate
    {q : ι → κ} (hq : Function.Surjective q) {f : ℂ → ℂ} {z : κ → ℂ}
    {G : (ι → ℂ) → ℂ} {H : (κ → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f (z ∘ q) G) (hH : IsRegCarlsonContinuation f z H)
    (hf : ContinuousOn (fun u => f (carlsonAffineForm z u)) (Convexity.StdSimplex.coordinateSet ℝ κ))
    (b : ι → ℂ) : G b = H (stdSimplexAggregate q b) := by
  have hA : AnalyticOnNhd ℂ (stdSimplexAggregate (R := ℂ) q) univ := by
    intro c _
    exact ((FunOnFinite.linearMap ℂ ℂ q).toContinuousLinearMap).analyticAt c
  apply congrFun (analyticOnNhd_eq_of_eqOn_realDirichletDomain hG.1
    (hH.1.comp hA (fun _ _ => mem_univ _)) ?_) b
  intro c hc
  change G (fun i => (c i : ℂ)) = H (stdSimplexAggregate q (fun i => (c i : ℂ)))
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have : IsEmpty κ := ⟨fun k => (hq k).elim fun i _ => isEmptyElim i⟩
    rw [hG.eq_native (by intro i; exact isEmptyElim i),
      hH.eq_native (by intro k; exact isEmptyElim k)]
    simp [regCarlsonDirichletAverage, regDirichletIntegral]
  | inr hι =>
    have : Nonempty κ := ⟨q (Classical.arbitrary ι)⟩
    have hc' := mem_mvRealBetaDomain_stdSimplexAggregate hq hc
    rw [aggregate_ofReal, hG.eq_native (by simpa [mvBetaConvergent, mvRealBetaDomain] using hc),
      hH.eq_native (by simpa [mvBetaConvergent, mvRealBetaDomain] using hc'),
      regCarlsonDirichletAverage_ofReal hc,
      regCarlsonDirichletAverage_ofReal hc', realCarlsonDirichletAverage_aggregate hq hc z f hf]
    congr 2
    rw [← aggregate_ofReal, sum_aggregate_dirichletParameters]

end DirichletTransform
end
