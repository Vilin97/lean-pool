/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.TestGraphUniformQuotient
public import LeanPool.PoincareGeometry.AlmostSchur.TestGraphVariational

/-! # The tested difference-quotient equation and its forcing estimate

The forcing is only L²: discrete integration by parts is applied to the flux,
never to the forcing. Support enlargement is an explicit hypothesis. This
module makes no global regularity assumption on extended coefficients.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Test the actual negative-forcing variational equation with a backwards quotient. -/
theorem tested_differenceQuotient_identity (b : OrthonormalBasis ι ℝ E)
    {U V : Set E} (hUV : U ⊆ V) (v : E) (h : ℝ)
    (hshift : (fun z => z + (-h) • v) ⁻¹' U ⊆ V)
    (J : ι → Lp ℝ 2 (volume : Measure E)) (f : Lp ℝ 2 (volume : Measure E))
    (hPDE : ∀ p ∈ c1SupportedTestGraph (fun i => b i) V,
      (∑ i, inner ℝ (J i) (p.2 i)) = inner ℝ (-f) p.1)
    {q : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))}
    (hq : q ∈ closure (c1SupportedTestGraph (fun i => b i) U)) :
    (∑ i, inner ℝ (directionalDifferenceQuotient (J i) v h) (q.2 i)) =
      inner ℝ f (directionalDifferenceQuotient q.1 v (-h)) := by
  have hd := differenceQuotient_mem_closure_c1SupportedTestGraph (fun i => b i)
    hUV v (-h) hshift hq
  have he := variational_eq_on_closure_c1SupportedTestGraph (fun i => b i) V J (-f) hPDE hd
  simp only [inner_neg_left] at he
  simp_rw [inner_directionalDifferenceQuotient_adjoint]
  rw [Finset.sum_neg_distrib, he, neg_neg]

/-- The forcing term is bounded uniformly in the step using the proved graph H¹ estimate. -/
theorem abs_forcing_differenceQuotient_le (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (v : E) (h : ℝ) (hh : h ≠ 0)
    (f : Lp ℝ 2 (volume : Measure E))
    {q : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))}
    (hq : q ∈ closure (c1SupportedTestGraph (fun i => b i) U)) :
    |inner ℝ f (directionalDifferenceQuotient q.1 v (-h))| ≤
      ‖f‖ * (‖v‖ * Real.sqrt (∑ i, ‖q.2 i‖ ^ 2)) := by
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left
      (norm_differenceQuotient_closure_c1SupportedTestGraph_le b hq v (-h) (neg_ne_zero.mpr hh))
      (norm_nonneg _))

/-- Uniform forcing control after testing the PDE; no derivative of the forcing is needed. -/
theorem abs_tested_differenceQuotient_le (b : OrthonormalBasis ι ℝ E)
    {U V : Set E} (hUV : U ⊆ V) (v : E) (h : ℝ) (hh : h ≠ 0)
    (hshift : (fun z => z + (-h) • v) ⁻¹' U ⊆ V)
    (J : ι → Lp ℝ 2 (volume : Measure E)) (f : Lp ℝ 2 (volume : Measure E))
    (hPDE : ∀ p ∈ c1SupportedTestGraph (fun i => b i) V,
      (∑ i, inner ℝ (J i) (p.2 i)) = inner ℝ (-f) p.1)
    {q : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))}
    (hq : q ∈ closure (c1SupportedTestGraph (fun i => b i) U)) :
    |∑ i, inner ℝ (directionalDifferenceQuotient (J i) v h) (q.2 i)| ≤
      ‖f‖ * (‖v‖ * Real.sqrt (∑ i, ‖q.2 i‖ ^ 2)) := by
  rw [tested_differenceQuotient_identity b hUV v h hshift J f hPDE hq]
  exact abs_forcing_differenceQuotient_le b v h hh f hq

end AlmostSchur
