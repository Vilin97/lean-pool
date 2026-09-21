/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.BrownianMultipleIntegralBox

/-!
# Finite ordered-box combinations for canonical Brownian multiple integrals

The ordered-box law for the canonical symmetrized multiple-integral operator extends linearly to
formal finite combinations.  On the deterministic side, restriction after symmetrization is the
corresponding simplex combination divided by the factorial.  On the stochastic side, the
factorial cancels and the result is the matching finite combination of Brownian increment chains.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable
section

namespace Malliavin.BrownianIteratedConstruction

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Formal finite combinations of ordered-box indicators in full product `L²`. -/
noncomputable def orderedBoxToIteratedKernel (n : ℕ) :
    (OrderedBoxIndex n →₀ ℝ) →ₗ[ℝ] IteratedKernel n :=
  Finsupp.linearCombination ℝ fun a ↦ boxKernel a.u a.v

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
theorem orderedBoxToIteratedKernel_single {n : ℕ} (a : OrderedBoxIndex n) (c : ℝ) :
    orderedBoxToIteratedKernel n (Finsupp.single a c) = c • boxKernel a.u a.v :=
  Finsupp.linearCombination_single _ _ _

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Restriction after symmetrization sends a finite full-product box combination to the
corresponding simplex combination with the inverse-factorial normalization. -/
theorem restrictToSimplex_symmetrizeL_orderedBoxToIteratedKernel
    (n : ℕ) (c : OrderedBoxIndex n →₀ ℝ) :
    restrictToSimplex n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
          (orderedBoxToIteratedKernel n c)) =
      ((n.factorial : ℝ)⁻¹) • orderedBoxToSimplexKernel n c := by
  unfold orderedBoxToIteratedKernel orderedBoxToSimplexKernel
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    restrictToSimplex_symmetrizeL_boxKernel, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_comm]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Whenever ordered boxes are dense in simplex `L²`, symmetrized finite full-product box
combinations still have dense restricted range. -/
theorem denseRange_restrictToSimplex_symmetrizeL_orderedBoxToIteratedKernel
    (n : ℕ) (hdense : OrderedBoxDense n) :
    DenseRange fun c : OrderedBoxIndex n →₀ ℝ ↦
      restrictToSimplex n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
          (orderedBoxToIteratedKernel n c)) := by
  have hfac : ((n.factorial : ℝ)) ≠ 0 := by
    exact_mod_cast n.factorial_ne_zero
  have hscale : Function.Surjective
      (fun f : IteratedIntegralConstruction.SimplexKernel n ↦
        ((n.factorial : ℝ)⁻¹) • f) := by
    intro f
    refine ⟨(n.factorial : ℝ) • f, ?_⟩
    change ((n.factorial : ℝ)⁻¹) • ((n.factorial : ℝ) • f) = f
    rw [smul_smul, inv_mul_cancel₀ hfac, one_smul]
  have hcomp := hscale.denseRange.comp hdense (continuous_const_smul _)
  have heq :
      (fun c : OrderedBoxIndex n →₀ ℝ ↦
        restrictToSimplex n
          (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
            (orderedBoxToIteratedKernel n c))) =
        (fun f : IteratedIntegralConstruction.SimplexKernel n ↦
          ((n.factorial : ℝ)⁻¹) • f) ∘ orderedBoxToSimplexKernel n := by
    funext c
    exact restrictToSimplex_symmetrizeL_orderedBoxToIteratedKernel n c
  rw [heq]
  exact hcomp

omit [CompleteSpace W] [BorelSpace W] in
/-- The canonical multiple-integral operator maps a finite ordered-box combination to the matching
finite combination of Brownian increment chains. -/
theorem brownianMultipleIntegralCLM_orderedBoxToIteratedKernel
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (c : OrderedBoxIndex n →₀ ℝ) :
    brownianMultipleIntegralCLM hB n (orderedBoxToIteratedKernel n c) =
      orderedBoxToRandom hB n c := by
  unfold orderedBoxToIteratedKernel orderedBoxToRandom
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    brownianMultipleIntegralCLM_orderedBox hB hsm]

omit [CompleteSpace W] [BorelSpace W] in
/-- The canonical multiple-integral operator restricted to formal finite ordered-box
combinations. -/
noncomputable def canonicalOrderedBoxMultipleIntegralMap
    (hB : IsPreBrownianReal B P) (n : ℕ) :
    (OrderedBoxIndex n →₀ ℝ) →ₗ[ℝ] RandomL2 P :=
  (brownianMultipleIntegralCLM hB n).toLinearMap.comp (orderedBoxToIteratedKernel n)

omit [CompleteSpace W] [BorelSpace W] in
/-- On finite ordered-box combinations, the bundled canonical multiple-integral map is exactly
the Brownian increment-chain map. -/
theorem canonicalOrderedBoxMultipleIntegralMap_eq_orderedBoxToRandom
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    canonicalOrderedBoxMultipleIntegralMap hB n = orderedBoxToRandom hB n := by
  apply LinearMap.ext
  intro c
  exact brownianMultipleIntegralCLM_orderedBoxToIteratedKernel hB hsm n c

omit [CompleteSpace W] [BorelSpace W] in
/-- The algebraic range of finite ordered Brownian increment chains of one fixed order. -/
noncomputable def brownianOrderedBoxOrderRange
    (hB : IsPreBrownianReal B P) (n : ℕ) : Submodule ℝ (RandomL2 P) :=
  LinearMap.range (orderedBoxToRandom hB n)

omit [CompleteSpace W] [BorelSpace W] in
/-- At every positive order, finite ordered Brownian increment chains are dense in the
corresponding canonical homogeneous chaos. -/
theorem brownianOrderedBoxOrderRange_closure_eq_homogeneousChaos
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    (brownianOrderedBoxOrderRange hB (n + 1)).topologicalClosure =
      (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P)) := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨c, rfl⟩
      rw [← simplexIntegral_orderedBoxToSimplexKernel hB hsm
        (orderedBoxDense_succ n)]
      rw [brownianHomogeneousChaos_succ_eq_range_simplexIntegralLI hB hsm]
      exact ⟨orderedBoxToSimplexKernel (n + 1) c, rfl⟩
    · exact (brownianHomogeneousChaos hB (n + 1)).isClosed
  · rw [brownianHomogeneousChaos_succ_eq_range_simplexIntegralLI hB hsm]
    rintro _ ⟨f, rfl⟩
    change simplexIntegral hB (n + 1) f ∈
      (brownianOrderedBoxOrderRange hB (n + 1)).topologicalClosure
    refine (orderedBoxDense_succ n).induction_on f
      ((brownianOrderedBoxOrderRange hB (n + 1)).isClosed_topologicalClosure.preimage
        (simplexIntegral hB (n + 1)).continuous) ?_
    intro c
    rw [simplexIntegral_orderedBoxToSimplexKernel hB hsm (orderedBoxDense_succ n)]
    apply Submodule.le_topologicalClosure
    exact ⟨c, rfl⟩

omit [CompleteSpace W] [BorelSpace W] in
/-- The positive-order canonical multiple-integral map restricted to finite ordered boxes already
has dense range in the full canonical homogeneous chaos. -/
theorem canonicalOrderedBoxMultipleIntegralMap_range_closure_eq_homogeneousChaos
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    (LinearMap.range
        (canonicalOrderedBoxMultipleIntegralMap hB (n + 1))).topologicalClosure =
      (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P)) := by
  rw [canonicalOrderedBoxMultipleIntegralMap_eq_orderedBoxToRandom hB hsm]
  exact brownianOrderedBoxOrderRange_closure_eq_homogeneousChaos hB hsm n

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
