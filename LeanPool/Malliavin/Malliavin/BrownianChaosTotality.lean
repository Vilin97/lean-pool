/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.BrownianChaosMartingaleRepresentation

/-!
# Totality criterion for the canonical Brownian chaos tower

The completed canonical Brownian chaos tower has the same closed span as the explicit finite
products of ordered, disjoint Brownian increments.  Thus its remaining totality question is
equivalent to a concrete dense-span statement for those products.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable
section

namespace Malliavin.BrownianIteratedConstruction

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- All finite products of ordered, disjoint Brownian increments, including the empty product. -/
def brownianOrderedChainSet (hB : IsPreBrownianReal B P) : Set (RandomL2 P) :=
  Set.range fun a : Σ n : ℕ, OrderedBoxIndex n =>
    chainIntegralLp hB a.2.u a.2.v

/-- The algebraic span of finite ordered Brownian increment products. -/
def brownianOrderedChainSpan (hB : IsPreBrownianReal B P) :
    Submodule ℝ (RandomL2 P) :=
  Submodule.span ℝ (brownianOrderedChainSet hB)

omit [CompleteSpace W] [BorelSpace W] in
private theorem chainIntegralLp_mem_iSup_brownianHomogeneousChaos
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {n : ℕ} (a : OrderedBoxIndex n) :
    chainIntegralLp hB a.u a.v ∈
      ⨆ k : ℕ, (brownianHomogeneousChaos hB k : Submodule ℝ (RandomL2 P)) := by
  cases n with
  | zero =>
      let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
      let f : IteratedKernel 0 := Lp.const 2 (iteratedKernelMeasure 0) (1 : ℝ)
      have hfint : ∫ t, f t ∂iteratedKernelMeasure 0 = 1 := by
        rw [integral_congr_ae (Lp.coeFn_const 2 (iteratedKernelMeasure 0) (1 : ℝ))]
        simp
      have hvalue : integralCLM hB 0 f = chainIntegralLp hB a.u a.v := by
        apply Lp.ext
        filter_upwards [integralCLM_zeroOrder hB f,
          coeFn_chainIntegralLp hB a.u a.v] with w hw hchain
        rw [hw, hfint, hchain]
        simp [chainIntegral]
      apply le_iSup (fun k : ℕ =>
        (brownianHomogeneousChaos hB k : Submodule ℝ (RandomL2 P))) 0
      rw [← hvalue]
      exact integralCLM_mem_brownianHomogeneousChaos hB 0 f
  | succ n =>
      apply le_iSup (fun k : ℕ =>
        (brownianHomogeneousChaos hB k : Submodule ℝ (RandomL2 P))) (n + 1)
      rw [← positiveIntegralCLM_box hB hsm (orderedBoxDense_succ n) a]
      exact integralCLM_mem_brownianHomogeneousChaos hB (n + 1)
        (boxKernel a.u a.v)

omit [CompleteSpace W] [BorelSpace W] in
private theorem integralCLM_mem_brownianOrderedChainSpan_closure
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f : IteratedKernel n) :
    integralCLM hB n f ∈ (brownianOrderedChainSpan hB).topologicalClosure := by
  cases n with
  | zero =>
      let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
      let a : OrderedBoxIndex 0 :=
        { u := fun i => Fin.elim0 i
          v := fun i => Fin.elim0 i
          valid := fun i => Fin.elim0 i
          ordered := fun i => Fin.elim0 i }
      let c : ℝ := ∫ t, f t ∂iteratedKernelMeasure 0
      have hvalue : integralCLM hB 0 f = c • chainIntegralLp hB a.u a.v := by
        have hconst : integralCLM hB 0 f = Lp.const 2 P c := by
          apply Lp.ext
          exact (integralCLM_zeroOrder hB f).trans (Lp.coeFn_const 2 P c).symm
        rw [hconst, chainIntegralLp_zero]
        change (Lp.constL 2 P ℝ) c = c • (Lp.constL 2 P ℝ) 1
        simpa using map_smul (Lp.constL 2 P ℝ) c (1 : ℝ)
      rw [hvalue]
      apply Submodule.le_topologicalClosure
      exact (brownianOrderedChainSpan hB).smul_mem c <|
        Submodule.subset_span ⟨⟨0, a⟩, rfl⟩
  | succ n =>
      change positiveIntegralCLM hB n f ∈
        (brownianOrderedChainSpan hB).topologicalClosure
      change simplexIntegral hB (n + 1) (restrictToSimplex (n + 1) f) ∈
        (brownianOrderedChainSpan hB).topologicalClosure
      refine (orderedBoxDense_succ n).induction_on (restrictToSimplex (n + 1) f)
        ((brownianOrderedChainSpan hB).isClosed_topologicalClosure.preimage
          (simplexIntegral hB (n + 1)).continuous) ?_
      intro d
      rw [simplexIntegral_orderedBoxToSimplexKernel hB hsm (orderedBoxDense_succ n)]
      unfold orderedBoxToRandom
      rw [Finsupp.linearCombination_apply]
      apply Submodule.sum_mem
      intro a _ha
      apply Submodule.smul_mem
      apply Submodule.le_topologicalClosure
      exact Submodule.subset_span ⟨⟨n + 1, a⟩, rfl⟩

omit [CompleteSpace W] [BorelSpace W] in
/-- Each completed Brownian homogeneous chaos lies in the closed span of explicit ordered
increment products. -/
theorem brownianHomogeneousChaos_le_orderedChainSpan_closure
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
      (brownianOrderedChainSpan hB).topologicalClosure := by
  unfold brownianHomogeneousChaos
  apply Submodule.topologicalClosure_minimal
  · rintro _ ⟨f, rfl⟩
    exact integralCLM_mem_brownianOrderedChainSpan_closure hB hsm n f
  · exact (brownianOrderedChainSpan hB).isClosed_topologicalClosure

omit [CompleteSpace W] [BorelSpace W] in
/-- Completing the explicit ordered increment products gives exactly the closed span of the
canonical Brownian homogeneous chaoses. -/
theorem brownianOrderedChainSpan_closure_eq_chaosClosure
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    (brownianOrderedChainSpan hB).topologicalClosure =
      (⨆ n : ℕ, (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P))
        ).topologicalClosure := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.mpr
    rintro F ⟨a, rfl⟩
    exact chainIntegralLp_mem_iSup_brownianHomogeneousChaos hB hsm a.2
  · apply Submodule.topologicalClosure_minimal
    · exact iSup_le fun n =>
        brownianHomogeneousChaos_le_orderedChainSpan_closure hB hsm n
    · exact (brownianOrderedChainSpan hB).isClosed_topologicalClosure

omit [CompleteSpace W] [BorelSpace W] in
/-- Canonical Brownian-chaos totality is equivalent to density of finite ordered increment
products. -/
theorem brownianChaosTotal_iff_dense_orderedChainSpan
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianChaosTotal hB ↔ Dense (brownianOrderedChainSpan hB : Set (RandomL2 P)) := by
  rw [BrownianChaosTotal, Submodule.dense_iff_topologicalClosure_eq_top,
    brownianOrderedChainSpan_closure_eq_chaosClosure hB hsm]

omit [CompleteSpace W] [BorelSpace W] in
/-- Density of explicit ordered Brownian increment products supplies natural martingale
representation. -/
theorem naturalMartingaleRepresentation_of_dense_orderedChainSpan
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hdense : Dense (brownianOrderedChainSpan hB : Set (RandomL2 P))) :
    NaturalMartingaleRepresentation hB hsm hnat :=
  naturalMartingaleRepresentation_of_brownianChaosTotal hB hsm hnat <|
    (brownianChaosTotal_iff_dense_orderedChainSpan hB hsm).2 hdense

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
