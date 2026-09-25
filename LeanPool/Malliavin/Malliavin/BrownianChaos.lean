/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.BrownianOrderedBoxDensity
public import LeanPool.Malliavin.Malliavin.NaturalClarkOcone
public import LeanPool.Malliavin.Malliavin.NaturalItoRange

/-!
# Brownian homogeneous chaoses from iterated Itô integrals

The ordered-box construction gives canonical Brownian multiple-integral operators.  This file
defines their closed homogeneous ranges and proves that every positive range lies in the closed
range of the natural Itô integral.
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

omit [CompleteSpace W] [BorelSpace W] in
private theorem chainIntegralLp_mem_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {n : ℕ} (a : OrderedBoxIndex (n + 1)) :
    chainIntegralLp hB a.u a.v ∈ naturalItoRange hB hsm rfl := by
  refine ⟨elementaryPredictable (Filtration.natural B hsm)
    (a.u (Fin.last n)) (a.v (Fin.last n))
    (orderedChainPrefixAdapted hB hsm a.u a.v a.valid a.ordered), ?_⟩
  exact (chainIntegralLp_succ_eq_naturalItoIntegral
    hB hsm a.u a.v a.valid a.ordered).symm

omit [CompleteSpace W] [BorelSpace W] in
private theorem orderedBoxToRandom_mem_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {n : ℕ} (c : OrderedBoxIndex (n + 1) →₀ ℝ) :
    orderedBoxToRandom hB (n + 1) c ∈ naturalItoRange hB hsm rfl := by
  unfold orderedBoxToRandom
  rw [Finsupp.linearCombination_apply]
  apply Submodule.sum_mem
  intro a _ha
  exact Submodule.smul_mem _ _ (chainIntegralLp_mem_naturalItoRange hB hsm a)

omit [CompleteSpace W] [BorelSpace W] in
/-- Every completed positive-order simplex integral is a natural Itô terminal value. -/
theorem simplexIntegral_mem_naturalItoRange_succ
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) {n : ℕ}
    (f : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    simplexIntegral hB (n + 1) f ∈ naturalItoRange hB hsm hnat := by
  subst 𝓅
  refine (orderedBoxDense_succ n).induction_on f
    ((isClosed_naturalItoRange hB hsm rfl).preimage
      (simplexIntegral hB (n + 1)).continuous) ?_
  intro c
  rw [simplexIntegral_orderedBoxToSimplexKernel hB hsm (orderedBoxDense_succ n)]
  exact orderedBoxToRandom_mem_naturalItoRange hB hsm c

omit [CompleteSpace W] [BorelSpace W] in
/-- Every output of the canonical positive-order Brownian operator is a natural Itô terminal
value. -/
theorem positiveIntegralCLM_mem_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (n : ℕ) (f : IteratedKernel (n + 1)) :
    positiveIntegralCLM hB n f ∈ naturalItoRange hB hsm hnat := by
  exact simplexIntegral_mem_naturalItoRange_succ hB hsm hnat
    (restrictToSimplex (n + 1) f)

/-- The unclosed range of the canonical Brownian order-`n` multiple-integral operator. -/
noncomputable def brownianMultipleIntegralRange
    (hB : IsPreBrownianReal B P) (n : ℕ) : Submodule ℝ (RandomL2 P) :=
  LinearMap.range (integralCLM hB n).toLinearMap

/-- The canonical Brownian `n`th homogeneous subspace. -/
noncomputable def brownianHomogeneousChaos
    (hB : IsPreBrownianReal B P) (n : ℕ) : ClosedSubmodule ℝ (RandomL2 P) :=
  (brownianMultipleIntegralRange hB n).closure

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Every output of the canonical order-`n` operator belongs to its Brownian homogeneous
chaos. -/
theorem integralCLM_mem_brownianHomogeneousChaos
    (hB : IsPreBrownianReal B P) (n : ℕ) (f : IteratedKernel n) :
    integralCLM hB n f ∈ brownianHomogeneousChaos hB n := by
  apply Submodule.le_topologicalClosure (brownianMultipleIntegralRange hB n)
  exact LinearMap.mem_range_self (integralCLM hB n).toLinearMap f

omit [CompleteSpace W] [BorelSpace W] in
/-- The unclosed Brownian multiple-integral ranges of distinct orders are orthogonal. -/
theorem brownianMultipleIntegralRange_isOrtho
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {m n : ℕ} (hmn : m ≠ n) :
    brownianMultipleIntegralRange hB m ⟂ brownianMultipleIntegralRange hB n := by
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  exact integralCLM_differentOrder hB hsm positiveOrderedBoxDense hmn f g

omit [CompleteSpace W] [BorelSpace W] in
/-- Distinct closed Brownian homogeneous chaoses remain orthogonal. -/
theorem brownianHomogeneousChaos_isOrtho
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {m n : ℕ} (hmn : m ≠ n) :
    (brownianHomogeneousChaos hB m : Submodule ℝ (RandomL2 P)) ⟂
      (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)) := by
  change (brownianMultipleIntegralRange hB m).topologicalClosure ≤
    (brownianMultipleIntegralRange hB n).topologicalClosureᗮ
  rw [Submodule.orthogonal_closure]
  exact Submodule.topologicalClosure_minimal (brownianMultipleIntegralRange hB m)
    (brownianMultipleIntegralRange_isOrtho hB hsm hmn).le
    (brownianMultipleIntegralRange hB n).isClosed_orthogonal

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The zeroth Brownian homogeneous chaos is killed by the centering operator. -/
theorem brownianHomogeneousChaos_zero_le_centeredPartCLM_ker
    (hB : IsPreBrownianReal B P) :
    (brownianHomogeneousChaos hB 0 : Submodule ℝ (RandomL2 P)) ≤
      (centeredPartCLM (P := P)).ker := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  unfold brownianHomogeneousChaos
  apply Submodule.topologicalClosure_minimal
  · rintro F ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    change centeredPartCLM (integralCLM hB 0 f) = 0
    let c : ℝ := ∫ t, f t ∂iteratedKernelMeasure 0
    have hconst : integralCLM hB 0 f = Lp.const 2 P c := by
      apply Lp.ext
      exact (integralCLM_zeroOrder hB f).trans (Lp.coeFn_const 2 P c).symm
    rw [hconst, centeredPartCLM_apply, expectationL2]
    have hint : ∫ w, (Lp.const 2 P c) w ∂P = c := by
      rw [integral_congr_ae (Lp.coeFn_const 2 P c)]
      simp
    rw [hint, sub_self]
  · exact (centeredPartCLM (P := P)).isClosed_ker

omit [CompleteSpace W] [BorelSpace W] in
/-- Every positive Brownian homogeneous chaos lies in the natural Itô range. -/
theorem brownianHomogeneousChaos_le_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (n : ℕ) (hn : 0 < n) :
    (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
      naturalItoRange hB hsm hnat := by
  unfold brownianHomogeneousChaos
  apply Submodule.topologicalClosure_minimal
  · rintro F ⟨f, rfl⟩
    cases n with
    | zero => exact (Nat.lt_irrefl 0 hn).elim
    | succ n => exact positiveIntegralCLM_mem_naturalItoRange hB hsm hnat n f
  · exact isClosed_naturalItoRange hB hsm hnat

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
