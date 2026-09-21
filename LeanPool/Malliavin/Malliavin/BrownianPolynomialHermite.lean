/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.BrownianHermite
import LeanPool.Malliavin.Malliavin.BrownianCylinderDensity
import LeanPool.Malliavin.Malliavin.BrownianChaosTotality

/-!
# Brownian polynomial generators and the stochastic Hermite gap

Generalized Hermite values of each finite Brownian step sum span exactly the same algebraic
subspace as its powers.  This file isolates the remaining stochastic input as the assertion that
those Wick values belong to the closed span of ordered, disjoint increment products, and proves
that this exact assertion implies canonical-chaos totality and natural martingale representation.
-/

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

/-- The generalized Hermite value of a finite Brownian step sum, assembled from its powers.
The variance parameter is the squared norm of the corresponding deterministic step kernel. -/
noncomputable def brownianWickPowerLp (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) : RandomL2 P :=
  polynomialFamilyLinearMap (brownianStepPowerLp hB v)
    (varianceHermite (‖stepToLp v‖ ^ 2) n)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- The Brownian Wick-power construction represents pointwise generalized Hermite evaluation. -/
theorem coeFn_brownianWickPowerLp (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    (brownianWickPowerLp hB v n : W → ℝ) =ᵐ[P]
      fun w ↦ (varianceHermite (‖stepToLp v‖ ^ 2) n).eval (stepSum B v w) := by
  apply coeFn_polynomialFamilyLinearMap
  intro k
  exact MemLp.coeFn_toLp _

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- For a fixed Brownian step sum, generalized Hermite values and ordinary powers have the same
algebraic span. -/
theorem span_range_brownianWickPowerLp_eq_power (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) :
    Submodule.span ℝ (Set.range (brownianWickPowerLp hB v)) =
      Submodule.span ℝ (Set.range (brownianStepPowerLp hB v)) := by
  exact span_range_polynomialFamilyLinearMap_varianceHermite (‖stepToLp v‖ ^ 2)
    (brownianStepPowerLp hB v)

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The zeroth Brownian Wick power is the constant-one random variable. -/
theorem brownianWickPowerLp_zero (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    brownianWickPowerLp hB v 0 = Lp.const 2 P (1 : ℝ) := by
  change polynomialFamilyLinearMap (brownianStepPowerLp hB v) 1 = _
  rw [show (1 : Polynomial ℝ) = Polynomial.X ^ 0 by simp,
    polynomialFamilyLinearMap_X_pow]
  unfold brownianStepPowerLp
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_two_stepSum_pow hB v 0),
    Lp.coeFn_const 2 P (1 : ℝ)] with w hpower hone
  rw [hpower, hone]
  simp only [pow_zero, Function.const_apply]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- The first Brownian Wick power is its finite Brownian step sum in `L²`. -/
theorem brownianWickPowerLp_one (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    brownianWickPowerLp hB v 1 = stepToRandom hB v := by
  change polynomialFamilyLinearMap (brownianStepPowerLp hB v) Polynomial.X = _
  rw [show (Polynomial.X : Polynomial ℝ) = Polynomial.X ^ 1 by simp,
    polynomialFamilyLinearMap_X_pow]
  unfold brownianStepPowerLp
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_two_stepSum_pow hB v 1),
    coeFn_stepToRandom hB v] with w hpower hstep
  rw [hpower, hstep]
  simp only [pow_one]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Every Brownian coordinate belongs already to the algebraic ordered-chain span. -/
theorem brownianLp_mem_orderedChainSpan (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    brownianLp hB t ∈ brownianOrderedChainSpan hB := by
  let a : OrderedBoxIndex 1 :=
    { u := fun _ ↦ 0
      v := fun _ ↦ t
      valid := fun _ ↦ by exact zero_le
      ordered := by
        intro i j hij
        have hEq : i = j := Subsingleton.elim _ _
        subst j
        exact (lt_irrefl i hij).elim }
  have hvalue : chainIntegralLp hB a.u a.v = brownianLp hB t := by
    apply Lp.ext
    filter_upwards [coeFn_chainIntegralLp hB a.u a.v,
      coeFn_brownianLp hB t, hB.eval_zero_ae_eq_zero] with w hchain hbrown hzero
    rw [hchain, hbrown]
    simp [chainIntegral, a, hzero]
  rw [← hvalue]
  apply Submodule.subset_span
  exact ⟨⟨1, a⟩, rfl⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Every finite Brownian step sum belongs already to the algebraic ordered-chain span. -/
theorem stepToRandom_mem_orderedChainSpan (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) :
    stepToRandom hB v ∈ brownianOrderedChainSpan hB := by
  induction v using Finsupp.induction with
  | zero =>
      rw [map_zero]
      exact (brownianOrderedChainSpan hB).zero_mem
  | single_add t c v _ _ ih =>
      rw [map_add, stepToRandom_single]
      exact (brownianOrderedChainSpan hB).add_mem
        ((brownianOrderedChainSpan hB).smul_mem c
          (brownianLp_mem_orderedChainSpan hB t)) ih

/-- The exact remaining stochastic Hermite input: every generalized Hermite value of a finite
Brownian step sum is approximable by finite products of ordered, disjoint increments. -/
def BrownianWickChainCompatible (hB : IsPreBrownianReal B P) : Prop :=
  ∀ v n, brownianWickPowerLp hB v n ∈
    (brownianOrderedChainSpan hB).topologicalClosure

/-- The genuinely higher-order part of stochastic Wick-chain compatibility. -/
def BrownianHigherWickChainCompatible (hB : IsPreBrownianReal B P) : Prop :=
  ∀ v n, 2 ≤ n → brownianWickPowerLp hB v n ∈
    (brownianOrderedChainSpan hB).topologicalClosure

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- Orders zero and one are automatic, so Wick-chain compatibility is exactly its higher-order
part. -/
theorem brownianWickChainCompatible_iff_higher (hB : IsPreBrownianReal B P) :
    BrownianWickChainCompatible hB ↔ BrownianHigherWickChainCompatible hB := by
  constructor
  · intro hwick v n _hn
    exact hwick v n
  · intro hhigher v n
    cases n with
    | zero =>
        rw [brownianWickPowerLp_zero hB v]
        apply Submodule.le_topologicalClosure
        let a : OrderedBoxIndex 0 :=
          { u := fun i ↦ Fin.elim0 i
            v := fun i ↦ Fin.elim0 i
            valid := fun i ↦ Fin.elim0 i
            ordered := fun i ↦ Fin.elim0 i }
        rw [← chainIntegralLp_zero hB a.u a.v]
        exact Submodule.subset_span ⟨⟨0, a⟩, rfl⟩
    | succ n =>
        cases n with
        | zero =>
            rw [brownianWickPowerLp_one hB v]
            exact Submodule.le_topologicalClosure _
              (stepToRandom_mem_orderedChainSpan hB v)
        | succ n =>
            exact hhigher v (n + 2) (by omega)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Wick-chain compatibility puts every Brownian step-sum power in the ordered-chain closure. -/
theorem brownianStepPowerLp_mem_orderedChainSpan_closure
    (hB : IsPreBrownianReal B P) (hwick : BrownianWickChainCompatible hB)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianStepPowerLp hB v n ∈
      (brownianOrderedChainSpan hB).topologicalClosure := by
  have hpower : brownianStepPowerLp hB v n ∈
      Submodule.span ℝ (Set.range (brownianStepPowerLp hB v)) :=
    Submodule.subset_span ⟨n, rfl⟩
  rw [← span_range_brownianWickPowerLp_eq_power hB v] at hpower
  exact (Submodule.span_le.mpr <| by
    rintro _ ⟨k, rfl⟩
    exact hwick v k) hpower

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Under Wick-chain compatibility, the entire Brownian polynomial span lies in the ordered-chain
closure. -/
theorem brownianPolynomialSpan_le_orderedChainSpan_closure
    (hB : IsPreBrownianReal B P) (hwick : BrownianWickChainCompatible hB) :
    brownianPolynomialSpan hB ≤
      (brownianOrderedChainSpan hB).topologicalClosure := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨v, n⟩, rfl⟩
  exact brownianStepPowerLp_mem_orderedChainSpan_closure hB hwick v n

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- Ambient Brownian polynomial density and Wick-chain compatibility imply ordered-chain
density. -/
theorem dense_orderedChainSpan_of_wickChainCompatible
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B)
    (hwick : BrownianWickChainCompatible hB) :
    Dense (brownianOrderedChainSpan hB : Set (RandomL2 P)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  have hpoly := dense_brownianPolynomialSpan hB hgen
  rw [Submodule.dense_iff_topologicalClosure_eq_top] at hpoly
  rw [← hpoly]
  exact Submodule.topologicalClosure_minimal (brownianPolynomialSpan hB)
    (brownianPolynomialSpan_le_orderedChainSpan_closure hB hwick)
    (brownianOrderedChainSpan hB).isClosed_topologicalClosure

omit [CompleteSpace W] [BorelSpace W] in
/-- The exact stochastic Hermite compatibility input supplies natural martingale
representation. -/
theorem naturalMartingaleRepresentation_of_wickChainCompatible
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hgen : IsWienerGenerated B) (hwick : BrownianWickChainCompatible hB) :
    NaturalMartingaleRepresentation hB hsm hnat := by
  exact naturalMartingaleRepresentation_of_dense_orderedChainSpan hB hsm hnat
    (dense_orderedChainSpan_of_wickChainCompatible hB hgen hwick)

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
