/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.BrownianChaosHilbertSum

/-!
# Canonical Brownian multiple Wiener--Itô operators

The canonical Brownian simplex operator gives the symmetrized multiple-integral operator
`Iₙ = n! Jₙ ∘ symmetrizeL`.  Unlike the previously selected law-level operator, this one is
constructed from Brownian increment products.  Its range agrees orderwise with the raw simplex
operator range, so its closed ranges are the canonical Brownian homogeneous chaoses.
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
/-- The canonical Brownian multiple-integral operator
`Iₙ = n! Jₙ ∘ symmetrizeL`. -/
noncomputable def brownianMultipleIntegralCLM
    (hB : IsPreBrownianReal B P) (n : ℕ) :
    IteratedKernel n →L[ℝ] RandomL2 P :=
  (n.factorial : ℝ) • (integralCLM hB n).comp
    (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
theorem brownianMultipleIntegralCLM_apply
    (hB : IsPreBrownianReal B P) (n : ℕ) (f : IteratedKernel n) :
    brownianMultipleIntegralCLM hB n f =
      (n.factorial : ℝ) • integralCLM hB n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f) :=
  rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The canonical Brownian multiple operator only depends on the symmetric part of its kernel. -/
theorem brownianMultipleIntegralCLM_symmetrize
    (hB : IsPreBrownianReal B P) (n : ℕ) (f : IteratedKernel n) :
    brownianMultipleIntegralCLM hB n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f) =
      brownianMultipleIntegralCLM hB n f := by
  simp only [brownianMultipleIntegralCLM, smul_apply,
    ContinuousLinearMap.comp_apply, symmetrizeL_symmetrizeL]

omit [CompleteSpace W] [BorelSpace W] in
/-- Polarized same-order isometry for the canonical Brownian multiple operators. -/
theorem inner_brownianMultipleIntegralCLM
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f g : IteratedKernel n) :
    inner ℝ (brownianMultipleIntegralCLM hB n f)
        (brownianMultipleIntegralCLM hB n g) =
      (n.factorial : ℝ) * inner ℝ
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g) := by
  rw [brownianMultipleIntegralCLM]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, real_inner_smul_left,
    real_inner_smul_right]
  rw [integralCLM_sameOrder hB hsm positiveOrderedBoxDense, MeasureTheory.L2.inner_def]
  have htile := integral_inner_symmetrizeL_eq_factorial_smul_setIntegral n f g
  rw [← Nat.cast_smul_eq_nsmul ℝ] at htile
  rw [htile]
  simp only [smul_eq_mul]

omit [CompleteSpace W] [BorelSpace W] in
/-- Canonical Brownian multiple integrals of different orders are orthogonal. -/
theorem inner_brownianMultipleIntegralCLM_of_ne
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {m n : ℕ} (hmn : m ≠ n) (f : IteratedKernel m) (g : IteratedKernel n) :
    inner ℝ (brownianMultipleIntegralCLM hB m f)
      (brownianMultipleIntegralCLM hB n g) = 0 := by
  rw [brownianMultipleIntegralCLM_apply, brownianMultipleIntegralCLM_apply,
    real_inner_smul_left, real_inner_smul_right,
    integralCLM_differentOrder hB hsm positiveOrderedBoxDense hmn, mul_zero, mul_zero]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Every simplex-kernel value of positive order is represented by a canonical symmetric
multiple integral. -/
theorem exists_brownianMultipleIntegralCLM_eq_simplexIntegral
    (hB : IsPreBrownianReal B P) (n : ℕ)
    (g : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    ∃ f : IteratedKernel (n + 1),
      brownianMultipleIntegralCLM hB (n + 1) f =
        simplexIntegral hB (n + 1) g := by
  let c : ℝ := ((n + 1).factorial : ℕ)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact_mod_cast (n + 1).factorial_ne_zero
  obtain ⟨f, hf⟩ :=
    IteratedIntegralConstruction.symmetrizeRestrict_surjective (n + 1) (c⁻¹ • g)
  refine ⟨f, ?_⟩
  rw [brownianMultipleIntegralCLM_apply]
  change c • simplexIntegral hB (n + 1)
      (restrictToSimplex (n + 1)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) (n + 1) 2 f)) = _
  have hf' : restrictToSimplex (n + 1)
      (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) (n + 1) 2 f) = c⁻¹ • g := by
    exact hf
  rw [hf', map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- The unclosed range of the canonical symmetrized Brownian multiple operator. -/
noncomputable def brownianSymmetricMultipleIntegralRange
    (hB : IsPreBrownianReal B P) (n : ℕ) : Submodule ℝ (RandomL2 P) :=
  LinearMap.range (brownianMultipleIntegralCLM hB n).toLinearMap

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Symmetrization does not change the orderwise canonical Brownian range. -/
theorem brownianSymmetricMultipleIntegralRange_eq
    (hB : IsPreBrownianReal B P) (n : ℕ) :
    brownianSymmetricMultipleIntegralRange hB n =
      brownianMultipleIntegralRange hB n := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    refine ⟨(n.factorial : ℝ) •
      symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f, ?_⟩
    change integralCLM hB n
      ((n.factorial : ℝ) • symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f) =
        (n.factorial : ℝ) • integralCLM hB n
          (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f)
    rw [map_smul]
  · cases n with
    | zero =>
        rintro _ ⟨f, rfl⟩
        refine ⟨f, ?_⟩
        change brownianMultipleIntegralCLM hB 0 f = integralCLM hB 0 f
        rw [brownianMultipleIntegralCLM_apply]
        have hfixed :
            symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) 0 2 f = f := by
          rw [symmetrizeL_eq_self_iff]
          intro σ
          have hσ : σ = 1 := Subsingleton.elim _ _
          subst σ
          exact Filter.Eventually.of_forall fun _ => rfl
        simp only [Nat.factorial_zero, Nat.cast_one, one_smul, hfixed]
    | succ n =>
        rintro _ ⟨f, rfl⟩
        obtain ⟨g, hg⟩ := exists_brownianMultipleIntegralCLM_eq_simplexIntegral hB n
          (restrictToSimplex (n + 1) f)
        refine ⟨g, ?_⟩
        exact hg.trans rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The canonical Brownian homogeneous chaos is also the closure of the genuine symmetrized
multiple-integral range. -/
theorem brownianHomogeneousChaos_eq_symmetricMultipleIntegralRange_closure
    (hB : IsPreBrownianReal B P) (n : ℕ) :
    (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)) =
      (brownianSymmetricMultipleIntegralRange hB n).topologicalClosure := by
  unfold brownianHomogeneousChaos
  change (brownianMultipleIntegralRange hB n).topologicalClosure =
    (brownianSymmetricMultipleIntegralRange hB n).topologicalClosure
  rw [brownianSymmetricMultipleIntegralRange_eq hB n]

omit [CompleteSpace W] [BorelSpace W] in
/-- At order one the canonical Brownian multiple operator is the genuine Wiener integral. -/
theorem brownianMultipleIntegralCLM_one_eq_wienerIntegralKernel
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    brownianMultipleIntegralCLM hB 1 = wienerIntegralKernel hB := by
  apply ContinuousLinearMap.ext
  intro f
  rw [brownianMultipleIntegralCLM_apply]
  have hfixed : symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) 1 2 f = f := by
    rw [symmetrizeL_eq_self_iff]
    intro σ
    have hσ : σ = 1 := Subsingleton.elim _ _
    subst σ
    exact Filter.Eventually.of_forall fun _ => rfl
  simp only [Nat.factorial_one, Nat.cast_one, one_smul, hfixed]
  have hone := (brownianIteratedIntegralFamily_isBrownian hB hsm).integral_one_eq hB
  change integralCLM hB 1 = wienerIntegralKernel hB at hone
  exact congrArg (fun T : IteratedKernel 1 →L[ℝ] RandomL2 P => T f) hone

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
