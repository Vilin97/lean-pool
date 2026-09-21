/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.BrownianMultipleIntegral

/-!
# Ordered-box values of canonical Brownian multiple integrals

Symmetrization averages all coordinate permutations of an ordered-box indicator.  On the strict
simplex only the identity permutation survives, so the factorial normalization in the canonical
multiple-integral operator cancels that average and recovers the Brownian increment chain.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace Malliavin.BrownianIteratedConstruction

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Restricting a symmetrized ordered-box indicator to the strict simplex leaves exactly its
identity-permutation contribution. -/
theorem restrictToSimplex_symmetrizeL_boxKernel {n : ℕ} (a : OrderedBoxIndex n) :
    restrictToSimplex n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 (boxKernel a.u a.v)) =
      ((n.factorial : ℝ)⁻¹) • orderedBoxSimplexKernel a := by
  apply Lp.ext
  have hbox :
      (boxKernel a.u a.v : (Fin n → ℝ≥0) → ℝ) =ᵐ[iteratedKernelMeasure n]
        (orderedBox a.u a.v).indicator fun _ ↦ (1 : ℝ) := by
    exact indicatorConstLp_coeFn
  have hsymm :
      (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
          (boxKernel a.u a.v) : (Fin n → ℝ≥0) → ℝ) =ᵐ[iteratedKernelMeasure n]
        symmetrize n ((orderedBox a.u a.v).indicator fun _ ↦ (1 : ℝ)) :=
    (coeFn_symmetrizeL (E := ℝ) (μ := nonnegativeLebesgueMeasure) n 2
      (boxKernel a.u a.v)).trans
        (symmetrize_congr_ae (μ := nonnegativeLebesgueMeasure) hbox)
  have hord :
      (orderedBoxSimplexKernel a : (Fin n → ℝ≥0) → ℝ) =ᵐ[
          (iteratedKernelMeasure n).restrict (simplex ℝ≥0 n)]
        (orderedBox a.u a.v).indicator fun _ ↦ (1 : ℝ) := by
    exact indicatorConstLp_coeFn
  filter_upwards [ae_restrict_mem (measurableSet_simplex n),
    restrictToSimplex_ae n
      (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 (boxKernel a.u a.v)),
    ae_restrict_of_ae hsymm,
    Lp.coeFn_smul ((n.factorial : ℝ)⁻¹) (orderedBoxSimplexKernel a),
    hord]
      with t ht hrestrict hsymm_t hsmul hindicator
  rw [hrestrict, hsymm_t, hsmul, Pi.smul_apply, hindicator]
  rw [symmetrize_apply]
  congr 1
  apply Finset.sum_eq_single 1
  · intro σ _hσmem hσ
    rw [Set.indicator_of_notMem]
    intro hmem
    have hσsimplex : t ∘ σ ∈ simplex ℝ≥0 n := orderedBox_subset_simplex a hmem
    have hEq : σ = 1 :=
      perm_eq_of_strictMono_comp (mem_simplex.mp ht).injective
        (mem_simplex.mp hσsimplex) (by
          have ht_one : t ∘ (1 : Equiv.Perm (Fin n)) = t := by
            funext i
            rfl
          rw [ht_one]
          exact mem_simplex.mp ht)
    exact hσ hEq
  · intro h
    exact (h (Finset.mem_univ (1 : Equiv.Perm (Fin n)))).elim

omit [CompleteSpace W] [BorelSpace W] in
/-- The canonical symmetrized Brownian multiple-integral operator has the Brownian chain value
on every ordered box. -/
theorem brownianMultipleIntegralCLM_orderedBox
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {n : ℕ} (a : OrderedBoxIndex n) :
    brownianMultipleIntegralCLM hB n (boxKernel a.u a.v) =
      chainIntegralLp hB a.u a.v := by
  cases n with
  | zero =>
      rw [brownianMultipleIntegralCLM_apply]
      have hfixed :
          symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) 0 2
              (boxKernel a.u a.v) =
            boxKernel a.u a.v := by
        rw [symmetrizeL_eq_self_iff]
        intro σ
        have hσ : σ = 1 := Subsingleton.elim _ _
        subst σ
        exact Eventually.of_forall fun _ ↦ rfl
      simp only [Nat.factorial_zero, Nat.cast_one, one_smul, hfixed]
      apply Lp.ext
      exact (IteratedIntegralFamily.box_zero (B := B)
        (family hB hsm positiveOrderedBoxDense) a.u a.v).trans
          (coeFn_chainIntegralLp hB a.u a.v).symm
  | succ n =>
      rw [brownianMultipleIntegralCLM_apply]
      change ((n + 1).factorial : ℝ) •
          simplexIntegral hB (n + 1)
            (restrictToSimplex (n + 1)
              (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) (n + 1) 2
                (boxKernel a.u a.v))) =
        chainIntegralLp hB a.u a.v
      rw [restrictToSimplex_symmetrizeL_boxKernel a, map_smul, smul_smul]
      have hfac : ((n + 1).factorial : ℝ) ≠ 0 := by
        exact_mod_cast (n + 1).factorial_ne_zero
      rw [mul_inv_cancel₀ hfac, one_smul]
      exact simplexIntegral_orderedBoxSimplexKernel hB hsm
        (positiveOrderedBoxDense n) a

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
