/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.OS.Axioms
import LeanPool.OSforGFF.Measure.Construct
import LeanPool.OSforGFF.Spacetime.Euclidean
import LeanPool.OSforGFF.Spacetime.DiscreteSymmetry
import LeanPool.OSforGFF.Schwinger.Defs

/-!
# Gaussian Free Field Assembly

Defines muGFF m as a ProbabilityMeasure and proves two OS axioms for general Gaussian measures:

- OS0 (alternative via quadratic form): Z[∑ᵢ zᵢJᵢ] = exp(−½ ∑ᵢⱼ zᵢzⱼ⟨Jᵢ,CJⱼ⟩) is entire
  (the primary OS0 proof via Hartogs is in `OS.os0Analyticity`)
- OS2 (Euclidean invariance): Z[gf] = Z[f] when covariance is E(4)-invariant
-/

open MeasureTheory Complex
open TopologicalSpace SchwartzMap

noncomputable section

open scoped BigOperators
open Finset

variable {E : Type*} [AddCommMonoid E] [Module ℂ E]

/-! ### OS0Alt Namespace

Alternative proof of OS0 for Gaussian measures via the explicit quadratic form expansion.
The main proof used by `OS.Master` is in `OS.os0Analyticity` (holomorphic integral theorem).
-/

namespace OS0Alt

/-- Helper lemma for bilinear expansion with finite sums -/
lemma bilin_sum_sum {E : Type*} [AddCommMonoid E] [Module ℂ E]
  (B : LinearMap.BilinMap ℂ E ℂ) (n : ℕ) (J : Fin n → E) (z : Fin n → ℂ) :
  B (∑ i, z i • J i) (∑ j, z j • J j) = ∑ i, ∑ j, z i * z j * B (J i) (J j) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  simp only [smul_eq_mul]
  congr 1; ext x; rw [Finset.mul_sum]
  congr 1; ext i; ring

end OS0Alt

/-- Assumption: The complex covariance is continuous bilinear -/
def CovarianceContinuous (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (J K : TestFunctionℂ), Continuous (fun z : ℂ =>
    SchwingerFunctionℂ₂ dμ_config (z • J) K)

/-! ## OS0: Analyticity for Gaussian Measures (OLD PROOF - in OS0Alt namespace)

The key insight is that for Gaussian measures, the generating functional
Z[∑ᵢ zᵢJᵢ] = exp(-½⟨∑ᵢ zᵢJᵢ, C(∑ⱼ zⱼJ⟩) = exp(-½ ∑ᵢⱼ zᵢzⱼ⟨Jᵢ, CJ⟩)
is the exponential of a polynomial in the complex variables zᵢ, hence entire.

Note: The primary proof is in `OSforGFF.OS.os0Analyticity`.
-/

namespace OS0Alt

/-- The `gjCovBilin` declaration. -/
def gjCovBilin (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_bilinear : CovarianceBilinear dμ_config) : LinearMap.BilinMap ℂ TestFunctionℂ ℂ :=
  LinearMap.mk₂ ℂ
    (fun x y => SchwingerFunctionℂ₂ dμ_config x y)
    (by intro x x' y  -- additivity in the 1st arg
        exact (h_bilinear 1 x x' y).2.1)
    (by intro a x y   -- homogeneity in the 1st arg
        exact (h_bilinear a x 0 y).1)
    (by intro x y y'  -- additivity in the 2nd arg
        have h := (h_bilinear 1 x y y').2.2.2
        simp only [add_comm y' y, add_comm (SchwingerFunctionℂ₂ dμ_config x y') _] at h
        exact h)
    (by intro a x y   -- homogeneity in the 2nd arg
        exact (h_bilinear a x 0 y).2.2.1)

theorem gaussian_satisfies_OS0
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_gaussian : isGaussianGJ dμ_config)
  (h_bilinear : CovarianceBilinear dμ_config)
  : os0Analyticity dμ_config := by
  intro n J
  -- Extract the Gaussian form: Z[f] = exp(-½⟨f, Cf⟩)
  have h_form : ∀ (f : TestFunctionℂ),
      GJGeneratingFunctionalℂ dμ_config f = Complex.exp (-(1/2 : ℂ) * SchwingerFunctionℂ₂ dμ_config
        f f) :=
    h_gaussian.2
  -- Rewrite the generating functional using Gaussian form
  have h_rewrite : (fun z : Fin n → ℂ => GJGeneratingFunctionalℂ dμ_config (∑ i, z i • J i)) =
                   (fun z => Complex.exp (-(1/2 : ℂ) * SchwingerFunctionℂ₂ dμ_config (∑ i,
                     z i • J i) (∑ i, z i • J i))) := by
    funext z
    exact h_form (∑ i, z i • J i)
  rw [h_rewrite]
  -- Show exp(-½ * quadratic_form) is analytic
  apply AnalyticOn.cexp
  apply AnalyticOn.mul
  · exact analyticOn_const
  · -- Show the quadratic form is analytic by expanding via bilinearity
    let B := gjCovBilin dμ_config h_bilinear
    -- Expand quadratic form: ⟨∑ᵢ zᵢJᵢ, C(∑ⱼ zⱼJ⟩) = ∑ᵢⱼ zᵢzⱼ⟨Jᵢ, CJ⟩
    have h_expansion : (fun z : Fin n → ℂ => SchwingerFunctionℂ₂ dμ_config (∑ i, z i • J i) (∑ i,
      z i • J i)) =
                       (fun z => ∑ i, ∑ j,
                         z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) := by
      funext z
      have h_eq : B (∑ i, z i • J i) (∑ i, z i • J i) = SchwingerFunctionℂ₂ dμ_config (∑ i,
        z i • J i) (∑ i, z i • J i) := rfl
      rw [← h_eq]
      exact bilin_sum_sum B n J z
    rw [h_expansion]
    -- Double sum of monomials is analytic
    -- Each monomial z_i * z_j is analytic, and finite sums of analytic functions are analytic
    have h_sum_analytic : AnalyticOnNhd ℂ (fun z : Fin n → ℂ => ∑ i, ∑ j,
      z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) Set.univ := by
      -- Each term z_i * z_j * constant is analytic
      have h_coord : ∀ i, AnalyticOnNhd ℂ (fun z : Fin n → ℂ => z i) Set.univ :=
        fun i => (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticOnNhd _
      have h_monomial : ∀ i j, AnalyticOnNhd ℂ (fun z : Fin n → ℂ => z i * z j *
        SchwingerFunctionℂ₂ dμ_config (J i) (J j)) Set.univ := fun i j =>
        ((h_coord i).mul (h_coord j)).mul analyticOnNhd_const
      have h_outer_sum : ∀ i, AnalyticOnNhd ℂ (fun z : Fin n → ℂ => ∑ j,
        z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) Set.univ := fun i => by
        rw [show (fun z : Fin n → ℂ => ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) =
            (∑ j : Fin n, fun z => z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) from by
          ext z; simp [Finset.sum_apply]]
        exact Finset.analyticOnNhd_sum _ fun j _ => h_monomial i j
      rw [show (fun z : Fin n → ℂ => ∑ i, ∑ j,
          z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) =
          (∑ i : Fin n, fun z => ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) from by
        ext z; simp [Finset.sum_apply]]
      exact Finset.analyticOnNhd_sum _ fun i _ => h_outer_sum i
    -- Convert from AnalyticOnNhd to AnalyticOn
    exact h_sum_analytic.analyticOn

end OS0Alt

/-! ## OS2: Euclidean Invariance for Translation-Invariant Gaussian Measures

Euclidean invariance follows if the covariance operator commutes with Euclidean transformations.
For translation-invariant measures, this is equivalent to the covariance depending only on
differences of spacetime points.
-/

/-- Assumption: The covariance is invariant under Euclidean transformations -/
def CovarianceEuclideanInvariant (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (g : QFT.E) (f h : TestFunction),
    SchwingerFunction₂ dμ_config (QFT.euclideanActionReal g f) (QFT.euclideanActionReal g h) =
    SchwingerFunction₂ dμ_config f h

/-- Assumption: The complex covariance is invariant under Euclidean transformations -/
def CovarianceEuclideanInvariantℂ (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (g : QFT.E) (f h : TestFunctionℂ),
    SchwingerFunctionℂ₂ dμ_config (QFT.euclideanAction g f) (QFT.euclideanAction g h) =
    SchwingerFunctionℂ₂ dμ_config f h

theorem gaussian_satisfies_OS2
  (dμ_config : ProbabilityMeasure FieldConfiguration)
  (h_gaussian : isGaussianGJ dμ_config)
  (h_euclidean_invariant : CovarianceEuclideanInvariantℂ dμ_config)
  : os2EuclideanInvariance dμ_config := by
  -- For Gaussian measures: Z[f] = exp(-½⟨f, Cf⟩)
  -- If C commutes with Euclidean transformations g, then:
  -- Z[gf] = exp(-½⟨gf, C(gf)⟩) = exp(-½⟨f, Cf⟩) = Z[f]
  intro g f
  -- Extract Gaussian form for both Z[f] and Z[gf]
  have h_form := h_gaussian.2
  -- Apply Gaussian form to both sides
  rw [h_form f, h_form (QFT.euclideanAction g f)]
  -- Show the exponents are equal: ⟨gf, C(gf)⟩ = ⟨f, Cf⟩
  -- This follows directly from Euclidean invariance of the complex covariance
  congr 2
  -- Use Euclidean invariance directly (symmetric form)
  exact (h_euclidean_invariant g f f).symm

/-! ## Implementation Strategy

To complete these proofs, we need to:

1. **Complete the Glimm-Jaffe reflection positivity argument:**
   - Time reflection properly implemented using `QFT.compTimeReflection` from DiscreteSymmetry ✓
   - Implement `covarianceOperator` as the Riesz representation of the 2-point function
   - Complete the proof of `glimm_jaffe_exponent_reflection_positive`
   - Show that the 4-term expansion in the exponent has non-negative real part

3. **Prove key lemmas:**
   - Schwartz map composition with smooth transformations
   - Properties of the bilinear form `distributionPairingℂReal`
   - Continuity and analyticity of exponential functionals

4. **Mathematical insights implemented:**
   - **OS0**: Polynomial → exponential → entire function ✓
   - **OS1**: Positive semidefinite covariance → bounded generating functional ✓
   - **OS2**: Covariance commutes with transformations → generating functional invariant ✓
   - **OS3**: Reflection positivity framework following Glimm-Jaffe Theorem 6.2.2 ✓ (structure)
   - **OS4**: Covariance decay → correlation decay ✓

5. **Glimm-Jaffe Theorem 6.2.2 Implementation:**
   - Defined the key expansion:
     `glimm_jaffe_exponent` captures ⟨Fbar - CF', C(Fbar - CF')⟩
   - Structured the proof around the exponential form
     Z[Fbar - CF'] = exp(-½⟨Fbar - CF', C(Fbar - CF')⟩)
   - The reflection positivity condition ensures Re⟨Fbar - CF', C(Fbar - CF')⟩ ≥ 0
   - This gives |Z[Fbar - CF']| ≤ 1, which is the heart of reflection positivity

6. **Connection to existing GFF work:**
   - Use results from `GFF.lean` and `GFF2.lean` where applicable
   - Translate L2-based proofs to distribution framework
   - Leverage the explicit Gaussian form of the generating functional

Note: The main theorem `gaussian_satisfies_all_GJ_OS_axioms` shows that Gaussian measures
satisfy all the OS axioms under appropriate assumptions on the covariance. The Glimm-Jaffe
approach for OS3 provides the mathematical foundation for reflection positivity in the
Gaussian Free Field context.
-/
