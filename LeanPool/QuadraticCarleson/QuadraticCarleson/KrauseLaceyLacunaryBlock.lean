/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyBlockHypothesis
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleBlockWeak
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositivePrincipalValueEndpoints

/-!
# From the two sparse inputs to the paper's frozen lacunary block

This module isolates the final purely formal implication in the middle-range
argument. A uniform individual Krause--Lacey sparse estimate and the finite
sparse-maximal weak theorem imply the exact logarithm-squared estimate for the
genuine all-radius frozen quadratic-Hilbert block. Thus neither truncation
radii nor the finite modulation enumeration remain hidden assumptions in the
positive endpoint assembly.
-/

open MeasureTheory
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyLacunaryBlock

open KrauseLaceyBlockHypothesis LacunaryMiddleSparseAdapter
open LacunaryMiddleBlockWeak LacunaryMiddleRange
open LacunaryOscillatoryScaling PositivePrincipalValueEndpoints
open QuadraticHilbertMaximalMeasurable


noncomputable
section

/-- Operational distribution-function version of the finite sparse maximal
lemma. The constant is universal: it is outside the quantifiers over the
family size, operator family, and individual sparse constant. -/
def HasFiniteSparseMaximalWeakBound (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ {N : ℕ} (T : Fin N → TestOperator) (A : ℝ),
    FiniteSparseMaximalHypothesis T A →
      HasWeakOneOneBound (K * A * paperLog 1 N ^ 2) (finiteMax T)

/-- The two analytic sparse inputs give the paper's exact frozen-block
Hilbert estimate. The proof includes the finite-radius approximation,
enumeration of `Q B τ`, its exact cardinality `B`, and restriction away from
the fivefold exceptional set. -/
theorem hasLogSquaredFrozenHilbertBlockWeakBounds_of_sparse
    {K A : ℝ} (hmax : HasFiniteSparseMaximalWeakBound K)
    (hKL : HasUniformFiniteRadiusQuadraticSparseBound A)
    (f : L0Infinity) (B : ℕ → ℕ) (c : ℕ) :
    HasLogSquaredFrozenHilbertBlockWeakBounds (f : ℝ → ℂ) B c (K * A) := by
  refine ⟨mul_nonneg hmax.1 hKL.1, ?_⟩
  intro k τ
  have hD : 0 ≤ K * A * paperLog 1 (B k : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg hmax.1 hKL.1) (sq_nonneg _)
  apply
    hasExtendedWeakL1Bound_frozenBlockHilbertMaxEnorm_restrict_of_uniform_finiteRadii
      f k (B k) c τ hD
  intro s
  have hweak := hmax.2
    (finiteRadiusQuadraticHilbertBlockFamily (B k) τ s) A
    (finiteRadiusQuadraticHilbertBlockFamily_sparseHypothesis hKL (B k) τ s)
  simpa only [card_Q] using hweak

/-- Uniform version on exactly the paper's `L0Infinity` input class. No
estimate on arbitrary integrable functions is required. -/
theorem hasUniformL0LogSquaredFrozenBlockWeakBounds_of_sparse
    {K A : ℝ} (hmax : HasFiniteSparseMaximalWeakBound K)
    (hKL : HasUniformFiniteRadiusQuadraticSparseBound A) :
    HasUniformL0LogSquaredFrozenBlockWeakBounds (4 * (K * A) + 128) := by
  intro f
  exact logSquaredFrozenBlockWeakBounds_of_hilbert
    f.measurable_toFun f.integrable
    (hasLogSquaredFrozenHilbertBlockWeakBounds_of_sparse
      hmax hKL f PositiveHighHeightEstimate.lacunaryHighCutoff 0)

/-- The paper-facing lacunary principal-value endpoint follows directly from
the ordinary Hilbert weak theorem and the two still-analytic sparse inputs. -/
theorem lacunary_principalValue_endpoint_of_sparse
    {CH : ℝ≥0∞} (hH : HilbertPrincipalValueClosure.HasUniformHilbertMaximalWeakBound CH)
    {K A : ℝ} (hmax : HasFiniteSparseMaximalWeakBound K)
    (hKL : HasUniformFiniteRadiusQuadraticSparseBound A) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ α : ℝ, 0 < α →
        volume {x | ENNReal.ofReal α < lacunaryPrincipalValueMaximal f x} ≤
          C * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 * paperLog 4 (‖f x‖ / α)) :=
  lacunary_principalValue_endpoint hH
    (hasUniformL0LogSquaredFrozenBlockWeakBounds_of_sparse hmax hKL)


end
end KrauseLaceyLacunaryBlock
end QuadraticCarleson
