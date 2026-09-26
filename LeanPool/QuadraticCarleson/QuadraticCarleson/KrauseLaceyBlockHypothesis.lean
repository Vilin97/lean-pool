/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleSparseAdapter

/-!
# The exact Krause--Lacey input for a finite modulation block

This file records the precise output that the analytic Krause--Lacey branch
must supply for the already-constructed finite-radius test operators, and
proves that it gives the abstract finite-family hypothesis used by the
logarithmic sparse-maximal lemma. It is deliberately below the desired weak
endpoint: it asks only for the individual uniform sparse `(1,p)` estimate.
-/

@[expose] public section

open Function MeasureTheory

namespace QuadraticCarleson
namespace KrauseLaceyBlockHypothesis

open KrauseLaceyFiniteRadiusAdapter LacunaryMiddleSparseAdapter
open LacunaryMiddleRange


noncomputable
section

/-- Uniform individual-operator form of the degree-two Krause--Lacey sparse
estimate, restricted to the finite-radius operators used in the limiting
argument. The constant is independent of modulation and of the finite set
of truncation radii. -/
def HasUniformFiniteRadiusQuadraticSparseBound (A : ℝ) : Prop :=
  0 ≤ A ∧ ∀ (lam : ℝ), lam ≠ 0 → ∀ s : Finset
      QuadraticHilbertMaximalMeasurable.densePositiveRadii,
    (∀ f : L0Infinity,
      LocallyIntegrable (finiteRadiusQuadraticHilbertMaxTestOperator lam s f) volume) ∧
    ∀ p : ℝ, 1 < p → p < 2 →
      IsSparseOnePBounded p
          (absoluteValueOperator (finiteRadiusQuadraticHilbertMaxTestOperator lam s)) ∧
        sparseOnePNorm p
            (absoluteValueOperator (finiteRadiusQuadraticHilbertMaxTestOperator lam s)) ≤
          A * holderConjugate p

/-- The uniform individual Krause--Lacey estimate supplies exactly the
finite-family hypothesis for every paper modulation block. -/
theorem finiteRadiusQuadraticHilbertBlockFamily_sparseHypothesis
    {A : ℝ} (hA : HasUniformFiniteRadiusQuadraticSparseBound A)
    (B : ℕ) (τ : ℤ)
    (s : Finset QuadraticHilbertMaximalMeasurable.densePositiveRadii) :
    FiniteSparseMaximalHypothesis
      (finiteRadiusQuadraticHilbertBlockFamily B τ s) A := by
  refine ⟨hA.1, ?_, ?_, ?_⟩
  · intro j f
    exact (hA.2 (dyadicModulation (modulationBlockIndex B τ j))
      (dyadicModulation_pos (modulationBlockIndex B τ j)).ne' s).1 f
  · intro j
    exact finiteRadiusQuadraticHilbertBlockFamily_isSublinear B τ s j
  · intro p hp hp2 j
    exact (hA.2 (dyadicModulation (modulationBlockIndex B τ j))
      (dyadicModulation_pos (modulationBlockIndex B τ j)).ne' s).2 p hp hp2

/-- The family cardinality in the abstract sparse lemma is literally the
paper's block length `B`. -/
theorem finiteRadiusQuadraticHilbertBlockFamily_cardinality
    (B : ℕ) (τ : ℤ) : (Q B τ).card = B :=
  card_Q B τ


end
end KrauseLaceyBlockHypothesis
end QuadraticCarleson
