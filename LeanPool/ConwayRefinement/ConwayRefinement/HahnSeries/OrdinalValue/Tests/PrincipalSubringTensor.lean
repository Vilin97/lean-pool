/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringTensor

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero
import Mathlib.Tactic.NormNum

/-!
# API checks for the principal graded tensor decomposition

The two-grade fixture has independently visible components in grades zero and one. Its image
therefore distinguishes the graded tensor equivalence from a construction that retains only the
degree-zero summand. The finite-support fixture is the monomial at exponent `-1`; proving that its
image is not a coefficient scalar distinguishes the factor `K(ℝ^{≤ 0})` from `K` itself.

The final round trip verifies both inverse identities on this nondegenerate element.
-/

public noncomputable section

namespace Tests

open scoped DirectSum HahnSeries NatOrdinal TensorProduct

private theorem gradedTensorApproachZero_ordinalValue_bound :
    Berarducci.ordinalValue approachZeroNonpositive < ω^ (1 + 1 : NatOrdinal) := by
  rw [Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
    approachZero_degree_eq_one]
  exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one (1 : NatOrdinal))

/-- The intrinsic degree-one class represented by the approach-zero series. -/
def gradedTensorApproachZeroLayer : Berarducci.PrincipalComponent ℚ 1 :=
  Berarducci.principalComponentMk 1 approachZeroNonpositive
    gradedTensorApproachZero_ordinalValue_bound

/-- The approach-zero degree-one class is nonzero. -/
theorem gradedTensorApproachZeroLayer_ne_zero :
    gradedTensorApproachZeroLayer ≠ 0 := by
  rw [gradedTensorApproachZeroLayer, ne_eq,
    Berarducci.principalComponentMk_eq_zero_iff,
    Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
      approachZero_degree_eq_one]
  exact lt_irrefl _

/-- The grade-zero class of the coefficient one. -/
def gradedTensorScalarLayer : Berarducci.PrincipalComponent ℚ 0 :=
  Berarducci.principalComponentScalarHom ℚ 1

/-- A principal graded element with nontrivial data in grades zero and one. -/
def gradedTensorTwoGradeElement : Berarducci.PrincipalSubring ℚ :=
  DirectSum.of _ 0 gradedTensorScalarLayer +
    DirectSum.of _ 1 gradedTensorApproachZeroLayer

/-- The two prescribed homogeneous components remain distinct in the direct sum. -/
theorem gradedTensorTwoGradeElement_components :
    gradedTensorTwoGradeElement 0 = gradedTensorScalarLayer ∧
      gradedTensorTwoGradeElement 1 = gradedTensorApproachZeroLayer := by
  simp [gradedTensorTwoGradeElement, DirectSum.of_apply]

/-- Tensoring the two-grade fixture with one preserves both homogeneous components through the
homogeneous-component equivalences. -/
theorem gradedTensorTwoGrade_components :
    Berarducci.principalSubringTensorEquiv ℚ
          (gradedTensorTwoGradeElement ⊗ₜ (1 : Berarducci.FiniteSupportRing)) 0 =
        Berarducci.principalComponentToHahnDegreeLayer ℚ 0
          gradedTensorScalarLayer ∧
      Berarducci.principalSubringTensorEquiv ℚ
          (gradedTensorTwoGradeElement ⊗ₜ (1 : Berarducci.FiniteSupportRing)) 1 =
        Berarducci.principalComponentToHahnDegreeLayer ℚ 1
          gradedTensorApproachZeroLayer := by
  constructor
  · rw [Berarducci.principalSubringTensorEquiv_tmul_apply,
      gradedTensorTwoGradeElement_components.1,
      Berarducci.principalComponentTensorEquiv_tmul, map_one, one_smul]
  · rw [Berarducci.principalSubringTensorEquiv_tmul_apply,
      gradedTensorTwoGradeElement_components.2,
      Berarducci.principalComponentTensorEquiv_tmul, map_one, one_smul]

/-- The positive-degree component survives; a degree-zero-only assembly fails this check. -/
theorem gradedTensorTwoGrade_positive_component_ne_zero :
    Berarducci.principalSubringTensorEquiv ℚ
        (gradedTensorTwoGradeElement ⊗ₜ (1 : Berarducci.FiniteSupportRing)) 1 ≠ 0 := by
  rw [gradedTensorTwoGrade_components.2]
  intro hzero
  apply gradedTensorApproachZeroLayer_ne_zero
  apply Berarducci.principalComponentToHahnDegreeLayer_injective ℚ 1
  simpa only [map_zero] using hzero

/-- The nonpositive exponent `-1` used by the finite-support factor fixture. -/
def gradedTensorExponentNegOne : {g : ℝ // g ≤ 0} := ⟨-1, by norm_num⟩

/-- The finite-support monomial at exponent `-1`. -/
def gradedTensorFiniteMonomial : Berarducci.FiniteSupportRing (K := ℚ) :=
  HahnSeries.Nonpositive.finiteSupportMonomial (K := ℚ) gradedTensorExponentNegOne

/-- The negative-exponent monomial is not a constant finite-support series. -/
theorem gradedTensorFiniteMonomial_not_scalar (k : ℚ) :
    gradedTensorFiniteMonomial ≠
      HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k := by
  intro h
  have hcoeff := congrArg
    (fun p : Berarducci.FiniteSupportRing (K := ℚ) ↦
      (((p : Berarducci.Series ℚ) : ℚ⟦ℝ⟧).coeff (-1))) h
  simp [gradedTensorFiniteMonomial, gradedTensorExponentNegOne,
    HahnSeries.Nonpositive.coe_finiteSupportMonomial,
    HahnSeries.Nonpositive.coe_finiteSupportScalarHom,
    HahnSeries.C_apply] at hcoeff

/-- The global equivalence retains the full finite-support factor rather than only coefficient
scalars. -/
theorem gradedTensorFiniteSupportFactor_not_scalar (k : ℚ) :
    Berarducci.principalSubringTensorEquiv ℚ
        (1 ⊗ₜ gradedTensorFiniteMonomial) ≠
      algebraMap ℚ (Berarducci.DegreeGraded ℚ) k := by
  rw [Berarducci.principalSubringTensorEquiv_one_tmul]
  intro h
  apply gradedTensorFiniteMonomial_not_scalar k
  apply Berarducci.finiteSupportGradedEmbedding_injective ℚ
  calc
    Berarducci.finiteSupportGradedEmbedding ℚ gradedTensorFiniteMonomial =
        algebraMap ℚ (Berarducci.DegreeGraded ℚ) k := h
    _ = Berarducci.finiteSupportGradedEmbedding ℚ
          (algebraMap ℚ (Berarducci.FiniteSupportRing (K := ℚ)) k) :=
      ((Berarducci.finiteSupportGradedEmbedding ℚ).commutes k).symm
    _ = Berarducci.finiteSupportGradedEmbedding ℚ
          (HahnSeries.Nonpositive.finiteSupportScalarHom (G := ℝ) k) := rfl

/-- The inverse equivalence recovers the positive-degree tensor component through the
homogeneous-component
inverse, without unfolding either equivalence. -/
theorem gradedTensor_inverse_positive_component :
    Berarducci.principalSubringTensorComponent ℚ 1
        ((Berarducci.principalSubringTensorEquiv ℚ).symm
          (Berarducci.principalSubringTensorEquiv ℚ
            (gradedTensorTwoGradeElement ⊗ₜ gradedTensorFiniteMonomial))) =
      gradedTensorApproachZeroLayer ⊗ₜ gradedTensorFiniteMonomial := by
  rw [Berarducci.principalSubringTensorComponent_symm_apply,
    Berarducci.principalSubringTensorEquiv_component,
    LinearEquiv.symm_apply_apply,
    Berarducci.principalSubringTensorComponent_tmul,
    gradedTensorTwoGradeElement_components.2]

/-- The opaque global equivalence is invertible on the nondegenerate two-grade,
negative-exponent fixture. -/
theorem gradedTensor_roundtrip :
    (Berarducci.principalSubringTensorEquiv ℚ).symm
        (Berarducci.principalSubringTensorEquiv ℚ
          (gradedTensorTwoGradeElement ⊗ₜ gradedTensorFiniteMonomial)) =
      gradedTensorTwoGradeElement ⊗ₜ gradedTensorFiniteMonomial :=
  (Berarducci.principalSubringTensorEquiv ℚ).symm_apply_apply _

end Tests
