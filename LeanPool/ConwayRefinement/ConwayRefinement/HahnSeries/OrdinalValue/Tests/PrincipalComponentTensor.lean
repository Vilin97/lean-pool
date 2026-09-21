/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponentTensor
public import Mathlib.LinearAlgebra.TensorProduct.Basis

import Mathlib.Tactic.NormNum

/-!
# API checks for extension of scalars on a homogeneous component

The fixture has two distinct finite-support exponents and a nonzero infinite-support coefficient
in `P_1`. Its two tensor coordinates are checked independently. The forward map agrees with
multiplication of representatives, and both inverse identities hold on the fixture.
-/

public noncomputable section

namespace Tests

open scoped HahnSeries NatOrdinal TensorProduct

private theorem approachZero_ordinalValue_bound_for_tensor :
    Berarducci.ordinalValue approachZeroNonpositive < ω^ (1 + 1 : NatOrdinal) := by
  rw [Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
    approachZero_degree_eq_one]
  exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one (1 : NatOrdinal))

/-- The intrinsic degree-one class of the approach-zero series. -/
def approachZeroPrincipalComponent : Berarducci.PrincipalComponent ℚ 1 :=
  Berarducci.principalComponentMk 1 approachZeroNonpositive
    approachZero_ordinalValue_bound_for_tensor

private theorem approachZeroPrincipalComponent_ne_zero :
    approachZeroPrincipalComponent ≠ 0 := by
  rw [approachZeroPrincipalComponent, ne_eq,
    Berarducci.principalComponentMk_eq_zero_iff,
    Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
      approachZero_degree_eq_one]
  exact lt_irrefl _

/-- The exponent zero in the nonpositive real cone. -/
def tensorExponentZero : {g : ℝ // g ≤ 0} := ⟨0, le_rfl⟩

/-- The exponent negative one in the nonpositive real cone. -/
def tensorExponentNegOne : {g : ℝ // g ≤ 0} := ⟨-1, by norm_num⟩

/-- A tensor with nonzero coordinates at the two distinct exponents `0` and `-1`. -/
def approachZeroTwoExponentTensor :
    Berarducci.PrincipalComponent ℚ 1 ⊗[ℚ]
      Berarducci.FiniteSupportRing (K := ℚ) :=
  approachZeroPrincipalComponent ⊗ₜ
      HahnSeries.Nonpositive.finiteSupportMonomial (K := ℚ) tensorExponentZero +
    ((2 : ℚ) • approachZeroPrincipalComponent) ⊗ₜ
      HahnSeries.Nonpositive.finiteSupportMonomial (K := ℚ) tensorExponentNegOne

/-- Both coordinates of the two-exponent fixture are retained by the canonical tensor-basis
presentation. -/
theorem approachZeroTwoExponentTensor_coordinates :
    TensorProduct.equivFinsuppOfBasisRight
        (HahnSeries.Nonpositive.finiteSupportBasis (G := ℝ) (K := ℚ))
        approachZeroTwoExponentTensor tensorExponentZero =
      approachZeroPrincipalComponent ∧
    TensorProduct.equivFinsuppOfBasisRight
        (HahnSeries.Nonpositive.finiteSupportBasis (G := ℝ) (K := ℚ))
        approachZeroTwoExponentTensor tensorExponentNegOne =
      (2 : ℚ) • approachZeroPrincipalComponent := by
  constructor <;>
    simp [approachZeroTwoExponentTensor,
      HahnSeries.Nonpositive.finiteSupportBasis_repr_apply,
      HahnSeries.Nonpositive.coe_finiteSupportMonomial,
      tensorExponentZero, tensorExponentNegOne]

/-- The two-exponent tensor is nonzero; in particular, it is not a one-term presentation in
which one of the two monomials has silently been discarded. -/
theorem approachZeroTwoExponentTensor_ne_zero :
    approachZeroTwoExponentTensor ≠ 0 := by
  intro hzero
  have hcoordinates := approachZeroTwoExponentTensor_coordinates.1
  rw [hzero, map_zero, Finsupp.zero_apply] at hcoordinates
  exact approachZeroPrincipalComponent_ne_zero hcoordinates.symm

/-- The public extension-of-scalars equivalence sends the two-exponent fixture to the sum of
the two corresponding homogeneous products. -/
theorem approachZeroTwoExponentTensor_forward :
    Berarducci.principalComponentTensorEquiv ℚ 1
        approachZeroTwoExponentTensor =
      HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv ℚ
          (HahnSeries.Nonpositive.finiteSupportMonomial
            (K := ℚ) tensorExponentZero) •
        Berarducci.principalComponentToHahnDegreeLayer ℚ 1
          approachZeroPrincipalComponent +
      HahnSeries.Nonpositive.degreeFiniteSupportResidueEquiv ℚ
          (HahnSeries.Nonpositive.finiteSupportMonomial
            (K := ℚ) tensorExponentNegOne) •
        Berarducci.principalComponentToHahnDegreeLayer ℚ 1
          ((2 : ℚ) • approachZeroPrincipalComponent) := by
  rw [approachZeroTwoExponentTensor, map_add,
    Berarducci.principalComponentTensorEquiv_tmul,
    Berarducci.principalComponentTensorEquiv_tmul]

/-- The representative formula sends the negative-one pure tensor to the degree-one class of
the translated approach-zero series. -/
theorem approachZeroTensorNegOne_representative :
    Berarducci.principalComponentTensorMap ℚ 1
        (approachZeroPrincipalComponent ⊗ₜ
          HahnSeries.Nonpositive.finiteSupportMonomial
            (K := ℚ) tensorExponentNegOne) =
      Berarducci.degreeLayerMk 1
        (((HahnSeries.Nonpositive.finiteSupportMonomial
          (K := ℚ) tensorExponentNegOne :
            Berarducci.FiniteSupportRing (K := ℚ)) : Berarducci.Series ℚ) *
              approachZeroNonpositive) (by
          rw [HahnSeries.Nonpositive.degree_mul, approachZero_degree_eq_one]
          exact (add_le_add (by
            exact (HahnSeries.degree_eq_zero.mpr ⟨by simp,
              (HahnSeries.Nonpositive.mem_finiteSupportSubring_iff _).mp
                (HahnSeries.Nonpositive.finiteSupportMonomial
                  (K := ℚ) tensorExponentNegOne).2⟩).le) le_rfl).trans_eq
                    (zero_add _)) := by
  exact Berarducci.principalComponentTensorMap_principal_monomial 1 approachZeroNonpositive
    approachZero_isPrincipal
      approachZero_degree_eq_one approachZero_ordinalValue_bound_for_tensor tensorExponentNegOne

/-- The public inverse is a genuine inverse on the nontrivial two-exponent fixture. -/
theorem approachZeroTwoExponentTensor_roundtrip :
    (Berarducci.principalComponentTensorEquiv ℚ 1).symm
        (Berarducci.principalComponentTensorEquiv ℚ 1
          approachZeroTwoExponentTensor) =
      approachZeroTwoExponentTensor :=
  (Berarducci.principalComponentTensorEquiv ℚ 1).symm_apply_apply _

end Tests
