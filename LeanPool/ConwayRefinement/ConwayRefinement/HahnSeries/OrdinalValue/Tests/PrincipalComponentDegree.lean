/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Tests.PrincipalComponent
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponentDegree

/-!
# API checks for the two presentations of `P_α`

The approach-zero series supplies a nonzero principal class of exact Hahn degree one. This module
places that class in the source subspace of the degree-graded component and checks that
the canonical linear equivalence sends it to the same representative in the intrinsic quotient
`J_{ω²} / J_ω`.

Multiplying the class by itself exercises two genuinely infinite principal representatives. The
compiled checks identify the underlying product in the degree-graded component and
verify that the equivalence commutes with homogeneous multiplication into degree `1 + 1`.
-/

public noncomputable section

namespace Tests

open HahnSeries
open scoped NatOrdinal

/-- The source homogeneous class of the approach-zero series in degree one. -/
def approachZeroPrincipalDegreeClass :
    Berarducci.principalDegreeClasses ℚ 1 := by
  refine ⟨Berarducci.degreeLayerMk 1 approachZeroNonpositive
    approachZero_degree_eq_one.le, ?_⟩
  rw [Berarducci.mem_principalDegreeClasses_iff,
    Berarducci.isPrincipalDegreeClass_iff]
  exact Or.inr ⟨approachZeroNonpositive, approachZero_isPrincipal,
    approachZero_degree_eq_one, rfl⟩

/-- The underlying class in the degree-graded ring has the expected representative. -/
@[simp]
theorem coe_approachZeroPrincipalDegreeClass :
    (approachZeroPrincipalDegreeClass :
      (HahnSeries.Nonpositive.degreeValuation ℚ).Component 1) =
        Berarducci.degreeLayerMk 1 approachZeroNonpositive
          approachZero_degree_eq_one.le :=
  (rfl)

/-- The approach-zero class is nonzero in the source degree-one component. -/
theorem approachZeroPrincipalDegreeClass_ne_zero :
    approachZeroPrincipalDegreeClass ≠ 0 := by
  intro hzero
  have hzero' := congrArg Subtype.val hzero
  rw [coe_approachZeroPrincipalDegreeClass] at hzero'
  have hlt := (Berarducci.degreeLayerMk_eq_zero_iff 1
    approachZeroNonpositive approachZero_degree_eq_one.le).mp hzero'
  rw [approachZero_degree_eq_one] at hlt
  exact lt_irrefl (1 : WithBot NatOrdinal) hlt

/-- The canonical equivalence sends the source class to the same intrinsic representative. -/
theorem approachZeroPrincipalDegreeClass_equiv :
    Berarducci.principalDegreeClassesEquivPrincipalComponent ℚ 1
        approachZeroPrincipalDegreeClass =
      Berarducci.principalComponentMk 1 approachZeroNonpositive
        approachZero_ordinalValue_bound := by
  rw [Berarducci.principalDegreeClassesEquivPrincipalComponent_apply,
    coe_approachZeroPrincipalDegreeClass,
    Berarducci.degreeLayerToPrincipalComponent_mk]

/-- The canonical equivalence commutes with a nontrivial coefficient scalar on the infinite
approach-zero class. -/
theorem approachZeroPrincipalDegreeClass_equiv_smul :
    Berarducci.principalDegreeClassesEquivPrincipalComponent ℚ 1
        ((2 : ℚ) • approachZeroPrincipalDegreeClass) =
      (2 : ℚ) • Berarducci.principalDegreeClassesEquivPrincipalComponent ℚ 1
        approachZeroPrincipalDegreeClass :=
  map_smul (Berarducci.principalDegreeClassesEquivPrincipalComponent ℚ 1)
    (2 : ℚ) approachZeroPrincipalDegreeClass

/-- On underlying degree classes, scalar multiplication by two is multiplication of the
infinite-support representative by the constant Hahn series `2`. -/
theorem coe_two_smul_approachZeroPrincipalDegreeClass :
    ((2 : ℚ) • approachZeroPrincipalDegreeClass :
      (HahnSeries.Nonpositive.degreeValuation ℚ).Component 1) =
        Berarducci.degreeLayerMk 1
          ((HahnSeries.Nonpositive.C : ℚ →+* Berarducci.Series ℚ) 2 *
            approachZeroNonpositive)
          (by
            rw [HahnSeries.Nonpositive.degree_mul,
              Berarducci.degree_C_eq_zero_of_ne (by norm_num),
              approachZero_degree_eq_one, zero_add]
            exact le_rfl) := by
  rw [coe_approachZeroPrincipalDegreeClass, Berarducci.smul_degreeLayerMk]

/-- Multiplication in the source component is represented by the square of the approach-zero series.
-/
theorem approachZeroPrincipalDegreeClass_mul_coe :
    (Berarducci.principalDegreeClassesMul
        approachZeroPrincipalDegreeClass
        approachZeroPrincipalDegreeClass :
      (HahnSeries.Nonpositive.degreeValuation ℚ).Component (1 + 1)) =
        Berarducci.degreeLayerMk (1 + 1)
          (approachZeroNonpositive * approachZeroNonpositive) (by
            rw [HahnSeries.Nonpositive.degree_mul, approachZero_degree_eq_one,
              WithBot.coe_add]
            exact le_rfl) := by
  rw [Berarducci.coe_principalDegreeClassesMul]
  exact Berarducci.degreeLayerMk_mul approachZeroNonpositive
    approachZeroNonpositive approachZero_degree_eq_one.le
    approachZero_degree_eq_one.le

/-- The source-to-intrinsic equivalence commutes with the nonconstant degree-one product. -/
theorem approachZeroPrincipalDegreeClass_mul_equiv :
    Berarducci.principalDegreeClassesEquivPrincipalComponent ℚ (1 + 1)
        (Berarducci.principalDegreeClassesMul
          approachZeroPrincipalDegreeClass
          approachZeroPrincipalDegreeClass) =
      Berarducci.principalComponentMul
        (Berarducci.principalDegreeClassesEquivPrincipalComponent ℚ 1
          approachZeroPrincipalDegreeClass)
        (Berarducci.principalDegreeClassesEquivPrincipalComponent ℚ 1
          approachZeroPrincipalDegreeClass) :=
  Berarducci.principalDegreeClassesEquivPrincipalComponent_mul _ _

end Tests
