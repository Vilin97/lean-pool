/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponent
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage

/-!
# API checks for the spaces `P_α`

The degree-zero fixture proves that a nonzero constant represents a nonzero class in `P_0`, while
a strictly negative monomial represents zero. This distinguishes the intrinsic quotient by `J`
from literal equality of representatives.

The approach-zero series has ordinal value `ω` and represents a nonzero class in `P_1`. Its class
has a principal representative of exact degree one by LM24, Remark 7.2.4. Multiplication by the
degree-zero class of one agrees with multiplication of representatives.
-/

universe v

public noncomputable section

namespace Tests

open HahnSeries
open scoped NatOrdinal

variable {K : Type v} [Field K]

section Generic

theorem one_ordinalValue_bound :
    Berarducci.ordinalValue (1 : Berarducci.Series K) < ω^ (0 + 1 : NatOrdinal) := by
  rw [Berarducci.ordinalValue_one]
  simpa using NatOrdinal.wpow_lt_wpow.mpr (zero_lt_one : (0 : NatOrdinal) < 1)

variable (K) in
/-- A nonzero constant gives a nonzero class in the intrinsic degree-zero component. -/
theorem principalComponent_zero_constant_ne_zero :
    Berarducci.principalComponentMk 0 (1 : Berarducci.Series K)
      (one_ordinalValue_bound (K := K)) ≠ 0 := by
  rw [ne_eq, Berarducci.principalComponentMk_eq_zero_iff]
  rw [Berarducci.ordinalValue_one]
  simp

def principalComponentNegativeMonomial : Berarducci.Series K :=
  HahnSeries.Nonpositive.single (-1 : ℝ) 1 (by norm_num)

theorem principalComponentNegativeMonomial_ordinalValue_eq_zero :
    Berarducci.ordinalValue (principalComponentNegativeMonomial (K := K)) = 0 := by
  apply Berarducci.ordinalValue_of_mem_negativeMonomialIdeal
  exact HahnSeries.Nonpositive.single_one_mem_negativeMonomialIdeal (by norm_num)

theorem principalComponentNegativeMonomial_ordinalValue_bound :
    Berarducci.ordinalValue (principalComponentNegativeMonomial (K := K)) <
      ω^ (0 + 1 : NatOrdinal) := by
  rw [principalComponentNegativeMonomial_ordinalValue_eq_zero]
  exact NatOrdinal.wpow_pos _

variable (K) in
/-- A nonzero series in `J` represents zero in `P_0`. -/
theorem principalComponent_zero_negativeMonomial_eq_zero :
    Berarducci.principalComponentMk 0 (principalComponentNegativeMonomial (K := K))
      (principalComponentNegativeMonomial_ordinalValue_bound (K := K)) = 0 := by
  rw [Berarducci.principalComponentMk_eq_zero_iff,
    principalComponentNegativeMonomial_ordinalValue_eq_zero]
  exact NatOrdinal.wpow_pos _

end Generic

section RationalFixture

theorem approachZero_ordinalValue_eq_omega :
    Berarducci.ordinalValue approachZeroNonpositive = NatOrdinal.of Ordinal.omega0 := by
  apply le_antisymm
  · simpa only [coe_approachZeroNonpositive, approachZero_supportOrderType] using
      Berarducci.ordinalValue_le_supportOrderType approachZeroNonpositive
  · have hone : 1 < Berarducci.ordinalValue approachZeroNonpositive := by
      apply Berarducci.one_lt_ordinalValue_of_constantCoeff_eq_zero_of_supportSup_eq_zero
      · rw [HahnSeries.Nonpositive.constantCoeff_apply, coe_approachZeroNonpositive]
        exact not_ne_iff.mp (by
          simpa [HahnSeries.mem_support] using zero_not_mem_approachZero_support)
      · exact approachZero_supportSup
    have hprincipal :=
      Berarducci.ordinalValue_isAdditivelyPrincipal_of_one_lt hone
    have honeVal : (1 : Ordinal) <
        (Berarducci.ordinalValue approachZeroNonpositive).val :=
      NatOrdinal.of_lt_iff.mp hone
    apply NatOrdinal.of_le_iff.mpr
    exact hprincipal.omega0_le_of_one_lt honeVal

theorem approachZero_ordinalValue_bound :
    Berarducci.ordinalValue approachZeroNonpositive < ω^ (1 + 1 : NatOrdinal) := by
  rw [approachZero_ordinalValue_eq_omega]
  have homega : NatOrdinal.of Ordinal.omega0 = ω^ (1 : NatOrdinal) := by
    apply NatOrdinal.val.injective
    simp only [NatOrdinal.val_of, NatOrdinal.val_wpow, NatOrdinal.val_one,
      Ordinal.opow_one]
  rw [homega]
  exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one (1 : NatOrdinal))

/-- The genuine infinite-support fixture gives a nonzero class in `P_1`. -/
theorem principalComponent_one_approachZero_ne_zero :
    Berarducci.principalComponentMk 1 approachZeroNonpositive
      approachZero_ordinalValue_bound ≠ 0 := by
  rw [ne_eq, Berarducci.principalComponentMk_eq_zero_iff,
    approachZero_ordinalValue_eq_omega]
  have homega : NatOrdinal.of Ordinal.omega0 = ω^ (1 : NatOrdinal) := by
    apply NatOrdinal.val.injective
    simp only [NatOrdinal.val_of, NatOrdinal.val_wpow, NatOrdinal.val_one,
      Ordinal.opow_one]
  rw [homega]
  exact lt_irrefl _

/-- The intrinsic class admits a principal representative of exact degree one. -/
theorem principalComponent_one_has_exact_principal_representative :
    ∃ (p : Berarducci.Series ℚ)
        (hpBound : Berarducci.ordinalValue p < ω^ (1 + 1 : NatOrdinal)),
      HahnSeries.Nonpositive.IsPrincipal p ∧
        (p : ℚ⟦ℝ⟧).degree = (1 : WithBot NatOrdinal) ∧
        Berarducci.principalComponentMk 1 p hpBound =
          Berarducci.principalComponentMk 1 approachZeroNonpositive
            approachZero_ordinalValue_bound :=
  Berarducci.exists_principal_representative_of_ne_zero 1 _
    principalComponent_one_approachZero_ne_zero

/-- Scalar multiplication by two is represented by multiplication by the corresponding constant
Hahn series on the infinite-support class. -/
theorem two_smul_principalComponent_one_approachZero :
    (2 : ℚ) • Berarducci.principalComponentMk 1 approachZeroNonpositive
        approachZero_ordinalValue_bound =
      Berarducci.principalComponentMk 1
        ((HahnSeries.Nonpositive.C : ℚ →+* Berarducci.Series ℚ) 2 *
          approachZeroNonpositive)
        (by
          simpa only [zero_add] using
            Berarducci.ordinalValue_mul_lt_wpow_add_one
              (Berarducci.ordinalValue_C_lt_wpow_one (2 : ℚ))
              approachZero_ordinalValue_bound) :=
  Berarducci.smul_principalComponentMk 1 2 approachZeroNonpositive
    approachZero_ordinalValue_bound

/-- Homogeneous multiplication sends the classes of `1` and the approach-zero series to the
class of their product in `P_1`. -/
theorem principalComponent_zero_mul_one_representation :
    Berarducci.principalComponentMul
        (Berarducci.principalComponentMk 0 (1 : Berarducci.Series ℚ)
          (one_ordinalValue_bound (K := ℚ)))
        (Berarducci.principalComponentMk 1 approachZeroNonpositive
          approachZero_ordinalValue_bound) =
      Berarducci.principalComponentMk (0 + 1) approachZeroNonpositive
        (by simpa using approachZero_ordinalValue_bound) := by
  rw [Berarducci.principalComponentMul_mk]
  rw [Berarducci.principalComponentMk_eq_iff]
  simp

end RationalFixture

end Tests
