/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalSubringFraction

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero

/-!
# API checks for the principal graded fraction field

The positive-degree fixture is the grade-one class of the approach-zero series. Its image in
`Frac(P̂)` is nonzero and does not belong to the image of the coefficient field. This separates
relative algebraic closure from the incorrect assertion that `Frac(P̂) = K`.

The inverse identity is also verified on a nonconstant fraction, rather than only on elements of
the underlying ring `P̂`.
-/

open scoped DirectSum HahnSeries NatOrdinal

namespace Tests

public noncomputable section

local instance principalSubringFractionClientSelfSMul :
    SMul (Berarducci.PrincipalSubring ℚ)
      (Berarducci.PrincipalSubringFractionField ℚ) :=
  (Berarducci.principalSubringFractionSelfAlgebra ℚ).toSMul

local instance principalSubringFractionClientSelfAlgebra :
    Algebra (Berarducci.PrincipalSubring ℚ)
      (Berarducci.PrincipalSubringFractionField ℚ) :=
  Berarducci.principalSubringFractionSelfAlgebra ℚ

local instance principalSubringFractionClientSMul :
    SMul ℚ (Berarducci.PrincipalSubringFractionField ℚ) :=
  (Berarducci.principalSubringFractionAlgebra ℚ).toSMul

local instance principalSubringFractionClientAlgebra :
    Algebra ℚ (Berarducci.PrincipalSubringFractionField ℚ) :=
  Berarducci.principalSubringFractionAlgebra ℚ

local instance principalSubringFractionClientIsScalarTower :
    IsScalarTower ℚ (Berarducci.PrincipalSubring ℚ)
      (Berarducci.PrincipalSubringFractionField ℚ) :=
  Berarducci.principalSubringFraction_isScalarTower ℚ

private theorem fractionApproachZero_ordinalValue_bound :
    Berarducci.ordinalValue approachZeroNonpositive < ω^ (1 + 1 : NatOrdinal) := by
  rw [Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
    approachZero_degree_eq_one]
  exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one (1 : NatOrdinal))

/-- The intrinsic degree-one class represented by the approach-zero series. -/
def fractionApproachZeroLayer : Berarducci.PrincipalComponent ℚ 1 :=
  Berarducci.principalComponentMk 1 approachZeroNonpositive
    fractionApproachZero_ordinalValue_bound

/-- The approach-zero degree-one class is nonzero. -/
theorem fractionApproachZeroLayer_ne_zero :
    fractionApproachZeroLayer ≠ 0 := by
  rw [fractionApproachZeroLayer, ne_eq,
    Berarducci.principalComponentMk_eq_zero_iff,
    Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
      approachZero_degree_eq_one]
  exact lt_irrefl _

/-- The homogeneous principal graded element represented by the approach-zero series. -/
def fractionPositiveDegree : Berarducci.PrincipalSubring ℚ :=
  DirectSum.of _ 1 fractionApproachZeroLayer

@[simp]
theorem fractionPositiveDegree_apply_one :
    fractionPositiveDegree 1 = fractionApproachZeroLayer := by
  simp [fractionPositiveDegree]

/-- The positive-degree fixture is nonzero in `P̂`. -/
theorem fractionPositiveDegree_ne_zero :
    fractionPositiveDegree ≠ 0 := by
  rw [fractionPositiveDegree,
    ← map_zero (DirectSum.of (Berarducci.PrincipalComponent ℚ) 1)]
  exact (DirectSum.of_injective 1).ne
    fractionApproachZeroLayer_ne_zero

/-- No coefficient scalar equals the positive-degree fixture. -/
theorem fractionPositiveDegree_not_scalar (k : ℚ) :
    fractionPositiveDegree ≠
      algebraMap ℚ (Berarducci.PrincipalSubring ℚ) k := by
  intro hscalar
  have hscalarZero :
      (algebraMap ℚ (Berarducci.PrincipalSubring ℚ) k) 1 = 0 := by
    rw [Berarducci.principalSubring_algebraMap_apply,
      DirectSum.of_apply]
    simp
  have hcomponent :=
    congrArg (fun x : Berarducci.PrincipalSubring ℚ ↦ x 1) hscalar
  rw [fractionPositiveDegree_apply_one, hscalarZero] at hcomponent
  exact fractionApproachZeroLayer_ne_zero hcomponent

/-- The image of the positive-degree fixture in the principal graded fraction field. -/
def fractionPositiveDegreeImage :
    Berarducci.PrincipalSubringFractionField ℚ :=
  Berarducci.principalSubringToFraction ℚ fractionPositiveDegree

/-- The positive-degree fixture remains nonzero in the fraction field. -/
theorem fractionPositiveDegreeImage_ne_zero :
    fractionPositiveDegreeImage ≠ 0 := by
  intro hzero
  apply fractionPositiveDegree_ne_zero
  apply Berarducci.principalSubringToFraction_injective ℚ
  simpa only [fractionPositiveDegreeImage, map_zero] using hzero

/-- The nonzero fixture admits the localization representation used at the start of LM24,
Lemma 6.3.3. -/
theorem fractionPositiveDegreeImage_exists_mk :
    ∃ (B : Berarducci.PrincipalSubring ℚ)
      (C : nonZeroDivisors (Berarducci.PrincipalSubring ℚ)),
      B ≠ 0 ∧ fractionPositiveDegreeImage =
        Berarducci.principalSubringFractionMk B C :=
  Berarducci.principalSubringFraction_exists_mk_of_ne_zero
    fractionPositiveDegreeImage_ne_zero

/-- The public localization-map equation identifies the fixture with its fraction `B / 1`. -/
theorem fractionPositiveDegree_toFraction_eq_mk :
    Berarducci.principalSubringToFraction ℚ
        fractionPositiveDegree =
      Berarducci.principalSubringFractionMk
        fractionPositiveDegree
        (1 : nonZeroDivisors (Berarducci.PrincipalSubring ℚ)) :=
  Berarducci.principalSubringToFraction_apply_eq_mk _

/-- The exposed scalar tower makes the two scalar actions on the fraction field compatible. -/
theorem fractionScalarTower_smul_assoc (k : ℚ) (B : Berarducci.PrincipalSubring ℚ)
    (x : Berarducci.PrincipalSubringFractionField ℚ) :
    (k • B) • x = k • (B • x) :=
  smul_assoc k B x

/-- The principal graded fraction field strictly contains the image of the coefficient field. -/
theorem fractionPositiveDegreeImage_not_scalar :
    fractionPositiveDegreeImage ∉
      (algebraMap ℚ
        (Berarducci.PrincipalSubringFractionField ℚ)).range := by
  rintro ⟨k, hk⟩
  apply fractionPositiveDegree_not_scalar k
  apply Berarducci.principalSubringToFraction_injective ℚ
  calc
    Berarducci.principalSubringToFraction ℚ fractionPositiveDegree =
        fractionPositiveDegreeImage := rfl
    _ = algebraMap ℚ (Berarducci.PrincipalSubringFractionField ℚ) k := hk.symm
    _ = Berarducci.principalSubringToFraction ℚ
        (algebraMap ℚ (Berarducci.PrincipalSubring ℚ) k) :=
      Berarducci.principalSubringFraction_algebraMap_apply k

/-- The nonzero positive-degree element has a multiplicative inverse in `Frac(P̂)`. -/
theorem fractionPositiveDegreeImage_mul_inv :
    fractionPositiveDegreeImage *
        fractionPositiveDegreeImage⁻¹ = 1 :=
  mul_inv_cancel₀ fractionPositiveDegreeImage_ne_zero

end

end Tests
