/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionExhaustiveProductFormula
public import Mathlib.NumberTheory.ClassNumber.FunctionField
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm

/-!
# Affine ideal degrees in a finite function field

The finite class group of the normalization of `K[X]` controls ideal classes,
but an affine ideal zeta series also needs finite coefficient sets.  This file
provides that missing finiteness layer for a finite separable extension of
`K(X)` over a finite field `K`.

First, every nonzero quotient of `K[X]` is finite: a nonzero ideal contains a
monic polynomial up to multiplication by a unit, and its quotient maps onto
the original quotient.  Module finiteness transfers this property to the
normalization of `K[X]` in the function field.  For a nonzero ideal `I`, its
affine degree is then the `K`-dimension of the quotient by `I`.  Consequently

`cardQuot I = |K| ^ degree(I)`,

and Mathlib's bounded-quotient-cardinality theorem makes the ideals of each
fixed degree into a finite type.  No Riemann--Roch or Hasse--Weil input is used.
-/

@[expose] public section

open scoped Polynomial nonZeroDivisors

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (K : Type*) [Field K] [Fintype K]

omit [Fintype K] in
/-- The polynomial ring over a finite field has finite quotients. -/
theorem ratFuncPolynomial_hasFiniteQuotients [Finite K] :
    Ring.HasFiniteQuotients K[X] := by
  constructor
  intro I hI
  obtain ⟨f, hfI, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  let g : K[X] := f * Polynomial.C f.leadingCoeff⁻¹
  have hgmonic : g.Monic := Polynomial.monic_mul_leadingCoeff_inv hf0
  have hgI : g ∈ I := by
    exact I.mul_mem_right (Polynomial.C f.leadingCoeff⁻¹) hfI
  have hspan : Ideal.span ({g} : Set K[X]) ≤ I := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hgI
  let : Module.Finite K (K[X] ⧸ Ideal.span ({g} : Set K[X])) :=
    hgmonic.finite_quotient
  let : Finite (K[X] ⧸ Ideal.span ({g} : Set K[X])) :=
    Module.finite_of_finite K
  exact Finite.of_surjective (Ideal.Quotient.factor hspan)
    (Ideal.Quotient.factor_surjective hspan)

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) affineIdealPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance affineIdealPolynomialTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance affineIdealClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance affineIdealClosureConstantAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure K L) :=
  RingHom.toAlgebra ((algebraMap K[X]
    (RatFuncFiniteIntegralClosure K L)).comp (algebraMap K K[X]))

local instance affineIdealClosureConstantTower :
    IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

omit [Fintype K] in
/-- The normalization of `K[X]` in a finite separable extension of `K(X)` has
finite quotients. -/
theorem ratFuncFiniteIntegralClosure_hasFiniteQuotients [Finite K] :
    Ring.HasFiniteQuotients (RatFuncFiniteIntegralClosure K L) := by
  let : Ring.HasFiniteQuotients K[X] :=
    ratFuncPolynomial_hasFiniteQuotients K
  exact Ring.HasFiniteQuotients.of_module_finite K[X]
    (RatFuncFiniteIntegralClosure K L)

omit [Fintype K] in
/-- The affine ideal class group is finite.  This is the function-field class
number theorem from Mathlib, stated at the normalization used by BGS. -/
theorem finiteExtensionAffineClassGroup_finite [Finite K] :
    Finite (ClassGroup (RatFuncFiniteIntegralClosure K L)) := by
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (ClassGroup (RatFuncFiniteIntegralClosure K L)) :=
    inferInstance
  exact Fintype.finite inferInstance

/-- Nonzero affine ideals in the normalization of `K[X]` in `L`. -/
abbrev FiniteExtensionAffineIdeal :=
  (Ideal (RatFuncFiniteIntegralClosure K L))⁰

/-- The degree of a nonzero affine ideal is the `K`-dimension of its quotient. -/
def finiteExtensionAffineIdealDegree
    (I : FiniteExtensionAffineIdeal K L) : ℕ := by
  letI : Ring.HasFiniteQuotients (RatFuncFiniteIntegralClosure K L) :=
    ratFuncFiniteIntegralClosure_hasFiniteQuotients K L
  have hI : (I : Ideal (RatFuncFiniteIntegralClosure K L)) ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.property
  letI : Finite (RatFuncFiniteIntegralClosure K L ⧸
      (I : Ideal (RatFuncFiniteIntegralClosure K L))) :=
    Ring.HasFiniteQuotients.finiteQuotient hI
  letI : Module.Finite K (RatFuncFiniteIntegralClosure K L ⧸
      (I : Ideal (RatFuncFiniteIntegralClosure K L))) :=
    Module.Finite.of_finite
  exact Module.finrank K (RatFuncFiniteIntegralClosure K L ⧸
    (I : Ideal (RatFuncFiniteIntegralClosure K L)))

/-- Quotient cardinality is the cardinality of the constant field raised to
the affine ideal degree. -/
theorem finiteExtensionAffineIdeal_cardQuot_eq_card_pow_degree
    (I : FiniteExtensionAffineIdeal K L) :
    (I : Ideal (RatFuncFiniteIntegralClosure K L)).cardQuot =
      Fintype.card K ^ finiteExtensionAffineIdealDegree K L I := by
  let : Ring.HasFiniteQuotients (RatFuncFiniteIntegralClosure K L) :=
    ratFuncFiniteIntegralClosure_hasFiniteQuotients K L
  have hI : (I : Ideal (RatFuncFiniteIntegralClosure K L)) ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.property
  let : Finite (RatFuncFiniteIntegralClosure K L ⧸
      (I : Ideal (RatFuncFiniteIntegralClosure K L))) :=
    Ring.HasFiniteQuotients.finiteQuotient hI
  let : Module.Finite K (RatFuncFiniteIntegralClosure K L ⧸
      (I : Ideal (RatFuncFiniteIntegralClosure K L))) :=
    Module.Finite.of_finite
  rw [Submodule.cardQuot_apply, finiteExtensionAffineIdealDegree,
    ← Nat.card_eq_fintype_card]
  exact Module.natCard_eq_pow_finrank

/-- An affine ideal has degree zero exactly when it is the unit ideal. -/
theorem finiteExtensionAffineIdealDegree_eq_zero_iff
    (I : FiniteExtensionAffineIdeal K L) :
    finiteExtensionAffineIdealDegree K L I = 0 ↔
      (I : Ideal (RatFuncFiniteIntegralClosure K L)) = ⊤ := by
  constructor
  · intro hdegree
    apply Submodule.cardQuot_eq_one_iff.mp
    rw [finiteExtensionAffineIdeal_cardQuot_eq_card_pow_degree K L I,
      hdegree, pow_zero]
  · intro hI
    let : Ring.HasFiniteQuotients (RatFuncFiniteIntegralClosure K L) :=
      ratFuncFiniteIntegralClosure_hasFiniteQuotients K L
    have hne : (I : Ideal (RatFuncFiniteIntegralClosure K L)) ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact mem_nonZeroDivisors_iff_ne_zero.mp I.property
    let : Finite (RatFuncFiniteIntegralClosure K L ⧸
        (I : Ideal (RatFuncFiniteIntegralClosure K L))) :=
      Ring.HasFiniteQuotients.finiteQuotient hne
    let : Module.Finite K (RatFuncFiniteIntegralClosure K L ⧸
        (I : Ideal (RatFuncFiniteIntegralClosure K L))) :=
      Module.Finite.of_finite
    rw [finiteExtensionAffineIdealDegree, hI]
    exact Module.finrank_zero_of_subsingleton

/-- There are only finitely many nonzero affine ideals of any prescribed
degree. -/
theorem finite_setOf_finiteExtensionAffineIdealDegree_eq (n : ℕ) :
    {I : FiniteExtensionAffineIdeal K L |
      finiteExtensionAffineIdealDegree K L I = n}.Finite := by
  let : Ring.HasFiniteQuotients (RatFuncFiniteIntegralClosure K L) :=
    ratFuncFiniteIntegralClosure_hasFiniteQuotients K L
  apply Set.Finite.of_injOn
    (f := fun I : FiniteExtensionAffineIdeal K L =>
      (I : Ideal (RatFuncFiniteIntegralClosure K L)))
    (t := {J : Ideal (RatFuncFiniteIntegralClosure K L) |
      J.cardQuot ≤ Fintype.card K ^ n})
  · intro I hI
    simp only [Set.mem_ofPred_eq] at hI ⊢
    rw [finiteExtensionAffineIdeal_cardQuot_eq_card_pow_degree K L I, hI]
  · intro I _ J _ hIJ
    exact Subtype.ext hIJ
  · exact Ring.HasFiniteQuotients.finite_cardQuot_le _

/-- A finite indexing type for nonzero affine ideals of degree `n`. -/
noncomputable instance finiteExtensionAffineIdealsOfDegree_fintype (n : ℕ) :
    Fintype {I : FiniteExtensionAffineIdeal K L //
      finiteExtensionAffineIdealDegree K L I = n} :=
  (finite_setOf_finiteExtensionAffineIdealDegree_eq K L n).fintype

/-- The number of nonzero affine ideals of degree `n`; this is the natural
coefficient sequence for the affine ideal zeta series. -/
noncomputable def finiteExtensionAffineIdealCount (n : ℕ) : ℕ :=
  Fintype.card {I : FiniteExtensionAffineIdeal K L //
    finiteExtensionAffineIdealDegree K L I = n}

end

end BGS.HasseWeil
