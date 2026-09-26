/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.BaseChange
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.StableInterval

/-!
# API checks for coefficient base change

Coefficient extension is exercised where it is supposed to be rigid: it fixes the support, hence
the ordinal value, and it carries constants to constants, so a nonzero constant series keeps its
ordinal value along any extension of fields. The zero series is checked separately, since an empty
support is the boundary case of the support computations.

On the homogeneous components, the checks run through the intrinsic classes rather than through
representatives: the class of an extended representative is the extension of the class,
componentwise
base change is
evaluated on a pure tensor, and its injectivity, valid for every field extension, shows that
distinct classes stay distinct.

The graded checks evaluate the base-change map on a homogeneous pure tensor, record that it is an
injective algebra map, and draw the conclusion used by the structure theorem: `E ⊗[K] P̂` is a
domain. They also record the graded ring homomorphism `P̂ → P̂^(E)` of coefficient extension on a
homogeneous element and as the factor of the base change on an arbitrary pure tensor. The
remaining checks record the coefficientwise formulas for a `K`-linear map between extensions: a
functional into `K`, and the structure map `K → E`, along which the coefficientwise map is
coefficient extension and preserves the ordinal value.
-/

universe v w

open scoped DirectSum HahnSeries NatOrdinal TensorProduct

public noncomputable section

namespace Tests

open Berarducci

open Berarducci

open HahnSeries.Nonpositive

variable {K : Type v} {E : Type w} [Field K] [Field E]

/-! ### Coefficient extension of nonpositive series -/

/-- Coefficient extension fixes the ordinal value of a nonzero constant series, and computes it as
the constant series on the extended value. This runs the extension along the structure map of a
genuine field extension rather than along an endomorphism of the base. -/
theorem baseChange_ordinalValue_coefficientMap_C [Algebra K E] (k : K) :
    ordinalValue (nonpositiveCoefficientMap (algebraMap K E)
        (HahnSeries.Nonpositive.C k)) =
      ordinalValue (HahnSeries.Nonpositive.C k) ∧
    nonpositiveCoefficientMap (algebraMap K E) (HahnSeries.Nonpositive.C k) =
      HahnSeries.Nonpositive.C (algebraMap K E k) :=
  ⟨ordinalValue_nonpositiveCoefficientMap _ _, nonpositiveCoefficientMap_C _ k⟩

/-- Boundary case: the zero series has empty support, and coefficient extension preserves both
the support and the individual coefficients there. -/
theorem baseChange_coefficientMap_zero (f : K →+* E) (x : ℝ) :
    ((nonpositiveCoefficientMap f (0 : HahnSeries.Nonpositive ℝ K) :
        HahnSeries.Nonpositive ℝ E) : E⟦ℝ⟧).support = ∅ ∧
      ((nonpositiveCoefficientMap f (0 : HahnSeries.Nonpositive ℝ K) :
        HahnSeries.Nonpositive ℝ E) : E⟦ℝ⟧).coeff x = 0 := by
  refine ⟨?_, ?_⟩
  · rw [support_nonpositiveCoefficientMap]
    simp
  · rw [coe_nonpositiveCoefficientMap]
    simp

/-- Deleting the constant term cannot increase the ordinal value or the support supremum. -/
theorem baseChange_ordinalValue_sub_C_constantCoeff_le (b : HahnSeries.Nonpositive ℝ K) :
    ordinalValue (b - HahnSeries.Nonpositive.C (HahnSeries.Nonpositive.constantCoeff b)) ≤
        ordinalValue b ∧
      supportSup (b - HahnSeries.Nonpositive.C (HahnSeries.Nonpositive.constantCoeff b)) ≤
        supportSup b := by
  have hsub : ((b - HahnSeries.Nonpositive.C (HahnSeries.Nonpositive.constantCoeff b) :
      HahnSeries.Nonpositive ℝ K) : K⟦ℝ⟧).support ⊆ (b : K⟦ℝ⟧).support := by
    rw [support_sub_C_constantCoeff]
    exact Set.sdiff_subset
  exact ⟨ordinalValue_le_of_support_subset _ _ hsub, supportSup_mono hsub⟩

/-- Interface check: along the structure map `K → E`, viewed as a `K`-linear map between the
extensions `K` and `E` of `K`, the coefficientwise linear map is coefficient extension, and it
preserves the ordinal value, as every injective `K`-linear map does. -/
theorem baseChange_linearCoeffMap_algebraMap [Algebra K E] (u : HahnSeries.Nonpositive ℝ K) :
    nonpositiveLinearCoeffMap (Algebra.linearMap K E) u =
        nonpositiveCoefficientMap (algebraMap K E) u ∧
      ordinalValue (nonpositiveLinearCoeffMap (Algebra.linearMap K E) u) = ordinalValue u :=
  ⟨Subtype.ext (by
      ext x
      rw [coe_nonpositiveLinearCoeffMap, coe_nonpositiveCoefficientMap]
      rfl),
    ordinalValue_nonpositiveLinearCoeffMap_of_injective _ (algebraMap K E).injective u⟩

/-! ### Base change of `P_α` -/

section Layer


/-- The class of an extended representative is the extension of the class, both for the additive
component map and for its semilinear refinement. -/
theorem baseChange_layer_mk [Algebra K E] (alpha : NatOrdinal)
    (u : HahnSeries.Nonpositive ℝ K) (hu : ordinalValue u < ω^ (alpha + 1)) :
    principalComponentCoefficientExtendAddHom (algebraMap K E) alpha
        (principalComponentMk alpha u hu) =
      principalComponentMk alpha (nonpositiveCoefficientMap (algebraMap K E) u)
        (by rw [ordinalValue_nonpositiveCoefficientMap]; exact hu) ∧
    principalComponentCoefficientExtend K E alpha (principalComponentMk alpha u hu) =
      principalComponentMk alpha (nonpositiveCoefficientMap (algebraMap K E) u)
        (by rw [ordinalValue_nonpositiveCoefficientMap]; exact hu) :=
  ⟨principalComponentCoefficientExtendAddHom_principalComponentMk _ alpha u hu,
    principalComponentCoefficientExtend_principalComponentMk E alpha u hu⟩

/-- Componentwise base change evaluates on a pure tensor as the scalar multiple of the extended
class. -/
theorem baseChange_layer_tmul [Algebra K E] (alpha : NatOrdinal) (e : E)
    (A : PrincipalComponent K alpha) :
    principalComponentBaseChange K E alpha (e ⊗ₜ[K] A) =
      e • principalComponentCoefficientExtend K E alpha A :=
  principalComponentBaseChange_tmul alpha e A

/-- Tensors with equal images are equal: componentwise base change reflects equality, for every
field extension `E / K`. -/
theorem baseChange_layer_eq_of_image_eq [Algebra K E]
    (alpha : NatOrdinal) {t₁ t₂ : E ⊗[K] PrincipalComponent K alpha}
    (h : principalComponentBaseChange K E alpha t₁ =
      principalComponentBaseChange K E alpha t₂) : t₁ = t₂ :=
  principalComponentBaseChange_injective K E alpha h

/-- Applying a `K`-linear functional coefficientwise acts coefficientwise, does not enlarge the
support, and does not increase the ordinal value. -/
theorem baseChange_linearCoeffMap_properties [Algebra K E] (r : E →ₗ[K] K)
    (u : HahnSeries.Nonpositive ℝ E) (x : ℝ) :
    ((nonpositiveLinearCoeffMap r u : HahnSeries.Nonpositive ℝ K) : K⟦ℝ⟧).coeff x =
        r ((u : E⟦ℝ⟧).coeff x) ∧
      ((nonpositiveLinearCoeffMap r u : HahnSeries.Nonpositive ℝ K) : K⟦ℝ⟧).support ⊆
        (u : E⟦ℝ⟧).support ∧
      ordinalValue (nonpositiveLinearCoeffMap r u) ≤ ordinalValue u :=
  ⟨coe_nonpositiveLinearCoeffMap r u x, support_nonpositiveLinearCoeffMap_subset r u,
    ordinalValue_nonpositiveLinearCoeffMap_le r u⟩

end Layer

/-! ### Base change of `P̂` and the quotient `P̂/I` -/

section Graded

variable [Algebra K E]

/-- The graded base change evaluates on a homogeneous pure tensor as the scalar multiple of the
extended homogeneous class. -/
theorem baseChange_graded_tmul_of (e : E) (alpha : NatOrdinal)
    (A : PrincipalComponent K alpha) :
    principalSubringBaseChange K E
        (e ⊗ₜ[K] DirectSum.of (PrincipalComponent K) alpha A) =
      e • DirectSum.of (PrincipalComponent E) alpha
        (principalComponentCoefficientExtend K E alpha A) :=
  principalSubringBaseChange_tmul_of e alpha A

/-- Coefficient extension of `P̂` is a ring homomorphism acting on a homogeneous element through
the component map, and the graded base change on any pure tensor `e ⊗ B` is `e` times the
coefficient
extension of `B`, whether or not `B` is homogeneous. -/
theorem baseChange_graded_coefficientExtend (e : E) (alpha : NatOrdinal)
    (A : PrincipalComponent K alpha) (B : PrincipalSubring K) :
    principalSubringCoefficientExtend K E (DirectSum.of (PrincipalComponent K) alpha A) =
        DirectSum.of (PrincipalComponent E) alpha
          (principalComponentCoefficientExtend K E alpha A) ∧
      principalSubringBaseChangeLinear K E (e ⊗ₜ[K] B) =
        e • principalSubringCoefficientExtend K E B :=
  ⟨principalSubringCoefficientExtend_of alpha A, principalSubringBaseChangeLinear_tmul e B⟩

/-- The graded base change is an injective `E`-algebra map, for every field extension. -/
theorem baseChange_graded_injective :
    Function.Injective (principalSubringBaseChange K E) :=
  principalSubringBaseChange_injective K E

/-- Consequently `E ⊗[K] P̂` is a domain. -/
theorem baseChange_graded_isDomain [CharZero E] :
    IsDomain (E ⊗[K] PrincipalSubring K) :=
  isDomain_tensor_principalSubring K E

end Graded

end Tests
