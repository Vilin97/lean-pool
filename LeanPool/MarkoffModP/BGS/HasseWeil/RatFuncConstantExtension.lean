/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Constant extensions of rational function fields

For a finite field extension `S / K`, this file constructs the coefficient
embedding `K(X) → S(X)` and proves that `S(X)` is a finite-dimensional
`K(X)`-vector space of dimension `[S : K]`.

The construction is explicit.  We first localize `S[X]` at the images of the
nonzero polynomials in `K[X]`, prove that this localization is a field, and
identify it with `S(X)`.  This is the rational-function-field base-change
input needed for the later constant extension of a general function field.
-/

open scoped Polynomial nonZeroDivisors

namespace BGS.HasseWeil

noncomputable section

variable (K S : Type*) [Field K] [Field S] [Algebra K S]

local instance polynomialCoefficientAlgebra : Algebra K[X] S[X] :=
  (Polynomial.mapRingHom (algebraMap K S)).toAlgebra

local instance polynomialCoefficientFaithfulSMul : FaithfulSMul K[X] S[X] where
  eq_of_smul_eq_smul h := by
    have hinj : Function.Injective (algebraMap K[X] S[X]) := by
      change Function.Injective (Polynomial.map (algebraMap K S))
      exact Polynomial.map_injective (algebraMap K S) (algebraMap K S).injective
    exact hinj (by simpa only [Algebra.smul_def, mul_one] using h 1)

/-- The coefficient extension on polynomial rings. -/
noncomputable def ratFuncCoefficientPolynomialAlgHom : K[X] →ₐ[K] S[X] :=
  Polynomial.mapAlgHom (Algebra.ofId K S)

theorem ratFuncCoefficientPolynomialAlgHom_injective :
    Function.Injective (ratFuncCoefficientPolynomialAlgHom K S) := by
  change Function.Injective (Polynomial.map (algebraMap K S))
  exact Polynomial.map_injective (algebraMap K S) (algebraMap K S).injective

private theorem ratFuncCoefficientPolynomialAlgHom_nonZeroDivisors :
    K[X]⁰ ≤ S[X]⁰.comap (ratFuncCoefficientPolynomialAlgHom K S) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (ratFuncCoefficientPolynomialAlgHom_injective K S)

/-- The canonical coefficient extension `K(X) → S(X)`. -/
noncomputable def ratFuncCoefficientAlgHom : RatFunc K →ₐ[K] RatFunc S :=
  RatFunc.mapAlgHom (ratFuncCoefficientPolynomialAlgHom K S)
    (ratFuncCoefficientPolynomialAlgHom_nonZeroDivisors K S)

theorem ratFuncCoefficientAlgHom_injective :
    Function.Injective (ratFuncCoefficientAlgHom K S) :=
  RatFunc.map_injective (ratFuncCoefficientPolynomialAlgHom K S)
    (ratFuncCoefficientPolynomialAlgHom_nonZeroDivisors K S)
    (ratFuncCoefficientPolynomialAlgHom_injective K S)

theorem ratFuncCoefficientAlgHom_algebraMap (p : K[X]) :
    ratFuncCoefficientAlgHom K S (algebraMap K[X] (RatFunc K) p) =
      algebraMap S[X] (RatFunc S) (algebraMap K[X] S[X] p) := by
  change RatFunc.map (ratFuncCoefficientPolynomialAlgHom K S)
      (ratFuncCoefficientPolynomialAlgHom_nonZeroDivisors K S)
        (algebraMap K[X] (RatFunc K) p) = _
  rw [show algebraMap K[X] (RatFunc K) p =
      algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) 1 by simp]
  rw [RatFunc.map_apply_div]
  simp only [map_one, div_one]
  congr 1

/-- The algebra structure on `S(X)` induced by coefficient extension. -/
@[reducible] noncomputable def ratFuncCoefficientAlgebra :
    Algebra (RatFunc K) (RatFunc S) :=
  (ratFuncCoefficientAlgHom K S).toAlgebra

local instance ratFuncCoefficientAlgebraInstance :
    Algebra (RatFunc K) (RatFunc S) :=
  ratFuncCoefficientAlgebra K S

/-- Localize `S[X]` by the images of all nonzero polynomials in `K[X]`. -/
abbrev RatFuncConstantLocalization :=
  Localization (Submonoid.map (algebraMap K[X] S[X]) K[X]⁰)

local instance ratFuncConstantLocalizationIsDomain :
    IsDomain (RatFuncConstantLocalization K S) :=
  IsLocalization.isDomain_localization
    (by
      simpa only [Algebra.algebraMapSubmonoid] using
        algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul S[X] le_rfl)

noncomputable local instance ratFuncConstantLocalizationAlgebra :
    Algebra (RatFunc K) (RatFuncConstantLocalization K S) :=
  (IsLocalization.map (RatFuncConstantLocalization K S)
    (algebraMap K[X] S[X]) (Submonoid.le_comap_map K[X]⁰)).toAlgebra

local instance ratFuncConstantLocalizationScalarTower :
    IsScalarTower K[X] (RatFunc K) (RatFuncConstantLocalization K S) :=
  let hmap : K[X]⁰ ≤ Submonoid.comap (algebraMap K[X] S[X])
      (Submonoid.map (algebraMap K[X] S[X]) K[X]⁰) :=
    Submonoid.le_comap_map K[X]⁰
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq K[X] S[X]
      (RatFuncConstantLocalization K S)]
    exact (IsLocalization.map_comp hmap).symm)

private noncomputable def polynomialModuleEquivPolynomial :
    PolynomialModule K S ≃ₗ[K[X]] S[X] where
  toEquiv := (PolynomialModule.equivPolynomial (R := K)).toEquiv
  map_add' := (PolynomialModule.equivPolynomial (R := K)).map_add
  map_smul' p x := by
    ext n
    change (p • x).coeff n =
      ((algebraMap K[X] S[X] p) *
        (PolynomialModule.equivPolynomial (R := K) x)).coeff n
    rw [PolynomialModule.smul_apply, Polynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    simp [Algebra.smul_def, PolynomialModule.equivPolynomial]

local instance polynomialCoefficientModuleFinite [FiniteDimensional K S] :
    Module.Finite K[X] S[X] := by
  let : Module.Finite K[X] (TensorProduct K K[X] S) :=
    Module.Finite.base_change K K[X] S
  exact Module.Finite.equiv
    ((PolynomialModule.polynomialTensorProductLEquivPolynomialModule K S).trans
      (polynomialModuleEquivPolynomial K S))

local instance ratFuncConstantLocalizationIsLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid S[X] K[X]⁰)
      (RatFuncConstantLocalization K S) := by
  change IsLocalization (Submonoid.map (algebraMap K[X] S[X]) K[X]⁰)
    (RatFuncConstantLocalization K S)
  infer_instance

local instance ratFuncConstantLocalizationFinite [FiniteDimensional K S] :
    Module.Finite (RatFunc K) (RatFuncConstantLocalization K S) :=
  Module.Finite.of_isLocalization K[X] S[X] K[X]⁰

noncomputable local instance ratFuncConstantLocalizationField
    [FiniteDimensional K S] : Field (RatFuncConstantLocalization K S) :=
  (IsField.of_isDomain_of_finite (RatFunc K)
    (RatFuncConstantLocalization K S)).toField

private theorem ratFuncConstantLocalizationSubmonoid_le :
    Submonoid.map (algebraMap K[X] S[X]) K[X]⁰ ≤ S[X]⁰ := by
  simpa only [Algebra.algebraMapSubmonoid] using
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul S[X] le_rfl

private noncomputable def ratFuncConstantLocalizationToRatFunc
    [FiniteDimensional K S] :
    RatFuncConstantLocalization K S →+* RatFunc S :=
  IsLocalization.map
    (M := Submonoid.map (algebraMap K[X] S[X]) K[X]⁰)
    (T := S[X]⁰) (RatFunc S) (RingHom.id S[X]) (by
      change Submonoid.map (algebraMap K[X] S[X]) K[X]⁰ ≤ S[X]⁰
      exact ratFuncConstantLocalizationSubmonoid_le K S)

private theorem ratFuncConstantLocalizationToRatFunc_algebraMap
    [FiniteDimensional K S] (p : S[X]) :
    ratFuncConstantLocalizationToRatFunc K S
        (algebraMap S[X] (RatFuncConstantLocalization K S) p) =
      algebraMap S[X] (RatFunc S) p := by
  let hM : Submonoid.map (algebraMap K[X] S[X]) K[X]⁰ ≤
      S[X]⁰.comap (RingHom.id S[X]) := by
    change Submonoid.map (algebraMap K[X] S[X]) K[X]⁰ ≤ S[X]⁰
    exact ratFuncConstantLocalizationSubmonoid_le K S
  have h := congrArg (fun f : S[X] →+* RatFunc S => f p)
    (IsLocalization.map_comp
      (Q := RatFunc S)
      (S := RatFuncConstantLocalization K S) hM)
  change (IsLocalization.map (RatFunc S) (RingHom.id S[X]) hM)
      (algebraMap S[X] (RatFuncConstantLocalization K S) p) =
    algebraMap S[X] (RatFunc S) p
  simpa only [RingHom.comp_apply, RingHom.id_apply] using h

private noncomputable def ratFuncToConstantLocalization
    [FiniteDimensional K S] :
    RatFunc S →+* RatFuncConstantLocalization K S :=
  IsFractionRing.lift (IsLocalization.injective
    (RatFuncConstantLocalization K S)
    (ratFuncConstantLocalizationSubmonoid_le K S))

private theorem ratFuncToConstantLocalization_algebraMap
    [FiniteDimensional K S] (p : S[X]) :
    ratFuncToConstantLocalization K S (algebraMap S[X] (RatFunc S) p) =
      algebraMap S[X] (RatFuncConstantLocalization K S) p := by
  exact IsFractionRing.lift_algebraMap _ p

/-- The localization of `S[X]` at nonzero `K[X]` is the full rational
function field `S(X)` when `S / K` is finite. -/
noncomputable def ratFuncConstantLocalizationRingEquiv
    [FiniteDimensional K S] :
    RatFuncConstantLocalization K S ≃+* RatFunc S where
  toFun := ratFuncConstantLocalizationToRatFunc K S
  invFun := ratFuncToConstantLocalization K S
  map_add' := map_add _
  map_mul' := map_mul _
  left_inv x := by
    have hcomp :
        (ratFuncToConstantLocalization K S).comp
            (ratFuncConstantLocalizationToRatFunc K S) =
          RingHom.id (RatFuncConstantLocalization K S) := by
      apply IsLocalization.ringHom_ext
        (Submonoid.map (algebraMap K[X] S[X]) K[X]⁰)
      apply RingHom.ext
      intro p
      simp only [RingHom.comp_apply,
        ratFuncConstantLocalizationToRatFunc_algebraMap,
        ratFuncToConstantLocalization_algebraMap, RingHom.id_apply]
    exact congrArg
      (fun f : RatFuncConstantLocalization K S →+*
        RatFuncConstantLocalization K S => f x) hcomp
  right_inv x := by
    have hcomp :
        (ratFuncConstantLocalizationToRatFunc K S).comp
            (ratFuncToConstantLocalization K S) =
          RingHom.id (RatFunc S) := by
      apply IsFractionRing.ringHom_ext (A := S[X])
      intro p
      simp only [RingHom.comp_apply,
        ratFuncConstantLocalizationToRatFunc_algebraMap,
        ratFuncToConstantLocalization_algebraMap, RingHom.id_apply]
    exact congrArg (fun f : RatFunc S →+* RatFunc S => f x) hcomp

theorem ratFuncConstantLocalizationRingEquiv_algebraMap
    [FiniteDimensional K S] (r : RatFunc K) :
    ratFuncConstantLocalizationRingEquiv K S
        (algebraMap (RatFunc K) (RatFuncConstantLocalization K S) r) =
      algebraMap (RatFunc K) (RatFunc S) r := by
  have hcomp :
      (ratFuncConstantLocalizationRingEquiv K S).toRingHom.comp
          (algebraMap (RatFunc K) (RatFuncConstantLocalization K S)) =
        algebraMap (RatFunc K) (RatFunc S) := by
    apply IsFractionRing.ringHom_ext (A := K[X])
    intro p
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply K[X] (RatFunc K)
      (RatFuncConstantLocalization K S)]
    rw [IsScalarTower.algebraMap_apply K[X] S[X]
      (RatFuncConstantLocalization K S)]
    change ratFuncConstantLocalizationToRatFunc K S
        (algebraMap S[X] (RatFuncConstantLocalization K S)
          (algebraMap K[X] S[X] p)) =
      ratFuncCoefficientAlgHom K S (algebraMap K[X] (RatFunc K) p)
    rw [ratFuncConstantLocalizationToRatFunc_algebraMap]
    exact (ratFuncCoefficientAlgHom_algebraMap K S p).symm
  exact congrArg (fun f : RatFunc K →+* RatFunc S => f r) hcomp

/-- The localization equivalence, now linear over the canonical coefficient
embedding `K(X) → S(X)`. -/
noncomputable def ratFuncConstantLocalizationLinearEquiv
    [FiniteDimensional K S] :
    RatFuncConstantLocalization K S ≃ₗ[RatFunc K] RatFunc S where
  toEquiv := (ratFuncConstantLocalizationRingEquiv K S).toEquiv
  map_add' := map_add (ratFuncConstantLocalizationRingEquiv K S)
  map_smul' r x := by
    change ratFuncConstantLocalizationRingEquiv K S
        (algebraMap (RatFunc K) (RatFuncConstantLocalization K S) r * x) =
      algebraMap (RatFunc K) (RatFunc S) r *
        ratFuncConstantLocalizationRingEquiv K S x
    rw [map_mul, ratFuncConstantLocalizationRingEquiv_algebraMap]

/-- A finite coefficient extension induces a finite extension of rational
function fields. -/
theorem ratFuncCoefficient_moduleFinite [FiniteDimensional K S] :
    Module.Finite (RatFunc K) (RatFunc S) :=
  Module.Finite.equiv (ratFuncConstantLocalizationLinearEquiv K S)

/-- Constant extension preserves the extension degree of rational function
fields: `[S(X) : K(X)] = [S : K]`. -/
theorem ratFuncCoefficient_finrank [FiniteDimensional K S] :
    Module.finrank (RatFunc K) (RatFunc S) = Module.finrank K S := by
  let ePoly :=
    (PolynomialModule.polynomialTensorProductLEquivPolynomialModule K S).trans
      (polynomialModuleEquivPolynomial K S)
  calc
    Module.finrank (RatFunc K) (RatFunc S) =
        Module.finrank (RatFunc K) (RatFuncConstantLocalization K S) :=
      (ratFuncConstantLocalizationLinearEquiv K S).finrank_eq.symm
    _ = Module.finrank K[X] (RatFuncConstantLocalization K S) := by
      simpa only [Module.finrank] using congrArg Cardinal.toNat
        (IsLocalization.rank_eq
          (N := RatFuncConstantLocalization K S) (RatFunc K) K[X]⁰ le_rfl)
    _ = Module.finrank K[X] S[X] := by
      exact IsLocalizedModule.finrank_eq K[X]⁰
        (IsScalarTower.toAlgHom K[X] S[X]
          (RatFuncConstantLocalization K S)).toLinearMap le_rfl
    _ = Module.finrank K[X] (TensorProduct K K[X] S) := ePoly.finrank_eq.symm
    _ = Module.finrank K S := Module.finrank_baseChange

end

end BGS.HasseWeil
