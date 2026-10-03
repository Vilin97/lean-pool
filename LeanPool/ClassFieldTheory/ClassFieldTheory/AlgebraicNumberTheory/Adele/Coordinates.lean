/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.Support
/-!
# Coordinate assembly for relative adeles

The chosen finite `K`-basis of `L` identifies
`𝔸_K ⊗[K] L` with a finite family of base adeles.  The support file
constructs and controls the forward coefficients; this file supplies the
inverse assembly map.  It is the global reconstruction half needed when
local tensor components have first been chosen place by place.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable
section


universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- A relative adele is linearly equivalent to its finite family of
base-adele coefficients in the chosen extension basis. -/
noncomputable def relativeAdeleCoefficientLinearEquiv :
    RelativeAdeleRing K L ≃ₗ[
      NumberField.AdeleRing (𝓞 K) K]
      (RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K) :=
  (relativeAdeleBasis (K := K) (L := L)).equivFun

omit [NumberField L] in
@[simp]
theorem relativeAdeleCoefficientLinearEquiv_apply
    (z : RelativeAdeleRing K L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    relativeAdeleCoefficientLinearEquiv
        (K := K) (L := L) z i =
      relativeAdeleCoefficient
        (K := K) (L := L) z i :=
  rfl

/-- Assemble a finite family of base adeles into a relative adele. -/
noncomputable def relativeAdeleOfCoefficients
    (a :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K) :
    RelativeAdeleRing K L :=
  (relativeAdeleCoefficientLinearEquiv
    (K := K) (L := L)).symm a

omit [NumberField L] in
@[simp]
theorem relativeAdeleCoefficient_ofCoefficients
    (a :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    relativeAdeleCoefficient
        (K := K) (L := L)
        (relativeAdeleOfCoefficients
          (K := K) (L := L) a) i =
      a i := by
  change
    relativeAdeleCoefficientLinearEquiv
        (K := K) (L := L)
        ((relativeAdeleCoefficientLinearEquiv
          (K := K) (L := L)).symm a) i =
      a i
  rw [LinearEquiv.apply_symm_apply]

omit [NumberField L] in
@[simp]
theorem relativeAdeleOfCoefficients_coefficients
    (z : RelativeAdeleRing K L) :
    relativeAdeleOfCoefficients
        (K := K) (L := L)
        (relativeAdeleCoefficient
          (K := K) (L := L) z) =
      z := by
  change
    (relativeAdeleCoefficientLinearEquiv
      (K := K) (L := L)).symm
        (relativeAdeleCoefficientLinearEquiv
          (K := K) (L := L) z) = z
  exact
    (relativeAdeleCoefficientLinearEquiv
      (K := K) (L := L)).symm_apply_apply z

omit [NumberField L] in
/-- Finite-place evaluation of an assembled relative adele is the
corresponding tensor sum of its coefficient components. -/
theorem relativeAdeleOfCoefficients_finiteComponent
    (a :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeAdeleFiniteComponent
        (K := K) (L := L) w
        (relativeAdeleOfCoefficients
          (K := K) (L := L) a) =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (a i).2 w ⊗ₜ[K]
          relativeExtensionBasis
            (K := K) (L := L) i := by
  rw [relativeAdeleFiniteComponent_eq_sum_tmul_coefficients]
  apply Finset.sum_congr rfl
  intro i _
  rw [relativeAdeleCoefficient_ofCoefficients]

omit [NumberField L] in
/-- Infinite-place evaluation of an assembled relative adele is the
corresponding tensor sum of its coefficient components. -/
theorem relativeAdeleOfCoefficients_infiniteComponent
    (a :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K)
    (w : InfinitePlace K) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w
        (relativeAdeleOfCoefficients
          (K := K) (L := L) a) =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (a i).1 w ⊗ₜ[K]
          relativeExtensionBasis
            (K := K) (L := L) i := by
  rw [relativeAdeleInfiniteComponent_eq_sum_tmul_coefficients]
  apply Finset.sum_congr rfl
  intro i _
  rw [relativeAdeleCoefficient_ofCoefficients]

/-- Assemble mutually inverse coordinate families into an actual relative
idele.  The inverse equation is checked after global coordinate assembly,
so no invertibility is hidden in the definition. -/
noncomputable def relativeIdeleOfCoefficientFamilies
    (a b :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K)
    (hab :
      relativeAdeleOfCoefficients
          (K := K) (L := L) a *
        relativeAdeleOfCoefficients
          (K := K) (L := L) b = 1) :
    RelativeIdeleGroup K L :=
  Units.mkOfMulEqOne
    (relativeAdeleOfCoefficients
      (K := K) (L := L) a)
    (relativeAdeleOfCoefficients
      (K := K) (L := L) b)
    hab

omit [NumberField L] in
@[simp]
theorem relativeIdeleOfCoefficientFamilies_coe
    (a b :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K)
    (hab :
      relativeAdeleOfCoefficients
          (K := K) (L := L) a *
        relativeAdeleOfCoefficients
          (K := K) (L := L) b = 1) :
    ((relativeIdeleOfCoefficientFamilies
        (K := K) (L := L) a b hab :
      RelativeIdeleGroup K L) :
        RelativeAdeleRing K L) =
      relativeAdeleOfCoefficients
        (K := K) (L := L) a :=
  Units.val_mkOfMulEqOne hab
