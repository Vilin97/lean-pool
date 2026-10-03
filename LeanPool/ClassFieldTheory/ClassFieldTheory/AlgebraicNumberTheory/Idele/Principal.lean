/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation
/-!
# Principal ideles and their Galois module structure

This module exposes the diagonal embedding and idele class group, identifies
field units with principal relative ideles, and transports low-degree Tate
cohomology across that identification.
-/

@[expose] public section

noncomputable
section

open RelativeIdeleGroup.Cohomology


open LocalClassFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The field-unit group is multiplicatively equivalent to the actual
subgroup of principal relative ideles. -/
noncomputable def fieldUnitsEquivPrincipalIdeles :
    Lˣ ≃*
      RelativeIdeleGroup.principalSubgroup K L :=
  MulEquiv.ofBijective
    (RelativeIdeleGroup.principalIdele K L).rangeRestrict
    ⟨fun _ _ h ↦
        RelativeIdeleGroup.principalIdele_injective K L
          (congrArg Subtype.val h),
      (RelativeIdeleGroup.principalIdele K L).rangeRestrict_surjective⟩

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem fieldUnitsEquivPrincipalIdeles_coe
    (x : Lˣ) :
    ((fieldUnitsEquivPrincipalIdeles K L x :
        RelativeIdeleGroup.principalSubgroup K L) :
      RelativeIdeleGroup K L) =
        RelativeIdeleGroup.principalIdele K L x :=
  rfl

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The identification of field units with principal ideles is equivariant
for the genuine Galois actions. -/
theorem fieldUnitsEquivPrincipalIdeles_smul
    (σ : L ≃ₐ[K] L) (x : Lˣ) :
    letI :=
      galoisGroupFieldUnitsMulDistribMulAction K L
    letI :=
      relativeIdeleMulDistribMulAction K L
    letI :=
      principalIdeleMulDistribMulAction K L
    fieldUnitsEquivPrincipalIdeles K L (σ • x) =
      σ • fieldUnitsEquivPrincipalIdeles K L x := by
  let _ :=
    galoisGroupFieldUnitsMulDistribMulAction K L
  let _ :=
    relativeIdeleMulDistribMulAction K L
  let _ :=
    principalIdeleMulDistribMulAction K L
  apply Subtype.ext
  change
    RelativeIdeleGroup.principalIdele K L
        (Units.mapEquiv σ.toMulEquiv x) =
      σ • RelativeIdeleGroup.principalIdele K L x
  exact
    (RelativeIdeleGroup.smul_principalIdele
      K L σ x).symm

/-- Degree-zero Tate cohomology of principal ideles is the actual
degree-zero cohomology of `Lˣ`. -/
noncomputable def fieldUnitsHerbrandH0EquivPrincipalIdeles :
    letI :=
      galoisGroupFieldUnitsMulDistribMulAction K L
    letI :=
      relativeIdeleMulDistribMulAction K L
    letI :=
      principalIdeleMulDistribMulAction K L
    HerbrandH0 (L ≃ₐ[K] L) Lˣ ≃*
      HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) := by
  letI :=
    galoisGroupFieldUnitsMulDistribMulAction K L
  letI :=
    relativeIdeleMulDistribMulAction K L
  letI :=
    principalIdeleMulDistribMulAction K L
  exact
    herbrandH0EquivariantMulEquiv
      (fieldUnitsEquivPrincipalIdeles K L)
      (fieldUnitsEquivPrincipalIdeles_smul K L)

/-- Degree-minus-one Tate cohomology of principal ideles is the actual
degree-minus-one cohomology of `Lˣ`. -/
noncomputable def fieldUnitsHerbrandHMinusOneEquivPrincipalIdeles
    (σ : L ≃ₐ[K] L) :
    letI :=
      galoisGroupFieldUnitsMulDistribMulAction K L
    letI :=
      relativeIdeleMulDistribMulAction K L
    letI :=
      principalIdeleMulDistribMulAction K L
    HerbrandHMinusOne (L ≃ₐ[K] L) Lˣ σ ≃*
      HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) σ := by
  letI :=
    galoisGroupFieldUnitsMulDistribMulAction K L
  letI :=
    relativeIdeleMulDistribMulAction K L
  letI :=
    principalIdeleMulDistribMulAction K L
  exact
    herbrandHMinusOneEquivariantMulEquiv
      (fieldUnitsEquivPrincipalIdeles K L)
      (fieldUnitsEquivPrincipalIdeles_smul K L) σ
omit [NumberField L] [IsGalois K L] in
/-- A defined Herbrand quotient for field units supplies the corresponding
defined quotient for the actual principal-idele subgroup. -/
theorem principalIdelesHerbrandQuotientDefined
    (σ : L ≃ₐ[K] L)
    (h :
      letI :=
        galoisGroupFieldUnitsMulDistribMulAction K L
      HerbrandQuotientDefined
        (L ≃ₐ[K] L) Lˣ σ) :
    letI :=
      relativeIdeleMulDistribMulAction K L
    letI :=
      principalIdeleMulDistribMulAction K L
    HerbrandQuotientDefined
      (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L) σ := by
  let _ :=
    galoisGroupFieldUnitsMulDistribMulAction K L
  let _ :=
    relativeIdeleMulDistribMulAction K L
  let _ :=
    principalIdeleMulDistribMulAction K L
  let _ : Finite
      (HerbrandH0 (L ≃ₐ[K] L) Lˣ) :=
    h.1
  let _ : Finite
      (HerbrandHMinusOne
        (L ≃ₐ[K] L) Lˣ σ) :=
    h.2
  exact
    ⟨herbrandH0Finite_of_equivariantMulEquiv
        (fieldUnitsEquivPrincipalIdeles K L)
        (fieldUnitsEquivPrincipalIdeles_smul K L),
      herbrandHMinusOneFinite_of_equivariantMulEquiv
        (fieldUnitsEquivPrincipalIdeles K L)
        (fieldUnitsEquivPrincipalIdeles_smul K L) σ⟩

omit [NumberField L] [IsGalois K L] in
/-- The field-unit and principal-idele Herbrand quotients agree. -/
theorem fieldUnits_herbrandQuotient_eq_principalIdeles
    (σ : L ≃ₐ[K] L)
    (h :
      letI :=
        galoisGroupFieldUnitsMulDistribMulAction K L
      HerbrandQuotientDefined
        (L ≃ₐ[K] L) Lˣ σ) :
    letI _fieldAction :=
      galoisGroupFieldUnitsMulDistribMulAction K L
    letI _relativeAction :=
      relativeIdeleMulDistribMulAction K L
    letI _principalAction :=
      principalIdeleMulDistribMulAction K L
    let _ :=
      principalIdelesHerbrandQuotientDefined
        K L σ h
    @herbrandQuotient
        (L ≃ₐ[K] L) Lˣ _ _ _
        (galoisGroupFieldUnitsMulDistribMulAction K L)
        σ =
      @herbrandQuotient
        (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L)
        _ _ _
        (principalIdeleMulDistribMulAction K L)
        σ := by
  let _ :=
    galoisGroupFieldUnitsMulDistribMulAction K L
  let _ :=
    relativeIdeleMulDistribMulAction K L
  let _ :=
    principalIdeleMulDistribMulAction K L
  let _ : Finite
      (HerbrandH0 (L ≃ₐ[K] L) Lˣ) :=
    h.1
  let _ : Finite
      (HerbrandHMinusOne
        (L ≃ₐ[K] L) Lˣ σ) :=
    h.2
  exact
    herbrandQuotient_eq_of_equivariantMulEquiv
      (fieldUnitsEquivPrincipalIdeles K L)
      (fieldUnitsEquivPrincipalIdeles_smul K L) σ
