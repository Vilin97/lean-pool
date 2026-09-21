/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerLift
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Basic

/-! # Teichmuller Decomposition -/
namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

/-!
# Teichmuller and principal-unit decompositions

Decomposes valuation-ring units and field units into residue roots, first principal units,
and a uniformizer factor.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- Multiplication of a Teichmuller representative and a first principal unit,
as a homomorphism into the full valuation-ring unit group. -/
def residueRootsTimesPrincipalUnitMulHom
    [Finite F.residueField] :
    higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
        higherPrincipalUnitGroup F 1 →*
      F.valuationSubringˣ where
  toFun z := (z.1 : F.valuationSubringˣ) * (z.2 : F.valuationSubringˣ)
  map_one' := by
    simp
  map_mul' := by
    intro x y
    simp [mul_left_comm, mul_comm]

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F)`.
-/
theorem residueRootsTimesPrincipalUnitMulHom_surjective
    [Finite F.residueField] :
    Function.Surjective
      (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F) := by
  intro u
  rcases higherPrincipalUnitGroup.residueRootsOfUnityResidueHom_surjective
      (F := F) (higherPrincipalUnitGroup.residueUnitHom F u) with
    ⟨zeta, hzeta⟩
  have hzeta' :
      higherPrincipalUnitGroup.residueUnitHom F
          (zeta : F.valuationSubringˣ) =
        higherPrincipalUnitGroup.residueUnitHom F u := by
    simpa [higherPrincipalUnitGroup.residueRootsOfUnityResidueHom] using hzeta
  let p : F.valuationSubringˣ := (zeta : F.valuationSubringˣ)⁻¹ * u
  have hp : p ∈ higherPrincipalUnitGroup F 1 := by
    rw [← higherPrincipalUnitGroup.residueUnitHom_eq_one_iff F p]
    dsimp [p]
    rw [map_mul, map_inv, hzeta']
    simp
  refine ⟨(zeta, ⟨p, hp⟩), ?_⟩
  change (zeta : F.valuationSubringˣ) * p = u
  dsimp [p]
  simp

/--
The specified map is injective: `Function.Injective
(higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F)`.
-/
theorem residueRootsTimesPrincipalUnitMulHom_injective
    [Finite F.residueField] :
    Function.Injective
      (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F) := by
  intro x y hxy
  have hxprincipal :
      higherPrincipalUnitGroup.residueUnitHom F
          (x.2 : F.valuationSubringˣ) = 1 :=
    (higherPrincipalUnitGroup.residueUnitHom_eq_one_iff
      F (x.2 : F.valuationSubringˣ)).2 x.2.property
  have hyprincipal :
      higherPrincipalUnitGroup.residueUnitHom F
          (y.2 : F.valuationSubringˣ) = 1 :=
    (higherPrincipalUnitGroup.residueUnitHom_eq_one_iff
      F (y.2 : F.valuationSubringˣ)).2 y.2.property
  have hmul :
      (x.1 : F.valuationSubringˣ) * (x.2 : F.valuationSubringˣ) =
        (y.1 : F.valuationSubringˣ) * (y.2 : F.valuationSubringˣ) := by
    simpa [higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom]
      using hxy
  have hresroot :
      higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F x.1 =
        higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F y.1 := by
    have hres :=
      congrArg (higherPrincipalUnitGroup.residueUnitHom F) hmul
    simpa [higherPrincipalUnitGroup.residueRootsOfUnityResidueHom,
      map_mul, hxprincipal, hyprincipal] using hres
  have hroot :
      x.1 = y.1 :=
    higherPrincipalUnitGroup.residueRootsOfUnityResidueHom_injective
      (F := F) hresroot
  apply Prod.ext
  · exact hroot
  · apply Subtype.ext
    calc
      (x.2 : F.valuationSubringˣ) =
          (x.1 : F.valuationSubringˣ)⁻¹ *
            ((x.1 : F.valuationSubringˣ) *
              (x.2 : F.valuationSubringˣ)) := by
        simp
      _ = (x.1 : F.valuationSubringˣ)⁻¹ *
            ((y.1 : F.valuationSubringˣ) *
              (y.2 : F.valuationSubringˣ)) := by
        rw [hmul]
      _ = (y.1 : F.valuationSubringˣ)⁻¹ *
            ((y.1 : F.valuationSubringˣ) *
              (y.2 : F.valuationSubringˣ)) := by
        rw [hroot]
      _ = (y.2 : F.valuationSubringˣ) := by
        simp

/--
The specified map is bijective: `Function.Bijective
(higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F)`.
-/
theorem residueRootsTimesPrincipalUnitMulHom_bijective
    [Finite F.residueField] :
    Function.Bijective
      (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F) :=
  ⟨higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom_injective F,
    higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom_surjective F⟩

/-- Unit-level form of the multiplicative unit decomposition:
`O^*` is the product of the lifted `(q - 1)`-roots of unity and `U^1`. -/
noncomputable def valuationSubringUnitsEquivRootsTimesPrincipalUnits
    [Finite F.residueField] :
    higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
        higherPrincipalUnitGroup F 1 ≃*
      F.valuationSubringˣ :=
  MulEquiv.ofBijective
    (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F)
    (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom_bijective F)

/--
The defining evaluation formula for `valuationSubringUnitsEquivRootsTimesPrincipalUnits` is
`higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits F z = (z.1 :
F.valuationSubringˣ) * (z.2 : F.valuationSubringˣ)`.
-/
@[simp] theorem valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply
    [Finite F.residueField]
    (z :
      higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
        higherPrincipalUnitGroup F 1) :
    higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F z =
      (z.1 : F.valuationSubringˣ) * (z.2 : F.valuationSubringˣ) :=
  rfl

/-- The natural inclusion of valuation-ring units into field units, kept local
to the principal-unit API to state the field-unit form of the multiplicative unit decomposition. -/
def valuationSubringUnitFieldUnitHom :
    F.valuationSubringˣ →* Kˣ :=
  Units.map F.valuation.valuationSubring.subtype.toMonoidHom

/--
The defining evaluation formula for `coe_valuationSubringUnitFieldUnitHom` is
`((higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u : Kˣ) : K) = (u :
F.valuationSubring)`.
-/
@[simp] theorem coe_valuationSubringUnitFieldUnitHom_apply
    (u : F.valuationSubringˣ) :
    ((higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u : Kˣ) :
        K) =
      (u : F.valuationSubring) :=
  rfl

/--
The specified map is injective: `Function.Injective
(higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F)`.
-/
theorem valuationSubringUnitFieldUnitHom_injective :
    Function.Injective
      (higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F) :=
  by
    change Function.Injective
      (Units.map F.valuation.valuationSubring.subtype.toMonoidHom)
    exact
      Units.map_injective
        F.valuation.valuationSubring.subtype_injective

/-- If the zero-valuation subgroup of a field-unit valuation is the usual
unit group of the valuation subring, then it is exactly the image of
valuation-ring units under `valuationSubringUnitFieldUnitHom`. -/
theorem mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup)
    (y : Kˣ) :
    y ∈ V.zeroSubgroup ↔
      ∃ u : F.valuationSubringˣ,
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y := by
  rw [hzero]
  constructor
  · intro hy
    let a : F.valuation.valuationSubring.unitGroup := ⟨y, hy⟩
    refine ⟨F.valuation.valuationSubring.unitGroupMulEquiv a, ?_⟩
    apply Units.ext
    simp [higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom, a]
  · rintro ⟨u, hu⟩
    rw [← hu]
    simp [higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom]

/-- Field-unit representative form of the multiplicative unit decomposition.

Given an existing unit-uniformizer decomposition for a normalized
integer-valued valuation whose zero subgroup is exactly the image of `O^*`,
every field unit is a product of a Teichmuller root, a first principal unit,
and a power of the chosen uniformizer. -/
theorem exists_roots_principalUnit_uniformizer_zpow
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ) (x : Kˣ) :
    ∃ ζ : higherPrincipalUnitGroup.residueRootsOfUnityGroup F,
    ∃ p : higherPrincipalUnitGroup F 1,
    ∃ n : ℤ,
      x =
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (ζ : F.valuationSubringˣ) *
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (p : F.valuationSubringˣ) *
          ϖ ^ n := by
  rcases V.exists_zeroSubgroup_mul_uniformizer_zpow hϖ x with
    ⟨u, hu, n, hx⟩
  rcases (hzero u).1 hu with ⟨a, ha⟩
  rcases
      higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom_surjective
        (F := F) a with
    ⟨zp, hzp⟩
  have hunit :
      (zp.1 : F.valuationSubringˣ) * (zp.2 : F.valuationSubringˣ) = a := by
    simpa [higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom]
      using hzp
  refine ⟨zp.1, zp.2, n, ?_⟩
  calc
    x = u * ϖ ^ n := hx
    _ =
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F a *
          ϖ ^ n := by
      rw [ha]
    _ =
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            ((zp.1 : F.valuationSubringˣ) *
              (zp.2 : F.valuationSubringˣ)) *
          ϖ ^ n := by
      rw [hunit]
    _ =
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (zp.1 : F.valuationSubringˣ) *
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (zp.2 : F.valuationSubringˣ) *
          ϖ ^ n := by
      rw [map_mul]

/-- Field-unit form with the standard subgroup equality hypothesis
`V.zeroSubgroup = O^*`. -/
theorem exists_roots_principalUnit_uniformizer_zpow_of_zeroSubgroup_eq_unitGroup
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ) (x : Kˣ) :
    ∃ ζ : higherPrincipalUnitGroup.residueRootsOfUnityGroup F,
    ∃ p : higherPrincipalUnitGroup F 1,
    ∃ n : ℤ,
      x =
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (ζ : F.valuationSubringˣ) *
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (p : F.valuationSubringˣ) *
          ϖ ^ n :=
  higherPrincipalUnitGroup.exists_roots_principalUnit_uniformizer_zpow
    (F := F) V
    (fun y =>
      higherPrincipalUnitGroup.mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
          (F := F) V hzero y)
    hϖ x

/-- Uniqueness of the field-unit form of the multiplicative unit decomposition:
with a fixed uniformizer, the Teichmuller representative, the first principal
unit, and the exponent are all uniquely determined. -/
theorem roots_principalUnit_uniformizer_zpow_eq_iff
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ)
    (ζ η : higherPrincipalUnitGroup.residueRootsOfUnityGroup F)
    (p q : higherPrincipalUnitGroup F 1) (m n : ℤ) :
    higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (ζ : F.valuationSubringˣ) *
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (p : F.valuationSubringˣ) *
        ϖ ^ m =
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (η : F.valuationSubringˣ) *
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (q : F.valuationSubringˣ) *
        ϖ ^ n ↔
      ζ = η ∧ p = q ∧ m = n := by
  have hleft :
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (ζ : F.valuationSubringˣ) *
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (p : F.valuationSubringˣ) ∈
        V.zeroSubgroup :=
    (hzero _).2
      ⟨(ζ : F.valuationSubringˣ) * (p : F.valuationSubringˣ), by
        rw [map_mul]⟩
  have hright :
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (η : F.valuationSubringˣ) *
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (q : F.valuationSubringˣ) ∈
        V.zeroSubgroup :=
    (hzero _).2
      ⟨(η : F.valuationSubringˣ) * (q : F.valuationSubringˣ), by
        rw [map_mul]⟩
  constructor
  · intro h
    have hnormal :=
      (V.unit_uniformizer_normal_form_eq_iff hϖ hleft hright).1 h
    rcases hnormal with ⟨hunit, hmn⟩
    have hvaluationUnit :
        (ζ : F.valuationSubringˣ) * (p : F.valuationSubringˣ) =
          (η : F.valuationSubringˣ) * (q : F.valuationSubringˣ) :=
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_injective
        (F := F)
        (by
          simpa [map_mul] using hunit)
    have hpair :
        (ζ, p) = (η, q) :=
      higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom_injective
        (F := F)
        (by
          simpa [higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom]
            using hvaluationUnit)
    cases hpair
    exact ⟨rfl, rfl, hmn⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- Uniqueness form under the standard subgroup equality hypothesis
`V.zeroSubgroup = O^*`. -/
theorem roots_principalUnit_uniformizer_zpow_eq_iff_of_zeroSubgroup_eq_unitGroup
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ)
    (ζ η : higherPrincipalUnitGroup.residueRootsOfUnityGroup F)
    (p q : higherPrincipalUnitGroup F 1) (m n : ℤ) :
    higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (ζ : F.valuationSubringˣ) *
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (p : F.valuationSubringˣ) *
        ϖ ^ m =
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (η : F.valuationSubringˣ) *
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (q : F.valuationSubringˣ) *
        ϖ ^ n ↔
      ζ = η ∧ p = q ∧ m = n :=
  higherPrincipalUnitGroup.roots_principalUnit_uniformizer_zpow_eq_iff
    (F := F) V
    (fun y =>
      higherPrincipalUnitGroup.mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
        (F := F) V hzero y)
    hϖ ζ η p q m n

/-- The three factors in the multiplicative field-unit decomposition: Teichmuller roots,
first principal units, and an integral power of a fixed uniformizer. -/
abbrev fieldUnitDecompositionFactors [Finite F.residueField] :
    Type u :=
  (higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
      higherPrincipalUnitGroup F 1) × Multiplicative ℤ

/--
Multiplication map from the three the multiplicative unit decomposition factors to field units.
-/
noncomputable def rootsPrincipalUnitUniformizerMulHom
    [Finite F.residueField] (ϖ : Kˣ) :
    higherPrincipalUnitGroup.fieldUnitDecompositionFactors F →* Kˣ where
  toFun z :=
    higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
        (z.1.1 : F.valuationSubringˣ) *
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
        (z.1.2 : F.valuationSubringˣ) *
      ϖ ^ Multiplicative.toAdd z.2
  map_one' := by
    simp
  map_mul' := by
    intro x y
    simp [higherPrincipalUnitGroup.fieldUnitDecompositionFactors,
      mul_assoc, mul_left_comm, mul_comm, zpow_add]

/--
The defining evaluation formula for `rootsPrincipalUnitUniformizerMulHom` is
`higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ z =
higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F (z.1.1 : F.valuationSubringˣ) *
higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F (z.1.2 : F.valuationSubringˣ) * ϖ ^
Multiplicative.toAdd z.2`.
-/
@[simp] theorem rootsPrincipalUnitUniformizerMulHom_apply
    [Finite F.residueField] (ϖ : Kˣ)
    (z : higherPrincipalUnitGroup.fieldUnitDecompositionFactors F) :
    higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ z =
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (z.1.1 : F.valuationSubringˣ) *
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (z.1.2 : F.valuationSubringˣ) *
        ϖ ^ Multiplicative.toAdd z.2 :=
  rfl

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ)`.
-/
theorem rootsPrincipalUnitUniformizerMulHom_surjective
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ) :
    Function.Surjective
      (higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ) := by
  intro x
  rcases
      higherPrincipalUnitGroup.exists_roots_principalUnit_uniformizer_zpow
        (F := F) V hzero hϖ x with
    ⟨ζ, p, n, hx⟩
  refine ⟨((ζ, p), Multiplicative.ofAdd n), ?_⟩
  exact hx.symm

/--
The specified map is injective: `Function.Injective
(higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ)`.
-/
theorem rootsPrincipalUnitUniformizerMulHom_injective
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ) :
    Function.Injective
      (higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ) := by
  rintro ⟨⟨ζ, p⟩, m⟩ ⟨⟨η, q⟩, n⟩ h
  have hmul :
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (ζ : F.valuationSubringˣ) *
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (p : F.valuationSubringˣ) *
          ϖ ^ Multiplicative.toAdd m =
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (η : F.valuationSubringˣ) *
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (q : F.valuationSubringˣ) *
          ϖ ^ Multiplicative.toAdd n := by
    exact h
  have hdecomp :=
    (higherPrincipalUnitGroup.roots_principalUnit_uniformizer_zpow_eq_iff
      (F := F) V hzero hϖ ζ η p q
        (Multiplicative.toAdd m) (Multiplicative.toAdd n)).1 hmul
  rcases hdecomp with ⟨hζη, hpq, hmn⟩
  have hmn' : m = n :=
    Multiplicative.toAdd.injective hmn
  simp [hζη, hpq, hmn']

/--
The specified map is bijective: `Function.Bijective
(higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ)`.
-/
theorem rootsPrincipalUnitUniformizerMulHom_bijective
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ) :
    Function.Bijective
      (higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ) :=
  ⟨higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_injective
      (F := F) V hzero hϖ,
    higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_surjective
      (F := F) V hzero hϖ⟩

/-- Group-isomorphism form of the multiplicative unit decomposition: after fixing
a uniformizer, `Kˣ` is the product of the lifted residue roots of unity, the
first principal units, and the infinite cyclic uniformizer factor. -/
noncomputable def fieldUnitsEquivRootsPrincipalUnitsUniformizer
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ) :
    higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ :=
  MulEquiv.ofBijective
    (higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ)
    (higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_bijective
      (F := F) V hzero hϖ)

/--
The defining evaluation formula for `fieldUnitsEquivRootsPrincipalUnitsUniformizer` is
`higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer (F := F) V hzero hϖ z =
higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F (z.1.1 : F.valuationSubringˣ) *
higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F (z.1.2 : F.valuationSubringˣ) * ϖ ^
Multiplicative.toAdd z.2`.
-/
@[simp] theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ)
    (z : higherPrincipalUnitGroup.fieldUnitDecompositionFactors F) :
    higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer
        (F := F) V hzero hϖ z =
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (z.1.1 : F.valuationSubringˣ) *
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (z.1.2 : F.valuationSubringˣ) *
        ϖ ^ Multiplicative.toAdd z.2 :=
  rfl

/-- Group-isomorphism form under the standard subgroup equality hypothesis
`V.zeroSubgroup = O^*`. -/
noncomputable def fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_zeroSubgroup_eq_unitGroup
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ) :
    higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ :=
  higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer
    (F := F) V
    (fun y =>
      higherPrincipalUnitGroup.mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
        (F := F) V hzero y)
    hϖ
end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
