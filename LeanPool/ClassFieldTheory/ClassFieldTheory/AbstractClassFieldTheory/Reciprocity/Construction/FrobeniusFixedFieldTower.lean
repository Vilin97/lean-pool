/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension
/-!
Bundles finite towers of Frobenius fixed fields together with the normality and finiteness data
needed for norm and unit calculations.
-/

@[expose] public section

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The Frobenius fixed field bundled with its proved absolute finiteness.
This is the field object used by valuation and unit APIs. -/
noncomputable def frobeniusFixedAbstractField
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : DegreeData.FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField K L hLK σ)
        (le_baseField (D.frobeniusFixedField K L hLK σ)))] :
    FiniteAbstractField G where
  field := D.frobeniusFixedField K L hLK σ
  finite := inferInstance

/-- A finite normal tower between two Frobenius fixed fields.

The ambient Galois extension, both Frobenius elements, the fixed-field
inclusion, and exactly the finiteness hypotheses needed by the unit
representation are stored once.  In particular, downstream statements no
longer re-thread the proof-dependent subgroup inclusions and quotient
instances independently. -/
structure FrobeniusFixedFieldTower
    (D : DegreeData G) [IsTopologicalGroup G] where
  /-- The finite-residue field in which the ambient Galois extension begins. -/
  ambientBase : DegreeData.FiniteResidueAbstractField D
  /-- The ambient Galois subextension. -/
  ambient : GaloisSubextension ambientBase.field
  /-- The Frobenius element whose fixed field is the base of the tower. -/
  baseFrobenius :
    D.FrobeniusElements ambientBase ambient.field ambient.below
  /-- The Frobenius element whose fixed field is the top of the tower. -/
  fieldFrobenius :
    D.FrobeniusElements ambientBase ambient.field ambient.below
  /-- Inclusion of the top fixed field into the base fixed field. -/
  field_le_base :
    (D.frobeniusFixedField ambientBase ambient.field ambient.below
        fieldFrobenius).toSubgroup ≤
      (D.frobeniusFixedField ambientBase ambient.field ambient.below
        baseFrobenius).toSubgroup
  /-- The relative quotient between the two fixed fields is finite. -/
  finiteQuotient :
    Finite
      ((D.frobeniusFixedField ambientBase ambient.field ambient.below
          baseFrobenius).toSubgroup ⧸
        extensionSubgroup
          (D.frobeniusFixedField ambientBase ambient.field ambient.below
            baseFrobenius)
          (D.frobeniusFixedField ambientBase ambient.field ambient.below
            fieldFrobenius)
          field_le_base)
  /-- The base fixed field is finite over the distinguished base. -/
  baseAbsoluteFinite :
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField ambientBase ambient.field ambient.below
            baseFrobenius)
          (le_baseField
            (D.frobeniusFixedField ambientBase ambient.field ambient.below
              baseFrobenius)))
  /-- The top fixed field is finite over the distinguished base. -/
  fieldAbsoluteFinite :
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField ambientBase ambient.field ambient.below
            fieldFrobenius)
          (le_baseField
            (D.frobeniusFixedField ambientBase ambient.field ambient.below
              fieldFrobenius)))
  /-- The relative subgroup between the fixed fields is normal. -/
  normal :
    (extensionSubgroup
      (D.frobeniusFixedField ambientBase ambient.field ambient.below
        baseFrobenius)
      (D.frobeniusFixedField ambientBase ambient.field ambient.below
        fieldFrobenius)
      field_le_base).Normal
  /-- The two chosen ambient Frobenius elements commute. -/
  commute :
    baseFrobenius.1 * fieldFrobenius.1 =
      fieldFrobenius.1 * baseFrobenius.1

namespace FrobeniusFixedFieldTower

variable {D : DegreeData G} [IsTopologicalGroup G]

/-- The lower fixed field, finite over the distinguished base. -/
noncomputable def base (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractField G := by
  letI : Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
            T.baseFrobenius)
          (le_baseField
            (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
              T.baseFrobenius))) :=
    T.baseAbsoluteFinite
  exact D.frobeniusFixedAbstractField T.ambientBase T.ambient.field
    T.ambient.below T.baseFrobenius

/-- The upper fixed field, finite over the distinguished base. -/
noncomputable def field (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractField G := by
  letI : Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
            T.fieldFrobenius)
          (le_baseField
            (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
              T.fieldFrobenius))) :=
    T.fieldAbsoluteFinite
  exact D.frobeniusFixedAbstractField T.ambientBase T.ambient.field
    T.ambient.below T.fieldFrobenius

/-- The fixed-field inclusion as a bundled Galois subextension. -/
noncomputable def toGaloisSubextension (T : FrobeniusFixedFieldTower D) :
    GaloisSubextension T.base.field where
  field := T.field.field
  below := T.field_le_base
  normal := T.normal

/-- The finite extension between the two bundled fixed fields. -/
noncomputable def extension (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractFieldExtension G where
  field := T.field
  base := T.base
  below := T.field_le_base
  finiteQuotient := T.finiteQuotient

/-- A concrete lower-fixed-field element representing its Frobenius class. -/
structure Representative (T : FrobeniusFixedFieldTower D) where
  /-- The chosen element in the base fixed-field subgroup. -/
  element : T.extension.base.field.toSubgroup
  /-- The chosen element maps to the prescribed ambient Frobenius class. -/
  mapsToFrobenius :
    D.frobeniusFixedFieldToClosure T.ambientBase T.ambient.field
        T.ambient.below T.baseFrobenius element =
      D.frobeniusInClosure T.ambientBase T.ambient.field
        T.ambient.below T.baseFrobenius

/-- The extension subgroup of a bundled Frobenius fixed-field tower is normal. -/
instance extensionNormal (T : FrobeniusFixedFieldTower D) :
    (extensionSubgroup T.extension.base.field T.extension.field.field
      T.extension.below).Normal :=
  T.normal

/-- A representative which generates the finite fixed-field quotient. -/
structure CyclicGenerator (T : FrobeniusFixedFieldTower D)
    extends Representative T where
  /-- Every relative Galois element is a power of the representative's class. -/
  generates :
    ∀ x :
      T.extension.base.field.toSubgroup ⧸
        extensionSubgroup T.extension.base.field T.extension.field.field
          T.extension.below,
      x ∈ Subgroup.zpowers (QuotientGroup.mk toRepresentative.element)

/-- The Galois quotient of a bundled Frobenius fixed-field extension is finite. -/
instance extensionFinite (T : FrobeniusFixedFieldTower D) :
    Finite
      (T.extension.base.field.toSubgroup ⧸
        extensionSubgroup T.extension.base.field T.extension.field.field
          T.extension.below) :=
  T.finiteQuotient

/-- The lower Frobenius fixed field in the tower is finite over the distinguished base field. -/
instance baseAbsoluteFiniteInstance (T : FrobeniusFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
            T.baseFrobenius)
          (le_baseField
            (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
              T.baseFrobenius))) :=
  T.baseAbsoluteFinite

/-- The upper Frobenius fixed field in the tower is finite over the distinguished base field. -/
instance fieldAbsoluteFiniteInstance (T : FrobeniusFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
            T.fieldFrobenius)
          (le_baseField
            (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
              T.fieldFrobenius))) :=
  T.fieldAbsoluteFinite

end FrobeniusFixedFieldTower

/-- A Frobenius fixed-field tower whose ambient Galois extension is finite.
The additional finiteness is stored on the opaque quotient object exposed by
`GaloisSubextension`. -/
structure FiniteAmbientFrobeniusFixedFieldTower
    (D : DegreeData G) [IsTopologicalGroup G]
    extends FrobeniusFixedFieldTower D where
  /-- The ambient Galois quotient is finite. -/
  ambientFinite : Finite toFrobeniusFixedFieldTower.ambient.extensionQuotient

namespace FiniteAmbientFrobeniusFixedFieldTower

variable {D : DegreeData G} [IsTopologicalGroup G]

/--
The ambient Galois quotient stored in a finite Frobenius fixed-field tower is finite.
-/
instance ambientQuotientFinite
    (T : FiniteAmbientFrobeniusFixedFieldTower D) :
    Finite T.ambient.extensionQuotient :=
  T.ambientFinite

/-- Finiteness transported to the quotient presentation required by the
underlying Frobenius calculations. -/
noncomputable instance ambientRepresentedQuotientFinite
    (T : FiniteAmbientFrobeniusFixedFieldTower D) :
    Finite
      (T.ambientBase.field.toSubgroup ⧸
        extensionSubgroup T.ambientBase.field T.ambient.field
          T.ambient.below) :=
  Finite.of_equiv T.ambient.extensionQuotient
    T.ambient.extensionQuotientMulEquiv

end FiniteAmbientFrobeniusFixedFieldTower

/-- The power tower fixed by `φⁿ² ≤ φⁿ`.

Only data already required by the universal norm-descent construction is
stored: the finite ambient Galois extension, a degree-one Frobenius, its
positive exponent, and the three fixed-field finiteness witnesses.  The
fixed-field inclusion, normality, and commutation relation are consequences
of the power construction. -/
structure FrobeniusPowerFixedFieldTower
    (D : DegreeData G) [IsTopologicalGroup G] where
  /-- The finite-residue field at the base of the ambient extension. -/
  ambientBase : DegreeData.FiniteResidueAbstractField D
  /-- The finite ambient Galois subextension. -/
  ambient : FiniteGaloisSubextension ambientBase.field
  /-- A chosen degree-one Frobenius element in the ambient extension. -/
  frobenius :
    D.FrobeniusElements ambientBase ambient.field ambient.below
  /-- The chosen Frobenius has exponent one. -/
  exponent_one :
    D.frobeniusExponent ambientBase ambient.field ambient.below frobenius = 1
  /-- The positive exponent defining the first fixed field. -/
  n : ℕ
  /-- Positivity of the fixed-field exponent. -/
  n_pos : 0 < n
  /-- The fixed field of the `n`-th Frobenius power is finite over the distinguished base. -/
  baseAbsoluteFinite :
    let σ := D.frobeniusPowerOfDegreeOne ambientBase ambient.field
      ambient.below frobenius exponent_one n n_pos
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField ambientBase ambient.field ambient.below σ)
          (le_baseField
            (D.frobeniusFixedField ambientBase ambient.field ambient.below σ)))
  /-- The fixed field of the `n²`-th Frobenius power is finite over the distinguished base. -/
  fieldAbsoluteFinite :
    let σn := D.frobeniusPowerOfDegreeOne ambientBase ambient.field
      ambient.below frobenius exponent_one (n * n) (Nat.mul_pos n_pos n_pos)
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField ambientBase ambient.field ambient.below σn)
          (le_baseField
            (D.frobeniusFixedField ambientBase ambient.field ambient.below σn)))
  /-- The relative quotient between the `n`- and `n²`-power fixed fields is finite. -/
  relativeFinite :
    let σ := D.frobeniusPowerOfDegreeOne ambientBase ambient.field
      ambient.below frobenius exponent_one n n_pos
    let σn := D.frobeniusPowerOfDegreeOne ambientBase ambient.field
      ambient.below frobenius exponent_one (n * n) (Nat.mul_pos n_pos n_pos)
    let hTS := D.frobeniusPowerFixedField_le ambientBase ambient.field
      ambient.below frobenius exponent_one n n n_pos n_pos
    Finite
      ((D.frobeniusFixedField ambientBase ambient.field ambient.below σ).toSubgroup ⧸
        extensionSubgroup
          (D.frobeniusFixedField ambientBase ambient.field ambient.below σ)
          (D.frobeniusFixedField ambientBase ambient.field ambient.below σn)
          hTS)

namespace FrobeniusPowerFixedFieldTower

variable {D : DegreeData G} [IsTopologicalGroup G]

/-- Forget ambient finiteness while retaining its Galois structure. -/
noncomputable def ambientGalois (P : FrobeniusPowerFixedFieldTower D) :
    GaloisSubextension P.ambientBase.field :=
  P.ambient.toGaloisSubextension

/-- The Frobenius element `φⁿ` defining the lower fixed field. -/
def baseFrobenius (P : FrobeniusPowerFixedFieldTower D) :
    D.FrobeniusElements P.ambientBase P.ambient.field P.ambient.below :=
  D.frobeniusPowerOfDegreeOne P.ambientBase P.ambient.field P.ambient.below
    P.frobenius P.exponent_one P.n P.n_pos

/-- The Frobenius element `φⁿ²` defining the upper fixed field. -/
def fieldFrobenius (P : FrobeniusPowerFixedFieldTower D) :
    D.FrobeniusElements P.ambientBase P.ambient.field P.ambient.below :=
  D.frobeniusPowerOfDegreeOne P.ambientBase P.ambient.field P.ambient.below
    P.frobenius P.exponent_one (P.n * P.n)
      (Nat.mul_pos P.n_pos P.n_pos)

/-- The original Frobenius commutes with its `n`-th power. -/
theorem frobenius_commute_base (P : FrobeniusPowerFixedFieldTower D) :
    P.frobenius.1 * P.baseFrobenius.1 =
      P.baseFrobenius.1 * P.frobenius.1 := by
  simpa [baseFrobenius] using
    ((Commute.refl P.frobenius.1).pow_right P.n).eq

/-- The original Frobenius commutes with its `n²`-th power. -/
theorem frobenius_commute_field (P : FrobeniusPowerFixedFieldTower D) :
    P.frobenius.1 * P.fieldFrobenius.1 =
      P.fieldFrobenius.1 * P.frobenius.1 := by
  simpa [fieldFrobenius] using
    ((Commute.refl P.frobenius.1).pow_right (P.n * P.n)).eq

/-- Inclusion of the field fixed by `φⁿ²` into the field fixed by `φⁿ`. -/
theorem field_le_base (P : FrobeniusPowerFixedFieldTower D) :
    (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
        P.fieldFrobenius).toSubgroup ≤
      (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
        P.baseFrobenius).toSubgroup :=
  D.frobeniusPowerFixedField_le P.ambientBase P.ambient.field P.ambient.below
    P.frobenius P.exponent_one P.n P.n P.n_pos P.n_pos

/-- Relative finiteness in the fixed-field presentation used by the
Frobenius action and norm lemmas.  The witness is projected from the power
tower rather than requested again from callers. -/
instance relativeRepresentedQuotientFinite
    (P : FrobeniusPowerFixedFieldTower D) :
    Finite
      ((D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
          P.baseFrobenius).toSubgroup ⧸
        extensionSubgroup
          (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
            P.baseFrobenius)
          (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
            P.fieldFrobenius)
          P.field_le_base) :=
  P.relativeFinite

/-- Absolute finiteness of the lower fixed field in the presentation used by
the Frobenius action API. -/
instance baseRepresentedAbsoluteFinite
    (P : FrobeniusPowerFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
            P.baseFrobenius)
          (le_baseField
            (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
              P.baseFrobenius))) :=
  P.baseAbsoluteFinite

/-- Absolute finiteness of the upper fixed field in the presentation used by
the Frobenius action API. -/
instance fieldRepresentedAbsoluteFinite
    (P : FrobeniusPowerFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
            P.fieldFrobenius)
          (le_baseField
            (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
              P.fieldFrobenius))) :=
  P.fieldAbsoluteFinite

/-- The power construction as the canonical fixed-field tower bundle. -/
noncomputable def toFrobeniusFixedFieldTower
    (P : FrobeniusPowerFixedFieldTower D) [T2Space G] :
    FrobeniusFixedFieldTower D where
  ambientBase := P.ambientBase
  ambient := P.ambientGalois
  baseFrobenius := P.baseFrobenius
  fieldFrobenius := P.fieldFrobenius
  field_le_base := P.field_le_base
  finiteQuotient := P.relativeFinite
  baseAbsoluteFinite := P.baseAbsoluteFinite
  fieldAbsoluteFinite := P.fieldAbsoluteFinite
  normal :=
    D.frobeniusPowerFixedField_normal P.ambientBase P.ambient.field
      P.ambient.below P.frobenius P.exponent_one P.n P.n P.n_pos P.n_pos
  commute := by
    change P.baseFrobenius.1 * P.fieldFrobenius.1 =
      P.fieldFrobenius.1 * P.baseFrobenius.1
    simpa [baseFrobenius, fieldFrobenius] using
      ((Commute.refl P.frobenius.1).pow_pow P.n (P.n * P.n)).eq

/-- The power tower together with the already assumed finiteness of its
ambient extension. -/
noncomputable def toFiniteAmbientFrobeniusFixedFieldTower
    (P : FrobeniusPowerFixedFieldTower D) [T2Space G] :
    FiniteAmbientFrobeniusFixedFieldTower D where
  toFrobeniusFixedFieldTower := P.toFrobeniusFixedFieldTower
  ambientFinite := by
    change Finite P.ambient.toGaloisSubextension.extensionQuotient
    exact Finite.of_equiv P.ambient.extensionQuotient
      P.ambient.toGaloisExtensionQuotientMulEquiv

end FrobeniusPowerFixedFieldTower

end DegreeData

end

end ClassFormation
