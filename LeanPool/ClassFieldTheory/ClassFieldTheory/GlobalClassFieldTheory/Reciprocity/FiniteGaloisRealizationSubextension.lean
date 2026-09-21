/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationCore
/-!
# The finite Galois subextension attached to a number-field tower

This module realizes `L / K` as a finite Galois subextension inside the common
rational separable closure.  It packages the relevant fixing subgroups,
normality, and finite-index data for abstract reciprocity.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open CyclicCohomology
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The relative fixing subgroup in the compatible realization is
normal.  This is the existing LCFT ambient-embedding theorem specialized
to the number-field tower. -/
theorem numberFieldTowerExtensionSubgroup_normal :
    (extensionSubgroup
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).Normal := by
  let j := numberFieldSeparableClosureEmbedding L
  let i :=
    j.comp (IsScalarTower.toAlgHom ℚ K L)
  let : Algebra K (SeparableClosure ℚ) :=
    i.toRingHom.toAlgebra
  let e := numberFieldTowerSeparableClosureEquiv K L
  change
    (extensionSubgroup
      (closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (AlgHom.fieldRange i))
      (closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (AlgHom.fieldRange j))
      _).Normal
  exact
    ambientEmbeddedExtensionSubgroup_normal
      ℚ K L j e

/-- The relative quotient of fixing subgroups in the compatible
realization is finite. -/
theorem numberFieldTowerExtensionQuotient_finite :
    letI :=
      numberFieldTowerExtensionSubgroup_normal K L
    Finite
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) := by
  let j := numberFieldSeparableClosureEmbedding L
  let i :=
    j.comp (IsScalarTower.toAlgHom ℚ K L)
  let : Algebra K (SeparableClosure ℚ) :=
    i.toRingHom.toAlgebra
  let e := numberFieldTowerSeparableClosureEquiv K L
  change
    Finite
      ((closedFixingSubgroup ℚ (SeparableClosure ℚ)
          (AlgHom.fieldRange i)).toSubgroup ⧸
        extensionSubgroup
          (closedFixingSubgroup ℚ (SeparableClosure ℚ)
            (AlgHom.fieldRange i))
          (closedFixingSubgroup ℚ (SeparableClosure ℚ)
            (AlgHom.fieldRange j))
          _)
  exact
    ambientEmbeddedExtensionQuotient_finite
      ℚ K L j e

/-- The compatible realization of `L / K` as the finite Galois
subextension consumed by abstract reciprocity. -/
noncomputable def numberFieldTowerFiniteGaloisSubextension :
    FiniteGaloisSubextension
      (numberFieldTowerBaseSubgroup K L) where
  field := numberFieldTowerTopSubgroup L
  below := numberFieldTowerTopSubgroup_le_baseSubgroup K L
  normal := numberFieldTowerExtensionSubgroup_normal K L
  finite := by
    let :=
      numberFieldTowerExtensionSubgroup_normal K L
    exact numberFieldTowerExtensionQuotient_finite K L

/-- The lower fixing subgroup, with its finite absolute-index witness,
is the finite abstract field consumed by abstract reciprocity. -/
@[reducible]
noncomputable def numberFieldTowerFiniteAbstractField :
    FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  field := numberFieldTowerBaseSubgroup K L
  finite := by
    simpa only [numberFieldTowerBaseSubgroup,
      numberFieldTowerBaseField] using
      (ambientEmbeddedAbsoluteQuotientFinite
        ℚ K (numberFieldTowerLowerEmbedding K L))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The compatible embedded absolute Galois subgroup of a number
field is open in the rational absolute Galois group. -/
theorem numberFieldTowerBaseSubgroup_isOpen :
    IsOpen
      ((numberFieldTowerBaseSubgroup K L :
          ClosedSubgroup
            (Gal(SeparableClosure ℚ / ℚ))) :
        Set (Gal(SeparableClosure ℚ / ℚ))) :=
  abstractFiniteClosedSubgroup_isOpen
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (numberFieldTowerFiniteAbstractField K L).finite

/-- The quotient represented by the compatible abstract subextension is
the actual `Gal(L / K)`. -/
noncomputable def
    numberFieldTowerExtensionQuotientEquivGaloisGroup :
    (numberFieldTowerFiniteGaloisSubextension K L).extensionQuotient ≃*
      Gal(L / K) := by
  let j := numberFieldSeparableClosureEmbedding L
  let i :=
    j.comp (IsScalarTower.toAlgHom ℚ K L)
  letI : Algebra K (SeparableClosure ℚ) :=
    i.toRingHom.toAlgebra
  let e := numberFieldTowerSeparableClosureEquiv K L
  let H₀ :=
    closedFixingSubgroup ℚ (SeparableClosure ℚ)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup ℚ (SeparableClosure ℚ)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change j.fieldRange.fixingSubgroup ≤ i.fieldRange.fixingSubgroup
    apply i.fieldRange.fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap K L y, rfl⟩
  letI : (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal
      ℚ K L j e
  change
    (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) ≃*
      Gal(L / K)
  exact
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      ℚ K L j e

/-- Under the compatible realization, the finite quotient class of an
absolute automorphism is its genuine restriction to `L`. -/
theorem
    numberFieldTowerExtensionQuotientEquivGaloisGroup_mk_baseSubgroupEquiv
    (σ :
      letI : Algebra K (SeparableClosure ℚ) :=
        numberFieldTowerSeparableClosureBaseAlgebra K L
      Gal(SeparableClosure ℚ / K)) :
    letI : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    letI :=
      numberFieldTowerExtensionSubgroup_normal K L
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
        (QuotientGroup.mk
          (numberFieldTowerSeparableClosureEquivBaseSubgroup
            K L σ)) =
      AlgEquiv.restrictNormalHom L σ := by
  let j :=
    numberFieldSeparableClosureEmbedding L
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let e :=
    numberFieldTowerSeparableClosureEquiv K L
  let :=
    numberFieldTowerExtensionSubgroup_normal K L
  apply AlgEquiv.ext
  intro x
  apply j.injective
  calc
    j
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (QuotientGroup.mk
            (numberFieldTowerSeparableClosureEquivBaseSubgroup
              K L σ)) x) =
        (numberFieldTowerSeparableClosureEquivBaseSubgroup
          K L σ).1.1 (j x) := by
      convert
        (ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
          ℚ K L j e
          (numberFieldTowerSeparableClosureEquivBaseSubgroup
            K L σ) x) using 1; rfl
    _ = σ (j x) := rfl
    _ =
        j
          ((AlgEquiv.restrictNormalHom L σ) x) := by
      exact
        (AlgEquiv.restrictNormal_commutes σ L x).symm

end Reciprocity
end GlobalClassFieldTheory

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The compatible finite Galois realization of an abelian number
field extension, bundled with commutativity of its actual abstract
quotient. -/
noncomputable def numberFieldTowerFiniteAbelianSubextension
    [hAbelian : IsAbelianGalois K L] :
    FiniteAbelianSubextension
      (numberFieldTowerBaseSubgroup K L) := by
  letI : IsGalois K L := hAbelian.toIsGalois
  exact
    { toFiniteGaloisExtension :=
        numberFieldTowerFiniteGaloisSubextension K L
      commutative := by
        let e :=
          numberFieldTowerExtensionQuotientEquivGaloisGroup K L
        exact
          { is_comm :=
              ⟨fun x y => by
                apply e.injective
                rw [map_mul, map_mul]
                exact
                  hAbelian.toIsMulCommutative.is_comm.comm
                    (e x) (e y)⟩ } }

end Reciprocity
end GlobalClassFieldTheory
