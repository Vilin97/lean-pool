/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction
/-!
# The completed theta-intertwining theorem: a prescribed Frobenius lift on the completed level

Arithmetic Frobenius on `(AlgebraicClosure κ)((T))` fixes the primitive
Lubin--Tate polynomial.  Using its primitive power basis, we extend
Frobenius to the completed level while prescribing the image of the
primitive point to be a chosen unit bracket.  The resulting semilinear field
endomorphism is surjective because that bracket is again a primitive
generator.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries Polynomial PowerSeries


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The completed unramified base carries coefficient-extension scalars for lifting Frobenius. -/
noncomputable local instance equalCharacteristicCompletedFrobeniusLiftBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

/-- The ordinary completed-base algebra structure on the splitting field,
named explicitly so it can coexist with its Frobenius twist. -/
@[reducible]
noncomputable def equalCharacteristicCompletedLevelOriginalAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  inferInstance

/-- The codomain algebra structure whose scalar map is arithmetic
Frobenius followed by the ordinary scalar inclusion. -/
@[reducible]
noncomputable def equalCharacteristicCompletedLevelFrobeniusAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  RingHom.toAlgebra
    ((algebraMap
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)).comp
      (equalCharacteristicCompletedUnramifiedFrobenius F.residueField).toAlgHom.toRingHom)

/-- The twisted level algebra map applies completed Frobenius before scalar extension. -/
theorem equalCharacteristicCompletedLevelFrobeniusAlgebra_algebraMap
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : equalCharacteristicCompletedUnramifiedField F.residueField) :
    @algebraMap
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)
        _ _ (equalCharacteristicCompletedLevelFrobeniusAlgebra F n) a =
      algebraMap
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)
        (equalCharacteristicCompletedUnramifiedFrobenius F.residueField a) :=
  rfl

/-- Arithmetic Frobenius fixes the completed primitive polynomial because
all of its coefficients descend to `κ((T))`. -/
theorem equalCharacteristicCompletedPrimitivePolynomial_frobenius
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedPrimitivePolynomial F n).map
        (equalCharacteristicCompletedUnramifiedFrobenius F.residueField).toAlgHom.toRingHom =
      equalCharacteristicCompletedPrimitivePolynomial F n := by
  unfold equalCharacteristicCompletedPrimitivePolynomial
  have hcomp :
      ((equalCharacteristicCompletedUnramifiedFrobenius F.residueField).toAlgHom.toRingHom).comp
          (algebraMap F.residueField⸨X⸩
            (equalCharacteristicCompletedUnramifiedField F.residueField)) =
        algebraMap F.residueField⸨X⸩
          (equalCharacteristicCompletedUnramifiedField F.residueField) := by
    apply RingHom.ext
    intro a
    exact
      (equalCharacteristicCompletedUnramifiedFrobenius F.residueField).commutes a
  rw [Polynomial.map_map, hcomp]

/-- A unit bracket is a root of the primitive minimal polynomial for the
Frobenius-twisted codomain algebra structure. -/
theorem equalCharacteristicCompletedUnitRoot_aeval_minpoly_frobenius
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    @Polynomial.aeval
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)
        _ _ (equalCharacteristicCompletedLevelFrobeniusAlgebra F n)
        (equalCharacteristicCompletedUnitRoot F n a)
        (minpoly (equalCharacteristicCompletedUnramifiedField F.residueField)
          (equalCharacteristicCompletedPrimitiveRoot F n)) = 0 := by
  rw [equalCharacteristicCompletedPrimitiveRoot_minpoly]
  change Polynomial.eval₂
      ((algebraMap
        (equalCharacteristicCompletedUnramifiedField F.residueField)
          (equalCharacteristicCompletedLevelField F n)).comp
        (equalCharacteristicCompletedUnramifiedFrobenius F.residueField).toAlgHom.toRingHom)
      (equalCharacteristicCompletedUnitRoot F n a)
      (equalCharacteristicCompletedPrimitivePolynomial F n) = 0
  rw [← Polynomial.eval₂_map,
    equalCharacteristicCompletedPrimitivePolynomial_frobenius]
  rw [← Polynomial.eval_map]
  exact equalCharacteristicCompletedUnitRoot_isRoot F n a

/-- The semilinear algebra homomorphism extending arithmetic Frobenius and
sending the primitive point to the prescribed unit bracket. -/
noncomputable def equalCharacteristicCompletedFrobeniusLiftAlgHom
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    @AlgHom
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)
      (equalCharacteristicCompletedLevelField F n)
      _ _ _
      (equalCharacteristicCompletedLevelOriginalAlgebra F n)
      (equalCharacteristicCompletedLevelFrobeniusAlgebra F n) :=
  @PowerBasis.lift
    (equalCharacteristicCompletedLevelField F n) _
    (equalCharacteristicCompletedUnramifiedField F.residueField) _
    (equalCharacteristicCompletedLevelOriginalAlgebra F n)
    (equalCharacteristicCompletedLevelField F n) _
    (equalCharacteristicCompletedLevelFrobeniusAlgebra F n)
    (equalCharacteristicCompletedPrimitivePowerBasis F n)
    (equalCharacteristicCompletedUnitRoot F n a) (by
      rw [equalCharacteristicCompletedPrimitivePowerBasis_gen]
      exact equalCharacteristicCompletedUnitRoot_aeval_minpoly_frobenius F n a)

/-- The semilinear Frobenius homomorphism sends the primitive root to its unit transform. -/
@[simp]
theorem equalCharacteristicCompletedFrobeniusLiftAlgHom_primitiveRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicCompletedFrobeniusLiftAlgHom F n a
        (equalCharacteristicCompletedPrimitiveRoot F n) =
      equalCharacteristicCompletedUnitRoot F n a := by
  change equalCharacteristicCompletedFrobeniusLiftAlgHom F n a
      (equalCharacteristicCompletedPrimitivePowerBasis F n).gen = _
  exact @PowerBasis.lift_gen
    (equalCharacteristicCompletedLevelField F n) _
    (equalCharacteristicCompletedUnramifiedField F.residueField) _
    (equalCharacteristicCompletedLevelOriginalAlgebra F n)
    (equalCharacteristicCompletedLevelField F n) _
    (equalCharacteristicCompletedLevelFrobeniusAlgebra F n)
    (equalCharacteristicCompletedPrimitivePowerBasis F n)
    (equalCharacteristicCompletedUnitRoot F n a)
    (equalCharacteristicCompletedUnitRoot_aeval_minpoly_frobenius F n a)

/-- The underlying field homomorphism of the prescribed Frobenius lift. -/
noncomputable def equalCharacteristicCompletedFrobeniusLift
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicCompletedLevelField F n →+*
      equalCharacteristicCompletedLevelField F n :=
  @AlgHom.toRingHom
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedLevelField F n)
    (equalCharacteristicCompletedLevelField F n)
    _ _ _
    (equalCharacteristicCompletedLevelOriginalAlgebra F n)
    (equalCharacteristicCompletedLevelFrobeniusAlgebra F n)
    (equalCharacteristicCompletedFrobeniusLiftAlgHom F n a)

/-- The Frobenius lift acts on base scalars by completed Frobenius. -/
@[simp]
theorem equalCharacteristicCompletedFrobeniusLift_algebraMap
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ)
    (b : equalCharacteristicCompletedUnramifiedField F.residueField) :
    equalCharacteristicCompletedFrobeniusLift F n a
        (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
          (equalCharacteristicCompletedLevelField F n) b) =
      algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)
        (equalCharacteristicCompletedUnramifiedFrobenius F.residueField b) := by
  change equalCharacteristicCompletedFrobeniusLiftAlgHom F n a
      (@algebraMap
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)
        _ _ (equalCharacteristicCompletedLevelOriginalAlgebra F n) b) =
    @algebraMap
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)
      _ _ (equalCharacteristicCompletedLevelFrobeniusAlgebra F n) b
  exact @AlgHom.commutes
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedLevelField F n)
    (equalCharacteristicCompletedLevelField F n)
    _ _ _
    (equalCharacteristicCompletedLevelOriginalAlgebra F n)
    (equalCharacteristicCompletedLevelFrobeniusAlgebra F n)
    (equalCharacteristicCompletedFrobeniusLiftAlgHom F n a) b

/-- The Frobenius lift sends the primitive root to the corresponding unit root. -/
@[simp]
theorem equalCharacteristicCompletedFrobeniusLift_primitiveRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicCompletedFrobeniusLift F n a
        (equalCharacteristicCompletedPrimitiveRoot F n) =
      equalCharacteristicCompletedUnitRoot F n a :=
  by
    change equalCharacteristicCompletedFrobeniusLiftAlgHom F n a
        (equalCharacteristicCompletedPrimitiveRoot F n) = _
    exact equalCharacteristicCompletedFrobeniusLiftAlgHom_primitiveRoot F n a

/-- The prescribed semilinear Frobenius lift is onto: its range contains
the whole completed base and the primitive generator given by the unit
bracket. -/
theorem equalCharacteristicCompletedFrobeniusLift_surjective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    Function.Surjective (equalCharacteristicCompletedFrobeniusLift F n a) := by
  let A := equalCharacteristicCompletedUnramifiedField F.residueField
  let E := equalCharacteristicCompletedLevelField F n
  let δ : E →+* E := equalCharacteristicCompletedFrobeniusLift F n a
  let R : Subring E := δ.range
  have hbase (b : A) : algebraMap A E b ∈ R := by
    refine ⟨algebraMap A E
      ((equalCharacteristicCompletedUnramifiedFrobenius F.residueField).symm b), ?_⟩
    change δ (algebraMap A E
      ((equalCharacteristicCompletedUnramifiedFrobenius F.residueField).symm b)) =
        algebraMap A E b
    rw [show δ = equalCharacteristicCompletedFrobeniusLift F n a by rfl,
      equalCharacteristicCompletedFrobeniusLift_algebraMap,
      (equalCharacteristicCompletedUnramifiedFrobenius
        F.residueField).apply_symm_apply]
  let S : Subalgebra A E :=
    { R with
      algebraMap_mem' := hbase }
  have hy : equalCharacteristicCompletedUnitRoot F n a ∈ S := by
    refine ⟨equalCharacteristicCompletedPrimitiveRoot F n, ?_⟩
    exact equalCharacteristicCompletedFrobeniusLift_primitiveRoot F n a
  have hle :
      Algebra.adjoin A
          ({equalCharacteristicCompletedUnitRoot F n a} : Set E) ≤ S := by
    apply Algebra.adjoin_le
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact hy
  rw [show Algebra.adjoin A
      ({equalCharacteristicCompletedUnitRoot F n a} : Set E) = ⊤ by
        exact equalCharacteristicCompletedUnitRoot_adjoin_eq_top F n a] at hle
  have hS : S = ⊤ := top_unique hle
  intro z
  have hz : z ∈ S := by rw [hS]; trivial
  exact hz

/-- The actual field automorphism extending arithmetic Frobenius and acting
on the primitive point by the prescribed unit bracket. -/
noncomputable def equalCharacteristicCompletedFrobeniusLiftEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicCompletedLevelField F n ≃+*
      equalCharacteristicCompletedLevelField F n :=
  RingEquiv.ofBijective (equalCharacteristicCompletedFrobeniusLift F n a)
    ⟨(equalCharacteristicCompletedFrobeniusLift F n a).injective,
      equalCharacteristicCompletedFrobeniusLift_surjective F n a⟩

/-- The Frobenius lift equivalence acts on base scalars by completed Frobenius. -/
@[simp]
theorem equalCharacteristicCompletedFrobeniusLiftEquiv_algebraMap
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ)
    (b : equalCharacteristicCompletedUnramifiedField F.residueField) :
    equalCharacteristicCompletedFrobeniusLiftEquiv F n a
        (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
          (equalCharacteristicCompletedLevelField F n) b) =
      algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)
        (equalCharacteristicCompletedUnramifiedFrobenius F.residueField b) :=
  equalCharacteristicCompletedFrobeniusLift_algebraMap F n a b

/-- The Frobenius lift equivalence sends the primitive root to its unit transform. -/
@[simp]
theorem equalCharacteristicCompletedFrobeniusLiftEquiv_primitiveRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicCompletedFrobeniusLiftEquiv F n a
        (equalCharacteristicCompletedPrimitiveRoot F n) =
      equalCharacteristicCompletedUnitRoot F n a :=
  equalCharacteristicCompletedFrobeniusLift_primitiveRoot F n a

end EqualCharacteristic
end LubinTate
