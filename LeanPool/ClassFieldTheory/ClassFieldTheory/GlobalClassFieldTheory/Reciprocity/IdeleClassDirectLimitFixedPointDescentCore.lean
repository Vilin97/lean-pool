/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteLevel
/-!
# Descent of fixed rational idele classes

An element of the rational idele-class direct limit which is fixed over a
finite intermediate field is represented at a finite Galois level.  Its
actual tower base change is Galois-fixed, hence descends to an idele class
of the intermediate field.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- If a finite-level representative of the rational idele-class direct
limit is fixed by the absolute Galois subgroup over `K`, then its actual
tower base change from `ℚ` to `K` is fixed by `Gal(U/K)`. -/
theorem rationalTowerRelativeIdeleClass_fixed_of_directLimit_fixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    [IsScalarTower ℚ K U]
    [FiniteDimensional K U]
    [IsGalois K U]
    (h_algebraMap : ∀ x : K,
      ((algebraMap K U x : U) : SeparableClosure ℚ) =
        (x : SeparableClosure ℚ))
    (d : RelativeIdeleGroup.ClassGroup ℚ U)
    (z : rationalIdeleClassDirectLimit)
    (hzU :
      z = (⟦⟨U, d⟩⟧ : rationalIdeleClassDirectLimit))
    (hz_fixed :
      ∀ σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ,
        σ ∈ K.fixingSubgroup → σ • z = z) :
    towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
          ((TowerRelativeIdeleGroup.classGroupEquiv
            ℚ K U).symm d) ∈
      RelativeIdeleGroup.galoisFixedClassSubgroup K U := by
  intro η
  let τ : U ≃ₐ[ℚ] U :=
    η.restrictScalars ℚ
  obtain ⟨σ, hσU⟩ :=
    (AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := U) (E := SeparableClosure ℚ)) τ
  have hσK : σ ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    let yK : K := ⟨y, hy⟩
    let yU : U := algebraMap K U yK
    have hη : η yU = yU := by
      exact η.commutes yK
    have hres :=
      DFunLike.congr_fun hσU yU
    calc
      σ y =
          σ ((yU : U) : SeparableClosure ℚ) := by
        rw [h_algebraMap yK]
      _ =
          (((AlgEquiv.restrictNormalHom U σ) yU : U) :
            SeparableClosure ℚ) :=
        (AlgEquiv.restrictNormal_commutes σ U yU).symm
      _ = ((τ yU : U) : SeparableClosure ℚ) :=
        congrArg Subtype.val hres
      _ = ((η yU : U) : SeparableClosure ℚ) := rfl
      _ = ((yU : U) : SeparableClosure ℚ) :=
        congrArg Subtype.val hη
      _ = y :=
        h_algebraMap yK
  have hzσ := hz_fixed σ hσK
  rw [hzU, DirectLimit.smul_def] at hzσ
  have hdQ :
      (AlgEquiv.restrictNormalHom U σ) • d = d :=
    (rationalRelativeIdeleClassToDirectLimit_injective U) hzσ
  have hdτ : τ • d = d := by
    rw [← hσU]
    exact hdQ
  calc
    η •
        towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
          ((TowerRelativeIdeleGroup.classGroupEquiv
            ℚ K U).symm d) =
        towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
          ((TowerRelativeIdeleGroup.classGroupEquiv
            ℚ K U).symm
            ((η.restrictScalars ℚ) • d)) :=
      (towerRelativeIdeleClassBaseChangeMulEquiv_smul
        ℚ K U η d).symm
    _ =
        towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
          ((TowerRelativeIdeleGroup.classGroupEquiv
            ℚ K U).symm d) :=
      congrArg
        (fun a =>
          towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
            ((TowerRelativeIdeleGroup.classGroupEquiv
              ℚ K U).symm a))
        hdτ

/-- An algebra structure on nested rational intermediate fields is the
canonical one induced by intermediate-field inclusion whenever its algebra
map agrees with the ambient inclusions. -/
theorem rationalIntermediateField_algebra_eq_inclusion
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    (hKU :
      K ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)))
    (h_algebraMap : ∀ x : K,
      ((algebraMap K U x : U) : SeparableClosure ℚ) =
        (x : SeparableClosure ℚ)) :
    (inferInstance : Algebra K U) =
      (IntermediateField.inclusion hKU).toRingHom.toAlgebra := by
  apply Algebra.algebra_ext
  intro x
  apply Subtype.ext
  exact h_algebraMap x

/-- The actual tower comparison from rational relative idele classes at `U`
to relative idele classes over the intermediate field `K`. -/
noncomputable def rationalRelativeIdeleClassTowerBaseChangeEquiv
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    [IsScalarTower ℚ K U]
    [FiniteDimensional K U]
    [IsGalois K U] :
    RelativeIdeleGroup.ClassGroup ℚ U ≃*
      RelativeIdeleGroup.ClassGroup K U :=
  (TowerRelativeIdeleGroup.classGroupEquiv
    ℚ K U).symm.trans
      (towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U)

/-- The actual idele class group of `K`, identified with the subgroup of
relative idele classes at `U` fixed by `Gal(U/K)`. This transports the
Herbrand fixed-subgroup target of `baseIdeleClassEquivFixed` to the concrete
Galois-fixed subgroup. -/
noncomputable def rationalIntermediateIdeleClassEquivGaloisFixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    [IsScalarTower ℚ K U]
    [FiniteDimensional K U]
    [IsGalois K U] :
    IdeleClassGroup K ≃*
      RelativeIdeleGroup.galoisFixedClassSubgroup K U := by
  letI :
      MulDistribMulAction (U ≃ₐ[K] U)
        (RelativeIdeleGroup.ClassGroup K U) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K U
  exact
    (RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed K U).trans
      (MulEquiv.subgroupCongr
        (RelativeIdeleGroup.Cohomology.ideleClass_fixedSubgroup_eq_galoisFixed
          K U))

/-- Under the concrete fixed-point equivalence, an idele class maps to its
actual relative class inclusion. -/
@[simp]
theorem rationalIntermediateIdeleClassEquivGaloisFixed_coe
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    [IsScalarTower ℚ K U]
    [FiniteDimensional K U]
    [IsGalois K U]
    (q : IdeleClassGroup K) :
    ((rationalIntermediateIdeleClassEquivGaloisFixed K U q :
        RelativeIdeleGroup.galoisFixedClassSubgroup K U) :
      RelativeIdeleGroup.ClassGroup K U) =
        RelativeIdeleGroup.classInclusion K U q := by
  let :
      MulDistribMulAction (U ≃ₐ[K] U)
        (RelativeIdeleGroup.ClassGroup K U) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K U
  change
    ((RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed K U q :
        CyclicCohomology.ProfiniteCohomology.Herbrand.fixedSubgroup
          (U ≃ₐ[K] U)
          (RelativeIdeleGroup.ClassGroup K U)) :
      RelativeIdeleGroup.ClassGroup K U) =
        RelativeIdeleGroup.classInclusion K U q
  exact
    RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed_coe K U q


end Reciprocity
end GlobalClassFieldTheory
