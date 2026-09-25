/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedPolynomialEvaluation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaAtCompletedLevel
/-!
# The completed theta-intertwining theorem: the direct target level inside the completed source
  level

The analytic value `theta(lambda)` is primitive torsion for the target
parameter `uT`.  We identify `uT` with the changed Laurent uniformizer,
deduce the actual primitive-polynomial equation, and obtain the canonical
embedding of the finite target Lubin--Tate level into the completed field.
-/

@[expose] public section

noncomputable
section

open scoped LaurentSeries Polynomial PowerSeries


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The Laurent-series base acts on the completed unramified field through the coefficient
embedding. -/
noncomputable local instance equalCharacteristicDirectTargetBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

/-- The completed level field is a Laurent-series algebra through the completed unramified base. -/
noncomputable local instance equalCharacteristicDirectTargetLevelAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  RingHom.toAlgebra
    ((algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)).comp
      (algebraMap F.residueField⸨X⸩
        (equalCharacteristicCompletedUnramifiedField F.residueField)))

local instance equalCharacteristicDirectTargetScalarTower
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

private instance equalCharacteristicDirectTargetLevelCharP
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    CharP (equalCharacteristicCompletedLevelField F n)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)).injective
    F.residueCharacteristic

/-- The direct analytic target parameter is exactly the image of the
changed Laurent uniformizer `uT`. -/
theorem equalCharacteristicCompletedLevelBaseHom_changedUniformizer
    (F : LocalField.{u, v} K)
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedLevelBaseHom F n
        (equalCharacteristicChangedLaurentUniformizer F a) =
      equalCharacteristicDirectThetaTargetUniformizer F a n := by
  change algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)
      (algebraMap F.residueField⸨X⸩
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          ((a : F.residueField⟦X⟧) * PowerSeries.X))) =
    algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)
      (algebraMap (AlgebraicClosure F.residueField)⟦X⟧
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (PowerSeries.map
            (algebraMap F.residueField (AlgebraicClosure F.residueField))
            (a : F.residueField⟦X⟧) * PowerSeries.X))
  apply congrArg (algebraMap
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedLevelField F n))
  have h := DFunLike.congr_fun
    (equalCharacteristicPowerSeriesLaurent_baseChange_commutes F)
    ((a : F.residueField⟦X⟧) * PowerSeries.X)
  simpa [RingHom.comp_apply, map_mul] using h.symm

/-- The genuine analytic value `theta(lambda)` is a root of the target
primitive polynomial over `k((T))`. -/
theorem equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isRoot_target
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    ((equalCharacteristicChangedPrimitivePolynomial F a n).map
      (equalCharacteristicCompletedLevelBaseHom F n)).IsRoot
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
        equalCharacteristicCompletedLevelField F n) := by
  apply equalCharacteristicChangedPrimitivePolynomial_isRoot_of_primitive
    F a
  · simpa [equalCharacteristicCompletedLevelBaseHom_changedUniformizer]
      using equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_torsion F a n
  · simpa [equalCharacteristicCompletedLevelBaseHom_changedUniformizer]
      using
        equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_not_torsion_pred
          F a n

/-- The finite target `uT` level embedded into the standard completed level,
sending its chosen generator to the analytic value `theta(lambda)`. -/
noncomputable def equalCharacteristicDirectTargetLevelFieldToCompleted
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedLevelField F a n
      →ₐ[F.residueField⸨X⸩]
        equalCharacteristicCompletedLevelField F n := by
  have hrootAeval : Polynomial.aeval
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
        equalCharacteristicCompletedLevelField F n)
      (minpoly F.residueField⸨X⸩
        (chosenEqualCharacteristicChangedPrimitiveRoot F a n)) = 0 := by
    rw [← equalCharacteristicChangedPrimitivePolynomial_eq_minpoly]
    rw [Polynomial.aeval_def,
      IsScalarTower.algebraMap_eq F.residueField⸨X⸩
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)]
    simpa [Polynomial.IsRoot, Polynomial.eval_map,
      equalCharacteristicCompletedLevelBaseHom] using
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isRoot_target
        F a n)
  let baseHom :
      F.residueField⸨X⸩ →ₐ[F.residueField⸨X⸩]
        equalCharacteristicCompletedLevelField F n :=
    Algebra.ofId F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n)
  have hroot :
      Polynomial.eval₂ baseHom
          (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
            equalCharacteristicCompletedLevelField F n)
          (minpoly F.residueField⸨X⸩
            (chosenEqualCharacteristicChangedPrimitiveRoot F a n)) = 0 := by
    simpa [baseHom, Polynomial.aeval_def] using hrootAeval
  let lift :
      AdjoinRoot (minpoly F.residueField⸨X⸩
        (chosenEqualCharacteristicChangedPrimitiveRoot F a n))
        →ₐ[F.residueField⸨X⸩]
          equalCharacteristicCompletedLevelField F n :=
    AdjoinRoot.liftAlgHom _ baseHom
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
        equalCharacteristicCompletedLevelField F n) hroot
  exact lift.comp
    (IntermediateField.adjoinRootEquivAdjoin F.residueField⸨X⸩
      (chosenEqualCharacteristicChangedPrimitiveRoot_isIntegral F a n)).symm.toAlgHom

/-- The target-level embedding has the prescribed value on its chosen
primitive generator. -/
@[simp]
theorem equalCharacteristicDirectTargetLevelFieldToCompleted_generator
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicDirectTargetLevelFieldToCompleted F a n
        (equalCharacteristicChangedLevelGenerator F a n) =
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
        equalCharacteristicCompletedLevelField F n) := by
  simp only [equalCharacteristicDirectTargetLevelFieldToCompleted,
    equalCharacteristicChangedLevelGenerator]
  rw [AlgHom.comp_apply]
  have hgen :
      (IntermediateField.adjoinRootEquivAdjoin F.residueField⸨X⸩
          (chosenEqualCharacteristicChangedPrimitiveRoot_isIntegral F a n)).symm.toAlgHom
          (IntermediateField.AdjoinSimple.gen F.residueField⸨X⸩
            (chosenEqualCharacteristicChangedPrimitiveRoot F a n)) =
        AdjoinRoot.root
          (minpoly F.residueField⸨X⸩
            (chosenEqualCharacteristicChangedPrimitiveRoot F a n)) :=
    IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen
      F.residueField⸨X⸩
      (chosenEqualCharacteristicChangedPrimitiveRoot_isIntegral F a n)
  rw [hgen, AdjoinRoot.liftAlgHom_root]

end EqualCharacteristic
end LubinTate
