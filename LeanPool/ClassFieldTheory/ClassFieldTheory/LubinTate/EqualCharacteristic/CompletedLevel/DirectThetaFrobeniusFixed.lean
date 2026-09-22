/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectBracketAtCompletedLevel
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusContinuity
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFirstIdentity
/-!
# The completed theta-intertwining theorem: Frobenius fixes the direct theta value

For the direct change of parameter `T -> uT`, the completed
Frobenius lift is prescribed by `[u⁻¹]` on the standard primitive point.
This file proves that it fixes the genuine convergent value `theta(lambda)`.

The proof first transports convergent power-series evaluations through the
semilinear Frobenius lift.  The first theta identity then reduces fixedness to
`[u]([u⁻¹](lambda)) = lambda`, which is the genuine finite bracket action
on the completed division point.
-/

noncomputable section

open Filter
open scoped LaurentSeries NNReal NormedField PowerSeries
  PowerSeries.WithPiTopology Topology Valued WithZero


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

private instance equalCharacteristicDirectThetaFixedLevelCharP
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    CharP (equalCharacteristicCompletedLevelField F n)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)).injective
    F.residueCharacteristic

/-- The Laurent-series base acts on the completed unramified field through the coefficient
embedding. -/
noncomputable local instance equalCharacteristicDirectThetaFixedBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

noncomputable local instance
    equalCharacteristicDirectThetaFixedBaseValuationIsNontrivial
    (F : LocalField.{u, v} K) :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰).IsNontrivial :=
  equalCharacteristicCompletedBaseValuationIsNontrivial F.residueField

/-- The discrete valuation on the completed unramified coefficient field has rank one. -/
noncomputable local instance
    equalCharacteristicDirectThetaFixedBaseValuationRankOne
    (F : LocalField.{u, v} K) :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰).RankOne :=
  equalCharacteristicCompletedBaseValuationRankOne F.residueField

/-- The canonical nontrivial norm on the completed unramified coefficient field. -/
noncomputable local instance equalCharacteristicDirectThetaFixedBaseNormedField
    (F : LocalField.{u, v} K) :
    NontriviallyNormedField
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedBaseNormedField F.residueField

/-- The canonical nontrivial norm on the completed Lubin–Tate field at level `n`. -/
noncomputable local instance equalCharacteristicDirectThetaFixedLevelNormedField
    (F : LocalField.{u, v} K) (n : ℕ) :
    NontriviallyNormedField (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelNormedField F n

noncomputable local instance equalCharacteristicDirectThetaFixedLevelIsUltrametric
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUltrametricDist (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelIsUltrametric F n

noncomputable local instance equalCharacteristicDirectThetaFixedLevelCompleteSpace
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelCompleteSpace F n

/-- The nonnegative-real-valued valuation on the completed Lubin–Tate field at level `n`. -/
noncomputable local instance equalCharacteristicDirectThetaFixedLevelValued
    (F : LocalField.{u, v} K) (n : ℕ) :
    Valued (equalCharacteristicCompletedLevelField F n) ℝ≥0 :=
  equalCharacteristicCompletedLevelValued F n

noncomputable local instance equalCharacteristicDirectThetaFixedIntegerLinearTopology
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsLinearTopology
      (Valued.integer (equalCharacteristicCompletedLevelField F n))
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerLinearTopology

noncomputable local instance equalCharacteristicDirectThetaFixedIntegerCompleteSpace
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerCompleteSpace

noncomputable local instance equalCharacteristicDirectThetaFixedIntegerUniformAddGroup
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUniformAddGroup
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerIsUniformAddGroup

private noncomputable local instance
    equalCharacteristicDirectThetaFixedCoefficientUniformSpace
    (F : LocalField.{u, v} K) :
    UniformSpace ((AlgebraicClosure F.residueField)⟦X⟧) := ⊥

private theorem equalCharacteristicDirectThetaFixedCoefficientHom_continuous
    (F : LocalField.{u, v} K) (n : ℕ) :
    Continuous (equalCharacteristicCompletedLevelCoefficientHom F n) :=
  continuous_of_discreteTopology

private noncomputable local instance
    equalCharacteristicDirectThetaFixedCoefficientAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra ((AlgebraicClosure F.residueField)⟦X⟧)
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  (equalCharacteristicCompletedLevelCoefficientHom F n).toAlgebra

/-- Restriction of the completed theta-intertwining theorem Frobenius lift to the spectral
valuation ring. -/
private noncomputable def equalCharacteristicCompletedIntegerFrobeniusLift
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) →+*
      Valued.integer (equalCharacteristicCompletedLevelField F n) where
  toFun x := ⟨equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹ x, by
    change ‖equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
      (x : equalCharacteristicCompletedLevelField F n)‖₊ ≤ 1
    exact_mod_cast (show
      ‖equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
        (x : equalCharacteristicCompletedLevelField F n)‖ ≤ 1 by
      rw [equalCharacteristicCompletedFrobeniusLift_norm]
      exact_mod_cast x.property)⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp]
private theorem equalCharacteristicCompletedIntegerFrobeniusLift_coe
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : Valued.integer (equalCharacteristicCompletedLevelField F n)) :
    ((equalCharacteristicCompletedIntegerFrobeniusLift F u n x :
      Valued.integer (equalCharacteristicCompletedLevelField F n)) :
        equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
        (x : equalCharacteristicCompletedLevelField F n) :=
  rfl

private theorem equalCharacteristicCompletedIntegerFrobeniusLift_continuous
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Continuous (equalCharacteristicCompletedIntegerFrobeniusLift F u n) := by
  exact
    ((equalCharacteristicCompletedFrobeniusLift_continuous F u n).comp
      continuous_subtype_val).subtype_mk _

private theorem
    equalCharacteristicCompletedIntegerFrobeniusLift_coefficientHom
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (f : (AlgebraicClosure F.residueField)⟦X⟧) :
    equalCharacteristicCompletedIntegerFrobeniusLift F u n
        (equalCharacteristicCompletedLevelCoefficientHom F n f) =
      equalCharacteristicCompletedLevelCoefficientHom F n
        (equalCharacteristicPowerSeriesFrobenius F.residueField f) := by
  apply Subtype.ext
  change equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
        (algebraMap
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)
        ((equalCharacteristicPowerSeriesToCompletedInteger F.residueField f :
          Valued.integer
            (equalCharacteristicCompletedUnramifiedField F.residueField)) :
          equalCharacteristicCompletedUnramifiedField F.residueField)) =
    algebraMap
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)
      ((equalCharacteristicPowerSeriesToCompletedInteger F.residueField
        (equalCharacteristicPowerSeriesFrobenius F.residueField f) :
        Valued.integer
          (equalCharacteristicCompletedUnramifiedField F.residueField)) :
        equalCharacteristicCompletedUnramifiedField F.residueField)
  rw [equalCharacteristicCompletedFrobeniusLiftEquiv_algebraMap]
  apply congrArg (algebraMap
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedLevelField F n))
  change
    equalCharacteristicCompletedUnramifiedFrobenius F.residueField
        (algebraMap ((AlgebraicClosure F.residueField)⟦X⟧)
          (equalCharacteristicCompletedUnramifiedField F.residueField) f) =
      algebraMap ((AlgebraicClosure F.residueField)⟦X⟧)
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicPowerSeriesFrobenius F.residueField f)
  exact
    equalCharacteristicCompletedUnramifiedFrobenius_algebraMap_powerSeries
      (k := F.residueField) f

private theorem equalCharacteristicCompletedIntegerFrobeniusLift_hasEval
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (hx : PowerSeries.HasEval x) :
    PowerSeries.HasEval
      (equalCharacteristicCompletedIntegerFrobeniusLift F u n x) := by
  change Tendsto
    (fun m : ℕ ↦
      (equalCharacteristicCompletedIntegerFrobeniusLift F u n x) ^ m)
    atTop (nhds 0)
  have h :=
    ((equalCharacteristicCompletedIntegerFrobeniusLift_continuous F u n).tendsto
      0).comp hx
  have hpow :
      (fun m : ℕ ↦
        (equalCharacteristicCompletedIntegerFrobeniusLift F u n x) ^ m) =
        (equalCharacteristicCompletedIntegerFrobeniusLift F u n) ∘
          (fun m : ℕ ↦ x ^ m) := by
    funext m
    exact (map_pow (equalCharacteristicCompletedIntegerFrobeniusLift F u n)
      x m).symm
  rw [hpow]
  simpa only [map_zero] using h

/-- Convergent evaluation is semilinear for the completed theta-intertwining theorem Frobenius
lift. -/
private theorem equalCharacteristicCompletedIntegerFrobeniusLift_evaluation
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (hx : PowerSeries.HasEval x)
    (f : ((AlgebraicClosure F.residueField)⟦X⟧)⟦X⟧) :
    equalCharacteristicCompletedIntegerFrobeniusLift F u n
        (equalCharacteristicCompletedLevelEvaluation F n x hx f) =
      equalCharacteristicCompletedLevelEvaluation F n
        (equalCharacteristicCompletedIntegerFrobeniusLift F u n x)
        (equalCharacteristicCompletedIntegerFrobeniusLift_hasEval F u n x hx)
        (PowerSeries.map
          (equalCharacteristicPowerSeriesFrobenius F.residueField) f) := by
  have hsource : HasSum
      (fun m : ℕ ↦
        equalCharacteristicCompletedLevelCoefficientHom F n
            (PowerSeries.coeff m f) * x ^ m)
      (equalCharacteristicCompletedLevelEvaluation F n x hx f) := by
    rw [equalCharacteristicCompletedLevelEvaluation,
      PowerSeries.coe_eval₂Hom]
    exact PowerSeries.hasSum_eval₂
      (equalCharacteristicDirectThetaFixedCoefficientHom_continuous F n)
      hx f
  have hmapped := hsource.map
    (equalCharacteristicCompletedIntegerFrobeniusLift F u n)
    (equalCharacteristicCompletedIntegerFrobeniusLift_continuous F u n)
  have hmapped' : HasSum
      (fun m : ℕ ↦
        equalCharacteristicCompletedLevelCoefficientHom F n
            (PowerSeries.coeff m
              (PowerSeries.map
                (equalCharacteristicPowerSeriesFrobenius F.residueField) f)) *
          (equalCharacteristicCompletedIntegerFrobeniusLift F u n x) ^ m)
      (equalCharacteristicCompletedIntegerFrobeniusLift F u n
        (equalCharacteristicCompletedLevelEvaluation F n x hx f)) := by
    convert hmapped using 1
    funext m
    simp only [Function.comp_apply, map_mul, map_pow,
      PowerSeries.coeff_map,
      equalCharacteristicCompletedIntegerFrobeniusLift_coefficientHom]
  apply HasSum.unique hmapped'
  rw [equalCharacteristicCompletedLevelEvaluation,
    PowerSeries.coe_eval₂Hom]
  exact PowerSeries.hasSum_eval₂
    (equalCharacteristicDirectThetaFixedCoefficientHom_continuous F n)
    (equalCharacteristicCompletedIntegerFrobeniusLift_hasEval F u n x hx)
    (PowerSeries.map
      (equalCharacteristicPowerSeriesFrobenius F.residueField) f)

private theorem equalCharacteristicCompletedFrobeniusLift_residueHom
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) (c : F.residueField) :
    equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
        (equalCharacteristicCompletedLevelResidueHom F n c) =
      equalCharacteristicCompletedLevelResidueHom F n c := by
  rw [equalCharacteristicCompletedLevelResidueHom, RingHom.comp_apply,
    equalCharacteristicCompletedLevelBaseHom, RingHom.comp_apply]
  change equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
      (algebraMap
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicCompletedUnramifiedField F.residueField)
          (algebraMap F.residueField F.residueField⸨X⸩ c))) = _
  rw [equalCharacteristicCompletedFrobeniusLiftEquiv_algebraMap]
  congr 1
  exact (equalCharacteristicCompletedUnramifiedFrobenius
    F.residueField).commutes _

private theorem equalCharacteristicCompletedFrobeniusLift_uniformizer
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
        (equalCharacteristicCompletedLevelUniformizer F n) =
      equalCharacteristicCompletedLevelUniformizer F n := by
  change equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
      (algebraMap
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)
        (equalCharacteristicCompletedBaseUniformizer F)) = _
  rw [equalCharacteristicCompletedFrobeniusLiftEquiv_algebraMap]
  congr 1
  exact equalCharacteristicCompletedUnramifiedFrobenius_uniformizer
    (k := F.residueField)

private theorem equalCharacteristicCompletedFrobeniusLift_piEnd
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicCompletedLevelField F n) :
    equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
        (equalCharacteristicLubinTateAmbientPiEnd F
          (equalCharacteristicCompletedLevelUniformizer F n) x) =
      equalCharacteristicLubinTateAmbientPiEnd F
        (equalCharacteristicCompletedLevelUniformizer F n)
        (equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹ x) := by
  simp only [equalCharacteristicLubinTateAmbientPiEnd_apply,
    map_add, map_pow, map_mul,
    equalCharacteristicCompletedFrobeniusLift_uniformizer]

private theorem equalCharacteristicCompletedFrobeniusLift_piIterate
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n i : ℕ)
    (x : equalCharacteristicCompletedLevelField F n) :
    equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
        (equalCharacteristicLubinTateAmbientPiIterate F
          (equalCharacteristicCompletedLevelUniformizer F n) i x) =
      equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicCompletedLevelUniformizer F n) i
        (equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹ x) := by
  induction i generalizing x with
  | zero =>
      rw [equalCharacteristicLubinTateAmbientPiIterate_zero,
        equalCharacteristicLubinTateAmbientPiIterate_zero]
  | succ i ih =>
      rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
        equalCharacteristicLubinTateAmbientPiIterate_succ, ih,
        equalCharacteristicCompletedFrobeniusLift_piEnd]

private theorem equalCharacteristicCompletedFrobeniusLift_ambientBracket
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n m : ℕ)
    (a : F.residueField⟦X⟧)
    (x : equalCharacteristicCompletedLevelField F n) :
    equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
        (equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicCompletedLevelResidueHom F n)
          (equalCharacteristicCompletedLevelUniformizer F n) m a x) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicCompletedLevelResidueHom F n)
        (equalCharacteristicCompletedLevelUniformizer F n) m a
        (equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹ x) := by
  rw [equalCharacteristicLubinTateAmbientBracket_apply, map_sum,
    equalCharacteristicLubinTateAmbientBracket_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul,
    equalCharacteristicCompletedFrobeniusLift_residueHom,
    equalCharacteristicCompletedFrobeniusLift_piIterate]

/-- The finite bracket `[u]` sends the prescribed Frobenius image
`[u⁻¹](lambda)` back to `lambda`. -/
private theorem
    equalCharacteristicCompletedFrobeniusLift_directBracketAtPrimitiveRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
        (equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicCompletedLevelResidueHom F n)
      (equalCharacteristicCompletedLevelUniformizer F n) (n + 1)
      (u : F.residueField⟦X⟧)
      (equalCharacteristicCompletedPrimitiveRoot F n)) =
      equalCharacteristicCompletedPrimitiveRoot F n := by
  rw [equalCharacteristicCompletedFrobeniusLift_ambientBracket]
  rw [show equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
      (equalCharacteristicCompletedPrimitiveRoot F n) =
        equalCharacteristicCompletedUnitRoot F n u⁻¹ by
    exact equalCharacteristicCompletedFrobeniusLiftEquiv_primitiveRoot F n u⁻¹]
  rw [equalCharacteristicCompletedUnitRoot]
  rw [← equalCharacteristicLubinTateAmbientBracket_mul_apply_of_torsion
    F (equalCharacteristicCompletedLevelResidueHom F n)
      (equalCharacteristicCompletedLevelUniformizer F n) (n + 1)
      (u : F.residueField⟦X⟧) ((u⁻¹ : F.residueField⟦X⟧ˣ) :
        F.residueField⟦X⟧)
      (equalCharacteristicCompletedPrimitiveRoot F n)
      (equalCharacteristicCompletedPrimitiveRoot_torsion F n)]
  have hu : (u : F.residueField⟦X⟧) *
      ((u⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧) = 1 := by
    simp
  rw [hu]
  exact equalCharacteristicLubinTateAmbientBracket_one_apply_of_torsion
    F (equalCharacteristicCompletedLevelResidueHom F n)
      (equalCharacteristicCompletedLevelUniformizer F n) (n + 1)
      (equalCharacteristicCompletedPrimitiveRoot F n)
      (equalCharacteristicCompletedPrimitiveRoot_torsion F n)

private theorem equalCharacteristicDirectThetaFixedEvaluation_hasEval_of_hasSubst
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (hx : PowerSeries.HasEval x)
    (a : ((AlgebraicClosure F.residueField)⟦X⟧)⟦X⟧)
    (ha : PowerSeries.HasSubst a) :
    PowerSeries.HasEval
      (equalCharacteristicCompletedLevelEvaluation F n x hx a) := by
  exact ha.hasEval.map
    (φ := equalCharacteristicCompletedLevelEvaluation F n x hx)
    (by
      rw [equalCharacteristicCompletedLevelEvaluation,
        PowerSeries.coe_eval₂Hom]
      exact PowerSeries.continuous_eval₂
        (equalCharacteristicDirectThetaFixedCoefficientHom_continuous F n) hx)

private theorem equalCharacteristicDirectThetaFixedEvaluation_subst
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (hx : PowerSeries.HasEval x)
    (a f : ((AlgebraicClosure F.residueField)⟦X⟧)⟦X⟧)
    (ha : PowerSeries.HasSubst a)
    (haEval : PowerSeries.HasEval
      (equalCharacteristicCompletedLevelEvaluation F n x hx a)) :
    equalCharacteristicCompletedLevelEvaluation F n x hx
        (PowerSeries.subst a f) =
      equalCharacteristicCompletedLevelEvaluation F n
        (equalCharacteristicCompletedLevelEvaluation F n x hx a) haEval f := by
  let R := (AlgebraicClosure F.residueField)⟦X⟧
  let S := Valued.integer (equalCharacteristicCompletedLevelField F n)
  simp only [equalCharacteristicCompletedLevelEvaluation,
    PowerSeries.coe_eval₂Hom]
  change PowerSeries.eval₂ (algebraMap R S) x (PowerSeries.subst a f) =
    PowerSeries.eval₂ (algebraMap R S)
      (PowerSeries.eval₂ (algebraMap R S) x a) f
  simpa only [PowerSeries.eval₂, PowerSeries.subst, Function.const_apply]
    using
      (MvPowerSeries.eval₂_subst
        (R := R) (S := R) (T := S)
        (a := fun _ : Unit ↦ a) ha.const
        (PowerSeries.hasEval hx) f)

private theorem equalCharacteristicDirectThetaFixedEvaluation_eq_of_point_eq
    (F : LocalField.{u, v} K) (n : ℕ)
    (x y : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy : x = y) :
    equalCharacteristicCompletedLevelEvaluation F n x hx =
      equalCharacteristicCompletedLevelEvaluation F n y hy := by
  subst y
  rfl

private theorem
    equalCharacteristicDirectBracketEvaluationAtPrimitiveRoot_eq_sourceIterate
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧) :
    equalCharacteristicCompletedLevelEvaluation F n
        (equalCharacteristicCompletedPrimitiveRootInteger F n)
        (equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n)
        (equalCharacteristicCompletedDirectBracket a) =
      equalCharacteristicCompletedDirectBracketAtSourceIterate F n 0 a := by
  have hpoint : equalCharacteristicDirectThetaSourceIterateInteger F n 0 =
      equalCharacteristicCompletedPrimitiveRootInteger F n := by
    apply Subtype.ext
    change
      equalCharacteristicLubinTateAmbientPiIterate F
          (equalCharacteristicCompletedLevelUniformizer F n) 0
          (equalCharacteristicCompletedPrimitiveRoot F n) =
        equalCharacteristicCompletedPrimitiveRoot F n
    exact equalCharacteristicLubinTateAmbientPiIterate_zero F
      (equalCharacteristicCompletedLevelUniformizer F n)
      (equalCharacteristicCompletedPrimitiveRoot F n)
  rw [equalCharacteristicCompletedDirectBracketAtSourceIterate]
  simp only [equalCharacteristicCompletedLevelEvaluation,
    PowerSeries.coe_eval₂Hom]
  rw [hpoint]

/-- Analytically evaluating `[u]` at the prescribed image
`[u⁻¹](lambda)` returns the original completed primitive point. -/
private theorem
    equalCharacteristicDirectBracketAtCompletedFrobeniusPrimitiveRoot_eq
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedLevelEvaluation F n
        (equalCharacteristicCompletedIntegerFrobeniusLift F u n
          (equalCharacteristicCompletedPrimitiveRootInteger F n))
        (equalCharacteristicCompletedIntegerFrobeniusLift_hasEval F u n
          (equalCharacteristicCompletedPrimitiveRootInteger F n)
          (equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n))
        (equalCharacteristicCompletedDirectBracket
          (u : F.residueField⟦X⟧)) =
      equalCharacteristicCompletedPrimitiveRootInteger F n := by
  have hsemi := equalCharacteristicCompletedIntegerFrobeniusLift_evaluation
    F u n (equalCharacteristicCompletedPrimitiveRootInteger F n)
      (equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n)
      (equalCharacteristicCompletedDirectBracket (u : F.residueField⟦X⟧))
  have hfixed : PowerSeries.map
      (equalCharacteristicPowerSeriesFrobenius F.residueField)
        (equalCharacteristicCompletedDirectBracket
          (u : F.residueField⟦X⟧)) =
      equalCharacteristicCompletedDirectBracket
        (u : F.residueField⟦X⟧) :=
    equalCharacteristicCompletedDirectBracket_frobenius
      (u : F.residueField⟦X⟧)
  rw [hfixed] at hsemi
  rw [← hsemi]
  apply Subtype.ext
  rw [equalCharacteristicCompletedIntegerFrobeniusLift_coe,
    equalCharacteristicDirectBracketEvaluationAtPrimitiveRoot_eq_sourceIterate,
    equalCharacteristicCompletedDirectBracketAtPrimitiveRoot_eq_ambient]
  exact
    equalCharacteristicCompletedFrobeniusLift_directBracketAtPrimitiveRoot
      F u n

private theorem
    equalCharacteristicCompletedIntegerFrobeniusLift_directThetaFixed
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedIntegerFrobeniusLift F u n
        (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F u n) =
      equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F u n := by
  let x := equalCharacteristicCompletedPrimitiveRootInteger F n
  let hx := equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n
  let δx := equalCharacteristicCompletedIntegerFrobeniusLift F u n x
  let hδx := equalCharacteristicCompletedIntegerFrobeniusLift_hasEval
    F u n x hx
  let H := equalCharacteristicCompletedDirectBracket
    (u : F.residueField⟦X⟧)
  let Θ := equalCharacteristicDirectThetaSeries u
  have hsemi := equalCharacteristicCompletedIntegerFrobeniusLift_evaluation
    F u n x hx Θ
  have hfirst : PowerSeries.map
      (equalCharacteristicPowerSeriesFrobenius F.residueField) Θ =
      PowerSeries.subst H Θ := by
    simpa only [H, Θ, equalCharacteristicDirectThetaSeriesFrobenius] using
      (equalCharacteristicDirectThetaSeriesFrobenius_eq_subst_directBracket u)
  have hH : PowerSeries.HasSubst H :=
    equalCharacteristicCompletedDirectBracket_hasSubst
      (u : F.residueField⟦X⟧)
  have hHEval : PowerSeries.HasEval
      (equalCharacteristicCompletedLevelEvaluation F n δx hδx H) :=
    equalCharacteristicDirectThetaFixedEvaluation_hasEval_of_hasSubst
      F n δx hδx H hH
  have hsubst := equalCharacteristicDirectThetaFixedEvaluation_subst
    F n δx hδx H Θ hH hHEval
  have hpoint :
      equalCharacteristicCompletedLevelEvaluation F n δx hδx H = x := by
    simpa only [x, hx, δx, hδx, H] using
      (equalCharacteristicDirectBracketAtCompletedFrobeniusPrimitiveRoot_eq
        F u n)
  have hevaluation :
      equalCharacteristicCompletedLevelEvaluation F n
          (equalCharacteristicCompletedLevelEvaluation F n δx hδx H)
          hHEval Θ =
        equalCharacteristicCompletedLevelEvaluation F n x hx Θ :=
    DFunLike.congr_fun
      (equalCharacteristicDirectThetaFixedEvaluation_eq_of_point_eq F n
        (equalCharacteristicCompletedLevelEvaluation F n δx hδx H)
        x hHEval hx hpoint) Θ
  change equalCharacteristicCompletedIntegerFrobeniusLift F u n
      (equalCharacteristicCompletedLevelEvaluation F n x hx Θ) =
    equalCharacteristicCompletedLevelEvaluation F n x hx Θ
  calc
    _ = equalCharacteristicCompletedLevelEvaluation F n δx hδx
        (PowerSeries.map
          (equalCharacteristicPowerSeriesFrobenius F.residueField) Θ) := hsemi
    _ = equalCharacteristicCompletedLevelEvaluation F n δx hδx
        (PowerSeries.subst H Θ) := by rw [hfirst]
    _ = equalCharacteristicCompletedLevelEvaluation F n
        (equalCharacteristicCompletedLevelEvaluation F n δx hδx H)
        hHEval Θ := hsubst
    _ = equalCharacteristicCompletedLevelEvaluation F n x hx Θ := hevaluation

/-- The completed theta-intertwining theorem in the direct orientation: the completed Frobenius lift
whose action on `lambda` is `[u⁻¹](lambda)` fixes the genuine analytic
theta value `theta(lambda)`. -/
theorem equalCharacteristicCompletedFrobeniusLift_directThetaFixed
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedFrobeniusLiftEquiv F n u⁻¹
        (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F u n :
          equalCharacteristicCompletedLevelField F n) =
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F u n :
        equalCharacteristicCompletedLevelField F n) := by
  exact congrArg Subtype.val
    (equalCharacteristicCompletedIntegerFrobeniusLift_directThetaFixed F u n)

end EqualCharacteristic
end LubinTate
