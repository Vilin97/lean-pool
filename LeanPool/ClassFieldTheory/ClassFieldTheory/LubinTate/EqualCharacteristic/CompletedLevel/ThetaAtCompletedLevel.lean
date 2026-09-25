/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaFirstIdentity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaEvaluation
/-!
# The completed theta-intertwining theorem: theta at a completed Lubin--Tate level

This file evaluates the theta series analytically at the chosen primitive
division point in the completed level field.
-/

@[expose] public section

noncomputable
section

open Filter
open scoped LaurentSeries NNReal PowerSeries PowerSeries.WithPiTopology
  Topology Valued WithZero


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

noncomputable local instance equalCharacteristicThetaAtLevelBaseValuationIsNontrivial
    (F : LocalField.{u, v} K) :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰).IsNontrivial :=
  equalCharacteristicCompletedBaseValuationIsNontrivial F.residueField

/-- The discrete valuation on the completed unramified coefficient field has rank one. -/
noncomputable local instance equalCharacteristicThetaAtLevelBaseValuationRankOne
    (F : LocalField.{u, v} K) :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰).RankOne :=
  equalCharacteristicCompletedBaseValuationRankOne F.residueField

/-- The canonical nontrivial norm on the completed unramified coefficient field. -/
noncomputable local instance equalCharacteristicThetaAtLevelBaseNormedField
    (F : LocalField.{u, v} K) :
    NontriviallyNormedField
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedBaseNormedField F.residueField

/-- The canonical nontrivial norm on the completed Lubin–Tate field at level `n`. -/
noncomputable local instance equalCharacteristicThetaAtLevelNormedField
    (F : LocalField.{u, v} K) (n : ℕ) :
    NontriviallyNormedField (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelNormedField F n

noncomputable local instance equalCharacteristicThetaAtLevelIsUltrametric
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUltrametricDist (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelIsUltrametric F n

noncomputable local instance equalCharacteristicThetaAtLevelCompleteSpace
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelCompleteSpace F n

/-- The nonnegative-real-valued valuation on the completed Lubin–Tate field at level `n`. -/
noncomputable local instance equalCharacteristicThetaAtLevelValued
    (F : LocalField.{u, v} K) (n : ℕ) :
    Valued (equalCharacteristicCompletedLevelField F n) ℝ≥0 :=
  equalCharacteristicCompletedLevelValued F n

noncomputable local instance equalCharacteristicThetaAtLevelLinearTopology
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsLinearTopology
      (Valued.integer (equalCharacteristicCompletedLevelField F n))
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerLinearTopology

noncomputable local instance equalCharacteristicThetaAtLevelCompleteInteger
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerCompleteSpace

noncomputable local instance equalCharacteristicThetaAtLevelUniformAddGroup
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUniformAddGroup
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerIsUniformAddGroup

/-- The integral inclusion from the completed maximal-unramified base into
the completed level field.  Integrality is preserved because the spectral
norm extends the base norm. -/
noncomputable def equalCharacteristicCompletedBaseIntegerToLevel
    (F : LocalField.{u, v} K) (n : ℕ) :
    Valued.integer
        (equalCharacteristicCompletedUnramifiedField F.residueField) →+*
      Valued.integer (equalCharacteristicCompletedLevelField F n) where
  toFun x := ⟨algebraMap
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) x, by
    change ‖algebraMap
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) (x :
        equalCharacteristicCompletedUnramifiedField F.residueField)‖₊ ≤ 1
    exact_mod_cast (show ‖algebraMap
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) (x :
        equalCharacteristicCompletedUnramifiedField F.residueField)‖ ≤ 1 by
          change spectralNorm
            (equalCharacteristicCompletedUnramifiedField F.residueField)
            (equalCharacteristicCompletedLevelField F n)
            (algebraMap
              (equalCharacteristicCompletedUnramifiedField F.residueField)
              (equalCharacteristicCompletedLevelField F n) (x :
                equalCharacteristicCompletedUnramifiedField
                  F.residueField)) ≤ 1
          rw [spectralNorm_extends,
            Valued.toNormedField.norm_le_one_iff]
          exact x.property)⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- Coefficients in `(AlgebraicClosure k)[[T]]`, analytically included in
the valuation ring of the completed level field. -/
noncomputable def equalCharacteristicCompletedLevelCoefficientHom
    (F : LocalField.{u, v} K) (n : ℕ) :
    (AlgebraicClosure F.residueField)⟦X⟧ →+*
      Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  (equalCharacteristicCompletedBaseIntegerToLevel F n).comp
    (powerSeriesEquivLaurentInteger
      (AlgebraicClosure F.residueField)).toRingHom

private noncomputable local instance equalCharacteristicThetaCoefficientUniformSpace
    (F : LocalField.{u, v} K) :
    UniformSpace ((AlgebraicClosure F.residueField)⟦X⟧) := ⊥

private theorem equalCharacteristicCompletedLevelCoefficientHom_continuous
    (F : LocalField.{u, v} K) (n : ℕ) :
    Continuous (equalCharacteristicCompletedLevelCoefficientHom F n) :=
  continuous_of_discreteTopology

private noncomputable local instance equalCharacteristicThetaAtLevelCoefficientAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra ((AlgebraicClosure F.residueField)⟦X⟧)
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  (equalCharacteristicCompletedLevelCoefficientHom F n).toAlgebra

/-- Analytic evaluation of an outer power series at an integral,
topologically nilpotent point of the completed level field. -/
noncomputable def equalCharacteristicCompletedLevelEvaluation
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (ha : PowerSeries.HasEval a) :
    ((AlgebraicClosure F.residueField)⟦X⟧)⟦X⟧ →+*
      Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  PowerSeries.eval₂Hom
    (equalCharacteristicCompletedLevelCoefficientHom_continuous F n) ha

/-- States the theorem `equalCharacteristicCompletedLevelEvaluation_X`. -/
@[simp]
theorem equalCharacteristicCompletedLevelEvaluation_X
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (ha : PowerSeries.HasEval a) :
    equalCharacteristicCompletedLevelEvaluation F n a ha PowerSeries.X = a := by
  rw [equalCharacteristicCompletedLevelEvaluation,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]

/-- States the theorem `equalCharacteristicCompletedLevelEvaluation_C`. -/
@[simp]
theorem equalCharacteristicCompletedLevelEvaluation_C
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (ha : PowerSeries.HasEval a)
    (f : (AlgebraicClosure F.residueField)⟦X⟧) :
    equalCharacteristicCompletedLevelEvaluation F n a ha (PowerSeries.C f) =
      equalCharacteristicCompletedLevelCoefficientHom F n f := by
  rw [equalCharacteristicCompletedLevelEvaluation,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]

/-- The image of `T` in the valuation ring of the completed level field. -/
noncomputable def equalCharacteristicCompletedLevelUniformizerInteger
    (F : LocalField.{u, v} K) (n : ℕ) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelCoefficientHom F n PowerSeries.X

/-- The genuine analytic value `theta(lambda_(n+1))`. -/
noncomputable def equalCharacteristicThetaAtCompletedPrimitiveRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelEvaluation F n
    (equalCharacteristicCompletedPrimitiveRootInteger F n)
    (equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n)
    (equalCharacteristicThetaSeries u)

/-- The coefficient expansion defining `theta(lambda_(n+1))` converges in
the completed level field. -/
theorem equalCharacteristicThetaAtCompletedPrimitiveRoot_hasSum
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    HasSum
      (fun m : ℕ ↦
        equalCharacteristicCompletedLevelCoefficientHom F n
            (PowerSeries.coeff m (equalCharacteristicThetaSeries u)) *
          equalCharacteristicCompletedPrimitiveRootInteger F n ^ m)
      (equalCharacteristicThetaAtCompletedPrimitiveRoot F u n) := by
  rw [equalCharacteristicThetaAtCompletedPrimitiveRoot,
    equalCharacteristicCompletedLevelEvaluation,
    PowerSeries.coe_eval₂Hom]
  exact PowerSeries.hasSum_eval₂
    (equalCharacteristicCompletedLevelCoefficientHom_continuous F n)
    (equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n)
    (equalCharacteristicThetaSeries u)

private theorem equalCharacteristicCompletedEvaluation_hasEval_of_hasSubst
    (F : LocalField.{u, v} K) (n : ℕ)
    [CharP K F.residueCharacteristic]
    (a : ((AlgebraicClosure F.residueField)⟦X⟧)⟦X⟧)
    (ha : PowerSeries.HasSubst a) :
    PowerSeries.HasEval
      (equalCharacteristicCompletedLevelEvaluation F n
        (equalCharacteristicCompletedPrimitiveRootInteger F n)
        (equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n) a) := by
  let hcoeff :=
    equalCharacteristicCompletedLevelCoefficientHom_continuous F n
  let hroot :=
    equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n
  have hformal : PowerSeries.HasEval a := ha.hasEval
  exact hformal.map
    (φ := equalCharacteristicCompletedLevelEvaluation F n
      (equalCharacteristicCompletedPrimitiveRootInteger F n) hroot)
    (by
      rw [equalCharacteristicCompletedLevelEvaluation,
        PowerSeries.coe_eval₂Hom]
      exact PowerSeries.continuous_eval₂ hcoeff hroot)

/-- The theta value is itself topologically nilpotent. -/
theorem equalCharacteristicThetaAtCompletedPrimitiveRoot_hasEval
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    PowerSeries.HasEval
      (equalCharacteristicThetaAtCompletedPrimitiveRoot F u n) := by
  rw [equalCharacteristicThetaAtCompletedPrimitiveRoot]
  exact equalCharacteristicCompletedEvaluation_hasEval_of_hasSubst F n
    (equalCharacteristicThetaSeries u)
    (equalCharacteristicThetaSeries_hasSubst u)

/-- The analytic value `[u](lambda_(n+1))` of the source Lubin--Tate
endomorphism occurring in the first theta identity. -/
noncomputable def equalCharacteristicSourceBracketAtCompletedPrimitiveRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelEvaluation F n
    (equalCharacteristicCompletedPrimitiveRootInteger F n)
    (equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n)
    (equalCharacteristicCompletedSourceBracket u)

/-- The analytically evaluated bracket remains topologically nilpotent, so
theta can itself be evaluated at `[u](lambda_(n+1))`. -/
theorem equalCharacteristicSourceBracketAtCompletedPrimitiveRoot_hasEval
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    PowerSeries.HasEval
      (equalCharacteristicSourceBracketAtCompletedPrimitiveRoot F u n) := by
  rw [equalCharacteristicSourceBracketAtCompletedPrimitiveRoot]
  exact equalCharacteristicCompletedEvaluation_hasEval_of_hasSubst F n
    (equalCharacteristicCompletedSourceBracket u)
    (equalCharacteristicCompletedSourceBracket_hasSubst u)

/-- Analytic evaluation commutes with a genuine formal substitution whose
inner series has nilpotent constant coefficient. -/
private theorem equalCharacteristicCompletedLevelEvaluation_subst
    (F : LocalField.{u, v} K) (n : ℕ)
    [CharP K F.residueCharacteristic]
    (a f : ((AlgebraicClosure F.residueField)⟦X⟧)⟦X⟧)
    (ha : PowerSeries.HasSubst a)
    (hroot : PowerSeries.HasEval
      (equalCharacteristicCompletedPrimitiveRootInteger F n))
    (haEval : PowerSeries.HasEval
      (equalCharacteristicCompletedLevelEvaluation F n
        (equalCharacteristicCompletedPrimitiveRootInteger F n) hroot a)) :
    equalCharacteristicCompletedLevelEvaluation F n
        (equalCharacteristicCompletedPrimitiveRootInteger F n) hroot
        (PowerSeries.subst a f) =
      equalCharacteristicCompletedLevelEvaluation F n
        (equalCharacteristicCompletedLevelEvaluation F n
          (equalCharacteristicCompletedPrimitiveRootInteger F n) hroot a)
        haEval f := by
  let R := (AlgebraicClosure F.residueField)⟦X⟧
  let S := Valued.integer (equalCharacteristicCompletedLevelField F n)
  simp only [equalCharacteristicCompletedLevelEvaluation,
    PowerSeries.coe_eval₂Hom]
  change PowerSeries.eval₂ (algebraMap R S)
      (equalCharacteristicCompletedPrimitiveRootInteger F n)
      (PowerSeries.subst a f) =
    PowerSeries.eval₂ (algebraMap R S)
      (PowerSeries.eval₂ (algebraMap R S)
        (equalCharacteristicCompletedPrimitiveRootInteger F n) a) f
  simpa only [PowerSeries.eval₂, PowerSeries.subst, Function.const_apply]
    using
      (MvPowerSeries.eval₂_subst
        (R := R) (S := R) (T := S)
        (a := fun _ : Unit ↦ a) ha.const
        (PowerSeries.hasEval hroot) f)

/-- The left side `theta^phi(lambda_(n+1))` of the first theta identity. -/
noncomputable def equalCharacteristicThetaFrobeniusAtCompletedPrimitiveRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelEvaluation F n
    (equalCharacteristicCompletedPrimitiveRootInteger F n)
    (equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n)
    (equalCharacteristicThetaSeriesFrobenius u)

/-- The completed theta-intertwining theorem, the first theta identity after genuine analytic
evaluation at the completed primitive point:

`theta^phi(lambda_(n+1)) = theta([u](lambda_(n+1)))`. -/
theorem equalCharacteristicTheta_firstIdentity_atCompletedPrimitiveRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicThetaFrobeniusAtCompletedPrimitiveRoot F u n =
      equalCharacteristicCompletedLevelEvaluation F n
        (equalCharacteristicSourceBracketAtCompletedPrimitiveRoot F u n)
        (equalCharacteristicSourceBracketAtCompletedPrimitiveRoot_hasEval
          F u n)
        (equalCharacteristicThetaSeries u) := by
  rw [equalCharacteristicThetaFrobeniusAtCompletedPrimitiveRoot,
    equalCharacteristicThetaSeriesFrobenius_eq_subst_sourceBracket]
  exact equalCharacteristicCompletedLevelEvaluation_subst F n
    (equalCharacteristicCompletedSourceBracket u)
    (equalCharacteristicThetaSeries u)
    (equalCharacteristicCompletedSourceBracket_hasSubst u)
    (equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n)
    (equalCharacteristicSourceBracketAtCompletedPrimitiveRoot_hasEval F u n)

/-- The analytic value of the source Lubin--Tate series
`Y^q + (u⁻¹T)Y` at the completed primitive root. -/
noncomputable def equalCharacteristicSourceLubinTateAtCompletedPrimitiveRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelEvaluation F n
    (equalCharacteristicCompletedPrimitiveRootInteger F n)
    (equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n)
    (equalCharacteristicCompletedLubinTateSeries
      (equalCharacteristicCompletedSourceUniformizer u))

/-- States the theorem `equalCharacteristicSourceLubinTateAtCompletedPrimitiveRoot_hasEval`. -/
theorem equalCharacteristicSourceLubinTateAtCompletedPrimitiveRoot_hasEval
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    PowerSeries.HasEval
      (equalCharacteristicSourceLubinTateAtCompletedPrimitiveRoot F u n) := by
  rw [equalCharacteristicSourceLubinTateAtCompletedPrimitiveRoot]
  exact equalCharacteristicCompletedEvaluation_hasEval_of_hasSubst F n
    (equalCharacteristicCompletedLubinTateSeries
      (equalCharacteristicCompletedSourceUniformizer u))
    (equalCharacteristicCompletedLubinTateSeries_hasSubst
      (equalCharacteristicCompletedSourceUniformizer u))

/-- The completed theta-intertwining theorem, the second theta identity after analytic evaluation:

`theta^phi(e_(u⁻¹T)(lambda)) = e_T(theta(lambda))`.

The right side is expanded inside the completed level valuation ring. -/
theorem equalCharacteristicTheta_secondIdentity_atCompletedPrimitiveRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedLevelEvaluation F n
        (equalCharacteristicSourceLubinTateAtCompletedPrimitiveRoot F u n)
        (equalCharacteristicSourceLubinTateAtCompletedPrimitiveRoot_hasEval
          F u n)
        (equalCharacteristicThetaSeriesFrobenius u) =
      equalCharacteristicThetaAtCompletedPrimitiveRoot F u n ^
          Nat.card F.residueField +
        equalCharacteristicCompletedLevelUniformizerInteger F n *
          equalCharacteristicThetaAtCompletedPrimitiveRoot F u n := by
  let root := equalCharacteristicCompletedPrimitiveRootInteger F n
  let hroot := equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n
  let source := equalCharacteristicCompletedLubinTateSeries
    (equalCharacteristicCompletedSourceUniformizer u)
  let theta := equalCharacteristicThetaSeries u
  let target := equalCharacteristicCompletedLubinTateSeries
    (k := F.residueField) PowerSeries.X
  have hleft := equalCharacteristicCompletedLevelEvaluation_subst F n
    source (equalCharacteristicThetaSeriesFrobenius u)
    (equalCharacteristicCompletedLubinTateSeries_hasSubst
      (equalCharacteristicCompletedSourceUniformizer u))
    hroot
    (equalCharacteristicSourceLubinTateAtCompletedPrimitiveRoot_hasEval F u n)
  have hright := equalCharacteristicCompletedLevelEvaluation_subst F n
    theta target (equalCharacteristicThetaSeries_hasSubst u) hroot
    (equalCharacteristicThetaAtCompletedPrimitiveRoot_hasEval F u n)
  have hintertwines := congrArg
    (equalCharacteristicCompletedLevelEvaluation F n root hroot)
    (equalCharacteristicThetaSeries_intertwines u)
  calc
    _ = equalCharacteristicCompletedLevelEvaluation F n root hroot
        (PowerSeries.subst source
          (equalCharacteristicThetaSeriesFrobenius u)) := by
          simpa [equalCharacteristicSourceLubinTateAtCompletedPrimitiveRoot,
            source, root, hroot] using hleft.symm
    _ = equalCharacteristicCompletedLevelEvaluation F n root hroot
        (PowerSeries.subst theta target) := by
          simpa [source, theta, target] using hintertwines
    _ = equalCharacteristicCompletedLevelEvaluation F n
        (equalCharacteristicThetaAtCompletedPrimitiveRoot F u n)
        (equalCharacteristicThetaAtCompletedPrimitiveRoot_hasEval F u n)
        target := by
          simpa [equalCharacteristicThetaAtCompletedPrimitiveRoot,
            theta, root, hroot] using hright
    _ = _ := by
      simp [target, equalCharacteristicCompletedLubinTateSeries,
        equalCharacteristicCompletedLevelUniformizerInteger]

end EqualCharacteristic
end LubinTate
