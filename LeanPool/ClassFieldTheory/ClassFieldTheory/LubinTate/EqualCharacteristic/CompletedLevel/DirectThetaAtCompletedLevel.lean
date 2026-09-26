/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaIteration
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaLocalInverse
/-!
# The completed theta-intertwining theorem: direct theta at the standard completed level

The standard completed primitive point `lambda` is a division-level `n + 1`
point for the source parameter `T`.  This file genuinely evaluates the
direct theta series at `lambda`, iterates

`theta^φ ∘ e_T = e_(uT) ∘ theta`,

and proves that `theta(lambda)` is primitive target `uT`-torsion at the
same division level.
-/

@[expose] public section

noncomputable
section

open Filter
open scoped LaurentSeries NNReal NormedField PowerSeries
  PowerSeries.WithPiTopology Topology Valued WithZero


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

private instance equalCharacteristicDirectThetaCompletedBaseCharP
    (F : LocalField.{u, v} K)
    :
    CharP (equalCharacteristicCompletedUnramifiedField F.residueField)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap F.residueField
      (equalCharacteristicCompletedUnramifiedField F.residueField)).injective
    F.residueCharacteristic

/-- The completed Lubin–Tate level field has the residue characteristic of the base field. -/
instance equalCharacteristicDirectThetaCompletedLevelCharP
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    CharP (equalCharacteristicCompletedLevelField F n)
      F.residueCharacteristic := by
  exact charP_of_injective_algebraMap
    (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)).injective
    F.residueCharacteristic

noncomputable local instance
    equalCharacteristicDirectThetaBaseValuationIsNontrivial
    (F : LocalField.{u, v} K) :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰).IsNontrivial :=
  equalCharacteristicCompletedBaseValuationIsNontrivial F.residueField

/-- The discrete valuation on the completed unramified coefficient field has rank one. -/
noncomputable local instance equalCharacteristicDirectThetaBaseValuationRankOne
    (F : LocalField.{u, v} K) :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰).RankOne :=
  equalCharacteristicCompletedBaseValuationRankOne F.residueField

/-- The canonical nontrivial norm on the completed unramified coefficient field. -/
noncomputable local instance equalCharacteristicDirectThetaBaseNormedField
    (F : LocalField.{u, v} K) :
    NontriviallyNormedField
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedBaseNormedField F.residueField

/-- The canonical nontrivial norm on the completed Lubin–Tate field at level `n`. -/
noncomputable local instance equalCharacteristicDirectThetaLevelNormedField
    (F : LocalField.{u, v} K) (n : ℕ) :
    NontriviallyNormedField (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelNormedField F n

noncomputable local instance equalCharacteristicDirectThetaLevelIsUltrametric
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUltrametricDist (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelIsUltrametric F n

noncomputable local instance equalCharacteristicDirectThetaLevelCompleteSpace
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelCompleteSpace F n

/-- The nonnegative-real-valued valuation on the completed Lubin–Tate field at level `n`. -/
noncomputable local instance equalCharacteristicDirectThetaLevelValued
    (F : LocalField.{u, v} K) (n : ℕ) :
    Valued (equalCharacteristicCompletedLevelField F n) ℝ≥0 :=
  equalCharacteristicCompletedLevelValued F n

noncomputable local instance equalCharacteristicDirectThetaIntegerLinearTopology
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsLinearTopology
      (Valued.integer (equalCharacteristicCompletedLevelField F n))
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerLinearTopology

noncomputable local instance equalCharacteristicDirectThetaIntegerCompleteSpace
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerCompleteSpace

noncomputable local instance equalCharacteristicDirectThetaIntegerUniformAddGroup
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUniformAddGroup
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerIsUniformAddGroup

private noncomputable local instance
    equalCharacteristicDirectThetaCoefficientUniformSpace
    (F : LocalField.{u, v} K) :
    UniformSpace ((AlgebraicClosure F.residueField)⟦X⟧) := ⊥

private theorem equalCharacteristicDirectThetaCoefficientHom_continuous
    (F : LocalField.{u, v} K) (n : ℕ) :
    Continuous (equalCharacteristicCompletedLevelCoefficientHom F n) :=
  continuous_of_discreteTopology

private noncomputable local instance equalCharacteristicDirectThetaCoefficientAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra ((AlgebraicClosure F.residueField)⟦X⟧)
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  (equalCharacteristicCompletedLevelCoefficientHom F n).toAlgebra

/-- The formal source `T` maps to the actual standard completed-level
uniformizer. -/
@[simp]
theorem equalCharacteristicDirectThetaSourceUniformizerInteger_coe
    (F : LocalField.{u, v} K) (n : ℕ) :
    ((equalCharacteristicCompletedLevelUniformizerInteger F n :
      Valued.integer (equalCharacteristicCompletedLevelField F n)) :
        equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicCompletedLevelUniformizer F n := by
  simp? [equalCharacteristicCompletedLevelUniformizerInteger,
    equalCharacteristicCompletedLevelCoefficientHom,
    equalCharacteristicCompletedBaseIntegerToLevel,
    equalCharacteristicCompletedLevelUniformizer,
    equalCharacteristicCompletedBaseUniformizer]
  exact congrArg
    (algebraMap
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n))
    (PowerSeries.coe_X (R := AlgebraicClosure F.residueField))

/-- The direct target parameter `uT` in the standard completed-level
valuation ring. -/
noncomputable def equalCharacteristicDirectThetaTargetUniformizerInteger
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelCoefficientHom F n
    (equalCharacteristicDirectCompletedTargetUniformizer u)

/-- The same genuine target parameter in the ambient completed level field. -/
noncomputable def equalCharacteristicDirectThetaTargetUniformizer
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedLevelField F n :=
  (equalCharacteristicDirectThetaTargetUniformizerInteger F u n :
    equalCharacteristicCompletedLevelField F n)

/-- Coercing the integral theta target uniformizer returns its field value. -/
@[simp]
theorem equalCharacteristicDirectThetaTargetUniformizerInteger_coe
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    ((equalCharacteristicDirectThetaTargetUniformizerInteger F u n :
      Valued.integer (equalCharacteristicCompletedLevelField F n)) :
        equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicDirectThetaTargetUniformizer F u n :=
  rfl

/-- The standard source orbit of the chosen primitive point. -/
noncomputable def equalCharacteristicDirectThetaSourceIterate
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n i : ℕ) :
    equalCharacteristicCompletedLevelField F n :=
  equalCharacteristicLubinTateAmbientPiIterate F
    (equalCharacteristicCompletedLevelUniformizer F n) i
    (equalCharacteristicCompletedPrimitiveRoot F n)

private theorem equalCharacteristicDirectTheta_sourceIterate_norm_lt_one_aux
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n i : ℕ)
    (x : equalCharacteristicCompletedLevelField F n) (hx : ‖x‖ < 1) :
    ‖equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicCompletedLevelUniformizer F n) i x‖ < 1 := by
  induction i generalizing x with
  | zero =>
      rw [equalCharacteristicLubinTateAmbientPiIterate, pow_zero]
      exact hx
  | succ i ih =>
      rw [equalCharacteristicLubinTateAmbientPiIterate_succ]
      apply ih
      rw [equalCharacteristicLubinTateAmbientPiEnd_apply]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg x) hx Nat.card_pos.ne'
      · rw [norm_mul]
        exact
          (mul_le_of_le_one_right (norm_nonneg _) hx.le).trans_lt
            (equalCharacteristicCompletedLevelUniformizer_norm_lt_one F n)

/-- Every direct theta source iterate has norm strictly below one. -/
theorem equalCharacteristicDirectThetaSourceIterate_norm_lt_one
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n i : ℕ) :
    ‖equalCharacteristicDirectThetaSourceIterate F n i‖ < 1 :=
  equalCharacteristicDirectTheta_sourceIterate_norm_lt_one_aux F n i
    (equalCharacteristicCompletedPrimitiveRoot F n)
    (equalCharacteristicCompletedPrimitiveRoot_norm_lt_one F n)

/-- Each source iterate as a point of the spectral valuation ring. -/
noncomputable def equalCharacteristicDirectThetaSourceIterateInteger
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n i : ℕ) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  ⟨equalCharacteristicDirectThetaSourceIterate F n i, by
    change ‖equalCharacteristicDirectThetaSourceIterate F n i‖₊ ≤ 1
    exact_mod_cast
      (equalCharacteristicDirectThetaSourceIterate_norm_lt_one F n i).le⟩

/-- Coercing an integral source iterate returns the underlying field element. -/
@[simp]
theorem equalCharacteristicDirectThetaSourceIterateInteger_coe
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n i : ℕ) :
    ((equalCharacteristicDirectThetaSourceIterateInteger F n i :
      Valued.integer (equalCharacteristicCompletedLevelField F n)) :
        equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicDirectThetaSourceIterate F n i :=
  rfl

/-- Each integral source iterate has norm strictly below one. -/
theorem equalCharacteristicDirectThetaSourceIterateInteger_norm_lt_one
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n i : ℕ) :
    ‖equalCharacteristicDirectThetaSourceIterateInteger F n i‖ < 1 := by
  change ‖equalCharacteristicDirectThetaSourceIterate F n i‖ < 1
  exact equalCharacteristicDirectThetaSourceIterate_norm_lt_one F n i

/-- Power series can be evaluated at every integral direct source iterate. -/
theorem equalCharacteristicDirectThetaSourceIterateInteger_hasEval
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n i : ℕ) :
    PowerSeries.HasEval
      (equalCharacteristicDirectThetaSourceIterateInteger F n i) := by
  change Tendsto
    (fun m : ℕ ↦ equalCharacteristicDirectThetaSourceIterateInteger
      F n i ^ m) atTop (nhds 0)
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (equalCharacteristicDirectThetaSourceIterateInteger_norm_lt_one F n i)

/-- Evaluating `e_T` moves one step along the actual source orbit. -/
theorem equalCharacteristicDirectTheta_sourceLubinTate_evaluation
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n i : ℕ) :
    equalCharacteristicCompletedLevelEvaluation F n
        (equalCharacteristicDirectThetaSourceIterateInteger F n i)
        (equalCharacteristicDirectThetaSourceIterateInteger_hasEval F n i)
        (equalCharacteristicCompletedLubinTateSeries
          (PowerSeries.X : (AlgebraicClosure F.residueField)⟦X⟧)) =
      equalCharacteristicDirectThetaSourceIterateInteger F n (i + 1) := by
  rw [equalCharacteristicCompletedLubinTateSeries,
    map_add, map_pow, map_mul,
    equalCharacteristicCompletedLevelEvaluation_X,
    equalCharacteristicCompletedLevelEvaluation_C]
  apply Subtype.ext
  change
    ((equalCharacteristicDirectThetaSourceIterateInteger F n i :
      Valued.integer (equalCharacteristicCompletedLevelField F n)) :
        equalCharacteristicCompletedLevelField F n) ^
          Nat.card F.residueField +
      ((equalCharacteristicCompletedLevelUniformizerInteger F n :
        Valued.integer (equalCharacteristicCompletedLevelField F n)) :
          equalCharacteristicCompletedLevelField F n) *
      ((equalCharacteristicDirectThetaSourceIterateInteger F n i :
        Valued.integer (equalCharacteristicCompletedLevelField F n)) :
          equalCharacteristicCompletedLevelField F n) =
      ((equalCharacteristicDirectThetaSourceIterateInteger F n (i + 1) :
        Valued.integer (equalCharacteristicCompletedLevelField F n)) :
          equalCharacteristicCompletedLevelField F n)
  rw [equalCharacteristicDirectThetaSourceIterateInteger_coe,
    equalCharacteristicDirectThetaSourceUniformizerInteger_coe,
    equalCharacteristicDirectThetaSourceIterateInteger_coe]
  rw [← equalCharacteristicLubinTateAmbientPiEnd_apply,
    equalCharacteristicDirectThetaSourceIterate,
    equalCharacteristicLubinTateAmbientPiEnd_iterate,
    ← equalCharacteristicLubinTateAmbientPiIterate_succ]
  rfl

private theorem equalCharacteristicDirectThetaEvaluation_hasEval_of_hasSubst
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (hx : PowerSeries.HasEval x)
    (a : ((AlgebraicClosure F.residueField)⟦X⟧)⟦X⟧)
    (ha : PowerSeries.HasSubst a) :
    PowerSeries.HasEval
      (equalCharacteristicCompletedLevelEvaluation F n x hx a) := by
  exact ha.hasEval.map
    ( φ := equalCharacteristicCompletedLevelEvaluation F n x hx)
    (by
      rw [equalCharacteristicCompletedLevelEvaluation,
        PowerSeries.coe_eval₂Hom]
      exact PowerSeries.continuous_eval₂
        (equalCharacteristicDirectThetaCoefficientHom_continuous F n) hx)

private theorem equalCharacteristicDirectThetaEvaluation_subst
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

/-- The analytic value of the `i`-th direct Frobenius twist at the `i`-th
standard source iterate. -/
noncomputable def
    equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n i : ℕ) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelEvaluation F n
    (equalCharacteristicDirectThetaSourceIterateInteger F n i)
    (equalCharacteristicDirectThetaSourceIterateInteger_hasEval F n i)
    (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i)

/-- The evaluated Frobenius theta iterate is summable at the matching source iterate. -/
theorem
    equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate_hasSum
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n i : ℕ) :
    HasSum
      (fun m : ℕ ↦
        equalCharacteristicCompletedLevelCoefficientHom F n
            (PowerSeries.coeff m
              (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i)) *
          equalCharacteristicDirectThetaSourceIterateInteger F n i ^ m)
      (equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate
        F u n i) := by
  rw [equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate,
    equalCharacteristicCompletedLevelEvaluation, PowerSeries.coe_eval₂Hom]
  exact PowerSeries.hasSum_eval₂
    (equalCharacteristicDirectThetaCoefficientHom_continuous F n)
    (equalCharacteristicDirectThetaSourceIterateInteger_hasEval F n i)
    (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i)

/-- The Frobenius theta iterate admits evaluation at the matching source iterate. -/
theorem
    equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate_hasEval
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n i : ℕ) :
    PowerSeries.HasEval
      (equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate
        F u n i) := by
  rw [equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate]
  exact equalCharacteristicDirectThetaEvaluation_hasEval_of_hasSubst
    F n (equalCharacteristicDirectThetaSourceIterateInteger F n i)
    (equalCharacteristicDirectThetaSourceIterateInteger_hasEval F n i)
    (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i)
    (equalCharacteristicDirectThetaSeriesFrobeniusIterate_hasSubst u i)

private theorem
    equalCharacteristicDirectThetaSeriesFrobeniusIterate_coeff_one_isUnit
    {k : Type*} [Field k] [Finite k] (u : k⟦X⟧ˣ) (i : ℕ) :
    IsUnit (PowerSeries.coeff 1
      (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i)) := by
  induction i with
  | zero =>
      rw [equalCharacteristicDirectThetaSeriesFrobeniusIterate_zero,
        equalCharacteristicDirectThetaSeries_coeff_one,
        PowerSeries.isUnit_iff_constantCoeff]
      apply isUnit_iff_ne_zero.mpr
      simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
        (equalCharacteristicSemilinearUnit_constantCoeff_ne_zero
          (u : k⟦X⟧)
          (by
            intro hzero
            have hunit := PowerSeries.isUnit_constantCoeff
              (u : k⟦X⟧) u.isUnit
            apply hunit.ne_zero
            simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero))
  | succ i ih =>
      rw [equalCharacteristicDirectThetaSeriesFrobeniusIterate_succ,
        PowerSeries.coeff_map]
      exact IsUnit.map (equalCharacteristicPowerSeriesFrobenius k) ih

private theorem
    equalCharacteristicDirectThetaFrobeniusIterateCoefficientOne_isUnit
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ)
    (n i : ℕ) :
    IsUnit
      (equalCharacteristicCompletedLevelCoefficientHom F n
        (PowerSeries.coeff 1
          (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i))) :=
  IsUnit.map (equalCharacteristicCompletedLevelCoefficientHom F n)
    (equalCharacteristicDirectThetaSeriesFrobeniusIterate_coeff_one_isUnit u i)

private theorem
    equalCharacteristicDirectThetaFrobeniusIterateAtZero_hasSum
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ)
    (n i : ℕ) :
    HasSum
      (fun m : ℕ ↦
        equalCharacteristicCompletedLevelCoefficientHom F n
            (PowerSeries.coeff m
              (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i)) *
          (0 : Valued.integer
            (equalCharacteristicCompletedLevelField F n)) ^ m)
      0 := by
  have hterms :
      (fun m : ℕ ↦
        equalCharacteristicCompletedLevelCoefficientHom F n
            (PowerSeries.coeff m
              (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i)) *
          (0 : Valued.integer
            (equalCharacteristicCompletedLevelField F n)) ^ m) =
        fun _ ↦ 0 := by
    funext m
    cases m with
    | zero =>
        simp [PowerSeries.coeff_zero_eq_constantCoeff_apply,
          equalCharacteristicDirectThetaSeriesFrobeniusIterate_constantCoeff]
    | succ m => simp
  rw [hterms]
  exact hasSum_zero

private theorem
    equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate_norm
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n i : ℕ) :
    ‖equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate F u n i‖ =
      ‖equalCharacteristicDirectThetaSourceIterateInteger F n i‖ := by
  have h := integralPowerSeriesEvaluation_norm_sub
    (fun m : ℕ ↦
      equalCharacteristicCompletedLevelCoefficientHom F n
        (PowerSeries.coeff m
          (equalCharacteristicDirectThetaSeriesFrobeniusIterate u i)))
    (equalCharacteristicDirectThetaFrobeniusIterateCoefficientOne_isUnit
      F u n i)
    (equalCharacteristicDirectThetaSourceIterateInteger F n i) 0
    (equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate F u n i) 0
    (equalCharacteristicDirectThetaSourceIterateInteger_norm_lt_one F n i)
    (by simp)
    (equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate_hasSum
      F u n i)
    (equalCharacteristicDirectThetaFrobeniusIterateAtZero_hasSum F u n i)
  simpa using h

/-- Analytic form of the `i`-th direct second identity. -/
theorem equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate_succ
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n i : ℕ) :
    equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate
        F u n (i + 1) =
      equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate F u n i ^
          Nat.card F.residueField +
        equalCharacteristicDirectThetaTargetUniformizerInteger F u n *
          equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate
            F u n i := by
  let x := equalCharacteristicDirectThetaSourceIterateInteger F n i
  let hx := equalCharacteristicDirectThetaSourceIterateInteger_hasEval F n i
  let source := equalCharacteristicCompletedLubinTateSeries
    (PowerSeries.X : (AlgebraicClosure F.residueField)⟦X⟧)
  let target := equalCharacteristicCompletedLubinTateSeries
    (equalCharacteristicDirectCompletedTargetUniformizer u)
  let twist := equalCharacteristicDirectThetaSeriesFrobeniusIterate u i
  let nextTwist :=
    equalCharacteristicDirectThetaSeriesFrobeniusIterate u (i + 1)
  have hsourceEval : PowerSeries.HasEval
      (equalCharacteristicCompletedLevelEvaluation F n x hx source) :=
    equalCharacteristicDirectThetaEvaluation_hasEval_of_hasSubst
      F n x hx source
      (equalCharacteristicCompletedLubinTateSeries_hasSubst
        (PowerSeries.X : (AlgebraicClosure F.residueField)⟦X⟧))
  have htwistEval : PowerSeries.HasEval
      (equalCharacteristicCompletedLevelEvaluation F n x hx twist) :=
    equalCharacteristicDirectThetaEvaluation_hasEval_of_hasSubst
      F n x hx twist
      (equalCharacteristicDirectThetaSeriesFrobeniusIterate_hasSubst u i)
  have hleft := equalCharacteristicDirectThetaEvaluation_subst
    F n x hx source nextTwist
    (equalCharacteristicCompletedLubinTateSeries_hasSubst
      (PowerSeries.X : (AlgebraicClosure F.residueField)⟦X⟧)) hsourceEval
  have hright := equalCharacteristicDirectThetaEvaluation_subst
    F n x hx twist target
    (equalCharacteristicDirectThetaSeriesFrobeniusIterate_hasSubst u i)
    htwistEval
  have hformal := congrArg
    (equalCharacteristicCompletedLevelEvaluation F n x hx)
    (equalCharacteristicDirectThetaSeriesFrobeniusIterate_intertwines u i)
  have hevaluated :
      equalCharacteristicCompletedLevelEvaluation F n
          (equalCharacteristicCompletedLevelEvaluation F n x hx source)
          hsourceEval nextTwist =
        equalCharacteristicCompletedLevelEvaluation F n
          (equalCharacteristicCompletedLevelEvaluation F n x hx twist)
          htwistEval target := by
    calc
      _ = equalCharacteristicCompletedLevelEvaluation F n x hx
          (PowerSeries.subst source nextTwist) := hleft.symm
      _ = equalCharacteristicCompletedLevelEvaluation F n x hx
          (PowerSeries.subst twist target) := by
            simpa [source, nextTwist, twist, target] using hformal
      _ = _ := hright
  simp only [x, source,
    equalCharacteristicDirectTheta_sourceLubinTate_evaluation] at hevaluated
  simpa only [x, hx, source, target, twist, nextTwist,
    equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate,
    equalCharacteristicCompletedLubinTateSeries,
    map_add, map_pow, map_mul,
    equalCharacteristicCompletedLevelEvaluation_X,
    equalCharacteristicCompletedLevelEvaluation_C,
    equalCharacteristicDirectThetaTargetUniformizerInteger] using hevaluated

/-- Genuine analytic evaluation of the direct theta series at the standard
completed primitive root `lambda`. -/
noncomputable def equalCharacteristicDirectThetaAtCompletedPrimitiveRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelEvaluation F n
    (equalCharacteristicCompletedPrimitiveRootInteger F n)
    (equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n)
    (equalCharacteristicDirectThetaSeries u)

/-- The coefficient expansion defining the direct theta value converges. -/
theorem equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_hasSum
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    HasSum
      (fun m : ℕ ↦
        equalCharacteristicCompletedLevelCoefficientHom F n
            (PowerSeries.coeff m (equalCharacteristicDirectThetaSeries u)) *
          equalCharacteristicCompletedPrimitiveRootInteger F n ^ m)
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F u n) := by
  rw [equalCharacteristicDirectThetaAtCompletedPrimitiveRoot,
    equalCharacteristicCompletedLevelEvaluation, PowerSeries.coe_eval₂Hom]
  exact PowerSeries.hasSum_eval₂
    (equalCharacteristicDirectThetaCoefficientHom_continuous F n)
    (equalCharacteristicCompletedPrimitiveRootInteger_hasEval F n)
    (equalCharacteristicDirectThetaSeries u)

private theorem
    equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate_zero
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate F u n 0 =
      equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F u n := by
  have hpoint :
      equalCharacteristicDirectThetaSourceIterateInteger F n 0 =
        equalCharacteristicCompletedPrimitiveRootInteger F n := by
    apply Subtype.ext
    change equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicCompletedLevelUniformizer F n) 0
        (equalCharacteristicCompletedPrimitiveRoot F n) =
      equalCharacteristicCompletedPrimitiveRoot F n
    rw [equalCharacteristicLubinTateAmbientPiIterate, pow_zero]
    rfl
  rw [equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate,
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot,
    equalCharacteristicDirectThetaSeriesFrobeniusIterate_zero]
  simp only [equalCharacteristicCompletedLevelEvaluation,
    PowerSeries.coe_eval₂Hom]
  rw [hpoint]

/-- The standard primitive root is killed by the source parameter `T` at
division level `n + 1`. -/
private theorem equalCharacteristicDirectThetaSourceRoot_torsion
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    IsEqualCharacteristicLubinTateAmbientTorsion F
      (equalCharacteristicCompletedLevelUniformizer F n) (n + 1)
      (equalCharacteristicCompletedPrimitiveRoot F n) := by
  let z := equalCharacteristicLubinTateAmbientPiIterate F
    (equalCharacteristicCompletedLevelUniformizer F n) n
    (equalCharacteristicCompletedPrimitiveRoot F n)
  have hz := equalCharacteristicCompletedPrimitiveRoot_equation F n
  change equalCharacteristicLubinTateAmbientPiIterate F
      (equalCharacteristicCompletedLevelUniformizer F n) (n + 1)
      (equalCharacteristicCompletedPrimitiveRoot F n) = 0
  rw [show n + 1 = 1 + n by omega,
    equalCharacteristicLubinTateAmbientPiIterate_add,
    equalCharacteristicLubinTateAmbientPiIterate_one,
    equalCharacteristicLubinTateAmbientPiEnd_apply]
  change z ^ Nat.card F.residueField +
      equalCharacteristicCompletedLevelUniformizer F n * z = 0
  have hq : Nat.card F.residueField ≠ 0 := Nat.card_pos.ne'
  rw [← pow_sub_one_mul hq, ← add_mul, hz, zero_mul]

/-- The standard primitive root is not killed at source division level `n`. -/
private theorem equalCharacteristicDirectThetaSourceRoot_not_torsion_pred
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    ¬ IsEqualCharacteristicLubinTateAmbientTorsion F
      (equalCharacteristicCompletedLevelUniformizer F n) n
      (equalCharacteristicCompletedPrimitiveRoot F n) := by
  intro hpred
  have heq := equalCharacteristicCompletedPrimitiveRoot_equation F n
  rw [hpred, zero_pow, zero_add] at heq
  · have ht : equalCharacteristicCompletedLevelUniformizer F n ≠ 0 := by
      rw [equalCharacteristicCompletedLevelUniformizer]
      apply (map_ne_zero
        (algebraMap
          (equalCharacteristicCompletedUnramifiedField F.residueField)
          (equalCharacteristicCompletedLevelField F n))).2
      change (HahnSeries.single 1 1 :
        (AlgebraicClosure F.residueField)⸨X⸩) ≠ 0
      exact HahnSeries.single_ne_zero one_ne_zero
    exact ht heq
  · exact Nat.sub_ne_zero_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- Iterating the evaluated second identity identifies the target `uT`
orbit of `theta(lambda)` with the successive twisted source evaluations. -/
theorem equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_targetIterate
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n i : ℕ) :
    equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicDirectThetaTargetUniformizer F u n) i
        (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F u n :
          equalCharacteristicCompletedLevelField F n) =
      (equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate
        F u n i : equalCharacteristicCompletedLevelField F n) := by
  induction i with
  | zero =>
      rw [equalCharacteristicLubinTateAmbientPiIterate, pow_zero]
      exact congrArg Subtype.val
        (equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate_zero
          F u n).symm
  | succ i ih =>
      rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
        ← equalCharacteristicLubinTateAmbientPiEnd_iterate, ih,
        equalCharacteristicLubinTateAmbientPiEnd_apply]
      have h := congrArg
        (fun z : Valued.integer
            (equalCharacteristicCompletedLevelField F n) ↦
          (z : equalCharacteristicCompletedLevelField F n))
        (equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate_succ
          F u n i)
      change
        (equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate
            F u n (i + 1) :
          equalCharacteristicCompletedLevelField F n) =
        (equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate
            F u n i :
          equalCharacteristicCompletedLevelField F n) ^
            Nat.card F.residueField +
          (equalCharacteristicDirectThetaTargetUniformizerInteger F u n :
            equalCharacteristicCompletedLevelField F n) *
            (equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate
              F u n i :
              equalCharacteristicCompletedLevelField F n) at h
      rw [equalCharacteristicDirectThetaTargetUniformizerInteger_coe] at h
      exact h.symm

/-- The direct theta value is killed by target `uT` at division level
`n + 1`. -/
theorem equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_torsion
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IsEqualCharacteristicLubinTateAmbientTorsion F
      (equalCharacteristicDirectThetaTargetUniformizer F u n) (n + 1)
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F u n :
        equalCharacteristicCompletedLevelField F n) := by
  have hsource := equalCharacteristicDirectThetaSourceRoot_torsion F n
  change equalCharacteristicDirectThetaSourceIterate F n (n + 1) = 0
    at hsource
  change equalCharacteristicLubinTateAmbientPiIterate F
      (equalCharacteristicDirectThetaTargetUniformizer F u n) (n + 1)
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F u n :
        equalCharacteristicCompletedLevelField F n) = 0
  rw [equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_targetIterate]
  apply norm_eq_zero.mp
  change ‖equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate
    F u n (n + 1)‖ = 0
  rw [equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate_norm]
  change ‖equalCharacteristicDirectThetaSourceIterate F n (n + 1)‖ = 0
  rw [hsource, norm_zero]

/-- The target value is not killed at division level `n`. -/
theorem equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_not_torsion_pred
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    ¬ IsEqualCharacteristicLubinTateAmbientTorsion F
      (equalCharacteristicDirectThetaTargetUniformizer F u n) n
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F u n :
        equalCharacteristicCompletedLevelField F n) := by
  intro htarget
  have hsource := equalCharacteristicDirectThetaSourceRoot_not_torsion_pred F n
  apply hsource
  change equalCharacteristicDirectThetaSourceIterate F n n = 0
  have htarget' := htarget
  change equalCharacteristicLubinTateAmbientPiIterate F
      (equalCharacteristicDirectThetaTargetUniformizer F u n) n
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F u n :
        equalCharacteristicCompletedLevelField F n) = 0 at htarget'
  rw [equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_targetIterate]
    at htarget'
  have hvalue :
      equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate
        F u n n = 0 := by
    apply Subtype.ext
    exact htarget'
  apply norm_eq_zero.mp
  change ‖equalCharacteristicDirectThetaSourceIterateInteger F n n‖ = 0
  rw [← equalCharacteristicDirectThetaFrobeniusIterateAtSourceIterate_norm,
    hvalue, norm_zero]

/-- Hence `theta(lambda)` is a primitive target `uT`-division point at
division level `n + 1`. -/
theorem equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isPrimitive
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IsEqualCharacteristicLubinTateAmbientTorsion F
        (equalCharacteristicDirectThetaTargetUniformizer F u n) (n + 1)
        (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F u n :
          equalCharacteristicCompletedLevelField F n) ∧
      ¬ IsEqualCharacteristicLubinTateAmbientTorsion F
        (equalCharacteristicDirectThetaTargetUniformizer F u n) n
        (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F u n :
          equalCharacteristicCompletedLevelField F n) :=
  ⟨equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_torsion F u n,
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_not_torsion_pred
      F u n⟩

end EqualCharacteristic
end LubinTate
