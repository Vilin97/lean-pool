/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracketRecursion
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaAtCompletedLevel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction
/-!
# The completed theta-intertwining theorem: the formal standard bracket at a completed division
  point

The first theta identity uses the independently constructed formal bracket,
whereas the completed Frobenius lift acts through the finite bracket from
the finite Lubin–Tate bracket construction.  This file proves that the two actions agree on the
  chosen primitive
division point.  The proof analytically evaluates the recursive identity

`[a](x) = a₀x + [tail(a)](e_T(x))`

and follows the source torsion orbit until the finite bracket terminates.
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

private instance equalCharacteristicDirectBracketLevelCharP
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    CharP (equalCharacteristicCompletedLevelField F n)
      F.residueCharacteristic :=
  equalCharacteristicDirectThetaCompletedLevelCharP F n

noncomputable local instance equalCharacteristicDirectBracketBaseValuationIsNontrivial
    (F : LocalField.{u, v} K) :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰).IsNontrivial :=
  equalCharacteristicCompletedBaseValuationIsNontrivial F.residueField

/-- The valuation on the completed unramified base of the direct-bracket construction has rank
one. -/
noncomputable local instance equalCharacteristicDirectBracketBaseValuationRankOne
    (F : LocalField.{u, v} K) :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰).RankOne :=
  equalCharacteristicCompletedBaseValuationRankOne F.residueField

/-- The canonical nontrivial norm on the completed unramified coefficient field. -/
noncomputable local instance equalCharacteristicDirectBracketBaseNormedField
    (F : LocalField.{u, v} K) :
    NontriviallyNormedField
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedBaseNormedField F.residueField

/-- The canonical nontrivial norm on the completed Lubin–Tate field at level `n`. -/
noncomputable local instance equalCharacteristicDirectBracketLevelNormedField
    (F : LocalField.{u, v} K) (n : ℕ) :
    NontriviallyNormedField (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelNormedField F n

noncomputable local instance equalCharacteristicDirectBracketLevelIsUltrametric
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUltrametricDist (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelIsUltrametric F n

noncomputable local instance equalCharacteristicDirectBracketLevelCompleteSpace
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelCompleteSpace F n

/-- The nonnegative-real-valued valuation on the completed Lubin–Tate field at level `n`. -/
noncomputable local instance equalCharacteristicDirectBracketLevelValued
    (F : LocalField.{u, v} K) (n : ℕ) :
    Valued (equalCharacteristicCompletedLevelField F n) ℝ≥0 :=
  equalCharacteristicCompletedLevelValued F n

noncomputable local instance equalCharacteristicDirectBracketIntegerLinearTopology
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsLinearTopology
      (Valued.integer (equalCharacteristicCompletedLevelField F n))
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerLinearTopology

noncomputable local instance equalCharacteristicDirectBracketIntegerCompleteSpace
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerCompleteSpace

noncomputable local instance equalCharacteristicDirectBracketIntegerUniformAddGroup
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUniformAddGroup
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  valuedIntegerIsUniformAddGroup

private noncomputable local instance
    equalCharacteristicDirectBracketCoefficientUniformSpace
    (F : LocalField.{u, v} K) :
    UniformSpace ((AlgebraicClosure F.residueField)⟦X⟧) := ⊥

private theorem equalCharacteristicDirectBracketCoefficientHom_continuous
    (F : LocalField.{u, v} K) (n : ℕ) :
    Continuous (equalCharacteristicCompletedLevelCoefficientHom F n) :=
  continuous_of_discreteTopology

private noncomputable local instance equalCharacteristicDirectBracketCoefficientAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra ((AlgebraicClosure F.residueField)⟦X⟧)
      (Valued.integer (equalCharacteristicCompletedLevelField F n)) :=
  (equalCharacteristicCompletedLevelCoefficientHom F n).toAlgebra

/-- Genuine analytic value of the standard formal bracket at the `i`-th
point of the source orbit. -/
noncomputable def equalCharacteristicCompletedDirectBracketAtSourceIterate
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n i : ℕ) (a : F.residueField⟦X⟧) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelEvaluation F n
    (equalCharacteristicDirectThetaSourceIterateInteger F n i)
    (equalCharacteristicDirectThetaSourceIterateInteger_hasEval F n i)
    (equalCharacteristicCompletedDirectBracket a)

private theorem equalCharacteristicDirectBracketEvaluation_hasEval_of_hasSubst
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
        (equalCharacteristicDirectBracketCoefficientHom_continuous F n) hx)

private theorem equalCharacteristicDirectBracketEvaluation_subst
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

private theorem equalCharacteristicCompletedLevelEvaluation_eq_of_point_eq
    (F : LocalField.{u, v} K) (n : ℕ)
    (x y : Valued.integer (equalCharacteristicCompletedLevelField F n))
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy : x = y) :
    equalCharacteristicCompletedLevelEvaluation F n x hx =
      equalCharacteristicCompletedLevelEvaluation F n y hy := by
  subst y
  rfl

private theorem equalCharacteristicCompletedLevelCoefficientHom_C_base
    (F : LocalField.{u, v} K) (n : ℕ) (c : F.residueField) :
    ((equalCharacteristicCompletedLevelCoefficientHom F n
        (PowerSeries.C
          (algebraMap F.residueField (AlgebraicClosure F.residueField) c)) :
      Valued.integer (equalCharacteristicCompletedLevelField F n)) :
        equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicCompletedLevelResidueHom F n c := by
  change algebraMap
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)
      (((equalCharacteristicPowerSeriesToCompletedInteger F.residueField)
        (PowerSeries.C
          (algebraMap F.residueField (AlgebraicClosure F.residueField) c)) :
        Valued.integer
          (equalCharacteristicCompletedUnramifiedField F.residueField)) :
        equalCharacteristicCompletedUnramifiedField F.residueField) =
    algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)
      ((laurentSeriesCoefficientMap
        (algebraMap F.residueField (AlgebraicClosure F.residueField)))
        (algebraMap F.residueField F.residueField⸨X⸩ c))
  apply congrArg (algebraMap
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedLevelField F n))
  change
    ((PowerSeries.C
      (algebraMap F.residueField (AlgebraicClosure F.residueField) c) :
        (AlgebraicClosure F.residueField)⟦X⟧) :
          (AlgebraicClosure F.residueField)⸨X⸩) = _
  rw [HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply,
    laurentSeriesCoefficientMap_C]

/-- Analytic version of the recursive bracket identity along the standard
source orbit. -/
theorem equalCharacteristicCompletedDirectBracketAtSourceIterate_recursion
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n i : ℕ) (a : F.residueField⟦X⟧) :
    ((equalCharacteristicCompletedDirectBracketAtSourceIterate F n i a :
      Valued.integer (equalCharacteristicCompletedLevelField F n)) :
        equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicCompletedLevelResidueHom F n
          (PowerSeries.coeff 0 a) *
        equalCharacteristicDirectThetaSourceIterate F n i +
      ((equalCharacteristicCompletedDirectBracketAtSourceIterate F n (i + 1)
          (equalCharacteristicPowerSeriesTail a) :
        Valued.integer (equalCharacteristicCompletedLevelField F n)) :
          equalCharacteristicCompletedLevelField F n) := by
  let x := equalCharacteristicDirectThetaSourceIterateInteger F n i
  let hx := equalCharacteristicDirectThetaSourceIterateInteger_hasEval F n i
  let E := equalCharacteristicCompletedLubinTateSeries
    (k := F.residueField)
    (PowerSeries.X : (AlgebraicClosure F.residueField)⟦X⟧)
  let H := equalCharacteristicCompletedDirectBracket
    (equalCharacteristicPowerSeriesTail a)
  have hE : PowerSeries.HasSubst E :=
    equalCharacteristicCompletedLubinTateSeries_hasSubst _
  have hEeval : PowerSeries.HasEval
      (equalCharacteristicCompletedLevelEvaluation F n x hx E) :=
    equalCharacteristicDirectBracketEvaluation_hasEval_of_hasSubst
      F n x hx E hE
  have hsubst := equalCharacteristicDirectBracketEvaluation_subst F n x hx
    E H hE hEeval
  have hformal := congrArg
    (equalCharacteristicCompletedLevelEvaluation F n x hx)
    (equalCharacteristicCompletedDirectBracket_recursion a)
  rw [map_add, map_mul,
    equalCharacteristicCompletedLevelEvaluation_X,
    equalCharacteristicCompletedLevelEvaluation_C] at hformal
  have hsource := equalCharacteristicDirectTheta_sourceLubinTate_evaluation
    F n i
  change equalCharacteristicCompletedLevelEvaluation F n x hx E =
      equalCharacteristicDirectThetaSourceIterateInteger F n (i + 1)
    at hsource
  have htail :
      equalCharacteristicCompletedLevelEvaluation F n x hx
          (PowerSeries.subst E H) =
        equalCharacteristicCompletedDirectBracketAtSourceIterate F n (i + 1)
          (equalCharacteristicPowerSeriesTail a) := by
    calc
      _ = equalCharacteristicCompletedLevelEvaluation F n
          (equalCharacteristicCompletedLevelEvaluation F n x hx E) hEeval H :=
        hsubst
      _ = _ := by
        exact DFunLike.congr_fun
          (equalCharacteristicCompletedLevelEvaluation_eq_of_point_eq F n
            (equalCharacteristicCompletedLevelEvaluation F n x hx E)
            (equalCharacteristicDirectThetaSourceIterateInteger F n (i + 1))
            hEeval
            (equalCharacteristicDirectThetaSourceIterateInteger_hasEval
              F n (i + 1)) hsource) H
  rw [htail] at hformal
  have hcoerce := congrArg
    (fun z : Valued.integer (equalCharacteristicCompletedLevelField F n) ↦
      (z : equalCharacteristicCompletedLevelField F n)) hformal
  change
    ((equalCharacteristicCompletedDirectBracketAtSourceIterate F n i a :
      Valued.integer (equalCharacteristicCompletedLevelField F n)) :
        equalCharacteristicCompletedLevelField F n) = _
  rw [← equalCharacteristicDirectThetaSourceIterateInteger_coe F n i]
  rw [← equalCharacteristicCompletedLevelCoefficientHom_C_base F n
    (PowerSeries.coeff 0 a)]
  simpa [equalCharacteristicCompletedDirectBracketAtSourceIterate,
    x, hx, H, E, map_add, map_mul] using hcoerce

/-- On a point killed at level `m`, the analytic formal bracket equals the
finite the finite Lubin–Tate bracket construction bracket with `m` terms. -/
theorem equalCharacteristicCompletedDirectBracketAtSourceIterate_eq_ambient
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n m i : ℕ) (a : F.residueField⟦X⟧)
    (htorsion : IsEqualCharacteristicLubinTateAmbientTorsion F
      (equalCharacteristicCompletedLevelUniformizer F n) m
      (equalCharacteristicDirectThetaSourceIterate F n i)) :
    ((equalCharacteristicCompletedDirectBracketAtSourceIterate F n i a :
      Valued.integer (equalCharacteristicCompletedLevelField F n)) :
        equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicCompletedLevelResidueHom F n)
        (equalCharacteristicCompletedLevelUniformizer F n) m a
        (equalCharacteristicDirectThetaSourceIterate F n i) := by
  induction m generalizing i a with
  | zero =>
      change equalCharacteristicDirectThetaSourceIterate F n i = 0 at htorsion
      have hxi : equalCharacteristicDirectThetaSourceIterateInteger F n i = 0 := by
        apply Subtype.ext
        exact htorsion
      rw [equalCharacteristicLubinTateAmbientBracket_apply]
      simp only [Finset.range_zero, Finset.sum_empty]
      let x := equalCharacteristicDirectThetaSourceIterateInteger F n i
      let hx := equalCharacteristicDirectThetaSourceIterateInteger_hasEval F n i
      let H := equalCharacteristicCompletedDirectBracket a
      have heval := DFunLike.congr_fun
        (equalCharacteristicCompletedLevelEvaluation_eq_of_point_eq F n
          x 0 hx PowerSeries.HasEval.zero hxi) H
      change ((equalCharacteristicCompletedLevelEvaluation F n x hx H :
        Valued.integer (equalCharacteristicCompletedLevelField F n)) :
          equalCharacteristicCompletedLevelField F n) = 0
      rw [heval]
      have hsub :
          equalCharacteristicCompletedLevelEvaluation F n 0
              PowerSeries.HasEval.zero H = 0 := by
        rw [equalCharacteristicCompletedLevelEvaluation,
          PowerSeries.coe_eval₂Hom]
        apply HasSum.unique
          (PowerSeries.hasSum_eval₂
            (equalCharacteristicDirectBracketCoefficientHom_continuous F n)
            PowerSeries.HasEval.zero H)
        have hterm :
            (fun d : ℕ ↦
              equalCharacteristicCompletedLevelCoefficientHom F n
                  (PowerSeries.coeff d H) *
                (0 : Valued.integer
                  (equalCharacteristicCompletedLevelField F n)) ^ d) =
              (fun _ : ℕ ↦ (0 : Valued.integer
                (equalCharacteristicCompletedLevelField F n))) := by
          funext d
          cases d with
          | zero =>
              simp [H, PowerSeries.coeff_zero_eq_constantCoeff_apply,
                equalCharacteristicCompletedDirectBracket_constantCoeff]
          | succ d => simp
        rw [hterm]
        exact hasSum_zero
      exact congrArg Subtype.val hsub
  | succ m ih =>
      have hsourceSucc :
          equalCharacteristicDirectThetaSourceIterate F n (i + 1) =
            equalCharacteristicLubinTateAmbientPiEnd F
              (equalCharacteristicCompletedLevelUniformizer F n)
              (equalCharacteristicDirectThetaSourceIterate F n i) := by
        change equalCharacteristicLubinTateAmbientPiIterate F
            (equalCharacteristicCompletedLevelUniformizer F n) (i + 1)
            (equalCharacteristicCompletedPrimitiveRoot F n) =
          equalCharacteristicLubinTateAmbientPiEnd F
            (equalCharacteristicCompletedLevelUniformizer F n)
            (equalCharacteristicLubinTateAmbientPiIterate F
              (equalCharacteristicCompletedLevelUniformizer F n) i
              (equalCharacteristicCompletedPrimitiveRoot F n))
        rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
          ← equalCharacteristicLubinTateAmbientPiEnd_iterate]
      have hnext : IsEqualCharacteristicLubinTateAmbientTorsion F
          (equalCharacteristicCompletedLevelUniformizer F n) m
          (equalCharacteristicDirectThetaSourceIterate F n (i + 1)) := by
        change equalCharacteristicLubinTateAmbientPiIterate F
            (equalCharacteristicCompletedLevelUniformizer F n) m
            (equalCharacteristicDirectThetaSourceIterate F n (i + 1)) = 0
        change equalCharacteristicLubinTateAmbientPiIterate F
            (equalCharacteristicCompletedLevelUniformizer F n) (m + 1)
            (equalCharacteristicDirectThetaSourceIterate F n i) = 0 at htorsion
        rw [equalCharacteristicLubinTateAmbientPiIterate_succ] at htorsion
        rw [hsourceSucc]
        exact htorsion
      rw [equalCharacteristicCompletedDirectBracketAtSourceIterate_recursion,
        ih (i := i + 1) (a := equalCharacteristicPowerSeriesTail a) hnext,
        equalCharacteristicLubinTateAmbientBracket_succ_apply]
      rw [hsourceSucc]

/-- At the chosen primitive point, the analytic formal bracket is exactly
the finite bracket used to define the completed Galois action. -/
theorem equalCharacteristicCompletedDirectBracketAtPrimitiveRoot_eq_ambient
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧) :
    ((equalCharacteristicCompletedDirectBracketAtSourceIterate F n 0 a :
      Valued.integer (equalCharacteristicCompletedLevelField F n)) :
        equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicCompletedLevelResidueHom F n)
        (equalCharacteristicCompletedLevelUniformizer F n) (n + 1) a
        (equalCharacteristicCompletedPrimitiveRoot F n) := by
  have h := equalCharacteristicCompletedDirectBracketAtSourceIterate_eq_ambient
    F n (n + 1) 0 a (equalCharacteristicCompletedPrimitiveRoot_torsion F n)
  change
    ((equalCharacteristicCompletedDirectBracketAtSourceIterate F n 0 a :
      Valued.integer (equalCharacteristicCompletedLevelField F n)) :
        equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicCompletedLevelResidueHom F n)
        (equalCharacteristicCompletedLevelUniformizer F n) (n + 1) a
        (equalCharacteristicCompletedPrimitiveRoot F n) at h
  exact h

/-- Unit specialization: the formal standard `[a]` at the primitive point
is the completed unit root used by the prescribed Frobenius lift. -/
theorem equalCharacteristicCompletedDirectBracketAtPrimitiveRoot_eq_unitRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    ((equalCharacteristicCompletedDirectBracketAtSourceIterate F n 0
        (a : F.residueField⟦X⟧) :
      Valued.integer (equalCharacteristicCompletedLevelField F n)) :
        equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicCompletedUnitRoot F n a := by
  exact equalCharacteristicCompletedDirectBracketAtPrimitiveRoot_eq_ambient
    F n (a : F.residueField⟦X⟧)

end EqualCharacteristic
end LubinTate
