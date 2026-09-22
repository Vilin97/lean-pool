/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedLevel
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveIrreducible
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
/-!
# The completed theta-intertwining theorem: primitive action for the changed completed level

The theta relation in the completed theta-intertwining theorem uses the source parameter `u⁻¹T`.
  We first
prove, genuinely by Eisenstein over `(AlgebraicClosure κ)[[T]]`, that its
primitive polynomial stays irreducible over the completed maximal-unramified
Laurent field.  We then enumerate its roots by source Lubin--Tate unit
brackets and show that every such primitive point generates the splitting
field.

The theta unit `u` and a source Lubin--Tate bracket unit `a` are deliberately
kept as distinct parameters.  Repository index `n` is division level `n + 1`.
-/

noncomputable section

open scoped LaurentSeries Polynomial PowerSeries


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- Coefficient extension makes the completed unramified base an algebra over residue-field
Laurent series for the changed primitive action. -/
noncomputable local instance equalCharacteristicChangedCompletedPrimitiveActionBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

/-- The image of the source unit `u⁻¹` in
`(AlgebraicClosure κ)[[T]]`. -/
noncomputable def equalCharacteristicChangedCompletedSourceUnit
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) :
    (AlgebraicClosure F.residueField)⟦X⟧ˣ :=
  Units.map
    (PowerSeries.map
      (algebraMap F.residueField (AlgebraicClosure F.residueField)))
    (equalCharacteristicThetaSourceUnit u)

/-- The integral primitive polynomial for source parameter `u⁻¹T`,
after coefficientwise extension to `(AlgebraicClosure κ)[[T]]`. -/
noncomputable def equalCharacteristicChangedCompletedIntegralPrimitivePolynomial
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Polynomial (AlgebraicClosure F.residueField)⟦X⟧ :=
  (equalCharacteristicChangedIntegralPrimitivePolynomial F
      (equalCharacteristicThetaSourceUnit u) n).map
    (PowerSeries.map
      (algebraMap F.residueField (AlgebraicClosure F.residueField)))

/-- The changed integral primitive polynomial remains monic after scalar extension. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_monic
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).Monic :=
  (equalCharacteristicChangedIntegralPrimitivePolynomial_monic F
    (equalCharacteristicThetaSourceUnit u) n).map _

/-- The completed integral primitive polynomial has degree `(q - 1) * q ^ n`. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_natDegree
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).natDegree =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial,
    (equalCharacteristicChangedIntegralPrimitivePolynomial_monic F
      (equalCharacteristicThetaSourceUnit u) n).natDegree_map,
    equalCharacteristicChangedIntegralPrimitivePolynomial_natDegree]

/-- Passage from the changed integral polynomial to Laurent series agrees
with the completed coefficientwise base change. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_map
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).map
        (algebraMap (AlgebraicClosure F.residueField)⟦X⟧
          (equalCharacteristicCompletedUnramifiedField F.residueField)) =
      equalCharacteristicChangedCompletedPrimitivePolynomial F u n := by
  rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial,
    Polynomial.map_map,
    equalCharacteristicPowerSeriesLaurent_baseChange_commutes,
    ← Polynomial.map_map]
  rfl

/-- Modulo `T`, the completed changed primitive polynomial is its single
leading monomial. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_map_constantCoeff
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).map
        (PowerSeries.constantCoeff
          (R := AlgebraicClosure F.residueField)) =
      Polynomial.X ^
        ((Nat.card F.residueField - 1) * Nat.card F.residueField ^ n) := by
  rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial,
    Polynomial.map_map]
  have hcomp :
      (PowerSeries.constantCoeff
          (R := AlgebraicClosure F.residueField)).comp
          (PowerSeries.map
            (algebraMap F.residueField (AlgebraicClosure F.residueField))) =
        (algebraMap F.residueField (AlgebraicClosure F.residueField)).comp
          (PowerSeries.constantCoeff (R := F.residueField)) := by
    ext f
    simp only [RingHom.comp_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map]
  rw [hcomp, ← Polynomial.map_map,
    equalCharacteristicChangedIntegralPrimitivePolynomial_map_constantCoeff]
  simp

/-- The constant coefficient is the mapped unit times `T`, rather than
merely `T`; this is the point at which the source `u⁻¹T` matters. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_coeff_zero
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).coeff 0 =
      (equalCharacteristicChangedCompletedSourceUnit F u :
        (AlgebraicClosure F.residueField)⟦X⟧) * PowerSeries.X := by
  rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial,
    Polynomial.coeff_map,
    equalCharacteristicChangedIntegralPrimitivePolynomial_coeff_zero]
  simp [equalCharacteristicChangedIntegralUniformizer,
    equalCharacteristicChangedCompletedSourceUnit]

private theorem equalCharacteristicChangedCompletedIntegralUniformizer_notMem_span_X_sq
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicChangedCompletedSourceUnit F u :
        (AlgebraicClosure F.residueField)⟦X⟧) * PowerSeries.X ∉
      (Ideal.span
        ({PowerSeries.X} :
          Set (AlgebraicClosure F.residueField)⟦X⟧)) ^ 2 := by
  intro h
  let a := equalCharacteristicChangedCompletedSourceUnit F u
  have hmul :=
    ((Ideal.span
      ({PowerSeries.X} :
        Set (AlgebraicClosure F.residueField)⟦X⟧)) ^ 2).mul_mem_left
      ((a⁻¹ : (AlgebraicClosure F.residueField)⟦X⟧ˣ) :
        (AlgebraicClosure F.residueField)⟦X⟧) h
  have hcancel :
      ((a⁻¹ : (AlgebraicClosure F.residueField)⟦X⟧ˣ) :
        (AlgebraicClosure F.residueField)⟦X⟧) *
          ((a : (AlgebraicClosure F.residueField)⟦X⟧) * PowerSeries.X) =
        PowerSeries.X := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hcancel] at hmul
  exact powerSeries_X_notMem_span_X_sq
    (AlgebraicClosure F.residueField) hmul

/-- The completed integral source polynomial is genuinely Eisenstein at
`(T)`. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_isEisensteinAt
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).IsEisensteinAt
      (Ideal.span
        ({PowerSeries.X} :
          Set (AlgebraicClosure F.residueField)⟦X⟧)) := by
  let Q := equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n
  let d := (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n
  have hmonic : Q.Monic :=
    equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_monic F u n
  refine hmonic.isEisensteinAt_of_mem_of_notMem
    PowerSeries.span_X_isPrime.ne_top ?_ ?_
  · intro i hi
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    have hcoeff :
        PowerSeries.constantCoeff
            ((equalCharacteristicChangedCompletedIntegralPrimitivePolynomial
              F u n).coeff i) =
          (Polynomial.X ^ d :
            Polynomial (AlgebraicClosure F.residueField)).coeff i := by
      simpa only [Polynomial.coeff_map, d] using
        congrArg
          (fun p : Polynomial (AlgebraicClosure F.residueField) ↦ p.coeff i)
          (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_map_constantCoeff
            F u n)
    have hid : i < d := by
      simpa [Q, d,
        equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_natDegree]
        using hi
    simpa [d, Polynomial.coeff_X_pow, ne_of_lt hid] using hcoeff
  · rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_coeff_zero]
    exact equalCharacteristicChangedCompletedIntegralUniformizer_notMem_span_X_sq F u

/-- The completed integral primitive polynomial is irreducible by Eisenstein's criterion. -/
theorem equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_irreducible
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Irreducible
      (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n) := by
  apply
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_isEisensteinAt
      F u n).irreducible
      PowerSeries.span_X_isPrime
      (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_monic
        F u n).isPrimitive
  rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_natDegree]
  exact Nat.mul_pos
    (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
    (Nat.pow_pos Nat.card_pos)

/-- The source primitive polynomial remains irreducible over the completed
maximal-unramified Laurent field. -/
theorem equalCharacteristicChangedCompletedPrimitivePolynomial_irreducible
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Irreducible (equalCharacteristicChangedCompletedPrimitivePolynomial F u n) := by
  have hmap :
      Irreducible
        ((equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F u n).map
          (algebraMap (AlgebraicClosure F.residueField)⟦X⟧
            (equalCharacteristicCompletedUnramifiedField F.residueField))) :=
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_monic
      F u n).irreducible_iff_irreducible_map_fraction_map.mp
      (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_irreducible
        F u n)
  rwa [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_map] at hmap

/-- The coefficientwise Laurent base map into the changed completed level. -/
noncomputable def equalCharacteristicChangedCompletedLevelBaseHom
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    F.residueField⸨X⸩ →+*
      equalCharacteristicChangedCompletedLevelField F u n :=
  (algebraMap
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicChangedCompletedLevelField F u n)).comp
    (algebraMap F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField))

/-- The residue-field coefficient map into the changed completed level. -/
noncomputable def equalCharacteristicChangedCompletedLevelResidueHom
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    F.residueField →+*
      equalCharacteristicChangedCompletedLevelField F u n :=
  (equalCharacteristicChangedCompletedLevelBaseHom F u n).comp
    (algebraMap F.residueField F.residueField⸨X⸩)

/-- The completed base map sends the changed source uniformizer to the level uniformizer. -/
@[simp]
theorem equalCharacteristicChangedCompletedLevelBaseHom_sourceUniformizer
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedCompletedLevelBaseHom F u n
        (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u)) =
      equalCharacteristicChangedCompletedLevelUniformizer F u n := by
  rw [equalCharacteristicChangedCompletedLevelBaseHom, RingHom.comp_apply]
  rfl

/-- The chosen changed completed primitive point is nonzero. -/
theorem equalCharacteristicChangedCompletedPrimitiveRoot_ne_zero
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedCompletedPrimitiveRoot F u n ≠ 0 := by
  intro hzero
  apply equalCharacteristicChangedCompletedPrimitiveRoot_not_torsion_pred F u n
  change equalCharacteristicLubinTateAmbientPiIterate F
      (equalCharacteristicChangedCompletedLevelUniformizer F u n) n
      (equalCharacteristicChangedCompletedPrimitiveRoot F u n) = 0
  rw [hzero, map_zero]

/-- The source LT bracket image attached to a bracket unit `a`.  The theta
unit is the separate parameter `u`. -/
noncomputable def equalCharacteristicChangedCompletedUnitRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicChangedCompletedLevelField F u n :=
  equalCharacteristicLubinTateAmbientBracket F
    (equalCharacteristicChangedCompletedLevelResidueHom F u n)
    (equalCharacteristicChangedCompletedLevelUniformizer F u n) (n + 1)
    (a : F.residueField⟦X⟧)
    (equalCharacteristicChangedCompletedPrimitiveRoot F u n)

private theorem equalCharacteristicChangedActionPiPolynomial_eval₂
    (F : LocalField.{u, v} K)
    (u : F.residueField⟦X⟧ˣ)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (f : F.residueField⸨X⸩ →+* A) (x : A) :
    Polynomial.eval₂ f x
        (equalCharacteristicChangedPiPolynomial F
          (equalCharacteristicThetaSourceUnit u)) =
      equalCharacteristicLubinTateAmbientPiEnd F
        (f (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u))) x := by
  rw [equalCharacteristicChangedPiPolynomial_eq]
  simp [equalCharacteristicLubinTateAmbientPiEnd_apply]

private theorem equalCharacteristicChangedActionPiPolynomialIterate_eval₂
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (f : F.residueField⸨X⸩ →+* A) (n : ℕ) (x : A) :
    Polynomial.eval₂ f x
        (equalCharacteristicChangedPiPolynomialIterate F
          (equalCharacteristicThetaSourceUnit u) n) =
      equalCharacteristicLubinTateAmbientPiIterate F
        (f (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u))) n x := by
  have hfun :
      (fun y : A ↦ Polynomial.eval₂ f y
        (equalCharacteristicChangedPiPolynomial F
          (equalCharacteristicThetaSourceUnit u))) =
      (fun y : A ↦ equalCharacteristicLubinTateAmbientPiEnd F
        (f (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u))) y) := by
    funext y
    exact equalCharacteristicChangedActionPiPolynomial_eval₂ F u f y
  calc
    Polynomial.eval₂ f x
        (equalCharacteristicChangedPiPolynomialIterate F
          (equalCharacteristicThetaSourceUnit u) n) =
        (fun y : A ↦ Polynomial.eval₂ f y
          (equalCharacteristicChangedPiPolynomial F
            (equalCharacteristicThetaSourceUnit u)))^[n] x := by
      rw [equalCharacteristicChangedPiPolynomialIterate,
        Polynomial.iterate_comp_eval₂, Polynomial.eval₂_X]
    _ = (fun y : A ↦ equalCharacteristicLubinTateAmbientPiEnd F
        (f (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u))) y)^[n] x := by
      exact congrArg (fun g : A → A ↦ g^[n] x) hfun
    _ = equalCharacteristicLubinTateAmbientPiIterate F
        (f (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u))) n x :=
      (equalCharacteristicLubinTateAmbientPiIterate_eq_function_iterate F
        (f (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u))) n x).symm

private theorem equalCharacteristicChangedActionPrimitivePolynomial_eval₂
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (f : F.residueField⸨X⸩ →+* A) (n : ℕ) (x : A) :
    Polynomial.eval₂ f x
        (equalCharacteristicChangedPrimitivePolynomial F
          (equalCharacteristicThetaSourceUnit u) n) =
      equalCharacteristicLubinTateAmbientPiIterate F
          (f (equalCharacteristicChangedLaurentUniformizer F
            (equalCharacteristicThetaSourceUnit u))) n x ^
          (Nat.card F.residueField - 1) +
        f (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u)) := by
  rw [equalCharacteristicChangedPrimitivePolynomial_eq,
    Polynomial.eval₂_add, Polynomial.eval₂_pow,
    equalCharacteristicChangedActionPiPolynomialIterate_eval₂,
    Polynomial.eval₂_C]

/-- Every source LT unit bracket of the chosen point is again a root of the
completed source primitive polynomial. -/
theorem equalCharacteristicChangedCompletedUnitRoot_isRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (a : F.residueField⟦X⟧ˣ) :
    ((equalCharacteristicChangedCompletedPrimitivePolynomial F u n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicChangedCompletedLevelField F u n))).IsRoot
      (equalCharacteristicChangedCompletedUnitRoot F u n a) := by
  let z := equalCharacteristicChangedCompletedUnitRoot F u n a
  let x := equalCharacteristicChangedCompletedPrimitiveRoot F u n
  let t := equalCharacteristicChangedCompletedLevelUniformizer F u n
  let ι := equalCharacteristicChangedCompletedLevelResidueHom F u n
  let c := PowerSeries.coeff 0 (a : F.residueField⟦X⟧)
  have hc : c ≠ 0 := powerSeries_unit_coeff_zero_ne_zero a
  have hcpow : c ^ (Nat.card F.residueField - 1) = 1 := by
    let := Fintype.ofFinite F.residueField
    simpa only [Nat.card_eq_fintype_card] using
      FiniteField.pow_card_sub_one_eq_one c hc
  have hziterate :
      equalCharacteristicLubinTateAmbientPiIterate F t n z =
        ι c * equalCharacteristicLubinTateAmbientPiIterate F t n x := by
    simpa [z, x, t, ι, c, equalCharacteristicChangedCompletedUnitRoot] using
      equalCharacteristicLubinTateAmbientPrimitive_iterate_bracket F
        (equalCharacteristicChangedCompletedLevelResidueHom F u n)
        (equalCharacteristicChangedCompletedLevelUniformizer F u n) n
        (a : F.residueField⟦X⟧)
        (equalCharacteristicChangedCompletedPrimitiveRoot F u n)
        (equalCharacteristicChangedCompletedPrimitiveRoot_torsion F u n)
  have hxEquation :=
    equalCharacteristicChangedCompletedPrimitiveRoot_equation F u n
  have hzEquation :
      equalCharacteristicLubinTateAmbientPiIterate F t n z ^
            (Nat.card F.residueField - 1) + t = 0 := by
    rw [hziterate, mul_pow, ← map_pow, hcpow, map_one, one_mul]
    exact hxEquation
  change Polynomial.eval z
      ((equalCharacteristicChangedCompletedPrimitivePolynomial F u n).map
        (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
          (equalCharacteristicChangedCompletedLevelField F u n))) = 0
  unfold equalCharacteristicChangedCompletedPrimitivePolynomial
  rw [Polynomial.eval_map, Polynomial.eval₂_map,
    equalCharacteristicChangedActionPrimitivePolynomial_eval₂]
  have ht :
      ((algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicChangedCompletedLevelField F u n)).comp
          (algebraMap F.residueField⸨X⸩
            (equalCharacteristicCompletedUnramifiedField F.residueField)))
          (equalCharacteristicChangedLaurentUniformizer F
            (equalCharacteristicThetaSourceUnit u)) =
        equalCharacteristicChangedCompletedLevelUniformizer F u n := by
    rfl
  rw [ht]
  exact hzEquation

/-- A source LT bracket is a polynomial expression in its input over the
completed-unramified base. -/
theorem equalCharacteristicChangedCompletedAmbientBracket_mem_adjoin
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n m : ℕ)
    (a : F.residueField⟦X⟧)
    (z : equalCharacteristicChangedCompletedLevelField F u n) :
    equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicChangedCompletedLevelResidueHom F u n)
        (equalCharacteristicChangedCompletedLevelUniformizer F u n) m a z ∈
      Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ({z} : Set (equalCharacteristicChangedCompletedLevelField F u n)) := by
  let A := equalCharacteristicCompletedUnramifiedField F.residueField
  let E := equalCharacteristicChangedCompletedLevelField F u n
  let t : E := equalCharacteristicChangedCompletedLevelUniformizer F u n
  let S : Subalgebra A E := Algebra.adjoin A ({z} : Set E)
  have hz : z ∈ S := Algebra.subset_adjoin (Set.mem_singleton z)
  have ht : t ∈ S := by
    change algebraMap A E
      (equalCharacteristicChangedCompletedBaseUniformizer F u) ∈ S
    exact S.algebraMap_mem _
  have hcoeff (c : F.residueField) :
      equalCharacteristicChangedCompletedLevelResidueHom F u n c ∈ S := by
    rw [equalCharacteristicChangedCompletedLevelResidueHom, RingHom.comp_apply,
      equalCharacteristicChangedCompletedLevelBaseHom, RingHom.comp_apply]
    exact S.algebraMap_mem _
  have hiterate (i : ℕ) :
      equalCharacteristicLubinTateAmbientPiIterate F t i z ∈ S := by
    induction i with
    | zero =>
        simpa [equalCharacteristicLubinTateAmbientPiIterate_zero] using hz
    | succ i ih =>
        rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
          ← equalCharacteristicLubinTateAmbientPiEnd_iterate,
          equalCharacteristicLubinTateAmbientPiEnd_apply]
        exact S.add_mem (S.pow_mem ih _) (S.mul_mem ht ih)
  rw [equalCharacteristicLubinTateAmbientBracket_apply]
  exact S.sum_mem fun i _ ↦ S.mul_mem (hcoeff _) (hiterate i)

/-- The visible source unit parameter root. -/
noncomputable def equalCharacteristicChangedCompletedUnitParameterRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicChangedCompletedLevelField F u n :=
  equalCharacteristicChangedCompletedUnitRoot F u n
    (equalCharacteristicLubinTateUnitParameterUnit F n a)

/-- Distinct visible source unit parameters give distinct roots. -/
theorem equalCharacteristicChangedCompletedUnitParameterRoot_injective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Function.Injective
      (equalCharacteristicChangedCompletedUnitParameterRoot F u n) := by
  intro a b hab
  apply equalCharacteristicLubinTateUnitParameter_eq_of_coeff_eq F n a b
  exact equalCharacteristicLubinTateAmbientPrimitive_bracket_eq_coeff F
    (equalCharacteristicChangedCompletedLevelResidueHom F u n)
    (equalCharacteristicChangedCompletedLevelUniformizer F u n) n
    (equalCharacteristicChangedCompletedPrimitiveRoot F u n)
    (equalCharacteristicChangedCompletedPrimitiveRoot_torsion F u n)
    (equalCharacteristicChangedCompletedPrimitiveRoot_not_torsion_pred F u n)
    (equalCharacteristicLubinTateUnitParameterSeries F n a)
    (equalCharacteristicLubinTateUnitParameterSeries F n b) hab

/-- Each unit parameter produces a root of the changed completed primitive polynomial. -/
theorem equalCharacteristicChangedCompletedUnitParameterRoot_isRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    ((equalCharacteristicChangedCompletedPrimitivePolynomial F u n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicChangedCompletedLevelField F u n))).IsRoot
      (equalCharacteristicChangedCompletedUnitParameterRoot F u n a) := by
  simpa [equalCharacteristicChangedCompletedUnitParameterRoot] using
    equalCharacteristicChangedCompletedUnitRoot_isRoot F u n
      (equalCharacteristicLubinTateUnitParameterUnit F n a)

/-- The completed source primitive polynomial is separable. -/
theorem equalCharacteristicChangedCompletedPrimitivePolynomial_separable
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedPrimitivePolynomial F u n).Separable := by
  unfold equalCharacteristicChangedCompletedPrimitivePolynomial
  exact (equalCharacteristicChangedPrimitivePolynomial_separable F
    (equalCharacteristicThetaSourceUnit u) n).map

/-- A visible source unit parameter as an element of the full root set. -/
noncomputable def equalCharacteristicChangedCompletedUnitParameterRootSet
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    (equalCharacteristicChangedCompletedPrimitivePolynomial F u n).rootSet
      (equalCharacteristicChangedCompletedLevelField F u n) :=
  ⟨equalCharacteristicChangedCompletedUnitParameterRoot F u n a,
    Polynomial.mem_rootSet.mpr
      ⟨(equalCharacteristicChangedCompletedPrimitivePolynomial_monic F u n).ne_zero,
        by
          rw [Polynomial.aeval_def, ← Polynomial.eval_map]
          exact equalCharacteristicChangedCompletedUnitParameterRoot_isRoot F u n a⟩⟩

/-- Distinct unit parameters give distinct completed primitive roots. -/
theorem equalCharacteristicChangedCompletedUnitParameterRootSet_injective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Function.Injective
      (equalCharacteristicChangedCompletedUnitParameterRootSet F u n) := by
  intro a b hab
  apply equalCharacteristicChangedCompletedUnitParameterRoot_injective F u n
  exact congrArg Subtype.val hab

/-- The completed changed primitive polynomial has the expected number of
roots in its splitting field. -/
theorem equalCharacteristicChangedCompletedPrimitiveRootSet_natCard
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Nat.card
        ((equalCharacteristicChangedCompletedPrimitivePolynomial F u n).rootSet
          (equalCharacteristicChangedCompletedLevelField F u n)) =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  rw [Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree
      (equalCharacteristicChangedCompletedPrimitivePolynomial_separable F u n)
      (equalCharacteristicChangedCompletedPrimitivePolynomial_splits F u n),
    equalCharacteristicChangedCompletedPrimitivePolynomial_natDegree]

/-- Visible source LT unit parameters enumerate every primitive root. -/
theorem equalCharacteristicChangedCompletedUnitParameterRootSet_bijective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Function.Bijective
      (equalCharacteristicChangedCompletedUnitParameterRootSet F u n) := by
  apply (Nat.bijective_iff_injective_and_card
    (equalCharacteristicChangedCompletedUnitParameterRootSet F u n)).mpr
  exact
    ⟨equalCharacteristicChangedCompletedUnitParameterRootSet_injective F u n,
      (equalCharacteristicLubinTateUnitParameter_natCard F n).trans
        (equalCharacteristicChangedCompletedPrimitiveRootSet_natCard F u n).symm⟩

/-- Every visible parameter root is a source bracket polynomial in the
chosen primitive point. -/
theorem equalCharacteristicChangedCompletedUnitParameterRoot_mem_adjoin
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicChangedCompletedUnitParameterRoot F u n a ∈
      Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ({equalCharacteristicChangedCompletedPrimitiveRoot F u n} :
          Set (equalCharacteristicChangedCompletedLevelField F u n)) := by
  let A := equalCharacteristicCompletedUnramifiedField F.residueField
  let E := equalCharacteristicChangedCompletedLevelField F u n
  let x : E := equalCharacteristicChangedCompletedPrimitiveRoot F u n
  let t : E := equalCharacteristicChangedCompletedLevelUniformizer F u n
  let S : Subalgebra A E := Algebra.adjoin A ({x} : Set E)
  have hx : x ∈ S := Algebra.subset_adjoin (Set.mem_singleton x)
  have ht : t ∈ S := by
    change algebraMap A E
      (equalCharacteristicChangedCompletedBaseUniformizer F u) ∈ S
    exact S.algebraMap_mem _
  have hcoeff (c : F.residueField) :
      equalCharacteristicChangedCompletedLevelResidueHom F u n c ∈ S := by
    rw [equalCharacteristicChangedCompletedLevelResidueHom, RingHom.comp_apply,
      equalCharacteristicChangedCompletedLevelBaseHom, RingHom.comp_apply]
    exact S.algebraMap_mem _
  have hiterate (i : ℕ) :
      equalCharacteristicLubinTateAmbientPiIterate F t i x ∈ S := by
    induction i with
    | zero =>
        simpa [equalCharacteristicLubinTateAmbientPiIterate_zero] using hx
    | succ i ih =>
        rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
          ← equalCharacteristicLubinTateAmbientPiEnd_iterate,
          equalCharacteristicLubinTateAmbientPiEnd_apply]
        exact S.add_mem (S.pow_mem ih _) (S.mul_mem ht ih)
  change equalCharacteristicLubinTateAmbientBracket F
      (equalCharacteristicChangedCompletedLevelResidueHom F u n) t (n + 1)
      (equalCharacteristicLubinTateUnitParameterSeries F n a) x ∈ S
  rw [equalCharacteristicLubinTateAmbientBracket_apply]
  exact S.sum_mem fun i _ ↦ S.mul_mem (hcoeff _) (hiterate i)

/-- Every root lies in the subfield generated by the chosen primitive
point. -/
theorem equalCharacteristicChangedCompletedPrimitiveRootSet_subset_adjoin
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    ((equalCharacteristicChangedCompletedPrimitivePolynomial F u n).rootSet
        (equalCharacteristicChangedCompletedLevelField F u n) :
      Set (equalCharacteristicChangedCompletedLevelField F u n)) ⊆
      Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ({equalCharacteristicChangedCompletedPrimitiveRoot F u n} :
          Set (equalCharacteristicChangedCompletedLevelField F u n)) := by
  intro y hy
  let yroot :=
    (show (equalCharacteristicChangedCompletedPrimitivePolynomial F u n).rootSet
        (equalCharacteristicChangedCompletedLevelField F u n) from ⟨y, hy⟩)
  obtain ⟨a, ha⟩ :=
    (equalCharacteristicChangedCompletedUnitParameterRootSet_bijective
      F u n).surjective yroot
  have hay : equalCharacteristicChangedCompletedUnitParameterRoot F u n a = y :=
    congrArg Subtype.val ha
  rw [← hay]
  exact equalCharacteristicChangedCompletedUnitParameterRoot_mem_adjoin F u n a

/-- The chosen primitive source point generates its completed splitting
field. -/
theorem equalCharacteristicChangedCompletedPrimitiveRoot_adjoin_eq_top
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ({equalCharacteristicChangedCompletedPrimitiveRoot F u n} :
          Set (equalCharacteristicChangedCompletedLevelField F u n)) = ⊤ := by
  have hall :
      Algebra.adjoin
          (equalCharacteristicCompletedUnramifiedField F.residueField)
          ((equalCharacteristicChangedCompletedPrimitivePolynomial F u n).rootSet
            (equalCharacteristicChangedCompletedLevelField F u n) :
            Set (equalCharacteristicChangedCompletedLevelField F u n)) ≤
        Algebra.adjoin
          (equalCharacteristicCompletedUnramifiedField F.residueField)
          ({equalCharacteristicChangedCompletedPrimitiveRoot F u n} :
            Set (equalCharacteristicChangedCompletedLevelField F u n)) :=
    Algebra.adjoin_le
      (equalCharacteristicChangedCompletedPrimitiveRootSet_subset_adjoin F u n)
  rw [equalCharacteristicChangedCompletedPrimitivePolynomial_adjoin_rootSet] at hall
  exact top_unique hall

/-- Every source LT unit bracket of the primitive point is itself a
primitive generator of the completed level field. -/
theorem equalCharacteristicChangedCompletedUnitRoot_adjoin_eq_top
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (a : F.residueField⟦X⟧ˣ) :
    Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ({equalCharacteristicChangedCompletedUnitRoot F u n a} :
          Set (equalCharacteristicChangedCompletedLevelField F u n)) = ⊤ := by
  let x := equalCharacteristicChangedCompletedPrimitiveRoot F u n
  let y := equalCharacteristicChangedCompletedUnitRoot F u n a
  let ι := equalCharacteristicChangedCompletedLevelResidueHom F u n
  let t := equalCharacteristicChangedCompletedLevelUniformizer F u n
  have hrecover :
      equalCharacteristicLubinTateAmbientBracket F ι t (n + 1)
          ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧) y = x := by
    change equalCharacteristicLubinTateAmbientBracket F ι t (n + 1)
        ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
        (equalCharacteristicLubinTateAmbientBracket F ι t (n + 1)
          (a : F.residueField⟦X⟧) x) = x
    rw [← equalCharacteristicLubinTateAmbientBracket_mul_apply_of_torsion
      F ι t (n + 1)
      ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
      (a : F.residueField⟦X⟧) x
      (equalCharacteristicChangedCompletedPrimitiveRoot_torsion F u n)]
    have hmul :
        ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧) *
            (a : F.residueField⟦X⟧) = 1 := by
      exact Units.inv_mul a
    rw [hmul]
    simp [equalCharacteristicLubinTateAmbientBracket_apply]
  have hxmem :
      x ∈ Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ({y} : Set (equalCharacteristicChangedCompletedLevelField F u n)) := by
    rw [← hrecover]
    exact equalCharacteristicChangedCompletedAmbientBracket_mem_adjoin
      F u n (n + 1)
      ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧) y
  have hle :
      Algebra.adjoin
          (equalCharacteristicCompletedUnramifiedField F.residueField)
          ({x} : Set (equalCharacteristicChangedCompletedLevelField F u n)) ≤
        Algebra.adjoin
          (equalCharacteristicCompletedUnramifiedField F.residueField)
          ({y} : Set (equalCharacteristicChangedCompletedLevelField F u n)) := by
    apply Algebra.adjoin_le
    intro z hz
    simpa only [Set.mem_singleton_iff] using hz ▸ hxmem
  rw [show Algebra.adjoin
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      ({x} : Set (equalCharacteristicChangedCompletedLevelField F u n)) = ⊤ by
        simpa [x] using
          equalCharacteristicChangedCompletedPrimitiveRoot_adjoin_eq_top F u n]
      at hle
  exact top_unique hle

/-- The chosen changed primitive point is integral over the completed
maximal-unramified base. -/
theorem equalCharacteristicChangedCompletedPrimitiveRoot_isIntegral
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IsIntegral
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicChangedCompletedPrimitiveRoot F u n) := by
  refine ⟨equalCharacteristicChangedCompletedPrimitivePolynomial F u n,
    equalCharacteristicChangedCompletedPrimitivePolynomial_monic F u n, ?_⟩
  rw [← Polynomial.eval_map]
  exact equalCharacteristicChangedCompletedPrimitiveRoot_isRoot F u n

/-- The completed source primitive polynomial is the minimal polynomial of
the chosen primitive point. -/
theorem equalCharacteristicChangedCompletedPrimitiveRoot_minpoly
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    minpoly (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicChangedCompletedPrimitiveRoot F u n) =
      equalCharacteristicChangedCompletedPrimitivePolynomial F u n := by
  have hroot :
      Polynomial.aeval (equalCharacteristicChangedCompletedPrimitiveRoot F u n)
          (equalCharacteristicChangedCompletedPrimitivePolynomial F u n) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact equalCharacteristicChangedCompletedPrimitiveRoot_isRoot F u n
  have hmin := minpoly.eq_of_irreducible
    (equalCharacteristicChangedCompletedPrimitivePolynomial_irreducible F u n)
    hroot
  rw [(equalCharacteristicChangedCompletedPrimitivePolynomial_monic F u n).leadingCoeff,
    inv_one, Polynomial.C_1, mul_one] at hmin
  exact hmin.symm

/-- The power basis generated by the completed primitive source point. -/
noncomputable def equalCharacteristicChangedCompletedPrimitivePowerBasis
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    PowerBasis
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicChangedCompletedLevelField F u n) :=
  PowerBasis.ofAdjoinEqTop
    (equalCharacteristicChangedCompletedPrimitiveRoot_isIntegral F u n)
    (equalCharacteristicChangedCompletedPrimitiveRoot_adjoin_eq_top F u n)

/-- The completed primitive power basis has the distinguished root as generator. -/
@[simp]
theorem equalCharacteristicChangedCompletedPrimitivePowerBasis_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedPrimitivePowerBasis F u n).gen =
      equalCharacteristicChangedCompletedPrimitiveRoot F u n :=
  PowerBasis.ofAdjoinEqTop_gen _ _

end EqualCharacteristic
end LubinTate
