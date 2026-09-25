/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.SplittingField.IsSplittingField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
/-!
# Towers of equal-characteristic Lubin--Tate level fields

The primitive roots used to define the finite levels are chosen independently
inside one separable closure.  This file proves that the resulting standard
level fields nevertheless form an increasing tower.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The `(n - m)`-fold Lubin--Tate predecessor of a primitive level-`n + 1`
point is a root of the primitive level-`m + 1` polynomial. -/
theorem equalCharacteristicLubinTatePrimitivePredecessor_isRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {m n : ℕ} (hmn : m ≤ n) :
    let y :=
      equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicSeparableUniformizer F) (n - m)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
    ((equalCharacteristicLubinTatePrimitivePolynomial F m).map
      (equalCharacteristicSeparableBaseHom F)).IsRoot y := by
  let y :=
    equalCharacteristicLubinTateAmbientPiIterate F
      (equalCharacteristicSeparableUniformizer F) (n - m)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
  have hyEquation :
      equalCharacteristicLubinTateAmbientPiIterate F
          (equalCharacteristicSeparableUniformizer F) m y ^
            (Nat.card F.residueField - 1) +
        equalCharacteristicSeparableUniformizer F = 0 := by
    rw [show
      equalCharacteristicLubinTateAmbientPiIterate F
          (equalCharacteristicSeparableUniformizer F) m y =
        equalCharacteristicLubinTateAmbientPiIterate F
          (equalCharacteristicSeparableUniformizer F) n
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) by
      simp only [y]
      rw [← equalCharacteristicLubinTateAmbientPiIterate_add,
        Nat.add_sub_of_le hmn]]
    exact chosenEqualCharacteristicLubinTatePrimitiveRoot_equation F n
  change Polynomial.eval y
      ((equalCharacteristicLubinTatePrimitivePolynomial F m).map
        (equalCharacteristicSeparableBaseHom F)) = 0
  rw [Polynomial.eval_map,
    equalCharacteristicLubinTatePrimitivePolynomial_eval₂]
  exact hyEquation

/-- The independently chosen equal-characteristic Lubin--Tate level fields
form an increasing tower inside the fixed separable closure. -/
theorem equalCharacteristicLubinTateLevelField_mono
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {m n : ℕ} (hmn : m ≤ n) :
    equalCharacteristicLubinTateLevelField F m ≤
      equalCharacteristicLubinTateLevelField F n := by
  let B := F.residueField⸨X⸩
  let S := SeparableClosure B
  let E := equalCharacteristicLubinTateLevelField F n
  let p := equalCharacteristicLubinTatePrimitivePolynomial F m
  let y : S :=
    equalCharacteristicLubinTateAmbientPiIterate F
      (equalCharacteristicSeparableUniformizer F) (n - m)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
  have hy_mem : y ∈ E := by
    exact
      chosenEqualCharacteristicLubinTatePrimitiveRoot_piIterate_mem_levelField
        F n (n - m)
  let yE : E := ⟨y, hy_mem⟩
  have hyp : (p.map (algebraMap B E)).IsRoot yE := by
    have hroot :=
      equalCharacteristicLubinTatePrimitivePredecessor_isRoot F hmn
    change Polynomial.eval y
        ((equalCharacteristicLubinTatePrimitivePolynomial F m).map
          (equalCharacteristicSeparableBaseHom F)) = 0 at hroot
    change Polynomial.eval yE (p.map (algebraMap B E)) = 0
    apply E.val.injective
    rw [map_zero, Polynomial.eval_map, Polynomial.hom_eval₂]
    have hcomp :
        E.val.toRingHom.comp (algebraMap B E) = algebraMap B S := by
      ext x
      rfl
    rw [hcomp]
    simpa [yE, p, Polynomial.eval₂_eq_eval_map,
      equalCharacteristicSeparableBaseHom_eq_algebraMap] using hroot
  have hp_minpoly : p = minpoly B yE := by
    apply minpoly.eq_of_irreducible_of_monic
      (equalCharacteristicLubinTatePrimitivePolynomial_irreducible F m)
      _ (equalCharacteristicLubinTatePrimitivePolynomial_monic F m)
    simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hyp
  let : FiniteDimensional B E :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let : IsGalois B E :=
    equalCharacteristicLubinTateLevelField_isGalois F n
  have hp_split_E : (p.map (algebraMap B E)).Splits := by
    rw [hp_minpoly]
    exact IsGalois.splits B yE
  have hp_split_S : (p.map (algebraMap B S)).Splits := by
    have h := hp_split_E.map E.val.toRingHom
    simpa [Polynomial.map_map] using h
  have hchosen_mem :
      chosenEqualCharacteristicLubinTatePrimitiveRoot F m ∈ E := by
    apply
      (IntermediateField.splits_iff_mem
        (F := E) hp_split_S).1 hp_split_E
    rw [Polynomial.mem_rootSet']
    constructor
    · exact
        ((equalCharacteristicLubinTatePrimitivePolynomial_monic F m).map
          (algebraMap B S)).ne_zero
    · simpa [Polynomial.aeval_def, p,
        equalCharacteristicSeparableBaseHom_eq_algebraMap] using
        chosenEqualCharacteristicLubinTatePrimitiveRoot_isRoot F m
  change IntermediateField.adjoin B
      {chosenEqualCharacteristicLubinTatePrimitiveRoot F m} ≤ E
  rw [IntermediateField.adjoin_le_iff]
  simpa using hchosen_mem

end EqualCharacteristic
end LubinTate
