/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveIrreducible
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
/-!
# The completed theta-intertwining theorem: primitive division points in the completed level

The completed level used in the proof of the completed theta-intertwining theorem is the
  splitting field of the
base-changed primitive division polynomial.  This file records that its chosen
root is genuinely primitive of level `n + 1`: it is killed by the next
Lubin--Tate iterate, but not by the preceding one.  These statements are the
algebraic input for extending arithmetic Frobenius to the completed level.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries Polynomial PowerSeries


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The coefficientwise Laurent-series algebra used by the completed
unramified base.  It is kept local so importing this file does not change
global type-class search. -/
noncomputable local instance equalCharacteristicCompletedPrimitiveActionBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

/-- The coefficientwise Laurent base map into the completed level field. -/
noncomputable def equalCharacteristicCompletedLevelBaseHom
    (F : LocalField.{u, v} K) (n : ℕ) :
    F.residueField⸨X⸩ →+*
      equalCharacteristicCompletedLevelField F n :=
  (algebraMap
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)).comp
    (algebraMap F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField))

/-- The residue-field coefficient map into the completed level. -/
noncomputable def equalCharacteristicCompletedLevelResidueHom
    (F : LocalField.{u, v} K) (n : ℕ) :
    F.residueField →+* equalCharacteristicCompletedLevelField F n :=
  (equalCharacteristicCompletedLevelBaseHom F n).comp
    (algebraMap F.residueField F.residueField⸨X⸩)

/-- States the theorem `equalCharacteristicCompletedLevelBaseHom_uniformizer`. -/
@[simp]
theorem equalCharacteristicCompletedLevelBaseHom_uniformizer
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicCompletedLevelBaseHom F n
        (equalCharacteristicLaurentUniformizer F) =
      equalCharacteristicCompletedLevelUniformizer F n := by
  rw [equalCharacteristicCompletedLevelBaseHom, RingHom.comp_apply,
    equalCharacteristicCompletedBase_algebraMap_uniformizer]
  rfl

/-- The chosen root in the completed splitting field is killed at level
`n + 1`. -/
theorem equalCharacteristicCompletedPrimitiveRoot_torsion
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    IsEqualCharacteristicLubinTateAmbientTorsion F
      (equalCharacteristicCompletedLevelUniformizer F n) (n + 1)
      (equalCharacteristicCompletedPrimitiveRoot F n) := by
  let t := equalCharacteristicCompletedLevelUniformizer F n
  let x := equalCharacteristicCompletedPrimitiveRoot F n
  let y := equalCharacteristicLubinTateAmbientPiIterate F t n x
  have heq : y ^ (Nat.card F.residueField - 1) + t = 0 := by
    simpa only [t, x, y] using
      (equalCharacteristicCompletedPrimitiveRoot_equation F n)
  change equalCharacteristicLubinTateAmbientPiIterate F t (n + 1) x = 0
  rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
    ← equalCharacteristicLubinTateAmbientPiEnd_iterate]
  change equalCharacteristicLubinTateAmbientPiEnd F t y = 0
  rw [equalCharacteristicLubinTateAmbientPiEnd_apply]
  calc
    y ^ Nat.card F.residueField + t * y =
        y * (y ^ (Nat.card F.residueField - 1) + t) := by
      rw [mul_add, mul_comm t y, ← pow_succ']
      rw [Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne')]
    _ = 0 := by rw [heq, mul_zero]

/-- The chosen completed root is not already killed at level `n`. -/
theorem equalCharacteristicCompletedPrimitiveRoot_not_torsion_pred
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    ¬ IsEqualCharacteristicLubinTateAmbientTorsion F
      (equalCharacteristicCompletedLevelUniformizer F n) n
      (equalCharacteristicCompletedPrimitiveRoot F n) := by
  intro hpred
  have heq := equalCharacteristicCompletedPrimitiveRoot_equation F n
  rw [hpred, zero_pow, zero_add] at heq
  · have hne :
        equalCharacteristicCompletedLevelBaseHom F n
              (equalCharacteristicLaurentUniformizer F) ≠
            equalCharacteristicCompletedLevelBaseHom F n 0 :=
      (equalCharacteristicCompletedLevelBaseHom F n).injective.ne
        (equalCharacteristicLaurentUniformizer_ne_zero F)
    exact hne (by simpa using heq)
  · exact Nat.sub_ne_zero_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- In particular, the chosen completed primitive point is nonzero. -/
theorem equalCharacteristicCompletedPrimitiveRoot_ne_zero
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicCompletedPrimitiveRoot F n ≠ 0 := by
  intro hzero
  apply equalCharacteristicCompletedPrimitiveRoot_not_torsion_pred F n
  change equalCharacteristicLubinTateAmbientPiIterate F
      (equalCharacteristicCompletedLevelUniformizer F n) n
      (equalCharacteristicCompletedPrimitiveRoot F n) = 0
  rw [hzero, map_zero]

/-- The bracket image of the completed primitive point attached to a
power-series unit. -/
noncomputable def equalCharacteristicCompletedUnitRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicCompletedLevelField F n :=
  equalCharacteristicLubinTateAmbientBracket F
    (equalCharacteristicCompletedLevelResidueHom F n)
    (equalCharacteristicCompletedLevelUniformizer F n) (n + 1)
    (a : F.residueField⟦X⟧)
    (equalCharacteristicCompletedPrimitiveRoot F n)

/-- Every unit bracket of the chosen completed point is again a root of the
completed primitive polynomial. -/
theorem equalCharacteristicCompletedUnitRoot_isRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    ((equalCharacteristicCompletedPrimitivePolynomial F n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n))).IsRoot
      (equalCharacteristicCompletedUnitRoot F n a) := by
  let z := equalCharacteristicCompletedUnitRoot F n a
  let x := equalCharacteristicCompletedPrimitiveRoot F n
  let t := equalCharacteristicCompletedLevelUniformizer F n
  let ι := equalCharacteristicCompletedLevelResidueHom F n
  let c := PowerSeries.coeff 0 (a : F.residueField⟦X⟧)
  have hc : c ≠ 0 := powerSeries_unit_coeff_zero_ne_zero a
  have hcpow : c ^ (Nat.card F.residueField - 1) = 1 := by
    let := Fintype.ofFinite F.residueField
    simpa only [Nat.card_eq_fintype_card] using
      FiniteField.pow_card_sub_one_eq_one c hc
  have hziterate :
      equalCharacteristicLubinTateAmbientPiIterate F t n z =
        ι c * equalCharacteristicLubinTateAmbientPiIterate F t n x := by
    simpa [z, x, t, ι, c, equalCharacteristicCompletedUnitRoot] using
      equalCharacteristicLubinTateAmbientPrimitive_iterate_bracket F
        (equalCharacteristicCompletedLevelResidueHom F n)
        (equalCharacteristicCompletedLevelUniformizer F n) n
        (a : F.residueField⟦X⟧)
        (equalCharacteristicCompletedPrimitiveRoot F n)
        (equalCharacteristicCompletedPrimitiveRoot_torsion F n)
  have hxEquation := equalCharacteristicCompletedPrimitiveRoot_equation F n
  have hzEquation :
      equalCharacteristicLubinTateAmbientPiIterate F t n z ^
            (Nat.card F.residueField - 1) + t = 0 := by
    rw [hziterate, mul_pow, ← map_pow, hcpow, map_one, one_mul]
    exact hxEquation
  change Polynomial.eval z
      ((equalCharacteristicCompletedPrimitivePolynomial F n).map
        (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
          (equalCharacteristicCompletedLevelField F n))) = 0
  unfold equalCharacteristicCompletedPrimitivePolynomial
  rw [Polynomial.eval_map, Polynomial.eval₂_map,
    equalCharacteristicLubinTatePrimitivePolynomial_eval₂]
  have ht :
      ((algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)).comp
          (algebraMap F.residueField⸨X⸩
            (equalCharacteristicCompletedUnramifiedField F.residueField)))
          (equalCharacteristicLaurentUniformizer F) =
        equalCharacteristicCompletedLevelUniformizer F n := by
    rw [RingHom.comp_apply,
      equalCharacteristicCompletedBase_algebraMap_uniformizer]
    rfl
  rw [ht]
  exact hzEquation

/-- A truncated bracket is a polynomial expression in its input over the
completed-unramified base. -/
theorem equalCharacteristicCompletedAmbientBracket_mem_adjoin
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n m : ℕ) (a : F.residueField⟦X⟧)
    (z : equalCharacteristicCompletedLevelField F n) :
    equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicCompletedLevelResidueHom F n)
        (equalCharacteristicCompletedLevelUniformizer F n) m a z ∈
      Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ({z} : Set (equalCharacteristicCompletedLevelField F n)) := by
  let A := equalCharacteristicCompletedUnramifiedField F.residueField
  let E := equalCharacteristicCompletedLevelField F n
  let t : E := equalCharacteristicCompletedLevelUniformizer F n
  let S : Subalgebra A E := Algebra.adjoin A ({z} : Set E)
  have hz : z ∈ S := Algebra.subset_adjoin (Set.mem_singleton z)
  have ht : t ∈ S := by
    change algebraMap A E (equalCharacteristicCompletedBaseUniformizer F) ∈ S
    exact S.algebraMap_mem _
  have hcoeff (c : F.residueField) :
      equalCharacteristicCompletedLevelResidueHom F n c ∈ S := by
    rw [equalCharacteristicCompletedLevelResidueHom, RingHom.comp_apply,
      equalCharacteristicCompletedLevelBaseHom, RingHom.comp_apply]
    exact S.algebraMap_mem _
  have hiterate (i : ℕ) :
      equalCharacteristicLubinTateAmbientPiIterate F t i z ∈ S := by
    induction i with
    | zero =>
        rw [equalCharacteristicLubinTateAmbientPiIterate, pow_zero]
        exact hz
    | succ i ih =>
        rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
          ← equalCharacteristicLubinTateAmbientPiEnd_iterate,
          equalCharacteristicLubinTateAmbientPiEnd_apply]
        exact S.add_mem (S.pow_mem ih _) (S.mul_mem ht ih)
  rw [equalCharacteristicLubinTateAmbientBracket_apply]
  exact S.sum_mem fun i _ ↦ S.mul_mem (hcoeff _) (hiterate i)

/-- The image of the completed primitive point attached to a visible unit
parameter. -/
noncomputable def equalCharacteristicCompletedUnitParameterRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicCompletedLevelField F n :=
  equalCharacteristicCompletedUnitRoot F n
    (equalCharacteristicLubinTateUnitParameterUnit F n a)

/-- Distinct visible unit parameters give distinct completed primitive
points. -/
theorem equalCharacteristicCompletedUnitParameterRoot_injective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Function.Injective (equalCharacteristicCompletedUnitParameterRoot F n) := by
  intro a b hab
  apply equalCharacteristicLubinTateUnitParameter_eq_of_coeff_eq F n a b
  exact equalCharacteristicLubinTateAmbientPrimitive_bracket_eq_coeff F
    (equalCharacteristicCompletedLevelResidueHom F n)
    (equalCharacteristicCompletedLevelUniformizer F n) n
    (equalCharacteristicCompletedPrimitiveRoot F n)
    (equalCharacteristicCompletedPrimitiveRoot_torsion F n)
    (equalCharacteristicCompletedPrimitiveRoot_not_torsion_pred F n)
    (equalCharacteristicLubinTateUnitParameterSeries F n a)
    (equalCharacteristicLubinTateUnitParameterSeries F n b) hab

/-- Every visible unit bracket of the chosen completed point is again a
root of the completed primitive polynomial. -/
theorem equalCharacteristicCompletedUnitParameterRoot_isRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    ((equalCharacteristicCompletedPrimitivePolynomial F n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n))).IsRoot
      (equalCharacteristicCompletedUnitParameterRoot F n a) := by
  simpa [equalCharacteristicCompletedUnitParameterRoot] using
    equalCharacteristicCompletedUnitRoot_isRoot F n
      (equalCharacteristicLubinTateUnitParameterUnit F n a)

/-- Base change to the completed maximal-unramified field preserves
separability of the primitive polynomial. -/
theorem equalCharacteristicCompletedPrimitivePolynomial_separable
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedPrimitivePolynomial F n).Separable := by
  unfold equalCharacteristicCompletedPrimitivePolynomial
  exact (equalCharacteristicLubinTatePrimitivePolynomial_separable F n).map

/-- A visible unit parameter, regarded as an element of the full root set
in the completed splitting field. -/
noncomputable def equalCharacteristicCompletedUnitParameterRootSet
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    (equalCharacteristicCompletedPrimitivePolynomial F n).rootSet
      (equalCharacteristicCompletedLevelField F n) :=
  ⟨equalCharacteristicCompletedUnitParameterRoot F n a,
    Polynomial.mem_rootSet.mpr
      ⟨(equalCharacteristicCompletedPrimitivePolynomial_monic F n).ne_zero,
        by
          rw [Polynomial.aeval_def, ← Polynomial.eval_map]
          exact equalCharacteristicCompletedUnitParameterRoot_isRoot F n a⟩⟩

/-- States the theorem `equalCharacteristicCompletedUnitParameterRootSet_injective`. -/
theorem equalCharacteristicCompletedUnitParameterRootSet_injective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Function.Injective (equalCharacteristicCompletedUnitParameterRootSet F n) := by
  intro a b hab
  apply equalCharacteristicCompletedUnitParameterRoot_injective F n
  exact congrArg Subtype.val hab

/-- The completed primitive polynomial has precisely the expected number
of roots in its splitting field. -/
theorem equalCharacteristicCompletedPrimitiveRootSet_natCard
    (F : LocalField.{u, v} K) (n : ℕ) :
    Nat.card
        ((equalCharacteristicCompletedPrimitivePolynomial F n).rootSet
          (equalCharacteristicCompletedLevelField F n)) =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  rw [Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree
      (equalCharacteristicCompletedPrimitivePolynomial_separable F n)
      (equalCharacteristicCompletedPrimitivePolynomial_splits F n),
    equalCharacteristicCompletedPrimitivePolynomial_natDegree]

/-- Visible unit parameters enumerate every root after passage to the
completed maximal-unramified base. -/
theorem equalCharacteristicCompletedUnitParameterRootSet_bijective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Function.Bijective
      (equalCharacteristicCompletedUnitParameterRootSet F n) := by
  apply (Nat.bijective_iff_injective_and_card
    (equalCharacteristicCompletedUnitParameterRootSet F n)).mpr
  exact ⟨equalCharacteristicCompletedUnitParameterRootSet_injective F n,
    (equalCharacteristicLubinTateUnitParameter_natCard F n).trans
      (equalCharacteristicCompletedPrimitiveRootSet_natCard F n).symm⟩

/-- Every parameter root is a polynomial expression in the chosen completed
primitive point, with coefficients in the completed-unramified base. -/
theorem equalCharacteristicCompletedUnitParameterRoot_mem_adjoin
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicCompletedUnitParameterRoot F n a ∈
      Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ({equalCharacteristicCompletedPrimitiveRoot F n} :
          Set (equalCharacteristicCompletedLevelField F n)) := by
  let A := equalCharacteristicCompletedUnramifiedField F.residueField
  let E := equalCharacteristicCompletedLevelField F n
  let x : E := equalCharacteristicCompletedPrimitiveRoot F n
  let t : E := equalCharacteristicCompletedLevelUniformizer F n
  let S : Subalgebra A E := Algebra.adjoin A ({x} : Set E)
  have hx : x ∈ S := Algebra.subset_adjoin (Set.mem_singleton x)
  have ht : t ∈ S := by
    change algebraMap A E (equalCharacteristicCompletedBaseUniformizer F) ∈ S
    exact S.algebraMap_mem _
  have hcoeff (c : F.residueField) :
      equalCharacteristicCompletedLevelResidueHom F n c ∈ S := by
    rw [equalCharacteristicCompletedLevelResidueHom, RingHom.comp_apply,
      equalCharacteristicCompletedLevelBaseHom, RingHom.comp_apply]
    exact S.algebraMap_mem _
  have hiterate (i : ℕ) :
      equalCharacteristicLubinTateAmbientPiIterate F t i x ∈ S := by
    induction i with
    | zero =>
        rw [equalCharacteristicLubinTateAmbientPiIterate, pow_zero]
        exact hx
    | succ i ih =>
        rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
          ← equalCharacteristicLubinTateAmbientPiEnd_iterate,
          equalCharacteristicLubinTateAmbientPiEnd_apply]
        exact S.add_mem (S.pow_mem ih _) (S.mul_mem ht ih)
  change equalCharacteristicLubinTateAmbientBracket F
      (equalCharacteristicCompletedLevelResidueHom F n) t (n + 1)
      (equalCharacteristicLubinTateUnitParameterSeries F n a) x ∈ S
  rw [equalCharacteristicLubinTateAmbientBracket_apply]
  exact S.sum_mem fun i _ ↦
    S.mul_mem (hcoeff _) (hiterate i)

/-- All roots of the completed primitive polynomial lie in the field
generated by the chosen primitive point. -/
theorem equalCharacteristicCompletedPrimitiveRootSet_subset_adjoin
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    ((equalCharacteristicCompletedPrimitivePolynomial F n).rootSet
        (equalCharacteristicCompletedLevelField F n) :
      Set (equalCharacteristicCompletedLevelField F n)) ⊆
      Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ({equalCharacteristicCompletedPrimitiveRoot F n} :
          Set (equalCharacteristicCompletedLevelField F n)) := by
  intro y hy
  let yroot :
      (equalCharacteristicCompletedPrimitivePolynomial F n).rootSet
        (equalCharacteristicCompletedLevelField F n) := ⟨y, hy⟩
  obtain ⟨a, ha⟩ :=
    (equalCharacteristicCompletedUnitParameterRootSet_bijective F n).surjective
      yroot
  have hay : equalCharacteristicCompletedUnitParameterRoot F n a = y :=
    congrArg Subtype.val ha
  rw [← hay]
  exact equalCharacteristicCompletedUnitParameterRoot_mem_adjoin F n a

/-- The chosen completed primitive point generates the completed splitting
field. -/
theorem equalCharacteristicCompletedPrimitiveRoot_adjoin_eq_top
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ({equalCharacteristicCompletedPrimitiveRoot F n} :
          Set (equalCharacteristicCompletedLevelField F n)) = ⊤ := by
  have hall :
      Algebra.adjoin
          (equalCharacteristicCompletedUnramifiedField F.residueField)
          ((equalCharacteristicCompletedPrimitivePolynomial F n).rootSet
            (equalCharacteristicCompletedLevelField F n) :
            Set (equalCharacteristicCompletedLevelField F n)) ≤
        Algebra.adjoin
          (equalCharacteristicCompletedUnramifiedField F.residueField)
          ({equalCharacteristicCompletedPrimitiveRoot F n} :
            Set (equalCharacteristicCompletedLevelField F n)) :=
    Algebra.adjoin_le
      (equalCharacteristicCompletedPrimitiveRootSet_subset_adjoin F n)
  rw [equalCharacteristicCompletedPrimitivePolynomial_adjoin_rootSet] at hall
  exact top_unique hall

/-- Every unit bracket of a primitive point is again a primitive generator
of the completed level field. -/
theorem equalCharacteristicCompletedUnitRoot_adjoin_eq_top
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ({equalCharacteristicCompletedUnitRoot F n a} :
          Set (equalCharacteristicCompletedLevelField F n)) = ⊤ := by
  let x := equalCharacteristicCompletedPrimitiveRoot F n
  let y := equalCharacteristicCompletedUnitRoot F n a
  let ι := equalCharacteristicCompletedLevelResidueHom F n
  let t := equalCharacteristicCompletedLevelUniformizer F n
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
      (equalCharacteristicCompletedPrimitiveRoot_torsion F n)]
    have hmul :
        ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧) *
            (↑a : F.residueField⟦X⟧) = 1 := by
      exact Units.inv_mul a
    rw [hmul]
    have hC := congrArg
      (fun f : AddMonoid.End (equalCharacteristicCompletedLevelField F n) ↦
        f x)
      (equalCharacteristicLubinTateAmbientBracket_C F ι t n
        (1 : F.residueField))
    change equalCharacteristicLubinTateAmbientBracket F ι t (n + 1)
        (PowerSeries.C 1) x =
      equalCharacteristicLubinTateAmbientCoefficientEnd F ι 1 x at hC
    simpa using hC
  have hxmem :
      x ∈ Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ({y} : Set (equalCharacteristicCompletedLevelField F n)) := by
    rw [← hrecover]
    exact equalCharacteristicCompletedAmbientBracket_mem_adjoin F n (n + 1)
      ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧) y
  have hle :
      Algebra.adjoin
          (equalCharacteristicCompletedUnramifiedField F.residueField)
          ({x} : Set (equalCharacteristicCompletedLevelField F n)) ≤
        Algebra.adjoin
          (equalCharacteristicCompletedUnramifiedField F.residueField)
          ({y} : Set (equalCharacteristicCompletedLevelField F n)) := by
    apply Algebra.adjoin_le
    intro z hz
    simpa only [Set.mem_singleton_iff] using hz ▸ hxmem
  rw [show Algebra.adjoin
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      ({x} : Set (equalCharacteristicCompletedLevelField F n)) = ⊤ by
        simpa [x] using equalCharacteristicCompletedPrimitiveRoot_adjoin_eq_top F n]
      at hle
  exact top_unique hle

/-- The chosen completed primitive point is integral over the completed
unramified base. -/
theorem equalCharacteristicCompletedPrimitiveRoot_isIntegral
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsIntegral
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedPrimitiveRoot F n) := by
  refine ⟨equalCharacteristicCompletedPrimitivePolynomial F n,
    equalCharacteristicCompletedPrimitivePolynomial_monic F n, ?_⟩
  rw [← Polynomial.eval_map]
  exact equalCharacteristicCompletedPrimitiveRoot_isRoot F n

/-- The completed primitive polynomial is the minimal polynomial of the
chosen primitive point. -/
theorem equalCharacteristicCompletedPrimitiveRoot_minpoly
    (F : LocalField.{u, v} K) (n : ℕ) :
    minpoly (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedPrimitiveRoot F n) =
      equalCharacteristicCompletedPrimitivePolynomial F n := by
  have hroot :
      Polynomial.aeval (equalCharacteristicCompletedPrimitiveRoot F n)
          (equalCharacteristicCompletedPrimitivePolynomial F n) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact equalCharacteristicCompletedPrimitiveRoot_isRoot F n
  have hmin := minpoly.eq_of_irreducible
    (equalCharacteristicCompletedPrimitivePolynomial_irreducible F n) hroot
  rw [(equalCharacteristicCompletedPrimitivePolynomial_monic F n).leadingCoeff,
    inv_one, Polynomial.C_1, mul_one] at hmin
  exact hmin.symm

/-- The power basis generated by the completed primitive division point. -/
noncomputable def equalCharacteristicCompletedPrimitivePowerBasis
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    PowerBasis
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  PowerBasis.ofAdjoinEqTop
    (equalCharacteristicCompletedPrimitiveRoot_isIntegral F n)
    (equalCharacteristicCompletedPrimitiveRoot_adjoin_eq_top F n)

/-- States the theorem `equalCharacteristicCompletedPrimitivePowerBasis_gen`. -/
@[simp]
theorem equalCharacteristicCompletedPrimitivePowerBasis_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    (equalCharacteristicCompletedPrimitivePowerBasis F n).gen =
      equalCharacteristicCompletedPrimitiveRoot F n :=
  PowerBasis.ofAdjoinEqTop_gen _ _

end EqualCharacteristic
end LubinTate
