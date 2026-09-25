/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CompletedUnramifiedField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveIrreducible
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveTorsion
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.SplittingField.Construction
/-!
# The completed theta-intertwining theorem: a completed Lubin--Tate level field

Let `k` be the residue field and put `K∞ = (AlgebraicClosure k)((T))`.
This file base-changes the primitive Lubin--Tate polynomial to `K∞`, takes
its genuine splitting field, and equips that finite extension with the
spectral norm.  A chosen primitive root is proved to lie in the maximal ideal
of the resulting complete valued field, hence is an actual analytic
evaluation point for the theta series of the completed theta-intertwining theorem.
-/

@[expose] public section

noncomputable
section

open Filter
open scoped LaurentSeries NNReal Polynomial PowerSeries Topology WithZero


universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The coefficientwise algebra structure
`k((T)) → (AlgebraicClosure k)((T))`. -/
noncomputable local instance equalCharacteristicCompletedLevelBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

/-- The completed unramified base has the residue characteristic. -/
local instance equalCharacteristicCompletedLevelBaseCharP
    (F : LocalField.{u, v} K)
    :
    CharP (equalCharacteristicCompletedUnramifiedField F.residueField)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap F.residueField
      (equalCharacteristicCompletedUnramifiedField F.residueField)).injective
    F.residueCharacteristic

/-- The Laurent valuation on the completed maximal-unramified base is
nontrivial, witnessed by `T`. -/
theorem equalCharacteristicCompletedBaseValuationIsNontrivial
    (k : Type v) [Field k] :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰).IsNontrivial := by
  let L := equalCharacteristicCompletedUnramifiedField k
  let x : L := equalCharacteristicCompletedUnramifiedFieldSingle k 1 1
  have hxv : (Valued.v : Valuation L ℤᵐ⁰) x =
      WithZero.exp (-1 : ℤ) := by
    change (Valued.v : Valuation (AlgebraicClosure k)⸨X⸩ ℤᵐ⁰)
      (HahnSeries.single 1 1) = WithZero.exp (-1 : ℤ)
    simpa using LaurentSeries.valuation_X_pow (AlgebraicClosure k) 1
  apply (Valuation.isNontrivial_iff_exists_lt_one
    (Valued.v : Valuation L ℤᵐ⁰)).2
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have hzero : (Valued.v : Valuation L ℤᵐ⁰) x = 0 := by
      rw [hx, map_zero]
    rw [hxv] at hzero
    exact WithZero.exp_ne_zero hzero
  · rw [hxv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega

noncomputable local instance equalCharacteristicCompletedBaseValuationIsNontrivialInstance
    (k : Type v) [Field k] :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰).IsNontrivial :=
  equalCharacteristicCompletedBaseValuationIsNontrivial k

/-- The rank-one structure on the discrete Laurent valuation. -/
@[implicit_reducible]
noncomputable def equalCharacteristicCompletedBaseValuationRankOne
    (k : Type v) [Field k] :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰).RankOne :=
  WithZeroValuation.rankOneOfUnitsIsCyclic
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰)

/-- The Laurent-series valuation on the completed unramified base has rank one. -/
noncomputable local instance equalCharacteristicCompletedBaseValuationRankOneInstance
    (k : Type v) [Field k] :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰).RankOne :=
  equalCharacteristicCompletedBaseValuationRankOne k

/-- The norm on the completed-unramified Laurent field induced by its
rank-one valuation. -/
@[reducible] noncomputable def equalCharacteristicCompletedBaseNormedField
    (k : Type v) [Field k] :
    NontriviallyNormedField
      (equalCharacteristicCompletedUnramifiedField k) :=
  Valued.toNontriviallyNormedField
    (L := equalCharacteristicCompletedUnramifiedField k) (Γ₀ := ℤᵐ⁰)

/-- The completed unramified base carries the nontrivial norm associated with its Laurent-series
valuation. -/
noncomputable local instance equalCharacteristicCompletedBaseNormedFieldInstance
    (k : Type v) [Field k] :
    NontriviallyNormedField
      (equalCharacteristicCompletedUnramifiedField k) :=
  equalCharacteristicCompletedBaseNormedField k

/-- The primitive level-`n+1` polynomial after coefficientwise base change
to `(AlgebraicClosure k)((T))`. -/
noncomputable def equalCharacteristicCompletedPrimitivePolynomial
    (F : LocalField.{u, v} K) (n : ℕ) :
    Polynomial (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  (equalCharacteristicLubinTatePrimitivePolynomial F n).map
    (algebraMap F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField))

/-- The completed primitive polynomial is monic. -/
theorem equalCharacteristicCompletedPrimitivePolynomial_monic
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedPrimitivePolynomial F n).Monic :=
  (equalCharacteristicLubinTatePrimitivePolynomial_monic F n).map _

/-- The completed primitive polynomial has degree `(q - 1) * q ^ n`. -/
theorem equalCharacteristicCompletedPrimitivePolynomial_natDegree
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedPrimitivePolynomial F n).natDegree =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  rw [equalCharacteristicCompletedPrimitivePolynomial,
    (equalCharacteristicLubinTatePrimitivePolynomial_monic F n).natDegree_map,
    equalCharacteristicLubinTatePrimitivePolynomial_natDegree]

/-- The actual finite completed level field used to evaluate theta. -/
def equalCharacteristicCompletedLevelField
    (F : LocalField.{u, v} K) (n : ℕ) :=
  (equalCharacteristicCompletedPrimitivePolynomial F n).SplittingField

/-- The splitting field of the completed primitive polynomial is a field. -/
instance equalCharacteristicCompletedLevelFieldField
    (F : LocalField.{u, v} K) (n : ℕ) :
    Field (equalCharacteristicCompletedLevelField F n) := by
  change Field (equalCharacteristicCompletedPrimitivePolynomial F n).SplittingField
  infer_instance

/-- The completed level field is an algebra over the completed unramified field. -/
noncomputable instance equalCharacteristicCompletedLevelFieldAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) := by
  change Algebra (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedPrimitivePolynomial F n).SplittingField
  infer_instance

/-- The completed Lubin–Tate level is a Laurent-series algebra by composition through the
completed unramified base. -/
noncomputable local instance equalCharacteristicCompletedLevelLaurentAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  ((algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)).comp
    (algebraMap F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField))).toAlgebra

noncomputable local instance equalCharacteristicCompletedLevelScalarTower
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The completed Lubin–Tate level has the residue characteristic. -/
local instance equalCharacteristicCompletedLevelCharP
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) :
    CharP (equalCharacteristicCompletedLevelField F n)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)).injective
    F.residueCharacteristic

section

/-- The completed Lubin–Tate level is a module over its completed unramified base via the chosen
algebra structure. -/
local instance equalCharacteristicCompletedLevelFieldModule
    (F : LocalField.{u, v} K) (n : ℕ) :
    @Module (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)
      (inferInstance : DivisionRing
        (equalCharacteristicCompletedUnramifiedField F.residueField)).toRing.toSemiring
      (inferInstance : AddCommGroup
        (equalCharacteristicCompletedLevelField F n)).toAddCommMonoid :=
  @Algebra.toModule
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedLevelField F n) _ _
    (equalCharacteristicCompletedLevelFieldAlgebra F n)

/-- The completed level field is finite-dimensional over its completed base. -/
instance equalCharacteristicCompletedLevelField_finiteDimensionalInstance
    (F : LocalField.{u, v} K) (n : ℕ) :
    FiniteDimensional
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) := by
  change FiniteDimensional
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedPrimitivePolynomial F n).SplittingField
  infer_instance

/-- The completed level field is algebraic over its completed base. -/
instance equalCharacteristicCompletedLevelField_isAlgebraic
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra.IsAlgebraic
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  @Algebra.IsAlgebraic.of_finite
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedLevelField F n) _ _ _
    (equalCharacteristicCompletedLevelFieldAlgebra F n)
    (equalCharacteristicCompletedLevelField_finiteDimensionalInstance F n)

/-- Comparison with the library splitting-field model. -/
noncomputable def equalCharacteristicCompletedLevelFieldEquivSplittingField
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicCompletedLevelField F n ≃ₐ[equalCharacteristicCompletedUnramifiedField
      F.residueField]
      (equalCharacteristicCompletedPrimitivePolynomial F n).SplittingField :=
  AlgEquiv.refl

/-- Construct a named completed-level element from the splitting-field
model. -/
noncomputable def equalCharacteristicCompletedLevelFieldOfSplittingField
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedPrimitivePolynomial F n).SplittingField →ₐ[
      equalCharacteristicCompletedUnramifiedField F.residueField]
      equalCharacteristicCompletedLevelField F n :=
  (equalCharacteristicCompletedLevelFieldEquivSplittingField F n).symm.toAlgHom

/-- The defining primitive polynomial splits over the named completed level
field. -/
theorem equalCharacteristicCompletedPrimitivePolynomial_splits
    (F : LocalField.{u, v} K) (n : ℕ) :
    ((equalCharacteristicCompletedPrimitivePolynomial F n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n))).Splits := by
  exact Polynomial.SplittingField.splits
    (equalCharacteristicCompletedPrimitivePolynomial F n)

/-- The roots of the defining polynomial generate the named completed level
field. -/
theorem equalCharacteristicCompletedPrimitivePolynomial_adjoin_rootSet
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ((equalCharacteristicCompletedPrimitivePolynomial F n).rootSet
          (equalCharacteristicCompletedLevelField F n) :
          Set (equalCharacteristicCompletedLevelField F n)) = ⊤ := by
  exact Polynomial.SplittingField.adjoin_rootSet
    (equalCharacteristicCompletedPrimitivePolynomial F n)

/-- The completed level field is finite-dimensional over the completed
maximal-unramified Laurent field. -/
theorem equalCharacteristicCompletedLevelField_finiteDimensional
    (F : LocalField.{u, v} K) (n : ℕ) :
    FiniteDimensional
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) := by
  infer_instance

private theorem equalCharacteristicCompletedPrimitivePolynomial_map_degree_ne_zero
    (F : LocalField.{u, v} K) (n : ℕ) :
    ((equalCharacteristicCompletedPrimitivePolynomial F n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n))).degree ≠ 0 := by
  have hmonic := (equalCharacteristicCompletedPrimitivePolynomial_monic F n).map
    (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n))
  rw [Polynomial.degree_eq_natDegree hmonic.ne_zero,
    (equalCharacteristicCompletedPrimitivePolynomial_monic F n).natDegree_map,
    equalCharacteristicCompletedPrimitivePolynomial_natDegree]
  exact_mod_cast (Nat.mul_pos
    (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
    (Nat.pow_pos Nat.card_pos)).ne'

/-- A chosen primitive root in the completed level field. -/
noncomputable def equalCharacteristicCompletedPrimitiveRoot
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicCompletedLevelField F n :=
  equalCharacteristicCompletedLevelFieldOfSplittingField F n
    (Polynomial.rootOfSplits
      (Polynomial.SplittingField.splits
        (equalCharacteristicCompletedPrimitivePolynomial F n))
      (by exact equalCharacteristicCompletedPrimitivePolynomial_map_degree_ne_zero F n))

/-- The chosen element is a root of the base-changed primitive polynomial.
-/
theorem equalCharacteristicCompletedPrimitiveRoot_isRoot
    (F : LocalField.{u, v} K) (n : ℕ) :
    ((equalCharacteristicCompletedPrimitivePolynomial F n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n))).IsRoot
          (equalCharacteristicCompletedPrimitiveRoot F n) := by
  exact Polynomial.eval_rootOfSplits
    (Polynomial.SplittingField.splits
      (equalCharacteristicCompletedPrimitivePolynomial F n))
    (equalCharacteristicCompletedPrimitivePolynomial_map_degree_ne_zero F n)

/-- The spectral norm on the finite completed level field. -/
@[reducible] noncomputable def equalCharacteristicCompletedLevelNormedField
    (F : LocalField.{u, v} K) (n : ℕ) :
    NontriviallyNormedField (equalCharacteristicCompletedLevelField F n) :=
  spectralNorm.nontriviallyNormedField
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedLevelField F n)

/-- The completed Lubin–Tate level carries the spectral norm extending the norm on its completed
base. -/
noncomputable local instance equalCharacteristicCompletedLevelNormedFieldInstance
    (F : LocalField.{u, v} K) (n : ℕ) :
    NontriviallyNormedField (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelNormedField F n

/-- The spectral norm is nonarchimedean. -/
theorem equalCharacteristicCompletedLevelIsUltrametric
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUltrametricDist (equalCharacteristicCompletedLevelField F n) :=
  ⟨fun x y z ↦ by
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
    rw [← sub_add_sub_cancel x y z]
    exact isNonarchimedean_spectralNorm
      (K := equalCharacteristicCompletedUnramifiedField F.residueField)
      (L := equalCharacteristicCompletedLevelField F n)
      (x - y) (y - z)⟩

noncomputable local instance equalCharacteristicCompletedLevelIsUltrametricInstance
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsUltrametricDist (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelIsUltrametric F n

/-- Finite dimensionality makes the spectral level field complete. -/
theorem equalCharacteristicCompletedLevelCompleteSpace
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace (equalCharacteristicCompletedLevelField F n) :=
  spectralNorm.completeSpace
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedLevelField F n)

noncomputable local instance equalCharacteristicCompletedLevelCompleteSpaceInstance
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteSpace (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelCompleteSpace F n

/-- The valuation attached to the spectral norm. -/
@[reducible] noncomputable def equalCharacteristicCompletedLevelValued
    (F : LocalField.{u, v} K) (n : ℕ) :
    Valued (equalCharacteristicCompletedLevelField F n) ℝ≥0 :=
  NormedField.toValued (K := equalCharacteristicCompletedLevelField F n)

/-- The completed Lubin–Tate level carries the real-valued valuation associated with its spectral
norm. -/
noncomputable local instance equalCharacteristicCompletedLevelValuedInstance
    (F : LocalField.{u, v} K) (n : ℕ) :
    Valued (equalCharacteristicCompletedLevelField F n) ℝ≥0 :=
  equalCharacteristicCompletedLevelValued F n

/-- The Laurent parameter in the completed maximal-unramified base. -/
noncomputable def equalCharacteristicCompletedBaseUniformizer
    (F : LocalField.{u, v} K) :
    equalCharacteristicCompletedUnramifiedField F.residueField :=
  equalCharacteristicCompletedUnramifiedFieldSingle F.residueField 1 1

/-- Coefficientwise base change fixes the Laurent parameter. -/
theorem equalCharacteristicCompletedBase_algebraMap_uniformizer
    (F : LocalField.{u, v} K) :
    algebraMap F.residueField⸨X⸩
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicLaurentUniformizer F) =
      equalCharacteristicCompletedBaseUniformizer F := by
  apply
    (equalCharacteristicCompletedUnramifiedFieldEquivLaurentSeries
      F.residueField).injective
  change
    laurentSeriesCoefficientMap
        (algebraMap F.residueField (AlgebraicClosure F.residueField))
        (equalCharacteristicLaurentUniformizer F) =
      HahnSeries.single 1 1
  ext m
  cases m with
  | ofNat i =>
      by_cases hi : i = 1
      · subst i
        simp [equalCharacteristicLaurentUniformizer,
          laurentSeriesCoefficientMap]
      · simp [equalCharacteristicLaurentUniformizer,
          laurentSeriesCoefficientMap, HahnSeries.coeff_single_of_ne, hi]
  | negSucc i =>
    simp [equalCharacteristicLaurentUniformizer,
      laurentSeriesCoefficientMap]

/-- The completed-base Laurent parameter has norm strictly less than one.
-/
theorem equalCharacteristicCompletedBaseUniformizer_norm_lt_one
    (F : LocalField.{u, v} K) :
    ‖equalCharacteristicCompletedBaseUniformizer F‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff,
    equalCharacteristicCompletedBaseUniformizer]
  have hxv :
      (Valued.v : Valuation
        (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰)
          (equalCharacteristicCompletedUnramifiedFieldSingle
            F.residueField 1 1) = WithZero.exp (-1 : ℤ) := by
    change (Valued.v :
      Valuation (AlgebraicClosure F.residueField)⸨X⸩ ℤᵐ⁰)
        (HahnSeries.single 1 1) = WithZero.exp (-1 : ℤ)
    simpa using
      LaurentSeries.valuation_X_pow (AlgebraicClosure F.residueField) 1
  rw [hxv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

/-- The image of `T` in the completed level field. -/
noncomputable def equalCharacteristicCompletedLevelUniformizer
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicCompletedLevelField F n :=
  algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedLevelField F n)
    (equalCharacteristicCompletedBaseUniformizer F)

/-- The spectral norm extends the norm of the completed-unramified base. -/
theorem equalCharacteristicCompletedLevelUniformizer_norm
    (F : LocalField.{u, v} K) (n : ℕ) :
    ‖equalCharacteristicCompletedLevelUniformizer F n‖ =
      ‖equalCharacteristicCompletedBaseUniformizer F‖ := by
  change spectralNorm
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)
        (equalCharacteristicCompletedBaseUniformizer F)) = _
  exact spectralNorm_extends _

/-- The completed level uniformizer has norm strictly below one. -/
theorem equalCharacteristicCompletedLevelUniformizer_norm_lt_one
    (F : LocalField.{u, v} K) (n : ℕ) :
    ‖equalCharacteristicCompletedLevelUniformizer F n‖ < 1 := by
  rw [equalCharacteristicCompletedLevelUniformizer_norm]
  exact equalCharacteristicCompletedBaseUniformizer_norm_lt_one F

/-- The chosen root satisfies the genuine primitive Lubin--Tate equation
over the completed-unramified base. -/
theorem equalCharacteristicCompletedPrimitiveRoot_equation
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicCompletedLevelUniformizer F n) n
        (equalCharacteristicCompletedPrimitiveRoot F n) ^
          (Nat.card F.residueField - 1) +
      equalCharacteristicCompletedLevelUniformizer F n = 0 := by
  have hroot := equalCharacteristicCompletedPrimitiveRoot_isRoot F n
  change Polynomial.eval
      (equalCharacteristicCompletedPrimitiveRoot F n)
      (((equalCharacteristicLubinTatePrimitivePolynomial F n).map
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicCompletedUnramifiedField F.residueField))).map
        (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
          (equalCharacteristicCompletedLevelField F n))) = 0 at hroot
  rw [Polynomial.map_map, Polynomial.eval_map,
    equalCharacteristicLubinTatePrimitivePolynomial_eval₂] at hroot
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
  rwa [ht] at hroot

/-- The original separable-closure level field embeds into the completed
level field, sending its primitive generator to the chosen completed root.
-/
noncomputable def equalCharacteristicLubinTateLevelFieldToCompleted
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateLevelField F n →ₐ[F.residueField⸨X⸩]
      equalCharacteristicCompletedLevelField F n := by
  have hrootAeval : Polynomial.aeval
      (equalCharacteristicCompletedPrimitiveRoot F n)
      (minpoly F.residueField⸨X⸩
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)) = 0 := by
    rw [← equalCharacteristicLubinTatePrimitivePolynomial_eq_minpoly]
    rw [Polynomial.aeval_def,
      IsScalarTower.algebraMap_eq F.residueField⸨X⸩
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicCompletedLevelField F n)]
    have hc := equalCharacteristicCompletedPrimitiveRoot_isRoot F n
    change Polynomial.eval
      (equalCharacteristicCompletedPrimitiveRoot F n)
      (((equalCharacteristicLubinTatePrimitivePolynomial F n).map
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicCompletedUnramifiedField F.residueField))).map
        (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
          (equalCharacteristicCompletedLevelField F n))) = 0 at hc
    rwa [Polynomial.map_map, Polynomial.eval_map] at hc
  let baseHom :
      F.residueField⸨X⸩ →ₐ[F.residueField⸨X⸩]
        equalCharacteristicCompletedLevelField F n :=
    Algebra.ofId F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n)
  have hroot :
      Polynomial.eval₂ baseHom
          (equalCharacteristicCompletedPrimitiveRoot F n)
          (minpoly F.residueField⸨X⸩
            (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)) = 0 := by
    simpa only [baseHom, Polynomial.aeval_def, Algebra.toRingHom_ofId] using hrootAeval
  let lift :
      AdjoinRoot (minpoly F.residueField⸨X⸩
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)) →ₐ[F.residueField⸨X⸩]
          equalCharacteristicCompletedLevelField F n :=
    AdjoinRoot.liftAlgHom _ baseHom
      (equalCharacteristicCompletedPrimitiveRoot F n) hroot
  exact lift.comp
    (IntermediateField.adjoinRootEquivAdjoin F.residueField⸨X⸩
      (chosenEqualCharacteristicLubinTatePrimitiveRoot_isIntegral F n)).symm.toAlgHom

/-- The canonical finite-level embedding sends its simple-extension generator
to the chosen primitive root in the completed level field. -/
@[simp]
theorem equalCharacteristicLubinTateLevelFieldToCompleted_generator
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateLevelFieldToCompleted F n
        (IntermediateField.AdjoinSimple.gen F.residueField⸨X⸩
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)) =
      equalCharacteristicCompletedPrimitiveRoot F n := by
  rw [equalCharacteristicLubinTateLevelFieldToCompleted, AlgHom.comp_apply]
  have hgen :
      (IntermediateField.adjoinRootEquivAdjoin F.residueField⸨X⸩
          (chosenEqualCharacteristicLubinTatePrimitiveRoot_isIntegral F n)).symm.toAlgHom
          (IntermediateField.AdjoinSimple.gen F.residueField⸨X⸩
            (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)) =
        AdjoinRoot.root
          (minpoly F.residueField⸨X⸩
            (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)) :=
    IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen
      F.residueField⸨X⸩
      (chosenEqualCharacteristicLubinTatePrimitiveRoot_isIntegral F n)
  rw [hgen, AdjoinRoot.liftAlgHom_root]

/-- If `x` has norm at least one, then `e(x) = x^q + Tx` has the
same norm as its leading term. -/
private theorem equalCharacteristicCompletedAmbientPiEnd_norm_of_one_le
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (x : equalCharacteristicCompletedLevelField F n)
    (hx : 1 ≤ ‖x‖) :
    ‖equalCharacteristicLubinTateAmbientPiEnd F
        (equalCharacteristicCompletedLevelUniformizer F n) x‖ =
      ‖x‖ ^ Nat.card F.residueField := by
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hqpos : 0 < Nat.card F.residueField := Nat.card_pos
  have hself : ‖x‖ ≤ ‖x‖ ^ Nat.card F.residueField := by
    calc
      ‖x‖ = 1 * ‖x‖ := (one_mul _).symm
      _ ≤ ‖x‖ ^ (Nat.card F.residueField - 1) * ‖x‖ :=
        mul_le_mul_of_nonneg_right
          (by
            exact one_le_pow₀ hx)
          (norm_nonneg x)
      _ = ‖x‖ ^ Nat.card F.residueField := by
        rw [← pow_succ,
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hqpos.ne')]
  have hterms :
      ‖equalCharacteristicCompletedLevelUniformizer F n * x‖ <
        ‖x ^ Nat.card F.residueField‖ := by
    rw [norm_mul, norm_pow]
    calc
      ‖equalCharacteristicCompletedLevelUniformizer F n‖ * ‖x‖ <
          1 * ‖x‖ :=
        mul_lt_mul_of_pos_right
          (equalCharacteristicCompletedLevelUniformizer_norm_lt_one F n)
          hxpos
      _ = ‖x‖ := one_mul _
      _ ≤ ‖x‖ ^ Nat.card F.residueField := hself
  rw [equalCharacteristicLubinTateAmbientPiEnd_apply,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hterms),
    max_eq_left hterms.le, norm_pow]

/-- Above the unit sphere, every Lubin--Tate iterate has the norm of its
leading `q`-power term. -/
private theorem equalCharacteristicCompletedAmbientPiIterate_norm_of_one_le
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (level i : ℕ) (x : equalCharacteristicCompletedLevelField F level)
    (hx : 1 ≤ ‖x‖) :
    ‖equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicCompletedLevelUniformizer F level) i x‖ =
      ‖x‖ ^ (Nat.card F.residueField ^ i) := by
  induction i generalizing x with
  | zero =>
      rw [equalCharacteristicLubinTateAmbientPiIterate]
      rw [pow_zero]
      rw [pow_zero]
      rw [pow_one]
      rfl
  | succ i ih =>
      have hend := equalCharacteristicCompletedAmbientPiEnd_norm_of_one_le
        F level x hx
      have hnext : 1 ≤
          ‖equalCharacteristicLubinTateAmbientPiEnd F
            (equalCharacteristicCompletedLevelUniformizer F level) x‖ := by
        rw [hend]
        exact one_le_pow₀ hx
      rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
        ih _ hnext, hend, ← pow_mul]
      congr 1
      rw [pow_succ, Nat.mul_comm]

/-- The primitive root lies strictly inside the unit ball.  This follows
directly from its Lubin--Tate equation and the spectral norm. -/
theorem equalCharacteristicCompletedPrimitiveRoot_norm_lt_one
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    ‖equalCharacteristicCompletedPrimitiveRoot F n‖ < 1 := by
  by_contra hnot
  have hrootge : 1 ≤ ‖equalCharacteristicCompletedPrimitiveRoot F n‖ :=
    le_of_not_gt hnot
  let z : equalCharacteristicCompletedLevelField F n :=
    equalCharacteristicLubinTateAmbientPiIterate F
      (equalCharacteristicCompletedLevelUniformizer F n) n
      (equalCharacteristicCompletedPrimitiveRoot F n)
  have hznorm : ‖z‖ =
      ‖equalCharacteristicCompletedPrimitiveRoot F n‖ ^
        (Nat.card F.residueField ^ n) :=
    equalCharacteristicCompletedAmbientPiIterate_norm_of_one_le
      F n n (equalCharacteristicCompletedPrimitiveRoot F n) hrootge
  have hzge : 1 ≤ ‖z‖ := by
    rw [hznorm]
    exact one_le_pow₀ hrootge
  have hzpowge : 1 ≤ ‖z ^ (Nat.card F.residueField - 1)‖ := by
    rw [norm_pow]
    exact one_le_pow₀ hzge
  have heq := equalCharacteristicCompletedPrimitiveRoot_equation F n
  change z ^ (Nat.card F.residueField - 1) +
      equalCharacteristicCompletedLevelUniformizer F n = 0 at heq
  have hnormeq : ‖z ^ (Nat.card F.residueField - 1)‖ =
      ‖equalCharacteristicCompletedLevelUniformizer F n‖ := by
    rw [eq_neg_of_add_eq_zero_left heq, norm_neg]
  rw [hnormeq] at hzpowge
  exact (not_le_of_gt
    (equalCharacteristicCompletedLevelUniformizer_norm_lt_one F n)) hzpowge

/-- The primitive root lifted to the spectral valuation ring. -/
noncomputable def equalCharacteristicCompletedPrimitiveRootInteger
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Valued.integer (equalCharacteristicCompletedLevelField F n) :=
  ⟨equalCharacteristicCompletedPrimitiveRoot F n, by
    change ‖equalCharacteristicCompletedPrimitiveRoot F n‖₊ ≤ 1
    exact_mod_cast
      (equalCharacteristicCompletedPrimitiveRoot_norm_lt_one F n).le⟩

/-- Coercing the integral primitive root returns the underlying completed root. -/
@[simp]
theorem equalCharacteristicCompletedPrimitiveRootInteger_coe
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    ((equalCharacteristicCompletedPrimitiveRootInteger F n :
      Valued.integer (equalCharacteristicCompletedLevelField F n)) :
        equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicCompletedPrimitiveRoot F n :=
  rfl

/-- The integral primitive root belongs to the maximal ideal. -/
theorem equalCharacteristicCompletedPrimitiveRootInteger_mem_maximalIdeal
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicCompletedPrimitiveRootInteger F n ∈
      Valued.maximalIdeal (equalCharacteristicCompletedLevelField F n) := by
  change equalCharacteristicCompletedPrimitiveRootInteger F n ∈
    IsLocalRing.maximalIdeal
      (Valued.integer (equalCharacteristicCompletedLevelField F n))
  apply (Valuation.mem_maximalIdeal_iff
    (equalCharacteristicCompletedLevelField F n)
    (Valued.v : Valuation (equalCharacteristicCompletedLevelField F n) ℝ≥0)).2
  change ‖equalCharacteristicCompletedPrimitiveRoot F n‖₊ < 1
  exact_mod_cast equalCharacteristicCompletedPrimitiveRoot_norm_lt_one F n

/-- The primitive root is a genuine analytic evaluation point for outer
power series over the completed level integer ring. -/
theorem equalCharacteristicCompletedPrimitiveRootInteger_hasEval
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    PowerSeries.HasEval
      (equalCharacteristicCompletedPrimitiveRootInteger F n) := by
  change Tendsto
    (fun i : ℕ ↦ equalCharacteristicCompletedPrimitiveRootInteger F n ^ i)
    atTop (nhds 0)
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
  change ‖equalCharacteristicCompletedPrimitiveRoot F n‖ < 1
  exact equalCharacteristicCompletedPrimitiveRoot_norm_lt_one F n

end

end EqualCharacteristic
end LubinTate
