/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizer
/-!
# The completed theta-intertwining theorem: the completed changed-uniformizer level

For `u ∈ κ⟦T⟧ˣ`, the theta construction used in the completed theta-intertwining theorem
  intertwines the
target parameter `T` with the source parameter `u⁻¹T`.  This file therefore
base-changes the primitive polynomial for `u⁻¹T` to the completed maximal-
unramified field, forms its genuine splitting field, and constructs the
primitive analytic evaluation point there.

The repository's primitive polynomial indexed by `n` cuts out division level
`n + 1`; this shift is kept explicit throughout.
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

/-- The completed unramified base is an algebra over residue-field Laurent series through
coefficient extension. -/
noncomputable local instance equalCharacteristicChangedCompletedBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

private instance equalCharacteristicChangedCompletedBaseCharP
    (F : LocalField.{u, v} K)
    :
    CharP (equalCharacteristicCompletedUnramifiedField F.residueField)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap F.residueField
      (equalCharacteristicCompletedUnramifiedField F.residueField)).injective
    F.residueCharacteristic

noncomputable local instance equalCharacteristicChangedCompletedBaseValuationIsNontrivial
    (k : Type v) [Field k] :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰).IsNontrivial :=
  equalCharacteristicCompletedBaseValuationIsNontrivial k

/-- The Laurent-series valuation on the changed completed base has rank one. -/
noncomputable local instance equalCharacteristicChangedCompletedBaseValuationRankOne
    (k : Type v) [Field k] :
    (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰).RankOne :=
  equalCharacteristicCompletedBaseValuationRankOne k

/-- The changed completed base carries the nontrivial norm associated with its Laurent-series
valuation. -/
noncomputable local instance equalCharacteristicChangedCompletedBaseNormedField
    (k : Type v) [Field k] :
    NontriviallyNormedField
      (equalCharacteristicCompletedUnramifiedField k) :=
  equalCharacteristicCompletedBaseNormedField k

/-- The source unit is `u⁻¹`; hence its parameter is `u⁻¹T`, in the
orientation of the theta intertwining relation. -/
noncomputable def equalCharacteristicThetaSourceUnit
    {k : Type*} [Field k] (u : k⟦X⟧ˣ) : k⟦X⟧ˣ :=
  u⁻¹

/-- The primitive polynomial for source parameter `u⁻¹T`, after base change
to `(AlgebraicClosure κ)((T))`. -/
noncomputable def equalCharacteristicChangedCompletedPrimitivePolynomial
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Polynomial (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  (equalCharacteristicChangedPrimitivePolynomial F
      (equalCharacteristicThetaSourceUnit u) n).map
    (algebraMap F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField))

/-- The changed primitive polynomial remains monic after completion. -/
theorem equalCharacteristicChangedCompletedPrimitivePolynomial_monic
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedPrimitivePolynomial F u n).Monic :=
  (equalCharacteristicChangedPrimitivePolynomial_monic F
    (equalCharacteristicThetaSourceUnit u) n).map _

/-- The completed changed primitive polynomial has degree `(q - 1) * q ^ n`. -/
theorem equalCharacteristicChangedCompletedPrimitivePolynomial_natDegree
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedPrimitivePolynomial F u n).natDegree =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  rw [equalCharacteristicChangedCompletedPrimitivePolynomial,
    (equalCharacteristicChangedPrimitivePolynomial_monic F
      (equalCharacteristicThetaSourceUnit u) n).natDegree_map,
    equalCharacteristicChangedPrimitivePolynomial_natDegree]

/-- The genuine splitting field of the source primitive polynomial. -/
def equalCharacteristicChangedCompletedLevelField
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :=
  (equalCharacteristicChangedCompletedPrimitivePolynomial F u n).SplittingField

/-- The splitting field of the completed changed primitive polynomial is a field. -/
instance equalCharacteristicChangedCompletedLevelFieldField
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Field (equalCharacteristicChangedCompletedLevelField F u n) := by
  change Field
    (equalCharacteristicChangedCompletedPrimitivePolynomial F u n).SplittingField
  infer_instance

/-- The changed completed level field is an algebra over the completed unramified field. -/
noncomputable instance equalCharacteristicChangedCompletedLevelFieldAlgebra
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Algebra (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicChangedCompletedLevelField F u n) := by
  change Algebra (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicChangedCompletedPrimitivePolynomial F u n).SplittingField
  infer_instance

section

/-- The changed completed Lubin–Tate level is a module over its completed unramified base via the
chosen algebra structure. -/
local instance equalCharacteristicChangedCompletedLevelFieldModule
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    @Module (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicChangedCompletedLevelField F u n)
      (inferInstance : DivisionRing
        (equalCharacteristicCompletedUnramifiedField F.residueField)).toRing.toSemiring
      (inferInstance : AddCommGroup
        (equalCharacteristicChangedCompletedLevelField F u n)).toAddCommMonoid :=
  @Algebra.toModule
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicChangedCompletedLevelField F u n) _ _
    (equalCharacteristicChangedCompletedLevelFieldAlgebra F u n)

/-- The changed completed level field is finite-dimensional over its completed base. -/
instance equalCharacteristicChangedCompletedLevelField_finiteDimensionalInstance
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    FiniteDimensional
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicChangedCompletedLevelField F u n) := by
  change FiniteDimensional
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicChangedCompletedPrimitivePolynomial F u n).SplittingField
  infer_instance

local instance equalCharacteristicChangedCompletedLevelField_isAlgebraic
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Algebra.IsAlgebraic
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicChangedCompletedLevelField F u n) :=
  @Algebra.IsAlgebraic.of_finite
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicChangedCompletedLevelField F u n) _ _ _
    (equalCharacteristicChangedCompletedLevelFieldAlgebra F u n)
    (equalCharacteristicChangedCompletedLevelField_finiteDimensionalInstance F u n)

/-- The changed completed level field has the residue characteristic. -/
instance equalCharacteristicChangedCompletedLevelField_charP
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    CharP (equalCharacteristicChangedCompletedLevelField F u n)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicChangedCompletedLevelField F u n)).injective
    F.residueCharacteristic

/-- Comparison with the library splitting-field model. -/
noncomputable def
    equalCharacteristicChangedCompletedLevelFieldEquivSplittingField
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedCompletedLevelField F u n
      ≃ₐ[equalCharacteristicCompletedUnramifiedField F.residueField]
      (equalCharacteristicChangedCompletedPrimitivePolynomial F u n).SplittingField :=
  AlgEquiv.refl

/-- Construct a named changed-level element from the splitting-field
model. -/
noncomputable def
    equalCharacteristicChangedCompletedLevelFieldOfSplittingField
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicChangedCompletedPrimitivePolynomial F u n).SplittingField
      →ₐ[equalCharacteristicCompletedUnramifiedField F.residueField]
        equalCharacteristicChangedCompletedLevelField F u n :=
  (equalCharacteristicChangedCompletedLevelFieldEquivSplittingField
    F u n).symm.toAlgHom

/-- The changed primitive polynomial splits over the named completed level
field. -/
theorem equalCharacteristicChangedCompletedPrimitivePolynomial_splits
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    ((equalCharacteristicChangedCompletedPrimitivePolynomial F u n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicChangedCompletedLevelField F u n))).Splits := by
  exact Polynomial.SplittingField.splits
    (equalCharacteristicChangedCompletedPrimitivePolynomial F u n)

/-- The roots of the changed primitive polynomial generate the named
completed level field. -/
theorem
    equalCharacteristicChangedCompletedPrimitivePolynomial_adjoin_rootSet
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Algebra.adjoin
        (equalCharacteristicCompletedUnramifiedField F.residueField)
        ((equalCharacteristicChangedCompletedPrimitivePolynomial F u n).rootSet
          (equalCharacteristicChangedCompletedLevelField F u n) :
          Set (equalCharacteristicChangedCompletedLevelField F u n)) = ⊤ := by
  exact Polynomial.SplittingField.adjoin_rootSet
    (equalCharacteristicChangedCompletedPrimitivePolynomial F u n)

/-- Supplies finite-dimensionality of the changed completed level field explicitly. -/
theorem equalCharacteristicChangedCompletedLevelField_finiteDimensional
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    FiniteDimensional
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicChangedCompletedLevelField F u n) := by
  infer_instance

private theorem equalCharacteristicChangedCompletedPrimitivePolynomial_map_degree_ne_zero
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    ((equalCharacteristicChangedCompletedPrimitivePolynomial F u n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicChangedCompletedLevelField F u n))).degree ≠ 0 := by
  have hmonic :=
    (equalCharacteristicChangedCompletedPrimitivePolynomial_monic F u n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicChangedCompletedLevelField F u n))
  rw [Polynomial.degree_eq_natDegree hmonic.ne_zero,
    (equalCharacteristicChangedCompletedPrimitivePolynomial_monic F u n).natDegree_map,
    equalCharacteristicChangedCompletedPrimitivePolynomial_natDegree]
  exact_mod_cast (Nat.mul_pos
    (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
    (Nat.pow_pos Nat.card_pos)).ne'

/-- A chosen primitive division-level `n + 1` point for source parameter
`u⁻¹T`. -/
noncomputable def equalCharacteristicChangedCompletedPrimitiveRoot
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedCompletedLevelField F u n :=
  equalCharacteristicChangedCompletedLevelFieldOfSplittingField F u n
    (Polynomial.rootOfSplits
      (Polynomial.SplittingField.splits
        (equalCharacteristicChangedCompletedPrimitivePolynomial F u n))
      (equalCharacteristicChangedCompletedPrimitivePolynomial_map_degree_ne_zero F u n))

/-- The distinguished completed primitive element is a root of the changed polynomial. -/
theorem equalCharacteristicChangedCompletedPrimitiveRoot_isRoot
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    ((equalCharacteristicChangedCompletedPrimitivePolynomial F u n).map
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicChangedCompletedLevelField F u n))).IsRoot
          (equalCharacteristicChangedCompletedPrimitiveRoot F u n) := by
  exact Polynomial.eval_rootOfSplits
    (Polynomial.SplittingField.splits
      (equalCharacteristicChangedCompletedPrimitivePolynomial F u n))
    (equalCharacteristicChangedCompletedPrimitivePolynomial_map_degree_ne_zero F u n)

/-- The spectral norm on the changed completed level field. -/
@[reducible]
noncomputable def equalCharacteristicChangedCompletedLevelNormedField
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    NontriviallyNormedField
      (equalCharacteristicChangedCompletedLevelField F u n) :=
  spectralNorm.nontriviallyNormedField
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicChangedCompletedLevelField F u n)

/-- The changed completed Lubin–Tate level carries the spectral norm extending its completed
base. -/
noncomputable local instance equalCharacteristicChangedCompletedLevelNormedFieldInstance
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    NontriviallyNormedField
      (equalCharacteristicChangedCompletedLevelField F u n) :=
  equalCharacteristicChangedCompletedLevelNormedField F u n

/-- The spectral norm on the changed completed level field is ultrametric. -/
theorem equalCharacteristicChangedCompletedLevelIsUltrametric
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IsUltrametricDist (equalCharacteristicChangedCompletedLevelField F u n) :=
  ⟨fun x y z ↦ by
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
    rw [← sub_add_sub_cancel x y z]
    exact isNonarchimedean_spectralNorm
      (K := equalCharacteristicCompletedUnramifiedField F.residueField)
      (L := equalCharacteristicChangedCompletedLevelField F u n)
      (x - y) (y - z)⟩

noncomputable local instance equalCharacteristicChangedCompletedLevelIsUltrametricInstance
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IsUltrametricDist (equalCharacteristicChangedCompletedLevelField F u n) :=
  equalCharacteristicChangedCompletedLevelIsUltrametric F u n

/-- The changed completed level field is complete for its spectral norm. -/
theorem equalCharacteristicChangedCompletedLevelCompleteSpace
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    CompleteSpace (equalCharacteristicChangedCompletedLevelField F u n) :=
  spectralNorm.completeSpace
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicChangedCompletedLevelField F u n)

noncomputable local instance equalCharacteristicChangedCompletedLevelCompleteSpaceInstance
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    CompleteSpace (equalCharacteristicChangedCompletedLevelField F u n) :=
  equalCharacteristicChangedCompletedLevelCompleteSpace F u n

/-- Defines `equalCharacteristicChangedCompletedLevelValued`. -/
@[reducible]
noncomputable def equalCharacteristicChangedCompletedLevelValued
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Valued (equalCharacteristicChangedCompletedLevelField F u n) ℝ≥0 :=
  NormedField.toValued (K := equalCharacteristicChangedCompletedLevelField F u n)

/-- The spectral norm gives the changed completed Lubin–Tate level its real-valued valuation. -/
noncomputable local instance equalCharacteristicChangedCompletedLevelValuedInstance
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Valued (equalCharacteristicChangedCompletedLevelField F u n) ℝ≥0 :=
  equalCharacteristicChangedCompletedLevelValued F u n

/-- The source parameter `u⁻¹T` in the completed maximal-unramified base. -/
noncomputable def equalCharacteristicChangedCompletedBaseUniformizer
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) :
    equalCharacteristicCompletedUnramifiedField F.residueField :=
  algebraMap F.residueField⸨X⸩
    (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicChangedLaurentUniformizer F
      (equalCharacteristicThetaSourceUnit u))

/-- The changed base uniformizer remains nonzero after completion. -/
theorem equalCharacteristicChangedCompletedBaseUniformizer_ne_zero
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) :
    equalCharacteristicChangedCompletedBaseUniformizer F u ≠ 0 := by
  exact (map_ne_zero
    (algebraMap F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField))).2
    (equalCharacteristicChangedLaurentUniformizer_ne_zero F
      (equalCharacteristicThetaSourceUnit u))

private theorem equalCharacteristicChangedLaurentUniformizer_valuation_le_exp_neg_one
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) :
    (Valued.v : Valuation F.residueField⸨X⸩ ℤᵐ⁰)
        (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u)) ≤
      WithZero.exp (-1 : ℤ) := by
  change (Valued.v : Valuation F.residueField⸨X⸩ ℤᵐ⁰)
      ((equalCharacteristicChangedIntegralUniformizer F
        (equalCharacteristicThetaSourceUnit u) : F.residueField⟦X⟧) :
          F.residueField⸨X⸩) ≤ WithZero.exp (-1 : ℤ)
  apply (LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero
    F.residueField _).2
  intro m hm
  have hm0 : m = 0 := Nat.lt_one_iff.mp hm
  subst m
  simp [equalCharacteristicChangedIntegralUniformizer]

/-- The completed source parameter `u⁻¹T` is topologically nilpotent. -/
theorem equalCharacteristicChangedCompletedBaseUniformizer_norm_lt_one
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) :
    ‖equalCharacteristicChangedCompletedBaseUniformizer F u‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff]
  have hval :
      (Valued.v : Valuation
        (equalCharacteristicCompletedUnramifiedField F.residueField) ℤᵐ⁰)
          (equalCharacteristicChangedCompletedBaseUniformizer F u) ≤
        WithZero.exp (-1 : ℤ) := by
    apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero
      (AlgebraicClosure F.residueField)).2
    intro m hm
    change equalCharacteristicCompletedUnramifiedFieldCoeff F.residueField
      (equalCharacteristicChangedCompletedBaseUniformizer F u) m = 0
    rw [equalCharacteristicChangedCompletedBaseUniformizer,
      equalCharacteristicCompletedUnramifiedFieldCoeff_algebraMap_laurentSeries]
    have hcoeff :
        (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u)).coeff m = 0 :=
      (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero F.residueField).1
        (equalCharacteristicChangedLaurentUniformizer_valuation_le_exp_neg_one F u)
        m hm
    rw [hcoeff, map_zero]
  exact lt_of_le_of_lt hval (by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega)

/-- The image of the source parameter in its completed splitting field. -/
noncomputable def equalCharacteristicChangedCompletedLevelUniformizer
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedCompletedLevelField F u n :=
  algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicChangedCompletedLevelField F u n)
    (equalCharacteristicChangedCompletedBaseUniformizer F u)

/-- The image of the changed uniformizer in the level field is nonzero. -/
theorem equalCharacteristicChangedCompletedLevelUniformizer_ne_zero
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedCompletedLevelUniformizer F u n ≠ 0 := by
  exact (map_ne_zero
    (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicChangedCompletedLevelField F u n))).2
    (equalCharacteristicChangedCompletedBaseUniformizer_ne_zero F u)

/-- The changed spectral norm extends the completed-base norm. -/
theorem equalCharacteristicChangedCompletedLevelUniformizer_norm
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    ‖equalCharacteristicChangedCompletedLevelUniformizer F u n‖ =
      ‖equalCharacteristicChangedCompletedBaseUniformizer F u‖ := by
  change spectralNorm
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicChangedCompletedLevelField F u n)
      (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicChangedCompletedLevelField F u n)
        (equalCharacteristicChangedCompletedBaseUniformizer F u)) = _
  exact spectralNorm_extends _

/-- The changed level uniformizer has norm strictly below one. -/
theorem equalCharacteristicChangedCompletedLevelUniformizer_norm_lt_one
    (F : LocalField.{u, v} K) (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    ‖equalCharacteristicChangedCompletedLevelUniformizer F u n‖ < 1 := by
  rw [equalCharacteristicChangedCompletedLevelUniformizer_norm]
  exact equalCharacteristicChangedCompletedBaseUniformizer_norm_lt_one F u

private theorem equalCharacteristicChangedPiPolynomial_eval₂
    (F : LocalField.{u, v} K)
    (u : F.residueField⟦X⟧ˣ)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (φ : F.residueField⸨X⸩ →+* A) (x : A) :
    Polynomial.eval₂ φ x
        (equalCharacteristicChangedPiPolynomial F
          (equalCharacteristicThetaSourceUnit u)) =
      equalCharacteristicLubinTateAmbientPiEnd F
        (φ (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u))) x := by
  rw [equalCharacteristicChangedPiPolynomial_eq]
  simp [equalCharacteristicLubinTateAmbientPiEnd_apply]

private theorem equalCharacteristicChangedPiPolynomialIterate_eval₂
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (φ : F.residueField⸨X⸩ →+* A) (n : ℕ) (x : A) :
    Polynomial.eval₂ φ x
        (equalCharacteristicChangedPiPolynomialIterate F
          (equalCharacteristicThetaSourceUnit u) n) =
      equalCharacteristicLubinTateAmbientPiIterate F
        (φ (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u))) n x := by
  have hfun :
      (fun y : A ↦ Polynomial.eval₂ φ y
        (equalCharacteristicChangedPiPolynomial F
          (equalCharacteristicThetaSourceUnit u))) =
      (fun y : A ↦ equalCharacteristicLubinTateAmbientPiEnd F
        (φ (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u))) y) := by
    funext y
    exact equalCharacteristicChangedPiPolynomial_eval₂ F u φ y
  calc
    Polynomial.eval₂ φ x
        (equalCharacteristicChangedPiPolynomialIterate F
          (equalCharacteristicThetaSourceUnit u) n) =
        (fun y : A ↦ Polynomial.eval₂ φ y
          (equalCharacteristicChangedPiPolynomial F
            (equalCharacteristicThetaSourceUnit u)))^[n] x := by
      rw [equalCharacteristicChangedPiPolynomialIterate,
        Polynomial.iterate_comp_eval₂, Polynomial.eval₂_X]
    _ = (fun y : A ↦ equalCharacteristicLubinTateAmbientPiEnd F
        (φ (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u))) y)^[n] x := by
      exact congrArg (fun f : A → A ↦ f^[n] x) hfun
    _ = equalCharacteristicLubinTateAmbientPiIterate F
        (φ (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u))) n x :=
      (equalCharacteristicLubinTateAmbientPiIterate_eq_function_iterate F
        (φ (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u))) n x).symm

private theorem equalCharacteristicChangedPrimitivePolynomial_eval₂
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ)
    {A : Type*} [Field A] [CharP A F.residueCharacteristic]
    (φ : F.residueField⸨X⸩ →+* A) (n : ℕ) (x : A) :
    Polynomial.eval₂ φ x
        (equalCharacteristicChangedPrimitivePolynomial F
          (equalCharacteristicThetaSourceUnit u) n) =
      equalCharacteristicLubinTateAmbientPiIterate F
          (φ (equalCharacteristicChangedLaurentUniformizer F
            (equalCharacteristicThetaSourceUnit u))) n x ^
          (Nat.card F.residueField - 1) +
        φ (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u)) := by
  rw [equalCharacteristicChangedPrimitivePolynomial_eq,
    Polynomial.eval₂_add, Polynomial.eval₂_pow,
    equalCharacteristicChangedPiPolynomialIterate_eval₂,
    Polynomial.eval₂_C]

/-- The chosen source point satisfies the primitive `u⁻¹T` equation. -/
theorem equalCharacteristicChangedCompletedPrimitiveRoot_equation
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicChangedCompletedLevelUniformizer F u n) n
        (equalCharacteristicChangedCompletedPrimitiveRoot F u n) ^
          (Nat.card F.residueField - 1) +
      equalCharacteristicChangedCompletedLevelUniformizer F u n = 0 := by
  have hroot := equalCharacteristicChangedCompletedPrimitiveRoot_isRoot F u n
  change Polynomial.eval
      (equalCharacteristicChangedCompletedPrimitiveRoot F u n)
      (((equalCharacteristicChangedPrimitivePolynomial F
        (equalCharacteristicThetaSourceUnit u) n).map
        (algebraMap F.residueField⸨X⸩
          (equalCharacteristicCompletedUnramifiedField F.residueField))).map
        (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
          (equalCharacteristicChangedCompletedLevelField F u n))) = 0 at hroot
  rw [Polynomial.map_map, Polynomial.eval_map,
    equalCharacteristicChangedPrimitivePolynomial_eval₂] at hroot
  have ht :
      ((algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
        (equalCharacteristicChangedCompletedLevelField F u n)).comp
          (algebraMap F.residueField⸨X⸩
            (equalCharacteristicCompletedUnramifiedField F.residueField)))
        (equalCharacteristicChangedLaurentUniformizer F
          (equalCharacteristicThetaSourceUnit u)) =
      equalCharacteristicChangedCompletedLevelUniformizer F u n := by
    rfl
  rwa [ht] at hroot

/-- The root is killed at division level `n + 1`. -/
theorem equalCharacteristicChangedCompletedPrimitiveRoot_torsion
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IsEqualCharacteristicLubinTateAmbientTorsion F
      (equalCharacteristicChangedCompletedLevelUniformizer F u n) (n + 1)
      (equalCharacteristicChangedCompletedPrimitiveRoot F u n) := by
  let z := equalCharacteristicLubinTateAmbientPiIterate F
    (equalCharacteristicChangedCompletedLevelUniformizer F u n) n
    (equalCharacteristicChangedCompletedPrimitiveRoot F u n)
  have hz := equalCharacteristicChangedCompletedPrimitiveRoot_equation F u n
  change equalCharacteristicLubinTateAmbientPiIterate F
      (equalCharacteristicChangedCompletedLevelUniformizer F u n) (n + 1)
      (equalCharacteristicChangedCompletedPrimitiveRoot F u n) = 0
  rw [show n + 1 = 1 + n by omega,
    equalCharacteristicLubinTateAmbientPiIterate_add,
    equalCharacteristicLubinTateAmbientPiIterate_one,
    equalCharacteristicLubinTateAmbientPiEnd_apply]
  change z ^ Nat.card F.residueField +
      equalCharacteristicChangedCompletedLevelUniformizer F u n * z = 0
  have hq : Nat.card F.residueField ≠ 0 := Nat.card_pos.ne'
  rw [← pow_sub_one_mul hq, ← add_mul, hz, zero_mul]

/-- The chosen root is not already a division-level `n` point. -/
theorem equalCharacteristicChangedCompletedPrimitiveRoot_not_torsion_pred
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    ¬ IsEqualCharacteristicLubinTateAmbientTorsion F
      (equalCharacteristicChangedCompletedLevelUniformizer F u n) n
      (equalCharacteristicChangedCompletedPrimitiveRoot F u n) := by
  intro hpred
  have heq := equalCharacteristicChangedCompletedPrimitiveRoot_equation F u n
  rw [hpred, zero_pow, zero_add] at heq
  · exact equalCharacteristicChangedCompletedLevelUniformizer_ne_zero F u n heq
  · exact Nat.sub_ne_zero_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- If `x` is on or outside the unit sphere, the changed Lubin--Tate
endomorphism has the norm of its leading term. -/
private theorem equalCharacteristicChangedCompletedAmbientPiEnd_norm_of_one_le
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicChangedCompletedLevelField F u n)
    (hx : 1 ≤ ‖x‖) :
    ‖equalCharacteristicLubinTateAmbientPiEnd F
        (equalCharacteristicChangedCompletedLevelUniformizer F u n) x‖ =
      ‖x‖ ^ Nat.card F.residueField := by
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hqpos : 0 < Nat.card F.residueField := Nat.card_pos
  have hself : ‖x‖ ≤ ‖x‖ ^ Nat.card F.residueField := by
    calc
      ‖x‖ = 1 * ‖x‖ := (one_mul _).symm
      _ ≤ ‖x‖ ^ (Nat.card F.residueField - 1) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hx) (norm_nonneg x)
      _ = ‖x‖ ^ Nat.card F.residueField := by
        rw [← pow_succ,
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hqpos.ne')]
  have hterms :
      ‖equalCharacteristicChangedCompletedLevelUniformizer F u n * x‖ <
        ‖x ^ Nat.card F.residueField‖ := by
    rw [norm_mul, norm_pow]
    calc
      ‖equalCharacteristicChangedCompletedLevelUniformizer F u n‖ * ‖x‖ <
          1 * ‖x‖ :=
        mul_lt_mul_of_pos_right
          (equalCharacteristicChangedCompletedLevelUniformizer_norm_lt_one F u n)
          hxpos
      _ = ‖x‖ := one_mul _
      _ ≤ ‖x‖ ^ Nat.card F.residueField := hself
  rw [equalCharacteristicLubinTateAmbientPiEnd_apply,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hterms),
    max_eq_left hterms.le, norm_pow]

/-- On or outside the unit sphere, every iterate has the norm of its
leading `q`-power term. -/
private theorem equalCharacteristicChangedCompletedAmbientPiIterate_norm_of_one_le
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (level i : ℕ)
    (x : equalCharacteristicChangedCompletedLevelField F u level)
    (hx : 1 ≤ ‖x‖) :
    ‖equalCharacteristicLubinTateAmbientPiIterate F
        (equalCharacteristicChangedCompletedLevelUniformizer F u level) i x‖ =
      ‖x‖ ^ (Nat.card F.residueField ^ i) := by
  induction i generalizing x with
  | zero =>
      simp [equalCharacteristicLubinTateAmbientPiIterate_zero]
  | succ i ih =>
      have hend := equalCharacteristicChangedCompletedAmbientPiEnd_norm_of_one_le
        F u level x hx
      have hnext : 1 ≤
          ‖equalCharacteristicLubinTateAmbientPiEnd F
            (equalCharacteristicChangedCompletedLevelUniformizer F u level) x‖ := by
        rw [hend]
        exact one_le_pow₀ hx
      rw [equalCharacteristicLubinTateAmbientPiIterate_succ,
        ih _ hnext, hend, ← pow_mul]
      congr 1
      rw [pow_succ, Nat.mul_comm]

/-- The primitive `u⁻¹T`-point lies strictly inside the spectral unit
ball. -/
theorem equalCharacteristicChangedCompletedPrimitiveRoot_norm_lt_one
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    ‖equalCharacteristicChangedCompletedPrimitiveRoot F u n‖ < 1 := by
  by_contra hnot
  have hrootge : 1 ≤
      ‖equalCharacteristicChangedCompletedPrimitiveRoot F u n‖ :=
    le_of_not_gt hnot
  let z : equalCharacteristicChangedCompletedLevelField F u n :=
    equalCharacteristicLubinTateAmbientPiIterate F
      (equalCharacteristicChangedCompletedLevelUniformizer F u n) n
      (equalCharacteristicChangedCompletedPrimitiveRoot F u n)
  have hznorm : ‖z‖ =
      ‖equalCharacteristicChangedCompletedPrimitiveRoot F u n‖ ^
        (Nat.card F.residueField ^ n) :=
    equalCharacteristicChangedCompletedAmbientPiIterate_norm_of_one_le
      F u n n (equalCharacteristicChangedCompletedPrimitiveRoot F u n) hrootge
  have hzge : 1 ≤ ‖z‖ := by
    rw [hznorm]
    exact one_le_pow₀ hrootge
  have hzpowge : 1 ≤ ‖z ^ (Nat.card F.residueField - 1)‖ := by
    rw [norm_pow]
    exact one_le_pow₀ hzge
  have heq := equalCharacteristicChangedCompletedPrimitiveRoot_equation F u n
  change z ^ (Nat.card F.residueField - 1) +
      equalCharacteristicChangedCompletedLevelUniformizer F u n = 0 at heq
  have hnormeq : ‖z ^ (Nat.card F.residueField - 1)‖ =
      ‖equalCharacteristicChangedCompletedLevelUniformizer F u n‖ := by
    rw [eq_neg_of_add_eq_zero_left heq, norm_neg]
  rw [hnormeq] at hzpowge
  exact (not_le_of_gt
    (equalCharacteristicChangedCompletedLevelUniformizer_norm_lt_one F u n)) hzpowge

/-- The changed primitive root as an element of the spectral valuation
ring. -/
noncomputable def equalCharacteristicChangedCompletedPrimitiveRootInteger
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Valued.integer (equalCharacteristicChangedCompletedLevelField F u n) :=
  ⟨equalCharacteristicChangedCompletedPrimitiveRoot F u n, by
    change ‖equalCharacteristicChangedCompletedPrimitiveRoot F u n‖₊ ≤ 1
    exact_mod_cast
      (equalCharacteristicChangedCompletedPrimitiveRoot_norm_lt_one F u n).le⟩

/-- Coercing the integral primitive root returns the underlying completed root. -/
@[simp]
theorem equalCharacteristicChangedCompletedPrimitiveRootInteger_coe
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    ((equalCharacteristicChangedCompletedPrimitiveRootInteger F u n :
      Valued.integer
        (equalCharacteristicChangedCompletedLevelField F u n)) :
          equalCharacteristicChangedCompletedLevelField F u n) =
      equalCharacteristicChangedCompletedPrimitiveRoot F u n :=
  rfl

/-- The integral primitive point lies in the maximal ideal. -/
theorem equalCharacteristicChangedCompletedPrimitiveRootInteger_mem_maximalIdeal
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicChangedCompletedPrimitiveRootInteger F u n ∈
      Valued.maximalIdeal
        (equalCharacteristicChangedCompletedLevelField F u n) := by
  change equalCharacteristicChangedCompletedPrimitiveRootInteger F u n ∈
    IsLocalRing.maximalIdeal
      (Valued.integer
        (equalCharacteristicChangedCompletedLevelField F u n))
  apply (Valuation.mem_maximalIdeal_iff
    (equalCharacteristicChangedCompletedLevelField F u n)
    (Valued.v : Valuation
      (equalCharacteristicChangedCompletedLevelField F u n) ℝ≥0)).2
  change ‖equalCharacteristicChangedCompletedPrimitiveRoot F u n‖₊ < 1
  exact_mod_cast
    equalCharacteristicChangedCompletedPrimitiveRoot_norm_lt_one F u n

/-- The maximal-ideal primitive point supports convergent power-series
evaluation. -/
theorem equalCharacteristicChangedCompletedPrimitiveRootInteger_hasEval
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (u : F.residueField⟦X⟧ˣ) (n : ℕ) :
    PowerSeries.HasEval
      (equalCharacteristicChangedCompletedPrimitiveRootInteger F u n) := by
  change Tendsto
    (fun i : ℕ ↦ equalCharacteristicChangedCompletedPrimitiveRootInteger F u n ^ i)
    atTop (nhds 0)
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
  change ‖equalCharacteristicChangedCompletedPrimitiveRoot F u n‖ < 1
  exact equalCharacteristicChangedCompletedPrimitiveRoot_norm_lt_one F u n

end

end EqualCharacteristic
end LubinTate
