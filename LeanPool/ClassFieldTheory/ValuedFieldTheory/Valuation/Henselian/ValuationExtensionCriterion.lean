/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.NonmonicReduction
/-!
# the factor-lifting criterion

Artin's monic coprime-factor lifting criterion implies the exact primitive
factorization form of Hensel's lemma from the primitive factorization definition.
-/

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  exists_extension_valuationSubring_with_hasExtension →
    exists_extension_valuationSubring_with_hasExtension


noncomputable section

open Polynomial

namespace DiscreteValuationField
open ValuationTheory.DiscreteValuationField

universe u

/-- The unit-leading-coefficient branch of the factor-lifting criterion.  Normalize the
ground-field irreducible polynomial to be monic, then normalize both residual
factors without changing their product or coprimality. -/
theorem MonicResidualCoprimeFactorLifting.leadingCoeff_unit_branch
    {K : Type u} [Field K] {V : ValuationSubring K}
    (hlift : MonicResidualCoprimeFactorLifting V)
    {Q : Polynomial V} (hQprim : Q.IsPrimitive)
    (hQirr : Irreducible (Q.map V.subtype))
    (hlead : IsUnit Q.leadingCoeff) :
    let qbar := Q.map (IsLocalRing.residue V)
    qbar.natDegree = Q.natDegree ∧
      ∀ a b : Polynomial (IsLocalRing.ResidueField V),
        qbar = a * b → IsCoprime a b →
          a.natDegree = 0 ∨ b.natDegree = 0 := by
  let qbar : Polynomial (IsLocalRing.ResidueField V) :=
    Q.map (IsLocalRing.residue V)
  have hdegree : qbar.natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff
      (IsLocalRing.residue V) hlead
  refine ⟨hdegree, ?_⟩
  intro a b hfactor hcoprime
  let u : Vˣ := hlead.unit
  let F : Polynomial V := Polynomial.C ((u⁻¹ : Vˣ) : V) * Q
  have hu : (u : V) = Q.leadingCoeff := hlead.unit_spec
  have hFmonic : F.Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    change (((u⁻¹ : Vˣ) : V) * Q.leadingCoeff) = 1
    rw [← hu]
    simp
  have hscalarUnitK : IsUnit (((u⁻¹ : Vˣ) : V) : K) := by
    exact isUnit_iff_ne_zero.mpr
      (V.subtype_injective.ne (Units.ne_zero (u⁻¹ : Vˣ)))
  have hCunitK :
      IsUnit (Polynomial.C (((u⁻¹ : Vˣ) : V) : K)) :=
    Polynomial.isUnit_C.mpr hscalarUnitK
  have hFmap :
      F.map V.subtype =
        Polynomial.C (((u⁻¹ : Vˣ) : V) : K) * Q.map V.subtype := by
    dsimp [F]
    rw [Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hFirr : Irreducible (F.map V.subtype) := by
    have hassoc : Associated (F.map V.subtype) (Q.map V.subtype) := by
      rw [hFmap]
      exact associated_unit_mul_left _ _ hCunitK
    exact hassoc.symm.irreducible hQirr
  let c : IsLocalRing.ResidueField V :=
    IsLocalRing.residue V (((u⁻¹ : Vˣ) : V))
  have hcunit : IsUnit c :=
    (IsLocalRing.residue V).isUnit_map (Units.isUnit (u⁻¹ : Vˣ))
  have hCunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr hcunit
  let a' : Polynomial (IsLocalRing.ResidueField V) := Polynomial.C c * a
  have hfactor' : F.map (IsLocalRing.residue V) = a' * b := by
    dsimp [F, a', c]
    rw [Polynomial.map_mul, Polynomial.map_C, hfactor]
    ring
  have hcoprime' : IsCoprime a' b :=
    (isCoprime_mul_unit_left_left hCunit a b).2 hcoprime
  have hqbar0 : qbar ≠ 0 :=
    residue_ne_zero_of_isPrimitive_valuationSubring V hQprim
  have hab0 : a ≠ 0 ∧ b ≠ 0 := by
    have hab : a * b ≠ 0 := by
      rw [← hfactor]
      exact hqbar0
    exact ⟨left_ne_zero_of_mul hab, right_ne_zero_of_mul hab⟩
  have ha'0 : a' ≠ 0 := by
    dsimp [a']
    exact mul_ne_zero hCunit.ne_zero hab0.1
  have ha'lead0 : a'.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr ha'0
  have hleadProduct : a'.leadingCoeff * b.leadingCoeff = 1 := by
    have hproductMonic : (a' * b).Monic := by
      rw [← hfactor']
      exact hFmonic.map (IsLocalRing.residue V)
    simpa only [Polynomial.Monic, Polynomial.leadingCoeff_mul] using hproductMonic
  let A : Polynomial (IsLocalRing.ResidueField V) :=
    Polynomial.C a'.leadingCoeff⁻¹ * a'
  let B : Polynomial (IsLocalRing.ResidueField V) :=
    Polynomial.C a'.leadingCoeff * b
  have hAmonic : A.Monic := by
    dsimp [A]
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ ha'lead0
  have hBmonic : B.Monic := by
    dsimp [B]
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    exact hleadProduct
  have hfactorAB : F.map (IsLocalRing.residue V) = A * B := by
    rw [hfactor']
    dsimp [A, B]
    rw [show
      (Polynomial.C a'.leadingCoeff⁻¹ * a') *
          (Polynomial.C a'.leadingCoeff * b) =
        (Polynomial.C a'.leadingCoeff⁻¹ *
          Polynomial.C a'.leadingCoeff) * (a' * b) by ring]
    rw [← Polynomial.C_mul, inv_mul_cancel₀ ha'lead0]
    simp
  have hCinvUnit : IsUnit (Polynomial.C a'.leadingCoeff⁻¹) :=
    Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr (inv_ne_zero ha'lead0))
  have hCleadUnit : IsUnit (Polynomial.C a'.leadingCoeff) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha'lead0)
  have hcoprimeAB : IsCoprime A B := by
    dsimp [A, B]
    exact
      (isCoprime_mul_units_left hCinvUnit hCleadUnit a' b).2 hcoprime'
  have hdegrees : A.natDegree = 0 ∨ B.natDegree = 0 :=
    hlift.irreducible_monic_reduction_coprime_factor_degree_zero
      hFmonic hFirr hAmonic hBmonic hfactorAB hcoprimeAB
  have hAdegree : A.natDegree = a'.natDegree := by
    dsimp [A]
    rw [Polynomial.natDegree_mul hCinvUnit.ne_zero ha'0,
      Polynomial.natDegree_C, Nat.zero_add]
  have hBdegree : B.natDegree = b.natDegree := by
    dsimp [B]
    rw [Polynomial.natDegree_mul hCleadUnit.ne_zero hab0.2,
      Polynomial.natDegree_C, Nat.zero_add]
  have ha'degree : a'.natDegree = a.natDegree := by
    dsimp [a']
    rw [Polynomial.natDegree_mul hCunit.ne_zero hab0.1,
      Polynomial.natDegree_C, Nat.zero_add]
  exact hdegrees.elim
    (fun hA ↦ Or.inl (ha'degree.symm.trans (hAdegree.symm.trans hA)))
    (fun hB ↦ Or.inr (hBdegree.symm.trans hB))

open AlgebraicNumberTheory.Valuations renaming
  primitive_irreducible_reduction_natDegree_zero_of_leadingCoeff_nonunit_of_roots_eq →
    primitive_reduction_natDegree_zero_of_roots_eq in
/-- the factor-lifting criterion's irreducible-factor input.  Exact monic lifting forces a
primitive irreducible polynomial to have either full-degree or constant
reduction, and the reduction has no coprime splitting into two nonconstant
factors. -/
theorem primitiveIrreducibleReductionProperty_of_monicResidualCoprimeFactorLifting
    {K : Type u} [Field K] (V : ValuationSubring K)
    (hlift : MonicResidualCoprimeFactorLifting V) :
    PrimitiveIrreducibleReductionProperty V := by
  intro Q hQprim hQirr
  let qbar : Polynomial (IsLocalRing.ResidueField V) :=
    Q.map (IsLocalRing.residue V)
  have hqbar0 : qbar ≠ 0 :=
    residue_ne_zero_of_isPrimitive_valuationSubring V hQprim
  by_cases hlead : IsUnit Q.leadingCoeff
  · have hbranch := hlift.leadingCoeff_unit_branch hQprim hQirr hlead
    exact ⟨Or.inr hbranch.1, hbranch.2⟩
  · let L : Type u := (Q.map V.subtype).SplittingField
    obtain ⟨B, _hB, _hlocal, _hpullback, hExt⟩ :=
      exists_extension_valuationSubring_with_hasExtension
        (L := L) V.valuation
    let : V.valuation.HasExtension B.valuation := hExt
    let : Normal K L :=
      Normal.of_isSplittingField (Q.map V.subtype)
    have hsplit :
        ((Q.map V.subtype).map (algebraMap K L)).Splits :=
      IsSplittingField.splits L (Q.map V.subtype)
    have hrootsEq : ∀ {a b : L},
        a ∈ ((Q.map V.subtype).map (algebraMap K L)).roots →
        b ∈ ((Q.map V.subtype).map (algebraMap K L)).roots →
        B.valuation a = B.valuation b := by
      intro a b ha hb
      exact hlift.irreducible_roots_same_valuation B hQirr hsplit ha hb
    have hdegree : qbar.natDegree = 0 :=
      primitive_reduction_natDegree_zero_of_roots_eq
        V B Q hQprim hQirr hlead hrootsEq
    refine ⟨Or.inl hdegree, ?_⟩
    intro a b hfactor _hcoprime
    have hab : a * b ≠ 0 := by
      rw [← hfactor]
      exact hqbar0
    have hmulDegree :=
      Polynomial.natDegree_mul (left_ne_zero_of_mul hab)
        (right_ne_zero_of_mul hab)
    have hsum : a.natDegree + b.natDegree = 0 := by
      rw [← hmulDegree, ← hfactor, hdegree]
    exact Or.inl (Nat.eq_zero_of_add_eq_zero_right hsum)

/-- the factor-lifting criterion: monic coprime-factor lifting is sufficient for
Hensel's lemma in the exact primitive factorization form of the primitive factorization
  definition. -/
theorem henselianValuationExtension
    {K : Type u} [Field K] (V : ValuationSubring K)
    (hlift : MonicResidualCoprimeFactorLifting V) :
    HenselFactorizationProperty V :=
  henselFactorization_of_primitiveIrreducibleReductionProperty V
    (primitiveIrreducibleReductionProperty_of_monicResidualCoprimeFactorLifting
      V hlift)

/-- Exact criterion form of the factor-lifting criterion.  The reverse implication is the
monic specialization of the primitive factorization definition. -/
theorem henselianValuationExtension_iff
    {K : Type u} [Field K] (V : ValuationSubring K) :
    MonicResidualCoprimeFactorLifting V ↔ HenselFactorizationProperty V :=
  ⟨henselianValuationExtension V,
    monicResidualCoprimeFactorLifting_of_henselFactorization⟩

end DiscreteValuationField

end
