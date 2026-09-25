/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveUniformizer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusEvaluation
/-!
# Residue Frobenius on completed p-adic Lubin--Tate levels

The completed multiplicative Lubin--Tate level is totally ramified over its
completed-unramified coefficient field.  Hence the canonical residue map is
an isomorphism.  Under this identification, every unit-indexed completed
Frobenius lift induces the arithmetic Frobenius `x ↦ x ^ p` on the residue
field.
-/

@[expose] public section

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ResidueField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The completed multiplicative level has residue degree one over the
completed-unramified coefficient field. -/
theorem padicCompletedLevel_residueDegree_eq_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    residueDegree
        (padicCompletedUnramifiedCompleteDVF p).toDVF
        (padicCompletedLevelCompleteDVF p n).toDVF = 1 := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let E := padicCompletedLevelField p n
  let : IsScalarTower base.valuationSubring
      target.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact
    (residueDegree_eq_one_iff_ramificationIndex_eq_degree_of_finite_separable
      base target).2
      (by
        simpa only [base, target] using
          padicCompletedLevel_ramificationIndex_eq_degree p n)

/-- The target residue field has linear rank one over the
completed-unramified residue field. -/
theorem padicCompletedLevel_residueField_finrank_eq_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Module.finrank
        (padicCompletedUnramifiedCompleteDVF p).residueField
        (padicCompletedLevelCompleteDVF p n).residueField = 1 := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let E := padicCompletedLevelField p n
  let : IsScalarTower base.valuationSubring
      target.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : target.maximalIdeal.LiesOver base.maximalIdeal :=
    maximalIdeal_liesOver base target
  have hfinrank :
      residueDegree base.toDVF target.toDVF =
        Module.finrank base.residueField target.residueField := by
    rw [residueDegree_eq_finrank_quotient base target]
    rfl
  change Module.finrank base.residueField target.residueField = 1
  calc
    Module.finrank base.residueField target.residueField =
        residueDegree base.toDVF target.toDVF :=
      hfinrank.symm
    _ = 1 := by
      simpa only [base, target] using
        padicCompletedLevel_residueDegree_eq_one p n

/-- The canonical residue map from the completed-unramified coefficient
field onto the completed level is surjective. -/
theorem padicCompletedLevel_residueMap_surjective
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Function.Surjective
      (residueMap
        (padicCompletedUnramifiedCompleteDVF p).toDVF
        (padicCompletedLevelCompleteDVF p n).toDVF) := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  have hbijective :
      Function.Bijective
        (algebraMap base.residueField target.residueField) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap).1
      (by
        simpa only [base, target] using
          padicCompletedLevel_residueField_finrank_eq_one p n)
  exact hbijective.2

/-- The canonical residue-field equivalence from the completed-unramified
coefficient field to a completed multiplicative level. -/
noncomputable def padicCompletedLevelResidueFieldEquiv
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedUnramifiedCompleteDVF p).residueField ≃+*
      (padicCompletedLevelCompleteDVF p n).residueField :=
  residueFieldEquivOfSurjective
    (padicCompletedUnramifiedCompleteDVF p).toDVF
    (padicCompletedLevelCompleteDVF p n).toDVF
    (padicCompletedLevel_residueMap_surjective p n)

/-- The completed-level residue equivalence evaluates by the canonical
residue map. -/
@[simp]
theorem padicCompletedLevelResidueFieldEquiv_apply
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedUnramifiedCompleteDVF p).residueField) :
    padicCompletedLevelResidueFieldEquiv p n x =
      residueMap
        (padicCompletedUnramifiedCompleteDVF p).toDVF
        (padicCompletedLevelCompleteDVF p n).toDVF x :=
  rfl

/-- On integral representatives, the completed-level residue equivalence is
the residue of the canonical valuation-ring inclusion. -/
theorem padicCompletedLevelResidueFieldEquiv_apply_residue
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
    padicCompletedLevelResidueFieldEquiv p n
        ((padicCompletedUnramifiedCompleteDVF p).residueMap a) =
      (padicCompletedLevelCompleteDVF p n).residueMap
        (integerMap
          (padicCompletedUnramifiedCompleteDVF p).toDVF
          (padicCompletedLevelCompleteDVF p n).toDVF a) := by
  exact
    residueFieldEquivOfSurjective_apply_residue
      (padicCompletedUnramifiedCompleteDVF p).toDVF
      (padicCompletedLevelCompleteDVF p n).toDVF
      (padicCompletedLevel_residueMap_surjective p n) a

private theorem
    padicCompletedUnramifiedWitt_residue_frobenius_eq_pow
    (p : ℕ) [Fact p.Prime]
    (a : padicCompletedUnramifiedWittRing p) :
    IsLocalRing.residue (padicCompletedUnramifiedWittRing p)
        (WittVector.frobenius a) =
      IsLocalRing.residue (padicCompletedUnramifiedWittRing p) a ^ p := by
  calc
    IsLocalRing.residue (padicCompletedUnramifiedWittRing p)
        (WittVector.frobenius a) =
        IsLocalRing.residue (padicCompletedUnramifiedWittRing p)
          (a ^ p) := by
      rw [residue_eq_residue_iff_sub_mem_maximalIdeal,
        padicCompletedUnramifiedWittRing_maximalIdeal,
        ← WittVector.ker_constantCoeff]
      change
        WittVector.constantCoeff
          (WittVector.frobenius a - a ^ p) = 0
      rw [map_sub, map_pow, WittVector.constantCoeff_apply,
        WittVector.coeff_frobenius_charP]
      exact sub_self _
    _ =
        IsLocalRing.residue (padicCompletedUnramifiedWittRing p) a ^ p := by
      rw [map_pow]

/-- The actual residue action induced by every unit-indexed completed
Frobenius lift is the arithmetic Frobenius `x ↦ x ^ p`. -/
theorem
    padicCompletedUnitFrobeniusIntegerEquiv_residue_apply_eq_pow
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicLocalField
      p).valuationSubringˣ)
    (x : (padicCompletedLevelCompleteDVF p n).residueField) :
    IsLocalRing.ResidueField.mapEquiv
        (padicCompletedUnitFrobeniusIntegerEquiv p n u) x =
      x ^ p := by
  let W := padicCompletedUnramifiedWittRing p
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let wittIntegerEquiv : W ≃+* base.valuationSubring :=
    padicCompletedUnramifiedWittRingEquivValuationSubring p
  let coefficientResidueEquiv :
      IsLocalRing.ResidueField W ≃+* target.residueField :=
    (IsLocalRing.ResidueField.mapEquiv wittIntegerEquiv).trans
      (padicCompletedLevelResidueFieldEquiv p n)
  have hcoefficient (a : W) :
      coefficientResidueEquiv (IsLocalRing.residue W a) =
        target.residueMap
          (padicCompletedLevelWittCoefficientHom p n a) := by
    simp only [coefficientResidueEquiv, RingEquiv.trans_apply,
      IsLocalRing.ResidueField.mapEquiv_apply]
    rfl
  obtain ⟨z, rfl⟩ := coefficientResidueEquiv.surjective x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
  calc
    IsLocalRing.ResidueField.mapEquiv
        (padicCompletedUnitFrobeniusIntegerEquiv p n u)
        (coefficientResidueEquiv (IsLocalRing.residue W a)) =
        target.residueMap
          (padicCompletedUnitFrobeniusIntegerEquiv p n u
            (padicCompletedLevelWittCoefficientHom p n a)) := by
      rw [hcoefficient]
      rfl
    _ =
        target.residueMap
          (padicCompletedLevelWittCoefficientHom p n
            (WittVector.frobenius a)) := by
      rw [padicCompletedUnitFrobeniusIntegerEquiv_wittCoefficientHom]
    _ =
        coefficientResidueEquiv
          (IsLocalRing.residue W (WittVector.frobenius a)) :=
      (hcoefficient (WittVector.frobenius a)).symm
    _ =
        coefficientResidueEquiv
          (IsLocalRing.residue W a ^ p) := by
      rw [padicCompletedUnramifiedWitt_residue_frobenius_eq_pow]
    _ = coefficientResidueEquiv (IsLocalRing.residue W a) ^ p := by
      rw [map_pow]

end LubinTate
