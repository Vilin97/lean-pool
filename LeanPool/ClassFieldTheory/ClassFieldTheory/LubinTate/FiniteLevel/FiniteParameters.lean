/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveAction
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
import Mathlib.GroupTheory.Coset.Card
/-!
# Finite unit parameters for standard Lubin--Tate levels

For a local field `F`, the unit parameters visible at primitive level `n + 1`
are the valuation-ring units modulo the higher principal-unit subgroup
`U^(n + 1)`.  This file records that quotient, chooses representatives, and
computes its cardinality as

`(q - 1) * q ^ n`,

where `q` is the residue-field cardinality.  The final declarations descend
the standard Lubin--Tate action on the chosen primitive point to this finite
parameter quotient.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF

variable {K : Type u} [Field K]

/-- The finite unit parameters visible on the primitive level-`n + 1`
standard Lubin--Tate torsion point. -/
def standardLubinTateUnitParameter
    (F : LocalField.{u, v} K) (n : ℕ) : Type u :=
  F.valuationSubringˣ ⧸
    CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)

/-- The finite unit parameter quotient carries its canonical commutative
group structure. -/
instance standardLubinTateUnitParameterCommGroup
    (F : LocalField.{u, v} K) (n : ℕ) :
    CommGroup (standardLubinTateUnitParameter F n) := by
  change CommGroup
    (F.valuationSubringˣ ⧸
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1))
  infer_instance

/-- The canonical class of a valuation-ring unit at primitive level
`n + 1`. -/
def standardLubinTateUnitParameterClass
    (F : LocalField.{u, v} K) (n : ℕ) :
    F.valuationSubringˣ →* standardLubinTateUnitParameter F n :=
  QuotientGroup.mk'
    (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1))

/-- The finite-level unit parameter space is finite. -/
noncomputable instance standardLubinTateUnitParameter_finite
    (F : LocalField.{u, v} K) (n : ℕ) :
    Finite (standardLubinTateUnitParameter F n) := by
  change Finite
    (F.valuationSubringˣ ⧸
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1))
  exact
    higherPrincipalUnitGroup.finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
      F.toCompleteDVF (n + 1)

/-- A chosen valuation-ring unit representing a finite unit parameter. -/
noncomputable def standardLubinTateUnitParameterChosenRepresentative
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : standardLubinTateUnitParameter F n) :
    F.valuationSubringˣ :=
  Classical.choose
    (QuotientGroup.mk'_surjective
      (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) a)

/-- The chosen representative has the prescribed quotient class. -/
@[simp]
theorem standardLubinTateUnitParameterChosenRepresentative_spec
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterClass F n
        (standardLubinTateUnitParameterChosenRepresentative F n a) = a :=
  Classical.choose_spec
    (QuotientGroup.mk'_surjective
      (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) a)

/-- Two valuation-ring units determine the same finite parameter exactly
when their quotient belongs to `U^(n + 1)`. -/
theorem standardLubinTateUnitParameterClass_eq_iff_div_mem
    (F : LocalField.{u, v} K) (n : ℕ)
    (a b : F.valuationSubringˣ) :
    standardLubinTateUnitParameterClass F n a =
        standardLubinTateUnitParameterClass F n b ↔
      a / b ∈
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1) := by
  change
    QuotientGroup.mk'
        (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) a =
      QuotientGroup.mk'
        (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) b ↔
      _
  exact QuotientGroup.eq_iff_div_mem

/-- The finite standard unit parameter set has cardinality
`(q - 1) * q ^ n`. -/
theorem standardLubinTateUnitParameter_natCard
    (F : LocalField.{u, v} K) (n : ℕ) :
    Nat.card (standardLubinTateUnitParameter F n) =
      (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n := by
  let D := F.toCompleteDVF
  let U := CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration D
  let Q :=
    F.valuationSubringˣ ⧸
      CompleteDVF.higherPrincipalUnitGroup D (n + 1)
  let H : Subgroup Q :=
    U.principalUnitSubgroupClassInQuotient 1 (n + 1)
  have hlevel : 1 ≤ n + 1 := by omega
  obtain ⟨π, hπ⟩ := F.exists_uniformizer
  have hquotient :
      Nat.card (Q ⧸ H) = Nat.card F.residueField - 1 := by
    calc
      Nat.card (Q ⧸ H) =
          Nat.card
            (F.valuationSubringˣ ⧸
              CompleteDVF.higherPrincipalUnitGroup D 1) := by
        exact Nat.card_congr
          (U.quotientModuloPrincipalUnitClassEquivQuotientOfLe
            hlevel).toEquiv
      _ = Nat.card F.residueFieldˣ := by
        exact Nat.card_congr
          (higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits D).toEquiv
      _ = Nat.card F.residueField - 1 := Nat.card_units F.residueField
  have hsubquotient :
      Nat.card H = Nat.card F.residueField ^ n := by
    calc
      Nat.card H =
          Nat.card (U.principalUnitSubquotient 1 (n + 1)) := by
        exact
          (Nat.card_congr
            (U.principalUnitSubquotientEquivClassInQuotientOfLe
              hlevel).toEquiv).symm
      _ =
          Nat.card
            (CompleteDVF.higherPrincipalUnitGroup D 1 ⧸
              (CompleteDVF.higherPrincipalUnitGroup D (n + 1)).subgroupOf
                (CompleteDVF.higherPrincipalUnitGroup D 1)) := by
        exact Nat.card_congr
          (U.principalUnitSubquotientConcreteEquiv 1 (n + 1)).toEquiv
      _ = Nat.card F.residueField ^ n := by
        simpa [D] using
          (higherPrincipalUnitGroup.card_principalUnitSubquotient_one_eq_residue_pow_of_uniformizer
            D hπ hlevel)
  change Nat.card Q =
    (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H,
    hquotient, hsubquotient]

/-- The primitive root attached to a finite unit parameter.  A representative
is chosen only to evaluate the primitive action; the theorem below shows that
the value depends only on its quotient class. -/
noncomputable def standardLubinTateUnitParameterRoot
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    SeparableClosure K :=
  standardLubinTatePrimitiveRootAction hπ n
    (standardLubinTateUnitParameterChosenRepresentative F n a)

/-- The parameter root can be evaluated using any representative of its
quotient class. -/
theorem standardLubinTateUnitParameterRoot_eq_action_of_class_eq
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n)
    (u : F.valuationSubringˣ)
    (hu : standardLubinTateUnitParameterClass F n u = a) :
    standardLubinTateUnitParameterRoot F hπ n a =
      standardLubinTatePrimitiveRootAction hπ n u := by
  apply
    standardLubinTatePrimitiveRootAction_eq_of_div_mem_higherPrincipalUnitGroup
      hπ n
  exact
    (standardLubinTateUnitParameterClass_eq_iff_div_mem F n
      (standardLubinTateUnitParameterChosenRepresentative F n a) u).mp
        ((standardLubinTateUnitParameterChosenRepresentative_spec F n a).trans
          hu.symm)

/-- Evaluating at a canonical quotient class recovers the primitive action
of the original valuation-ring unit. -/
@[simp]
theorem standardLubinTateUnitParameterRoot_class
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (u : F.valuationSubringˣ) :
    standardLubinTateUnitParameterRoot F hπ n
        (standardLubinTateUnitParameterClass F n u) =
      standardLubinTatePrimitiveRootAction hπ n u :=
  standardLubinTateUnitParameterRoot_eq_action_of_class_eq
    F hπ n _ u rfl

/-- Every finite unit parameter gives a root of the primitive level
polynomial. -/
theorem standardLubinTateUnitParameterRoot_isRoot
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    ((standardLubinTatePrimitivePolynomialOverField F π n).map
      (algebraMap K (SeparableClosure K))).IsRoot
        (standardLubinTateUnitParameterRoot F hπ n a) := by
  simpa [standardLubinTateUnitParameterRoot] using
    standardLubinTatePrimitiveRootAction_isRoot hπ n
      (standardLubinTateUnitParameterChosenRepresentative F n a)

end LubinTate

end
