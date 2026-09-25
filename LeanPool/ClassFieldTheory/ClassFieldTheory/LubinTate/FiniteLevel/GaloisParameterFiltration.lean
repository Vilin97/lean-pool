/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelAbelian
/-!
# Principal-unit filtration on finite Lubin--Tate Galois groups

The multiplicative equivalence between finite unit parameters and the
Galois group transports the image of `U_F^k` to a subgroup of the Galois
group.  This file records membership both for quotient parameters and for
valuation-ring unit representatives, and preserves the expected cardinality
`q ^ (n + 1 - k)`.
-/

@[expose] public section

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF

variable {K : Type u} [Field K]

/-- The image of the `k`-th finite unit-parameter subgroup in the Galois
group of the standard level-`n + 1` Lubin--Tate extension. -/
noncomputable def standardLubinTateGaloisParameterSubgroup
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) :
    Subgroup (Gal((standardLubinTateLevelField hπ n)/K)) :=
  Subgroup.map (standardLubinTateUnitParameterToGalHom F hπ n)
    (standardLubinTateUnitParameterSubgroup F n k)

/-- The explicit parameter-to-Galois map reflects membership in every
transported parameter subgroup. -/
theorem standardLubinTateUnitParameterToGal_mem_galoisParameterSubgroup_iff
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (a : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterToGal F hπ n a ∈
        standardLubinTateGaloisParameterSubgroup F hπ n k ↔
      a ∈ standardLubinTateUnitParameterSubgroup F n k := by
  change
    standardLubinTateUnitParameterToGalHom F hπ n a ∈
        Subgroup.map (standardLubinTateUnitParameterToGalHom F hπ n)
          (standardLubinTateUnitParameterSubgroup F n k) ↔
      a ∈ standardLubinTateUnitParameterSubgroup F n k
  constructor
  · rintro ⟨b, hb, hba⟩
    have hba' : b = a := by
      apply standardLubinTateUnitParameterToGal_injective F hπ n
      simpa only [standardLubinTateUnitParameterToGalHom_apply] using hba
    change a ∈
      (standardLubinTateUnitParameterSubgroup F n k :
        Set (standardLubinTateUnitParameter F n))
    simpa only [hba'] using hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- On a valuation-ring unit representative, membership in the transported
Galois subgroup is exactly membership in `U_F^k`. -/
theorem
    standardLubinTateUnitParameterToGal_class_mem_galoisParameterSubgroup_iff
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (hkn : k ≤ n + 1) (u : F.valuationSubringˣ) :
    standardLubinTateUnitParameterToGal F hπ n
          (standardLubinTateUnitParameterClass F n u) ∈
        standardLubinTateGaloisParameterSubgroup F hπ n k ↔
      u ∈ higherPrincipalUnitGroup F.toCompleteDVF k := by
  rw [standardLubinTateUnitParameterToGal_mem_galoisParameterSubgroup_iff,
    standardLubinTateUnitParameterClass_mem_subgroup_iff F n k hkn u]

/-- Restricting the parameter-to-Galois homomorphism gives a multiplicative
equivalence onto the transported subgroup. -/
noncomputable def
    standardLubinTateUnitParameterSubgroupEquivGaloisParameterSubgroup
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) :
    standardLubinTateUnitParameterSubgroup F n k ≃*
      standardLubinTateGaloisParameterSubgroup F hπ n k := by
  let f := standardLubinTateUnitParameterToGalHom F hπ n
  let H := standardLubinTateUnitParameterSubgroup F n k
  refine MulEquiv.ofBijective (f.subgroupMap H) ⟨?_, ?_⟩
  · intro a b hab
    have hval := congrArg Subtype.val hab
    apply Subtype.ext
    apply standardLubinTateUnitParameterToGal_injective F hπ n
    change f (a : standardLubinTateUnitParameter F n) =
      f (b : standardLubinTateUnitParameter F n) at hval
    simpa only [f, standardLubinTateUnitParameterToGalHom_apply] using hval
  · exact f.subgroupMap_surjective H

/-- The transported Galois filtration has the same cardinality as its
finite unit-parameter source. -/
theorem standardLubinTateGaloisParameterSubgroup_natCard
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    Nat.card (standardLubinTateGaloisParameterSubgroup F hπ n k) =
      Nat.card F.residueField ^ (n + 1 - k) := by
  calc
    Nat.card (standardLubinTateGaloisParameterSubgroup F hπ n k) =
        Nat.card (standardLubinTateUnitParameterSubgroup F n k) := by
      exact
        (Nat.card_congr
          (standardLubinTateUnitParameterSubgroupEquivGaloisParameterSubgroup
            F hπ n k).toEquiv).symm
    _ = Nat.card F.residueField ^ (n + 1 - k) :=
      standardLubinTateUnitParameterSubgroup_natCard
        F hπ n k hk hkn

end LubinTate

end
