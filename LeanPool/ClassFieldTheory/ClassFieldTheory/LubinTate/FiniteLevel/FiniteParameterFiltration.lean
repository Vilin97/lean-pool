/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters
/-!
# Principal-unit filtration on finite Lubin--Tate parameters

The parameter group at primitive level `n + 1` is
`O_Fˣ / U_F^(n + 1)`.  The image of `U_F^k` gives its natural decreasing
filtration.  For `1 ≤ k ≤ n + 1`, that image has cardinality
`q ^ (n + 1 - k)`.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF

variable {K : Type u} [Field K]

/-- The image of the `k`-th higher principal-unit group in the finite
parameter quotient at primitive level `n + 1`. -/
def standardLubinTateUnitParameterSubgroup
    (F : LocalField.{u, v} K) (n k : ℕ) :
    Subgroup (standardLubinTateUnitParameter F n) :=
  (higherPrincipalUnitGroup.toPrincipalUnitFiltration
    F.toCompleteDVF).principalUnitSubgroupClassInQuotient
    k (n + 1)

/-- A represented finite parameter belongs to the `k`-th parameter subgroup
exactly when its representative lies in `U_F^k`. -/
theorem standardLubinTateUnitParameterClass_mem_subgroup_iff
    (F : LocalField.{u, v} K) (n k : ℕ) (hk : k ≤ n + 1)
    (u : F.valuationSubringˣ) :
    standardLubinTateUnitParameterClass F n u ∈
        standardLubinTateUnitParameterSubgroup F n k ↔
      u ∈ higherPrincipalUnitGroup F.toCompleteDVF k := by
  change
    QuotientGroup.mk'
        (higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) u ∈
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration
        F.toCompleteDVF).principalUnitSubgroupClassInQuotient
        k (n + 1) ↔
      u ∈ higherPrincipalUnitGroup F.toCompleteDVF k
  exact
    AntitoneSubgroupFiltration.quotient_principalUnitSubgroup_mk_mem_classInQuotient_iff
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F.toCompleteDVF)
      hk u

/-- The `k`-th finite parameter subgroup has cardinality
`q ^ (n + 1 - k)` throughout the principal-unit range. -/
theorem standardLubinTateUnitParameterSubgroup_natCard
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    Nat.card (standardLubinTateUnitParameterSubgroup F n k) =
      Nat.card F.residueField ^ (n + 1 - k) := by
  let D := F.toCompleteDVF
  let U := higherPrincipalUnitGroup.toPrincipalUnitFiltration D
  let hfinite (i j : ℕ) : Finite (U.principalUnitSubquotient i j) :=
    higherPrincipalUnitGroup.finite_principalUnitSubquotient_of_finite_residue D i j
  have hnormal : ∀ i : ℕ, (U.principalUnitSubgroup i).Normal := by
    intro i
    change (higherPrincipalUnitGroup D i).Normal
    infer_instance
  have hend : k + (n + 1 - k) = n + 1 :=
    Nat.add_sub_of_le hkn
  calc
    Nat.card (standardLubinTateUnitParameterSubgroup F n k) =
        Nat.card (U.principalUnitSubquotient k (n + 1)) := by
      exact
        (Nat.card_congr
          (U.principalUnitSubquotientEquivClassInQuotientOfLe hkn).toEquiv).symm
    _ = Nat.card
          (U.principalUnitSubquotient k (k + (n + 1 - k))) := by
      rw [hend]
    _ =
        ∏ i ∈ Finset.range (n + 1 - k),
          Nat.card (U.principalUnitGradedPiece (k + i)) := by
      rw [U.card_principalUnitSubquotient_eq_prod_gradedPiece
        hnormal k (n + 1 - k)]
    _ =
        ∏ _i ∈ Finset.range (n + 1 - k),
          Nat.card F.residueField := by
      apply Finset.prod_congr rfl
      intro i _hi
      have hki : 1 ≤ k + i := by omega
      calc
        Nat.card (U.principalUnitGradedPiece (k + i)) =
            Nat.card
              (higherPrincipalUnitGroup.principalUnitSuccQuot
                D (k + i)) :=
          Nat.card_congr
            (higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece
              D (k + i)).symm.toEquiv
        _ = Nat.card F.residueField :=
          higherPrincipalUnitGroup.card_principalUnitSuccQuot_eq_residue_of_uniformizer
            D hπ (k + i) hki
    _ = Nat.card F.residueField ^ (n + 1 - k) := by
      simp

end LubinTate

end
