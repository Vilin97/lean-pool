/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.FinitePart
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.MultiplicativelyPrincipal

import Mathlib.Tactic.NormNum

/-!
# Multiplicative factors at successor exponents

Let `alpha` be a natural ordinal whose constant Cantor coefficient is positive. The final
multiplicatively principal factor of `omega ^ alpha` is `omega`; deleting that factor leaves
`omega ^ (alpha.removeNat 1)`. These are the ordinal identities behind Berarducci's principal
and residual values for a principal series of successor degree.

The proof uses the canonical factorisation from Berarducci, Definition 6.4. It appends `omega`
to the factorisation at the predecessor exponent and invokes the uniqueness theorem for the
nonincreasing factor list.
-/

open scoped NatOrdinal

public noncomputable section

namespace Ordinal

private theorem omega0_isMultiplicativelyPrincipal :
    IsMultiplicativelyPrincipal omega0 := by
  simpa using isMultiplicativelyPrincipal_omega0_opow_opow 0

private theorem multiplicativePrincipalFactors_wpow_eq_append_omega0
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff) :
    (omega0 ^ alpha.val).multiplicativePrincipalFactors =
      (omega0 ^ (alpha.removeNat 1).val).multiplicativePrincipalFactors ++ [omega0] := by
  let factors := (omega0 ^ (alpha.removeNat 1).val).multiplicativePrincipalFactors
  have halphaOne : 1 ≤ alpha.constantCoeff := halpha
  have hpred : (alpha.removeNat 1).val + ((1 : ℕ) : Ordinal) = alpha.val := by
    have h := congrArg NatOrdinal.val (NatOrdinal.removeNat_add_natCast halphaOne)
    calc
      (alpha.removeNat 1).val + ((1 : ℕ) : Ordinal) =
          (alpha.removeNat 1 + (1 : ℕ)).val :=
        (NatOrdinal.val_add_natCast (alpha.removeNat 1) 1).symm
      _ = alpha.val := h
  have htargetPrincipal : IsAdditivelyPrincipal (omega0 ^ alpha.val) :=
    isAdditivelyPrincipal_omega0_opow alpha.val
  have hfactorsProd : factors.prod = omega0 ^ (alpha.removeNat 1).val :=
    multiplicativePrincipalFactors_prod
      (isAdditivelyPrincipal_omega0_opow (alpha.removeNat 1).val)
  have hprod : (factors ++ [omega0]).prod = omega0 ^ alpha.val := by
    rw [List.prod_append, List.prod_singleton, hfactorsProd]
    calc
      omega0 ^ (alpha.removeNat 1).val * omega0 =
          omega0 ^ (alpha.removeNat 1).val * omega0 ^ (1 : Ordinal) := by
        congr 1
        exact (opow_one omega0).symm
      _ = omega0 ^ ((alpha.removeNat 1).val + (1 : Ordinal)) :=
        (opow_add _ _ _).symm
      _ = omega0 ^ alpha.val := by
        apply congrArg (omega0 ^ ·)
        simpa using hpred
  have hprincipal : ∀ f ∈ factors ++ [omega0], IsMultiplicativelyPrincipal f := by
    intro f hf
    rw [List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · exact isMultiplicativelyPrincipal_of_mem_multiplicativePrincipalFactors hf
    · exact omega0_isMultiplicativelyPrincipal
  have hone : ∀ f ∈ factors ++ [omega0], 1 < f := by
    intro f hf
    rw [List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · exact one_lt_of_mem_multiplicativePrincipalFactors hf
    · exact one_lt_omega0
  have hsorted : (factors ++ [omega0]).SortedGE := by
    rw [List.sortedGE_iff_pairwise, List.pairwise_append]
    refine ⟨List.sortedGE_iff_pairwise.mp
      (multiplicativePrincipalFactors_sortedGE _), by simp, ?_⟩
    intro f hf g hg
    simp only [List.mem_singleton] at hg
    subst g
    have hinfinite :=
      isInfiniteMultiplicativelyPrincipal_of_mem_multiplicativePrincipalFactors hf
    exact hinfinite.isAdditivelyPrincipal.omega0_le_of_one_lt
      (one_lt_of_mem_multiplicativePrincipalFactors hf)
  exact
    (multiplicativePrincipalFactors_unique
      htargetPrincipal hprod hprincipal hone hsorted).symm

/-- A positive constant Cantor coefficient contributes a final term `1` to the uncompressed
Cantor normal form. -/
theorem one_mem_additivePrincipalTerms_of_constantCoeff_pos
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff) :
    (1 : Ordinal) ∈ alpha.val.additivePrincipalTerms := by
  let terms := (alpha.removeNat 1).val.additivePrincipalTerms
  have halphaOne : 1 ≤ alpha.constantCoeff := halpha
  have hpred : (alpha.removeNat 1).val + (1 : Ordinal) = alpha.val := by
    have h := congrArg NatOrdinal.val (NatOrdinal.removeNat_add_natCast halphaOne)
    calc
      (alpha.removeNat 1).val + (1 : Ordinal) =
          (alpha.removeNat 1).val + ((1 : ℕ) : Ordinal) := by norm_num
      _ = (alpha.removeNat 1 + (1 : ℕ)).val :=
        (NatOrdinal.val_add_natCast (alpha.removeNat 1) 1).symm
      _ = alpha.val := h
  have hsum : (terms ++ [1]).sum = alpha.val := by
    rw [List.sum_append, List.sum_singleton, additivePrincipalTerms_sum]
    exact hpred
  have hprincipal : ∀ a ∈ terms ++ [1], IsAdditivelyPrincipal a := by
    intro a ha
    rw [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact isAdditivelyPrincipal_of_mem_additivePrincipalTerms ha
    · simpa using isAdditivelyPrincipal_omega0_opow 0
  have hsorted : (terms ++ [1]).SortedGE := by
    rw [List.sortedGE_iff_pairwise, List.pairwise_append]
    refine ⟨List.sortedGE_iff_pairwise.mp (additivePrincipalTerms_sortedGE _), by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact Order.one_le_iff_ne_zero.mpr
      (isAdditivelyPrincipal_of_mem_additivePrincipalTerms ha).ne_zero
  have hterms : terms ++ [1] = alpha.val.additivePrincipalTerms :=
    additivePrincipalTerms_unique hsum hprincipal hsorted
  rw [← hterms]
  simp

/-- The principal factor of `omega ^ alpha` is `omega` when `alpha` has positive constant
Cantor coefficient. -/
theorem AdditivePrincipalAboveOne.principalFactor_wpow_of_constantCoeff_pos
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff)
    (hadd : IsAdditivelyPrincipal (omega0 ^ alpha.val))
    (hone : 1 < omega0 ^ alpha.val) :
    AdditivePrincipalAboveOne.principalFactor
        (⟨omega0 ^ alpha.val, hadd, hone⟩ : AdditivePrincipalAboveOne) = omega0 := by
  rw [AdditivePrincipalAboveOne.principalFactor_eq_getLast]
  let source := (omega0 ^ alpha.val).multiplicativePrincipalFactors
  let target :=
    (omega0 ^ (alpha.removeNat 1).val).multiplicativePrincipalFactors ++ [omega0]
  have hsource : source = target :=
    multiplicativePrincipalFactors_wpow_eq_append_omega0 alpha halpha
  calc
    source.getLast (multiplicativePrincipalFactors_ne_nil hadd hone) =
        target.getLast (by simp [target]) :=
      List.getLast_congr _ _ hsource
    _ = omega0 := by
      simp [target]

/-- The residual factor of `omega ^ alpha` is the power at the predecessor exponent when
`alpha` has positive constant Cantor coefficient. -/
theorem AdditivePrincipalAboveOne.residualFactor_wpow_of_constantCoeff_pos
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff)
    (hadd : IsAdditivelyPrincipal (omega0 ^ alpha.val))
    (hone : 1 < omega0 ^ alpha.val) :
    AdditivePrincipalAboveOne.residualFactor
        (⟨omega0 ^ alpha.val, hadd, hone⟩ : AdditivePrincipalAboveOne) =
      omega0 ^ (alpha.removeNat 1).val := by
  rw [AdditivePrincipalAboveOne.residualFactor_eq_dropLast_prod]
  let factors := (omega0 ^ (alpha.removeNat 1).val).multiplicativePrincipalFactors
  have hsource : (omega0 ^ alpha.val).multiplicativePrincipalFactors =
      factors ++ [omega0] :=
    multiplicativePrincipalFactors_wpow_eq_append_omega0 alpha halpha
  rw [hsource]
  have hdrop : (factors ++ [omega0]).dropLast = factors := by
    induction factors with
    | nil => rfl
    | cons a factors ih =>
        cases factors with
        | nil => rfl
        | cons b factors =>
            change (a :: b :: (factors ++ [omega0])).dropLast = a :: b :: factors
            rw [List.dropLast_cons_cons]
            exact congrArg (List.cons a) ih
  rw [hdrop]
  exact multiplicativePrincipalFactors_prod
    (isAdditivelyPrincipal_omega0_opow (alpha.removeNat 1).val)

end Ordinal
