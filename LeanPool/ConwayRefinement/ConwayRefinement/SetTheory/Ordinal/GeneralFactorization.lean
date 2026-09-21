/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.MultiplicativelyPrincipal

/-!
# Canonical multiplicative factors of a power of `ω`, at every exponent

The canonical multiplicatively principal factors of `ω ^ α` are `ω` raised to the Cantor terms
of `α`, so the residual factor deletes the least such term. `SuccessorFactorization` is the
case of positive constant Cantor coefficient, where deleting the least term is deleting `1`.
-/

open Ordinal List

universe u

public noncomputable section

namespace Ordinal

private theorem dropLast_map_opow (l : List Ordinal.{u}) :
    (l.map (fun a ↦ omega0 ^ a)).dropLast = l.dropLast.map (fun a ↦ omega0 ^ a) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      cases t with
      | nil => simp
      | cons b u => simp

private theorem prod_map_opow (l : List Ordinal.{u}) :
    (l.map (fun a ↦ omega0 ^ a)).prod = omega0 ^ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.map_cons, List.prod_cons, ih, List.sum_cons, opow_add]

theorem multiplicativePrincipalFactors_omega0_opow (alpha : Ordinal.{u}) :
    (omega0 ^ alpha).multiplicativePrincipalFactors =
      alpha.additivePrincipalTerms.map (fun a ↦ omega0 ^ a) := by
  symm
  apply multiplicativePrincipalFactors_unique
  · exact isAdditivelyPrincipal_omega0_opow alpha
  · rw [prod_map_opow, additivePrincipalTerms_sum]
  · intro f hf
    rw [List.mem_map] at hf
    obtain ⟨a, ha, rfl⟩ := hf
    obtain ⟨e, rfl⟩ :=
      isAdditivelyPrincipal_iff.mp (isAdditivelyPrincipal_of_mem_additivePrincipalTerms ha)
    exact isMultiplicativelyPrincipal_omega0_opow_opow e
  · intro f hf
    rw [List.mem_map] at hf
    obtain ⟨a, ha, rfl⟩ := hf
    obtain ⟨e, rfl⟩ :=
      isAdditivelyPrincipal_iff.mp (isAdditivelyPrincipal_of_mem_additivePrincipalTerms ha)
    calc (1 : Ordinal) < omega0 := one_lt_omega0
      _ = omega0 ^ (1 : Ordinal) := (opow_one _).symm
      _ ≤ omega0 ^ (omega0 ^ e) :=
          opow_le_opow_right omega0_pos (Order.one_le_iff_pos.mpr (opow_pos e omega0_pos))
  · have hs := additivePrincipalTerms_sortedGE alpha
    rw [List.sortedGE_iff_pairwise] at hs ⊢
    exact hs.map _ fun _ _ hxy ↦ opow_le_opow_right omega0_pos hxy

theorem residualFactor_omega0_opow (alpha : Ordinal.{u})
    (hadd : IsAdditivelyPrincipal (omega0 ^ alpha)) (hone : 1 < omega0 ^ alpha) :
    AdditivePrincipalAboveOne.residualFactor ⟨omega0 ^ alpha, hadd, hone⟩ =
      omega0 ^ alpha.additivePrincipalTerms.dropLast.sum := by
  rw [AdditivePrincipalAboveOne.residualFactor_eq_dropLast_prod,
    multiplicativePrincipalFactors_omega0_opow, dropLast_map_opow, prod_map_opow]

theorem principalFactor_omega0_opow (alpha : Ordinal.{u})
    (hadd : IsAdditivelyPrincipal (omega0 ^ alpha)) (hone : 1 < omega0 ^ alpha)
    (hne : alpha.additivePrincipalTerms ≠ []) :
    AdditivePrincipalAboveOne.principalFactor ⟨omega0 ^ alpha, hadd, hone⟩ =
      omega0 ^ alpha.additivePrincipalTerms.getLast hne := by
  rw [AdditivePrincipalAboveOne.principalFactor_eq_getLast]
  simp only [multiplicativePrincipalFactors_omega0_opow]
  exact List.getLast_map _

end Ordinal

end
