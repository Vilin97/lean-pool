/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.Data.Sum.Order
import Mathlib.Order.OmegaCompletePartialOrder
import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Sum


/-!
# ωCPO instance for coproducts

This file provides the `OmegaCompletePartialOrder` instance for `Sum α β`.
-/

namespace OmegaCompletePartialOrder.Sum

variable {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]

@[simps! -isSimp]
noncomputable instance instSumLeanPool : OmegaCompletePartialOrder (Sum α β) where
  ωSup c := Sum.map ωSup ωSup (Chain.Sum.distrib c)
  le_ωSup c i := by
    cases c using Chain.Sum.distrib_cases with
    | inl c =>
      simp only [Chain.Sum.inl_coe, Chain.Sum.distrib_inl, Sum.map_inl, ge_iff_le,
        Sum.inl_le_inl_iff]
      apply le_ωSup
    | inr c =>
      simp only [Chain.Sum.inr_coe, Chain.Sum.distrib_inr, Sum.map_inr, ge_iff_le,
        Sum.inr_le_inr_iff]
      apply le_ωSup
  ωSup_le c x hx := by
    cases c using Chain.Sum.distrib_cases with
    | inl c =>
      cases x with
      | inl x =>
        simp only [Chain.Sum.inl_coe, ge_iff_le, Sum.inl_le_inl_iff, Chain.Sum.distrib_inl,
          Sum.map_inl, ωSup_le_iff] at ⊢ hx
        exact hx
      | inr x => simp only [Chain.Sum.inl_coe, ge_iff_le, Sum.not_inl_le_inr, forall_const] at hx
    | inr c =>
      cases x with
      | inl x => simp only [Chain.Sum.inr_coe, ge_iff_le, Sum.not_inr_le_inl, forall_const] at hx
      | inr x =>
        simp only [Chain.Sum.inr_coe, ge_iff_le, Sum.inr_le_inr_iff, Chain.Sum.distrib_inr,
          Sum.map_inr, ωSup_le_iff] at ⊢ hx
        exact hx

@[simp]
lemma ωSup_inl (c : Chain α) : ωSup (Chain.Sum.inl c : Chain (α ⊕ β)) = .inl (ωSup c) := by
  simp only [ωSup, Chain.Sum.distrib_inl, Sum.map_inl]

@[simp]
lemma ωSup_inr (c : Chain β) : ωSup (Chain.Sum.inr c : Chain (α ⊕ β)) = .inr (ωSup c) := by
  simp only [ωSup, Chain.Sum.distrib_inr, Sum.map_inr]

end OmegaCompletePartialOrder.Sum
