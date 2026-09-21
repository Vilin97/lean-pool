/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType
public import Mathlib.Data.Sum.Order

/-!
# API check for order type of a union

This client partitions the well-order `ω + 1` into its final point and its initial copy of `ω`.
Listing the final point first gives ordinary ordinal sum `1 + ω = ω`, which is too small to bound
the union. The Hessenberg sum is `1 ⊕ ω = ω + 1`, and the generic union theorem is sharp.

The example therefore distinguishes the theorem from the plausible but false replacement of
Hessenberg addition by ordinary ordinal addition. It imports only the public set-order-type API.
-/

public noncomputable section

namespace Tests

open Ordinal

private instance : WellFoundedLT (ℕ ⊕ₗ Unit) :=
  (Sum.Lex.toLexRelIsoLT (α := ℕ) (β := Unit)).symm.toRelEmbedding.isWellFounded

private def initialOmega : Set (ℕ ⊕ₗ Unit) :=
  Set.range (fun n : ℕ ↦ Sum.inlₗ n)

private def finalPoint : Set (ℕ ⊕ₗ Unit) :=
  Set.range (fun u : Unit ↦ Sum.inrₗ u)

private def initialOmegaOrderIso : ℕ ≃o initialOmega where
  toEquiv := Equiv.ofInjective (fun n : ℕ ↦ Sum.inlₗ n)
    Sum.Lex.inl_strictMono.injective
  map_rel_iff' := Sum.Lex.inl_le_inl_iff

private def finalPointOrderIso : Unit ≃o finalPoint where
  toEquiv := Equiv.ofInjective (fun u : Unit ↦ Sum.inrₗ u)
    Sum.Lex.inr_strictMono.injective
  map_rel_iff' := Sum.Lex.inr_le_inr_iff

private theorem finalPoint_union_initialOmega :
    finalPoint ∪ initialOmega = Set.univ := by
  ext x
  induction x using Lex.rec with
  | h x =>
      cases x <;> simp [finalPoint, initialOmega]

private def unionOrderIso : ↥(finalPoint ∪ initialOmega) ≃o (ℕ ⊕ₗ Unit) :=
  (OrderIso.setCongr _ _ finalPoint_union_initialOmega).trans OrderIso.Set.univ

private theorem initialOmega_orderType :
    (Set.IsPWO.of_linearOrder initialOmega).orderType = Ordinal.omega0 := by
  rw [Set.IsPWO.orderType_eq_typeLT_of_orderIso _ initialOmegaOrderIso.symm,
    Ordinal.type_nat_lt]

private theorem finalPoint_orderType :
    (Set.IsPWO.of_linearOrder finalPoint).orderType = 1 := by
  rw [Set.IsPWO.orderType_eq_typeLT_of_orderIso _ finalPointOrderIso.symm]
  simp

private theorem union_orderType :
    ((Set.IsPWO.of_linearOrder finalPoint).union
      (Set.IsPWO.of_linearOrder initialOmega)).orderType =
        Ordinal.omega0 + 1 := by
  rw [Set.IsPWO.orderType_eq_typeLT_of_orderIso _ unionOrderIso]
  calc
    typeLT (ℕ ⊕ₗ Unit) =
        Ordinal.type (Sum.Lex (· < · : ℕ → ℕ → Prop)
          (· < · : Unit → Unit → Prop)) :=
      (Sum.Lex.toLexRelIsoLT (α := ℕ) (β := Unit)).ordinalType_congr.symm
    _ = Ordinal.omega0 + 1 := by
      rw [Ordinal.type_sum_lex, Ordinal.type_nat_lt]
      simp

/-- The Hessenberg union bound can be sharp when the corresponding ordinary ordinal sum is too
small. -/
theorem naturalUnionBound_distinguishes_ordinaryAdd :
    ∃ (s t : Set (ℕ ⊕ₗ Unit)) (hs : s.IsPWO) (ht : t.IsPWO),
      (hs.union ht).orderType =
          (NatOrdinal.of hs.orderType + NatOrdinal.of ht.orderType).val ∧
        ¬(hs.union ht).orderType ≤ hs.orderType + ht.orderType := by
  let hs : finalPoint.IsPWO := Set.IsPWO.of_linearOrder finalPoint
  let ht : initialOmega.IsPWO := Set.IsPWO.of_linearOrder initialOmega
  refine ⟨finalPoint, initialOmega, hs, ht, ?_, ?_⟩
  · apply le_antisymm
    · exact Set.IsPWO.orderType_union_le_naturalAdd hs ht
    · rw [union_orderType, finalPoint_orderType, initialOmega_orderType]
      rw [add_comm]
      change (NatOrdinal.of Ordinal.omega0 + 1).val ≤ Ordinal.omega0 + 1
      rw [← NatOrdinal.of_add_one, NatOrdinal.val_of]
  · rw [union_orderType, finalPoint_orderType, initialOmega_orderType,
      Ordinal.one_add_omega0]
    exact not_le_of_gt (lt_add_one Ordinal.omega0)

end Tests
