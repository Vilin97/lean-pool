/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Iterate
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType

/-!
# Support order type of iterated Hahn series

Flattening an iterated Hahn series orders its support lexicographically, with the outer exponent
dominant. Choosing one nonzero inner coefficient over each outer support point therefore embeds
the outer support into the flattened support. In particular, flattening cannot decrease the
ordinary support order type contributed by the outer series.
-/

public noncomputable section

open Ordinal

namespace HahnSeries

universe u v

variable {R : Type v} {Γ Γ' : Type u}
variable [Semiring R]
variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
variable [AddCommMonoid Γ'] [LinearOrder Γ'] [IsOrderedCancelAddMonoid Γ']

/-- The outer support order type of an iterated Hahn series is no larger than the support order
type of its flattening. -/
theorem supportOrderType_outer_le_iterateRingEquiv (x : R⟦Γ'⟧⟦Γ⟧) :
    x.supportOrderType ≤ (iterateRingEquiv x).supportOrderType := by
  let inner : ↑x.support → Γ' := fun g ↦ Classical.choose
    (Function.ne_iff.mp (coeff_fun_eq_zero_iff.not.mpr ((mem_support x g).mp g.2)))
  have hinner (g : ↑x.support) : (x.coeff g.1).coeff (inner g) ≠ 0 :=
    Classical.choose_spec
      (Function.ne_iff.mp (coeff_fun_eq_zero_iff.not.mpr ((mem_support x g).mp g.2)))
  let f : ↑x.support → ↑(iterateRingEquiv x).support := fun g ↦
    ⟨toLex (g.1, inner g), by
      rw [mem_support, iterateRingEquiv_coeff]
      exact hinner g⟩
  have hf : StrictMono f := by
    intro a b hab
    change toLex (a.1, inner a) < toLex (b.1, inner b)
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl hab
  letI : WellFoundedLT ↑x.support := x.isPWO_support.isWF
  letI : WellFoundedLT ↑(iterateRingEquiv x).support :=
    (iterateRingEquiv x).isPWO_support.isWF
  rw [supportOrderType_eq_setOrderType, supportOrderType_eq_setOrderType]
  calc
    x.isPWO_support.orderType = typeLT ↑x.support :=
      x.isPWO_support.orderType_eq_typeLT_of_orderIso (OrderIso.refl ↑x.support)
    _ ≤ typeLT ↑(iterateRingEquiv x).support :=
      (OrderEmbedding.ofStrictMono f hf).ltEmbedding.ordinal_type_le
    _ = (iterateRingEquiv x).isPWO_support.orderType :=
      ((iterateRingEquiv x).isPWO_support.orderType_eq_typeLT_of_orderIso
        (OrderIso.refl ↑(iterateRingEquiv x).support)).symm

end HahnSeries
