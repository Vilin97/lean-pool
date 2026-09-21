/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DomainEquiv
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Translation

/-!
# Support order type under exponent-domain restriction

Restricting a Hahn series to the range of an ordered exponent embedding cannot increase its
ordinary support order type. The support inclusion itself crosses exponent types, so the proof
uses the induced order embedding between the two support subtypes.
-/

public noncomputable section

open Ordinal

namespace HahnSeries

universe u v

variable {R : Type v} {G H : Type u}
variable [LinearOrder G] [LinearOrder H]

section Restrict

variable [Zero R]

/-- Restricting the exponent domain along an order embedding cannot increase support order type.
-/
theorem supportOrderType_restrictDomain_le (f : G ↪o H) (x : R⟦H⟧) :
    (restrictDomain f x).supportOrderType ≤ x.supportOrderType := by
  let e : ↑(restrictDomain f x).support → ↑x.support := fun g ↦
    ⟨f g.1, by
      rw [mem_support]
      have hg := (mem_support (restrictDomain f x) g.1).mp g.2
      rw [restrictDomain_coeff] at hg
      exact hg⟩
  have he : StrictMono e := by
    intro a b hab
    exact f.strictMono hab
  letI : WellFoundedLT ↑(restrictDomain f x).support :=
    (restrictDomain f x).isPWO_support.isWF
  letI : WellFoundedLT ↑x.support := x.isPWO_support.isWF
  rw [supportOrderType_eq_setOrderType, supportOrderType_eq_setOrderType]
  calc
    (restrictDomain f x).isPWO_support.orderType =
        typeLT ↑(restrictDomain f x).support :=
      (restrictDomain f x).isPWO_support.orderType_eq_typeLT_of_orderIso
        (OrderIso.refl ↑(restrictDomain f x).support)
    _ ≤ typeLT ↑x.support :=
      (OrderEmbedding.ofStrictMono e he).ltEmbedding.ordinal_type_le
    _ = x.isPWO_support.orderType :=
      (x.isPWO_support.orderType_eq_typeLT_of_orderIso
        (OrderIso.refl ↑x.support)).symm

end Restrict

section RingEquiv

variable [Semiring R]
variable [AddCommMonoid G] [IsOrderedCancelAddMonoid G]
variable [AddCommMonoid H] [IsOrderedCancelAddMonoid H]

/-- Reindexing exponents along an ordered additive equivalence preserves support order type. -/
@[simp]
theorem supportOrderType_embDomainRingEquiv (e : G ≃+o H) (x : R⟦G⟧) :
    (embDomainRingEquiv e x).supportOrderType = x.supportOrderType := by
  rw [supportOrderType_eq_setOrderType, supportOrderType_eq_setOrderType]
  letI : WellFoundedLT x.support := x.isWF_support
  let supportEquiv : (embDomainRingEquiv e x).support ≃o x.support :=
    (OrderIso.setCongr _ (e '' x.support) (support_embDomainRingEquiv e x)).trans
      (StrictMonoOn.orderIso e x.support
        (e.strictMono.strictMonoOn x.support)).symm
  exact (embDomainRingEquiv e x).isPWO_support.orderType_eq_typeLT_of_orderIso
    supportEquiv |>.trans
      (x.isPWO_support.orderType_eq_typeLT_of_orderIso (OrderIso.refl x.support)).symm

end RingEquiv

end HahnSeries
