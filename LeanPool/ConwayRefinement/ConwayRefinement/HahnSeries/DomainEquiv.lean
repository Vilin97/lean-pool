/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Domain
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.HahnSeries.Cardinal
public import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Reindexing Hahn series along an ordered additive equivalence

An ordered additive equivalence of exponent groups induces a ring equivalence of Hahn-series
rings. This packages Mathlib's one-way exponent-domain embedding together with its inverse.
-/

public noncomputable section

namespace HahnSeries

variable {R G H : Type*}
variable [Semiring R]
variable [AddCommMonoid G] [LinearOrder G] [IsOrderedCancelAddMonoid G]
variable [AddCommMonoid H] [LinearOrder H] [IsOrderedCancelAddMonoid H]

/-- Reindex Hahn-series exponents along an ordered additive equivalence. -/
def embDomainRingEquiv (e : G ≃+o H) : R⟦G⟧ ≃+* R⟦H⟧ := by
  let f : G →+ H := e.toAddEquiv.toAddMonoidHom
  let F : R⟦G⟧ →+* R⟦H⟧ :=
    embDomainRingHom f e.injective fun _ _ ↦ e.map_le_map_iff'
  apply RingEquiv.ofBijective F
  constructor
  · exact embDomain_injective
  · intro y
    refine ⟨embDomain e.symm.toOrderIso.toOrderEmbedding y, ?_⟩
    ext h
    dsimp [F, f]
    have outer := embDomain_coeff (f := e.toOrderIso.toOrderEmbedding)
      (x := embDomain e.symm.toOrderIso.toOrderEmbedding y) (a := e.symm h)
    have inner := embDomain_coeff (f := e.symm.toOrderIso.toOrderEmbedding) (x := y) (a := h)
    have heh : e.toOrderIso.toOrderEmbedding (e.symm h) = h := e.apply_symm_apply h
    rw [heh] at outer
    exact outer.trans inner

@[simp]
theorem embDomainRingEquiv_coeff (e : G ≃+o H) (x : R⟦G⟧) (g : G) :
    (embDomainRingEquiv e x).coeff (e g) = x.coeff g :=
  embDomain_coeff

/-- Reindexing exponents maps a singleton Hahn series to the corresponding singleton. -/
@[simp]
theorem embDomainRingEquiv_single (e : G ≃+o H) (g : G) (r : R) :
    embDomainRingEquiv e (single g r) = single (e g) r := by
  change embDomain e.toOrderIso.toOrderEmbedding (single g r) = single (e g) r
  exact embDomain_single

/-- Reindexing exponents along an ordered additive equivalence maps support pointwise. -/
@[simp]
theorem support_embDomainRingEquiv (e : G ≃+o H) (x : R⟦G⟧) :
    (embDomainRingEquiv e x).support = e '' x.support := by
  change (embDomain e.toOrderIso.toOrderEmbedding x).support = _
  exact support_embDomain e.toOrderIso.toOrderEmbedding x

section Cardinal

universe u v

variable {S : Type v} {G' H' : Type u}
variable [Semiring S]
variable [AddCommMonoid G'] [LinearOrder G'] [IsOrderedCancelAddMonoid G']
variable [AddCommMonoid H'] [LinearOrder H'] [IsOrderedCancelAddMonoid H']

/-- Reindexing exponents along an ordered additive equivalence preserves support cardinality. -/
theorem cardSupp_embDomainRingEquiv (e : G' ≃+o H') (x : S⟦G'⟧) :
    (embDomainRingEquiv e x).cardSupp = x.cardSupp := by
  rw [cardSupp, cardSupp]
  have hsupport : (embDomainRingEquiv e x).support = (fun g ↦ e g) '' x.support := by
    ext h
    constructor
    · intro hh
      refine ⟨e.symm h, ?_, e.apply_symm_apply h⟩
      rw [HahnSeries.mem_support]
      have hhCoeff := (HahnSeries.mem_support _ _).mp hh
      rw [← e.apply_symm_apply h, embDomainRingEquiv_coeff] at hhCoeff
      exact hhCoeff
    · rintro ⟨g, hg, rfl⟩
      rw [HahnSeries.mem_support, embDomainRingEquiv_coeff]
      exact (HahnSeries.mem_support _ _).mp hg
  rw [hsupport]
  exact Cardinal.mk_image_eq (f := fun g : G' ↦ e g) e.injective

end Cardinal

end HahnSeries
