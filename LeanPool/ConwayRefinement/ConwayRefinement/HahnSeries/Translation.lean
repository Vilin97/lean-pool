/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
public import Mathlib.Algebra.Order.Group.OrderIso

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Domain

/-!
# Translation of Hahn-series exponents

An order isomorphism between exponent types induces an additive equivalence between the
corresponding Hahn-series types. Translation by `a` is the specialization to the order
isomorphism `g ↦ a + g`. Its support is the translate of the original support, and it preserves
support order type.

For a semiring of coefficients, translation agrees with multiplication on either side by the
coefficient-one monomial at `a`. Thus `HahnSeries.translate a x` is the operation denoted by
`t^a x` or `x t^a` in LM24.

The construction uses `HahnSeries.embDomain`; the exact support formula comes from the
domain-embedding interface.
-/

universe u v w

public noncomputable section

namespace HahnSeries

section Reindex

variable {R : Type w} {G : Type u} {H : Type v}
variable [PartialOrder G] [PartialOrder H] [AddMonoid R]

/-- Reindex Hahn-series exponents along an order isomorphism. -/
def embDomainAddEquiv (e : G ≃o H) : R⟦G⟧ ≃+ R⟦H⟧ where
  toFun := embDomain e.toOrderEmbedding
  invFun := embDomain e.symm.toOrderEmbedding
  left_inv x := by
    ext g
    have outer := embDomain_coeff (f := e.symm.toOrderEmbedding)
      (x := embDomain e.toOrderEmbedding x) (a := e g)
    have inner := embDomain_coeff (f := e.toOrderEmbedding) (x := x) (a := g)
    simpa using outer.trans inner
  right_inv x := by
    ext h
    have outer := embDomain_coeff (f := e.toOrderEmbedding)
      (x := embDomain e.symm.toOrderEmbedding x) (a := e.symm h)
    have inner := embDomain_coeff (f := e.symm.toOrderEmbedding) (x := x) (a := h)
    simpa using outer.trans inner
  map_add' := embDomain_add e.toOrderEmbedding

@[simp]
theorem coeff_embDomainAddEquiv (e : G ≃o H) (x : R⟦G⟧) (g : G) :
    (embDomainAddEquiv e x).coeff (e g) = x.coeff g :=
  embDomain_coeff

end Reindex

section OrderType

variable {R : Type v} {G H : Type u}
variable [LinearOrder G] [LinearOrder H] [AddMonoid R]

/-- Reindexing along an order isomorphism preserves ordinary support order type. -/
@[simp]
theorem supportOrderType_embDomainAddEquiv (e : G ≃o H) (x : R⟦G⟧) :
    (embDomainAddEquiv e x).supportOrderType = x.supportOrderType := by
  rw [supportOrderType_eq_setOrderType, supportOrderType_eq_setOrderType]
  let : WellFoundedLT x.support := x.isWF_support
  let supportEquiv : (embDomainAddEquiv e x).support ≃o x.support :=
    (Set.orderIsoOfEq _ (e '' x.support) (support_embDomain e.toOrderEmbedding x)).trans
      (StrictMonoOn.orderIso e x.support (e.strictMono.strictMonoOn x.support)).symm
  exact (embDomainAddEquiv e x).isPWO_support.orderType_eq_typeLT_of_orderIso supportEquiv |>.trans
    (x.isPWO_support.orderType_eq_typeLT_of_orderIso (OrderIso.refl x.support)).symm

end OrderType

section Translation

variable {R : Type v} {G : Type u}
variable [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [AddMonoid R]

/-- Translate every exponent in a Hahn series by `a`. -/
def translate (a : G) : R⟦G⟧ ≃+ R⟦G⟧ :=
  embDomainAddEquiv (OrderIso.addLeft a)

theorem coeff_translate_add (a g : G) (x : R⟦G⟧) :
    (translate a x).coeff (a + g) = x.coeff g :=
  coeff_embDomainAddEquiv _ _ _

/-- Translation evaluates at `g` by reading the original coefficient at `g - a`. -/
@[simp]
theorem coeff_translate (a g : G) (x : R⟦G⟧) :
    (translate a x).coeff g = x.coeff (g - a) := by
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    coeff_translate_add a (g - a) x

/-- The support of a translated Hahn series is the corresponding translate of its support. -/
theorem support_translate (a : G) (x : R⟦G⟧) :
    (translate a x).support = (a + ·) '' x.support :=
  support_embDomain _ _

@[simp]
theorem translate_zero_apply (x : R⟦G⟧) : translate 0 x = x := by
  ext g
  simp

@[simp]
theorem translate_add_apply (a b : G) (x : R⟦G⟧) :
    translate a (translate b x) = translate (a + b) x := by
  ext g
  simp [sub_sub]

theorem translate_neg_apply (a : G) (x : R⟦G⟧) :
    translate (-a) (translate a x) = x := by
  rw [translate_add_apply, neg_add_cancel, translate_zero_apply]

end Translation

section TranslationOrderType

variable {R : Type v} {G : Type u}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [AddMonoid R]

/-- Translation preserves ordinary support order type. -/
@[simp]
theorem supportOrderType_translate (a : G) (x : R⟦G⟧) :
    (translate a x).supportOrderType = x.supportOrderType :=
  supportOrderType_embDomainAddEquiv (R := R) _ _

/-- Translation preserves LM24 degree. -/
@[simp]
theorem degree_translate (a : G) (x : R⟦G⟧) :
    (translate a x).degree = x.degree := by
  rw [degree_eq_cantorDegree, supportOrderType_translate, ← degree_eq_cantorDegree]

/-- Weak lower truncation commutes with translation after shifting the cutoff. -/
theorem truncLE_translate (a c : G) (x : R⟦G⟧) :
    truncLE c (translate a x) = translate a (truncLE (c - a) x) := by
  ext g
  simp only [HahnSeries.coeff_truncLE, coeff_translate]
  by_cases hgc : g ≤ c
  · have hsub : g - a ≤ c - a := sub_le_sub_right hgc a
    simp [hgc, hsub]
  · have hsub : ¬g - a ≤ c - a := fun h ↦ hgc ((sub_le_sub_iff_right a).mp h)
    simp [hgc, hsub]

end TranslationOrderType

section Monomial

variable {R : Type v} {G : Type u}
variable [PartialOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [Semiring R]

/-- Left multiplication by the coefficient-one monomial at `a` translates exponents by `a`. -/
theorem single_one_mul_eq_translate (a : G) (x : R⟦G⟧) :
    single a 1 * x = translate a x := by
  ext g
  rw [coeff_single_mul, coeff_translate, one_mul]

/-- Right multiplication by the coefficient-one monomial at `a` translates exponents by `a`. -/
theorem mul_single_one_eq_translate (x : R⟦G⟧) (a : G) :
    x * single a 1 = translate a x := by
  ext g
  rw [coeff_mul_single, coeff_translate, mul_one]

/-- The product of two translated Hahn series is the translate of their product by the sum of
the two shifts. -/
theorem translate_mul_translate (a b : G) (x y : R⟦G⟧) :
    translate a x * translate b y = translate (a + b) (x * y) := by
  calc
    translate a x * translate b y =
        (single a 1 * x) * (single b 1 * y) := by
      rw [single_one_mul_eq_translate, single_one_mul_eq_translate]
    _ = single a 1 * (x * single b 1) * y := by simp only [mul_assoc]
    _ = single a 1 * translate b x * y := by
      rw [mul_single_one_eq_translate x b]
    _ = single a 1 * (single b 1 * x) * y := by
      rw [single_one_mul_eq_translate b x]
    _ = (single a 1 * single b 1) * (x * y) := by simp only [mul_assoc]
    _ = single (a + b) 1 * (x * y) := by rw [single_mul_single, one_mul]
    _ = translate (a + b) (x * y) := single_one_mul_eq_translate _ _

end Monomial

end HahnSeries
