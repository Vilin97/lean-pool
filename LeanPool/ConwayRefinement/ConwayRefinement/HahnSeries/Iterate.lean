/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.HahnSeries.Cardinal
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Iterated Hahn series as Hahn series on a lexicographic product

Mathlib's `HahnSeries.iterateEquiv` identifies an iterated Hahn series with a Hahn series whose
exponent group is a lexicographic product, but provides only an equivalence of the underlying
types. This file proves that flattening preserves addition and multiplication and packages the
identification as a ring equivalence.

The outer exponent is the dominant coordinate. Multiplicativity reindexes the nested finite sums
over the outer and inner additive antidiagonals by the single additive antidiagonal in the
lexicographic product.
-/

public section

namespace HahnSeries

open Finset

variable {R Γ Γ' : Type*}
variable [Semiring R]
variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
variable [AddCommMonoid Γ'] [LinearOrder Γ'] [IsOrderedCancelAddMonoid Γ']

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [AddCommMonoid Γ'] [IsOrderedCancelAddMonoid Γ'] in
private theorem ofIterate_add (x y : R⟦Γ'⟧⟦Γ⟧) :
    ofIterate (x + y) = ofIterate x + ofIterate y := by
  ext g
  simp [ofIterate]

private theorem ofIterate_mul (x y : R⟦Γ'⟧⟦Γ⟧) :
    ofIterate (x * y) = ofIterate x * ofIterate y := by
  ext g
  rcases g with ⟨g, g'⟩
  simp only [ofIterate, coeff_mul]
  rw [coeff_sum]
  simp only [coeff_mul]
  rw [Finset.sum_sigma']
  apply Finset.sum_bij
      (fun z _ ↦ (toLex (z.1.1, z.2.1), toLex (z.1.2, z.2.2)))
  · intro z hz
    rw [Finset.mem_sigma] at hz
    rw [Finset.mem_addAntidiagonal] at hz
    rw [Finset.mem_addAntidiagonal] at hz
    rw [Finset.mem_addAntidiagonal]
    exact ⟨hz.2.1, hz.2.2.1, Prod.ext hz.1.2.2 hz.2.2.2⟩
  · intro z₁ hz₁ z₂ hz₂ heq
    have hbase : z₁.1 = z₂.1 :=
      Prod.ext (congrArg (fun z ↦ (ofLex z.1).1) heq)
        (congrArg (fun z ↦ (ofLex z.2).1) heq)
    have hfiber : z₁.2 = z₂.2 :=
      Prod.ext (congrArg (fun z ↦ (ofLex z.1).2) heq)
        (congrArg (fun z ↦ (ofLex z.2).2) heq)
    exact Sigma.ext hbase (heq_of_eq hfiber)
  · intro z hz
    rw [Finset.mem_addAntidiagonal] at hz
    refine ⟨⟨((ofLex z.1).1, (ofLex z.2).1), ((ofLex z.1).2, (ofLex z.2).2)⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma, Finset.mem_addAntidiagonal, Finset.mem_addAntidiagonal]
      exact ⟨⟨ne_zero_of_coeff_ne_zero hz.1, ne_zero_of_coeff_ne_zero hz.2.1,
        congrArg Prod.fst hz.2.2⟩, hz.1, hz.2.1, congrArg Prod.snd hz.2.2⟩
    · rfl
  · intro z hz
    rfl

/-- The equivalence between iterated Hahn series and Hahn series on the lexicographic product,
as a ring equivalence. The outer exponent is the dominant coordinate. -/
noncomputable def iterateRingEquiv : R⟦Γ'⟧⟦Γ⟧ ≃+* R⟦Γ ×ₗ Γ'⟧ :=
  { iterateEquiv with
    map_add' := ofIterate_add
    map_mul' := ofIterate_mul }

@[simp]
theorem iterateRingEquiv_coeff (x : R⟦Γ'⟧⟦Γ⟧) (g : Γ) (g' : Γ') :
    (iterateRingEquiv x).coeff (toLex (g, g')) = (x.coeff g).coeff g' := (rfl)

section Cardinal

open Cardinal

universe u v

variable {S : Type v} {Λ Λ' : Type u}
variable [Semiring S]
variable [AddCommMonoid Λ] [LinearOrder Λ] [IsOrderedCancelAddMonoid Λ]
variable [AddCommMonoid Λ'] [LinearOrder Λ'] [IsOrderedCancelAddMonoid Λ']

/-- The outer support of an iterated Hahn series is no larger than the support of its
flattening. -/
theorem cardSupp_outer_le_cardSupp_iterateRingEquiv (x : S⟦Λ'⟧⟦Λ⟧) :
    x.cardSupp ≤ (iterateRingEquiv x).cardSupp := by
  rw [cardSupp, cardSupp]
  let f : (Λ ×ₗ Λ') → Λ := fun p ↦ (ofLex p).1
  have hsubset : x.support ⊆ f '' (iterateRingEquiv x).support := by
    intro g hg
    have hg0 : x.coeff g ≠ 0 := (mem_support x g).mp hg
    have hfun : (x.coeff g).coeff ≠ 0 := coeff_fun_eq_zero_iff.not.mpr hg0
    obtain ⟨g', hg'⟩ := Function.ne_iff.mp hfun
    refine ⟨toLex (g, g'), ?_, rfl⟩
    rw [mem_support, iterateRingEquiv_coeff]
    exact hg'
  exact (Cardinal.mk_le_mk_of_subset hsubset).trans Cardinal.mk_image_le

/-- Each coefficient support of an iterated Hahn series is no larger than the support of its
flattening. -/
theorem cardSupp_coeff_le_cardSupp_iterateRingEquiv (x : S⟦Λ'⟧⟦Λ⟧) (g : Λ) :
    (x.coeff g).cardSupp ≤ (iterateRingEquiv x).cardSupp := by
  rw [cardSupp, cardSupp]
  let f : Λ' → (Λ ×ₗ Λ') := fun g' ↦ toLex (g, g')
  have hsubset : f '' (x.coeff g).support ⊆ (iterateRingEquiv x).support := by
    rintro _ ⟨g', hg', rfl⟩
    rw [mem_support, iterateRingEquiv_coeff]
    exact (mem_support (x.coeff g) g').mp hg'
  have hf : Function.Injective f := by
    intro a b h
    exact congrArg (fun p : Λ ×ₗ Λ' ↦ (ofLex p).2) h
  rw [← Cardinal.mk_image_eq hf]
  exact Cardinal.mk_le_mk_of_subset hsubset

/-- If `κ` is regular, flattening preserves the bound `< κ` when both the outer support and
all coefficient supports satisfy that bound. -/
theorem cardSupp_iterateRingEquiv_lt_of_isRegular {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) (x : S⟦Λ'⟧⟦Λ⟧) (houter : x.cardSupp < κ)
    (hcoeff : ∀ g, (x.coeff g).cardSupp < κ) :
    (iterateRingEquiv x).cardSupp < κ := by
  let t : ↥x.support → Set (Λ ×ₗ Λ') := fun g ↦
    (fun g' ↦ toLex (g.1, g')) '' (x.coeff g.1).support
  have hsupport : (iterateRingEquiv x).support = ⋃ g, t g := by
    ext p
    constructor
    · intro hp
      have hp' : (x.coeff (ofLex p).1).coeff (ofLex p).2 ≠ 0 := by
        have hpCoeff := (mem_support _ _).mp hp
        rw [show p = toLex ((ofLex p).1, (ofLex p).2) by simp] at hpCoeff
        rwa [iterateRingEquiv_coeff] at hpCoeff
      have hg : (ofLex p).1 ∈ x.support := by
        rw [mem_support]
        exact ne_zero_of_coeff_ne_zero hp'
      rw [Set.mem_iUnion]
      refine ⟨⟨(ofLex p).1, hg⟩, ?_⟩
      exact ⟨(ofLex p).2, (mem_support _ _).mpr hp', by simp⟩
    · rw [Set.mem_iUnion]
      rintro ⟨g, b, hb, rfl⟩
      rw [mem_support, iterateRingEquiv_coeff]
      exact (mem_support _ _).mp hb
  rw [cardSupp, hsupport]
  apply (Cardinal.card_iUnion_lt_iff_forall_of_isRegular hκ houter).mpr
  intro g
  let f : Λ' → (Λ ×ₗ Λ') := fun g' ↦ toLex (g.1, g')
  have hf : Function.Injective f := by
    intro a b h
    exact congrArg (fun p : Λ ×ₗ Λ' ↦ (ofLex p).2) h
  rw [show t g = f '' (x.coeff g.1).support from rfl, Cardinal.mk_image_eq hf]
  exact hcoeff g.1

end Cardinal

end HahnSeries
