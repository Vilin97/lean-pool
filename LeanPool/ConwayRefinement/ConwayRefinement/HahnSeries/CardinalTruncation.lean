/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.PrimalPreimage
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import LeanPool.ConwayRefinement.ConwayRefinement.Order.Archimedean
public import Mathlib.RingTheory.HahnSeries.Cardinal
public import Mathlib.SetTheory.Cardinal.Cofinality.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Cardinal-bounded Hahn truncation integer parts

This file models the support-cardinality bound in the Hahn fields `K((G))_κ` used by LM24.
It intersects the nonpositive-support and constant-coefficient conditions with Mathlib's subfield
of series having fewer than `κ` terms.

The fraction-subring lemmas isolate the two nonzero-class alternatives in LM24, assumption
`(A2)_σ`. If `κ ≤ cof(G)`, a support of cardinality less than `κ` is not cofinal, so a
monomial shift supplies a denominator in the truncation integer part. If `G = {0}`, the same
conclusion follows exactly when the coefficient subring has fraction subring equal to the whole
coefficient field.
-/

universe u v

public noncomputable section

open Cardinal

namespace HahnSeries

variable {G : Type u} {R : Type v} {κ : Cardinal.{u}}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field R]

/-- A Hahn series over an Archimedean exponent group has countable support. -/
theorem cardSupp_le_aleph0_of_archimedean [Archimedean G] (x : R⟦G⟧) :
    x.cardSupp ≤ ℵ₀ := by
  rw [cardSupp, Cardinal.le_aleph0_iff_set_countable]
  exact x.isPWO_support.countable_of_archimedean

variable [Fact (ℵ₀ < κ)]

/-- The field of Hahn series with fewer than `κ` support terms. -/
abbrev CardSuppLTField := ↥(cardSuppLTSubfield G R κ)

/-- The `κ`-bounded nonpositive Hahn series whose coefficient at zero belongs to `Z`. -/
def cardSuppLTTruncationIntegerPart (Z : Subring R) : Subring (CardSuppLTField (G := G) (R := R)
    (κ := κ)) where
  carrier x := (x : R⟦G⟧).support ⊆ Set.Iic 0 ∧ (x : R⟦G⟧).coeff 0 ∈ Z
  zero_mem' := by
    constructor
    · simp
    · simp
  one_mem' := by
    constructor
    · intro g hg
      have hg0 : g = 0 := support_single_subset hg
      simp [hg0]
    · simp
  add_mem' := fun {x y} hx hy => by
    constructor
    · intro g hg
      rcases support_add_subset (x : R⟦G⟧) (y : R⟦G⟧) hg with hg | hg
      · exact hx.1 hg
      · exact hy.1 hg
    · change (((x : R⟦G⟧) + (y : R⟦G⟧)).coeff 0) ∈ Z
      rw [coeff_add]
      exact Z.add_mem hx.2 hy.2
  neg_mem' := fun {x} hx => by
    constructor
    · exact (support_neg_subset (x : R⟦G⟧)).trans hx.1
    · change ((-(x : R⟦G⟧)).coeff 0) ∈ Z
      rw [coeff_neg]
      exact Z.neg_mem hx.2
  mul_mem' := fun {x y} hx hy => by
    constructor
    · intro g hg
      obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hg
      exact add_nonpos (hx.1 hi) (hy.1 hj)
    · let x' : Nonpositive G R := ⟨x, hx.1⟩
      let y' : Nonpositive G R := ⟨y, hy.1⟩
      change (((x' : R⟦G⟧) * (y' : R⟦G⟧)).coeff 0) ∈ Z
      rw [Nonpositive.coeff_zero_mul]
      exact Z.mul_mem hx.2 hy.2

/-- Membership in the `κ`-bounded truncation integer part. -/
@[simp]
theorem mem_cardSuppLTTruncationIntegerPart {Z : Subring R} {x : CardSuppLTField (G := G) (R := R)
    (κ := κ)} :
    x ∈ cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z ↔
      (x : R⟦G⟧).support ⊆ Set.Iic 0 ∧ (x : R⟦G⟧).coeff 0 ∈ Z :=
  Iff.rfl

namespace CardSuppLTTruncationIntegerPart

/-- Forget the cardinal bound while retaining the nonpositive-support witness. -/
def toNonpositiveRingHom (Z : Subring R) :
    cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z →+*
      Nonpositive G R where
  toFun x := ⟨x, x.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Forgetting the bound and then coercing to a Hahn series preserves the underlying series. -/
@[simp]
theorem coe_toNonpositiveRingHom (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    (toNonpositiveRingHom Z x : R⟦G⟧) = (x : CardSuppLTField (G := G) (R := R) (κ := κ)) :=
  (rfl)

/-- Forgetting the cardinal bound is injective. -/
theorem toNonpositiveRingHom_injective (Z : Subring R) :
    Function.Injective (toNonpositiveRingHom (G := G) (R := R) (κ := κ) Z) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  have hraw := congrArg (fun q : Nonpositive G R ↦ (q : R⟦G⟧)) hxy
  simpa only [coe_toNonpositiveRingHom] using hraw

/-- Forgetting the bound retains the proof that the support has cardinality less than `κ`. -/
theorem cardSupp_toNonpositiveRingHom_lt (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    (toNonpositiveRingHom Z x : R⟦G⟧).cardSupp < κ := by
  rw [coe_toNonpositiveRingHom]
  exact (mem_cardSuppLTSubfield (Γ := G) (R := R) (κ := κ)).mp x.1.2

/-- Forget the cardinal bound on a bounded truncation-integer-part element. -/
def toTruncationIntegerPartRingHom (Z : Subring R) :
    cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z →+*
      truncationIntegerPart G Z where
  toFun x := ⟨toNonpositiveRingHom Z x,
    (mem_truncationIntegerPart (R := R) (Γ := G)).mpr x.2.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Forgetting the bound preserves the underlying nonpositive Hahn series. -/
@[simp]
theorem coe_toTruncationIntegerPartRingHom (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    (toTruncationIntegerPartRingHom Z x : Nonpositive G R) = toNonpositiveRingHom Z x :=
  (rfl)

/-- Forgetting the cardinal bound on a truncation integer part is injective. -/
theorem toTruncationIntegerPartRingHom_injective (Z : Subring R) :
    Function.Injective
      (toTruncationIntegerPartRingHom (G := G) (R := R) (κ := κ) Z) := by
  intro x y hxy
  apply toNonpositiveRingHom_injective Z
  have h := congrArg (fun q : truncationIntegerPart G Z ↦ (q : Nonpositive G R)) hxy
  simpa only [coe_toTruncationIntegerPartRingHom] using h

end CardSuppLTTruncationIntegerPart

/-- If `κ ≤ cof(G)`, the `κ`-bounded truncation integer part has the whole bounded Hahn
field as its fraction subring. -/
@[blueprint "thm:bounded-hahn-integer-part-fraction-field"
  (phase := "Finitely many Archimedean classes")
  (title := "Fraction fields of bounded Hahn integer parts")
  (statement := /--
    Let $G$ be an ordered abelian group, let $K$ be a field, and let
    $\kappa>\aleph_0$.  If $\kappa\le\operatorname{cof}(G)$, then the bounded
    Hahn field $K((G))_\kappa$ is the fraction field of
    $Z+K((G^{<0}))_\kappa$ for every subring $Z\subseteq K$.
  -/)
  (proof := /--
    The support of a series in $K((G))_\kappa$ has cardinality less than
    $\kappa$, so it is not cofinal in $G$.  Choose an upper bound $x$ for the
    support and put $u=\max\{x,0\}$.  Multiplication by $t^{-u}$ moves the
    support strictly below zero and gives constant coefficient zero.  Thus
    both $t^{-u}$ and $t^{-u}b$ belong to the bounded Hahn integer part, and
    $b=(t^{-u}b)/t^{-u}$.
  -/)]
theorem fracSubring_cardSuppLTTruncationIntegerPart_eq_top_of_le_cof (Z : Subring R)
    (hcof : κ ≤ Order.cof G) :
    Subring.fracSubring
      (cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) = ⊤ := by
  apply top_unique
  intro b _
  have hsnot : ¬ IsCofinal (b : R⟦G⟧).support := by
    intro hs
    have hκcard : κ ≤ #(b : R⟦G⟧).support :=
      (Order.le_cof_iff.mp hcof) _ hs
    exact (not_lt_of_ge hκcard) b.2
  obtain ⟨x, hx⟩ := not_isCofinal_iff.mp hsnot
  let u : G := max x 0
  let d0 : R⟦G⟧ := single (-u) 1
  have hdcard : d0.cardSupp < κ :=
    (cardSupp_single_le (-u) (1 : R)).trans_lt
      (one_lt_aleph0.trans (Fact.out : ℵ₀ < κ))
  let d : CardSuppLTField (G := G) (R := R) (κ := κ) := ⟨d0, hdcard⟩
  have hdu : -u ≤ 0 := neg_nonpos.mpr (le_max_right x 0)
  have hdmem : d ∈ cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z := by
    rw [mem_cardSuppLTTruncationIntegerPart]
    constructor
    · intro g hg
      have hg' : g ∈ (single (-u) (1 : R)).support := by
        simpa [d, d0] using hg
      have hg_eq : g = -u := by
        exact eq_of_mem_support_single hg'
      rw [hg_eq]
      exact hdu
    · by_cases hu : u = 0
      · simp [d, d0, hu]
      · have hnu : -u ≠ 0 := neg_ne_zero.mpr hu
        have hzero : (single (-u) (1 : R)).coeff 0 = 0 :=
          coeff_single_of_ne (Ne.symm hnu)
        simp [d, d0, hzero]
  let a0 : R⟦G⟧ := d0 * (b : R⟦G⟧)
  have hacard : a0.cardSupp < κ :=
    (cardSupp_single_mul_le (b : R⟦G⟧) (-u) (1 : R)).trans_lt b.2
  let a : CardSuppLTField (G := G) (R := R) (κ := κ) := ⟨a0, hacard⟩
  have hamem : a ∈ cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z := by
    rw [mem_cardSuppLTTruncationIntegerPart]
    constructor
    · intro g hg
      have hcoeff : (b : R⟦G⟧).coeff (g + u) ≠ 0 := by
        simpa [a, a0, d0, coeff_single_mul, sub_eq_add_neg] using hg
      have hlt : g + u < x := hx _ hcoeff
      have hxu : x ≤ u := le_max_left x 0
      have hxu' : x ≤ 0 + u := by simpa using hxu
      have hgu : g + u < 0 + u := hlt.trans_le hxu'
      simpa using hgu.le
    · have : (a0.coeff 0) = (b : R⟦G⟧).coeff u := by
        simp [a0, d0, coeff_single_mul, sub_eq_add_neg]
      rw [this]
      have hnot : u ∉ (b : R⟦G⟧).support := by
        intro humem
        have := hx u humem
        exact (not_lt_of_ge (le_max_left x 0)) this
      have hzero : (b : R⟦G⟧).coeff u = 0 := by
        simpa [mem_support] using hnot
      rw [hzero]
      exact Z.zero_mem
  have hdF : d ∈ Subring.fracSubring
      (cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :=
    Subring.le_fracSubring hdmem
  have haF : a ∈ Subring.fracSubring
      (cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :=
    Subring.le_fracSubring hamem
  have hd0 : d ≠ 0 := by
    intro h
    have := congrArg (fun z : CardSuppLTField (G := G) (R := R) (κ := κ) =>
      (z : R⟦G⟧).coeff (-u)) h
    simp [d, d0] at this
  have hba : a = d * b := rfl
  rw [show b = a * d⁻¹ by rw [hba, mul_comm d b, mul_inv_cancel_right₀ hd0]]
  exact (Subring.fracSubring _).mul_mem haF (Subring.inv_mem_fracSubring hdF)

/-- For the zero exponent group, a coefficient-level fraction-subring equality lifts to the
`κ`-bounded Hahn truncation integer part. -/
theorem fracSubring_cardSuppLTTruncationIntegerPart_eq_top_of_subsingleton (Z : Subring R)
    [Subsingleton G] (hfrac : Subring.fracSubring Z = ⊤) :
    Subring.fracSubring
      (cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) = ⊤ := by
  apply top_unique
  intro b _
  let r : R := (b : R⟦G⟧).coeff 0
  have hrF : r ∈ Subring.fracSubring Z := by
    rw [hfrac]
    trivial
  obtain ⟨z, hzZ, hz0, hzrZ⟩ := Subring.exists_den hrF
  let d0 : R⟦G⟧ := single 0 z
  have hdcard : d0.cardSupp < κ :=
    (cardSupp_single_le (0 : G) z).trans_lt
      (one_lt_aleph0.trans (Fact.out : ℵ₀ < κ))
  let d : CardSuppLTField (G := G) (R := R) (κ := κ) := ⟨d0, hdcard⟩
  have hdmem : d ∈ cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z := by
    rw [mem_cardSuppLTTruncationIntegerPart]
    constructor
    · intro g hg
      have hg_eq : g = 0 := Subsingleton.elim _ _
      simp [hg_eq]
    · simpa [d, d0] using hzZ
  let a0 : R⟦G⟧ := single 0 (z * r)
  have hacard : a0.cardSupp < κ :=
    (cardSupp_single_le (0 : G) (z * r)).trans_lt
      (one_lt_aleph0.trans (Fact.out : ℵ₀ < κ))
  let a : CardSuppLTField (G := G) (R := R) (κ := κ) := ⟨a0, hacard⟩
  have hamem : a ∈ cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z := by
    rw [mem_cardSuppLTTruncationIntegerPart]
    constructor
    · intro g hg
      have hg_eq : g = 0 := Subsingleton.elim _ _
      simp [hg_eq]
    · simpa [a, a0] using hzrZ
  have hbC : (b : R⟦G⟧) = single 0 r := by
    ext g
    have hg : g = 0 := Subsingleton.elim _ _
    subst g
    simp [r]
  have hdF : d ∈ Subring.fracSubring
      (cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :=
    Subring.le_fracSubring hdmem
  have haF : a ∈ Subring.fracSubring
      (cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :=
    Subring.le_fracSubring hamem
  have hd0 : d ≠ 0 := by
    intro h
    have := congrArg (fun w : CardSuppLTField (G := G) (R := R) (κ := κ) =>
      (w : R⟦G⟧).coeff 0) h
    simp [d, d0, hz0] at this
  have hba : a = d * b := by
    apply Subtype.ext
    change a0 = d0 * (b : R⟦G⟧)
    rw [hbC]
    simp [a0, d0]
  rw [show b = a * d⁻¹ by rw [hba, mul_comm d b, mul_inv_cancel_right₀ hd0]]
  exact (Subring.fracSubring _).mul_mem haF (Subring.inv_mem_fracSubring hdF)

end HahnSeries
