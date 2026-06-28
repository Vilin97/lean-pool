/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.QuotientKernel

/-!
# Finite product quotients

This file lifts the quotient/fiber contract from one observation space to
product-space targets.  This is the generic shape behind retrieval-style
targets: a target may depend on a left object and a right object, while the
compressed observation is the product of independently compressed codes.

The ranking section adds a comparison observation with one left item and two
right items.  It proves that a score factoring through a pair product quotient
induces a pairwise ordering rule factoring through the corresponding comparison
quotient.
-/

namespace OrdvecFormalization

/-! ## Product quotients -/

/-- Product map induced by two quotient maps. -/
def productMap {Ω₁ Ω₂ Z₁ Z₂ : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    Ω₁ × Ω₂ → Z₁ × Z₂ :=
  Prod.map Q₁ Q₂

@[simp]
theorem productMap_apply {Ω₁ Ω₂ Z₁ Z₂ : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) (x : Ω₁ × Ω₂) :
    productMap Q₁ Q₂ x = (Q₁ x.1, Q₂ x.2) :=
  rfl

theorem productMap_eq_iff {Ω₁ Ω₂ Z₁ Z₂ : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (x₁ x₂ : Ω₁ × Ω₂) :
    productMap Q₁ Q₂ x₁ = productMap Q₁ Q₂ x₂ ↔
      Q₁ x₁.1 = Q₁ x₂.1 ∧ Q₂ x₁.2 = Q₂ x₂.2 := by
  cases x₁
  cases x₂
  simp [productMap, Prod.map]

/--
A product target is invariant on product quotient fibers when same left code
and same right code force the same target value.
-/
def ProductFiberInvariant {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (target : Ω₁ × Ω₂ → A) : Prop :=
  ∀ ⦃x₁ x₂ : Ω₁⦄ ⦃y₁ y₂ : Ω₂⦄,
    Q₁ x₁ = Q₁ x₂ →
    Q₂ y₁ = Q₂ y₂ →
    target (x₁, y₁) = target (x₂, y₂)

/-- Product fiber invariance is exactly kernel containment for `productMap`. -/
theorem kernelContainedInTarget_productMap_iff_productFiberInvariant
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (target : Ω₁ × Ω₂ → A) :
    KernelContainedInTarget (productMap Q₁ Q₂) target ↔
      ProductFiberInvariant Q₁ Q₂ target := by
  constructor
  · intro hker x₁ x₂ y₁ y₂ h₁ h₂
    exact hker (Prod.ext h₁ h₂)
  · intro hinv p₁ p₂ hker
    rcases p₁ with ⟨x₁, y₁⟩
    rcases p₂ with ⟨x₂, y₂⟩
    exact hinv (congrArg Prod.fst hker) (congrArg Prod.snd hker)

/-- A target factoring through a product quotient is invariant on product fibers. -/
theorem ruleFactorsThrough_product_fiberInvariant
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (target : Ω₁ × Ω₂ → A)
    (h : RuleFactorsThrough (productMap Q₁ Q₂) target) :
    ProductFiberInvariant Q₁ Q₂ target := by
  exact (kernelContainedInTarget_productMap_iff_productFiberInvariant
    Q₁ Q₂ target).mp (ruleFactorsThrough_fiberInvariant
      (productMap Q₁ Q₂) target h)

/-- Under surjectivity, product fiber invariance builds a product quotient rule. -/
theorem productFiberInvariant_ruleFactorsThrough_of_surjective
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (target : Ω₁ × Ω₂ → A)
    (h₁ : Function.Surjective Q₁)
    (h₂ : Function.Surjective Q₂)
    (hinv : ProductFiberInvariant Q₁ Q₂ target) :
    RuleFactorsThrough (productMap Q₁ Q₂) target := by
  refine ⟨fun z =>
    target (Classical.choose (h₁ z.1), Classical.choose (h₂ z.2)), ?_⟩
  intro p
  rcases p with ⟨x, y⟩
  have hx : Q₁ (Classical.choose (h₁ (Q₁ x))) = Q₁ x :=
    Classical.choose_spec (h₁ (Q₁ x))
  have hy : Q₂ (Classical.choose (h₂ (Q₂ y))) = Q₂ y :=
    Classical.choose_spec (h₂ (Q₂ y))
  exact (hinv hx hy).symm

/--
Factoring through the reachable image of a product map is exactly product fiber
invariance.  This avoids any surjectivity claim about the full ambient product
codomain.
-/
theorem ruleFactorsThrough_productMap_image_iff_productFiberInvariant
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (target : Ω₁ × Ω₂ → A) :
    RuleFactorsThrough (imageQuotient (productMap Q₁ Q₂)) target ↔
      ProductFiberInvariant Q₁ Q₂ target := by
  rw [ruleFactorsThrough_image_iff_kernelContainedInTarget,
    kernelContainedInTarget_productMap_iff_productFiberInvariant]

/--
A product-factorized target gives a right-space quotient rule at every fixed
left input.
-/
theorem ruleFactorsThrough_product_fixedLeft
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (target : Ω₁ × Ω₂ → A)
    (h : RuleFactorsThrough (productMap Q₁ Q₂) target)
    (x : Ω₁) :
    RuleFactorsThrough Q₂ (fun y : Ω₂ => target (x, y)) := by
  rcases h with ⟨targetQ, htarget⟩
  refine ⟨fun z₂ => targetQ (Q₁ x, z₂), ?_⟩
  intro y
  exact htarget (x, y)

/--
A product-factorized target gives a left-space quotient rule at every fixed
right input.
-/
theorem ruleFactorsThrough_product_fixedRight
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (target : Ω₁ × Ω₂ → A)
    (h : RuleFactorsThrough (productMap Q₁ Q₂) target)
    (y : Ω₂) :
    RuleFactorsThrough Q₁ (fun x : Ω₁ => target (x, y)) := by
  rcases h with ⟨targetQ, htarget⟩
  refine ⟨fun z₁ => targetQ (z₁, Q₂ y), ?_⟩
  intro x
  exact htarget (x, y)

/-! ## Product samples and finite falsifiers -/

/-- A finite product sample has no same-product-code label contradictions. -/
def ProductSampleConsistent {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (label : Ω₁ × Ω₂ → A) (sample : Finset (Ω₁ × Ω₂)) : Prop :=
  ∀ ⦃p₁ p₂ : Ω₁ × Ω₂⦄,
    p₁ ∈ sample →
    p₂ ∈ sample →
    Q₁ p₁.1 = Q₁ p₂.1 →
    Q₂ p₁.2 = Q₂ p₂.2 →
    label p₁ = label p₂

/-- Product sample consistency is the usual sample consistency for `productMap`. -/
theorem productSampleConsistent_iff_sampleConsistent_productMap
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (label : Ω₁ × Ω₂ → A) (sample : Finset (Ω₁ × Ω₂)) :
    ProductSampleConsistent Q₁ Q₂ label sample ↔
      SampleConsistent (productMap Q₁ Q₂) label sample := by
  constructor
  · intro hprod p₁ p₂ hp₁ hp₂ hcode
    exact hprod hp₁ hp₂ (congrArg Prod.fst hcode) (congrArg Prod.snd hcode)
  · intro hsample p₁ p₂ hp₁ hp₂ h₁ h₂
    exact hsample hp₁ hp₂ (Prod.ext h₁ h₂)

/-- A product-factorized target cannot contradict itself on a finite product sample. -/
theorem productSampleConsistent_of_ruleFactorsThrough
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (target : Ω₁ × Ω₂ → A) (sample : Finset (Ω₁ × Ω₂))
    (h : RuleFactorsThrough (productMap Q₁ Q₂) target) :
    ProductSampleConsistent Q₁ Q₂ target sample := by
  intro p₁ p₂ _hp₁ _hp₂ h₁ h₂
  rcases p₁ with ⟨x₁, y₁⟩
  rcases p₂ with ⟨x₂, y₂⟩
  exact ruleFactorsThrough_product_fiberInvariant Q₁ Q₂ target h h₁ h₂

/--
A finite product sample is product-consistent iff some product-quotient rule
fits it.
-/
theorem productSampleConsistent_iff_exists_productRuleFitsSample
    {Ω₁ Ω₂ Z₁ Z₂ A : Type} [Inhabited A]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (label : Ω₁ × Ω₂ → A) (sample : Finset (Ω₁ × Ω₂)) :
    ProductSampleConsistent Q₁ Q₂ label sample ↔
      ∃ ruleZ : Z₁ × Z₂ → A,
        QuotientRuleFitsSample (productMap Q₁ Q₂) label sample ruleZ := by
  rw [productSampleConsistent_iff_sampleConsistent_productMap,
    sampleConsistent_iff_exists_quotientRuleFitsSample]

/--
If two sampled product observations have the same product quotient code but
different labels, no product-quotient rule can fit the sample.
-/
theorem no_productQuotientTarget_of_sample_collision
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (label : Ω₁ × Ω₂ → A) (sample : Finset (Ω₁ × Ω₂))
    {p₁ p₂ : Ω₁ × Ω₂}
    (hp₁ : p₁ ∈ sample) (hp₂ : p₂ ∈ sample)
    (h₁ : Q₁ p₁.1 = Q₁ p₂.1)
    (h₂ : Q₂ p₁.2 = Q₂ p₂.2)
    (hlabel : label p₁ ≠ label p₂) :
    ¬ ∃ target : Ω₁ × Ω₂ → A,
      RuleFactorsThrough (productMap Q₁ Q₂) target ∧
        (∀ ⦃p : Ω₁ × Ω₂⦄, p ∈ sample → target p = label p) := by
  rintro ⟨target, hfac, hfit⟩
  have hsame : target p₁ = target p₂ := by
    rcases p₁ with ⟨x₁, y₁⟩
    rcases p₂ with ⟨x₂, y₂⟩
    exact ruleFactorsThrough_product_fiberInvariant Q₁ Q₂ target hfac h₁ h₂
  exact hlabel (by
    rw [← hfit hp₁, ← hfit hp₂]
    exact hsame)

/-! ## Product-rule and multi-target search spaces -/

/-- Observed product quotient buckets in a finite product sample. -/
abbrev ObservedProductQuotients {Ω₁ Ω₂ Z₁ Z₂ : Type}
    [DecidableEq Z₁] [DecidableEq Z₂]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (sample : Finset (Ω₁ × Ω₂)) : Finset (Z₁ × Z₂) :=
  ObservedQuotients (productMap Q₁ Q₂) sample

/-- Reachable product quotient buckets that have not appeared in a finite sample. -/
abbrev UnobservedReachableProductQuotients {Ω₁ Ω₂ Z₁ Z₂ : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (sample : Finset (Ω₁ × Ω₂)) : Type :=
  UnobservedReachableQuotients (productMap Q₁ Q₂) sample

/--
The full product-quotient rule space over ambient product codomain has size
`|A| ^ (|Z₁| * |Z₂|)`.
-/
theorem card_productQuotientRules {Z₁ Z₂ A : Type}
    [DecidableEq Z₁] [DecidableEq Z₂] [Fintype Z₁] [Fintype Z₂] [Fintype A] :
    Fintype.card (Z₁ × Z₂ → A) =
      Fintype.card A ^ (Fintype.card Z₁ * Fintype.card Z₂) := by
  rw [Fintype.card_fun, Fintype.card_prod]

/--
The reachable image of a product map is contained in the product of the two
reachable component images.
-/
theorem productMap_image_subset_product_images
    {Ω₁ Ω₂ Z₁ Z₂ : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    QuotientImageFinset (productMap Q₁ Q₂) ⊆
      (QuotientImageFinset Q₁).product (QuotientImageFinset Q₂) := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨p, _hp, hp⟩
  rw [← hp]
  exact Finset.mem_product.mpr
    ⟨Finset.mem_image.mpr ⟨p.1, Finset.mem_univ p.1, rfl⟩,
      Finset.mem_image.mpr ⟨p.2, Finset.mem_univ p.2, rfl⟩⟩

/--
The reachable image of a product map is exactly the product of the reachable
component images.
-/
theorem productMap_image_eq_product_images
    {Ω₁ Ω₂ Z₁ Z₂ : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    QuotientImageFinset (productMap Q₁ Q₂) =
      (QuotientImageFinset Q₁).product (QuotientImageFinset Q₂) := by
  apply Finset.Subset.antisymm
  · exact productMap_image_subset_product_images Q₁ Q₂
  · intro z hz
    rcases Finset.mem_product.mp hz with ⟨hz₁, hz₂⟩
    rcases Finset.mem_image.mp hz₁ with ⟨x, _hx, hx⟩
    rcases Finset.mem_image.mp hz₂ with ⟨y, _hy, hy⟩
    exact Finset.mem_image.mpr
      ⟨(x, y), Finset.mem_univ (x, y), Prod.ext hx hy⟩

/--
The number of reachable product codes is exactly the product of the numbers of
reachable component codes.
-/
theorem productMap_image_card_eq_product_images_card
    {Ω₁ Ω₂ Z₁ Z₂ : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    (QuotientImageFinset (productMap Q₁ Q₂)).card =
      (QuotientImageFinset Q₁).card * (QuotientImageFinset Q₂).card := by
  rw [productMap_image_eq_product_images Q₁ Q₂]
  simp

/--
The number of reachable product codes is bounded by the product of the numbers
of reachable component codes.
-/
theorem productMap_image_card_le_product_images_card
    {Ω₁ Ω₂ Z₁ Z₂ : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    (QuotientImageFinset (productMap Q₁ Q₂)).card ≤
      (QuotientImageFinset Q₁).card * (QuotientImageFinset Q₂).card := by
  rw [productMap_image_card_eq_product_images_card Q₁ Q₂]

/--
Rules on the reachable product image have search-space size
`|A| ^ |image(productMap Q₁ Q₂)|`.
-/
theorem card_productImageQuotientRules
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂] [Fintype A]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    Fintype.card (QuotientImageBucket (productMap Q₁ Q₂) → A) =
      Fintype.card A ^ (QuotientImageFinset (productMap Q₁ Q₂)).card := by
  exact card_quotientImageRules (productMap Q₁ Q₂)

/--
Rules on the reachable product image have search-space size
`|A| ^ (|image Q₁| * |image Q₂|)`.
-/
theorem card_productImageQuotientRules_eq_product_images
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂] [Fintype A]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    Fintype.card (QuotientImageBucket (productMap Q₁ Q₂) → A) =
      Fintype.card A ^
        ((QuotientImageFinset Q₁).card * (QuotientImageFinset Q₂).card) := by
  rw [card_productImageQuotientRules Q₁ Q₂,
    productMap_image_card_eq_product_images_card Q₁ Q₂]

/--
Product-image quotient rules are bounded by assigning labels to every
component-image pair.
-/
theorem card_productImageQuotientRules_le_product_images
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂] [Fintype A]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    Fintype.card (QuotientImageBucket (productMap Q₁ Q₂) → A) ≤
      Fintype.card A ^
        ((QuotientImageFinset Q₁).card * (QuotientImageFinset Q₂).card) := by
  rw [card_productImageQuotientRules_eq_product_images Q₁ Q₂]

namespace RuleFactorsThrough

/-- Pairing two product-factorized targets is equivalent to factoring both components. -/
theorem product_pair_iff {Ω₁ Ω₂ Z₁ Z₂ A B : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (targetA : Ω₁ × Ω₂ → A) (targetB : Ω₁ × Ω₂ → B) :
    RuleFactorsThrough (productMap Q₁ Q₂) (fun p => (targetA p, targetB p)) ↔
      RuleFactorsThrough (productMap Q₁ Q₂) targetA ∧
        RuleFactorsThrough (productMap Q₁ Q₂) targetB :=
  RuleFactorsThrough.prod_iff (productMap Q₁ Q₂) targetA targetB

end RuleFactorsThrough

namespace ProductSampleConsistent

/-- Product-sample consistency for a paired label is componentwise consistency. -/
theorem prod_iff {Ω₁ Ω₂ Z₁ Z₂ A B : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (labelA : Ω₁ × Ω₂ → A) (labelB : Ω₁ × Ω₂ → B)
    (sample : Finset (Ω₁ × Ω₂)) :
    ProductSampleConsistent Q₁ Q₂ (fun p => (labelA p, labelB p)) sample ↔
      ProductSampleConsistent Q₁ Q₂ labelA sample ∧
        ProductSampleConsistent Q₁ Q₂ labelB sample := by
  constructor
  · intro hpair
    constructor
    · intro p₁ p₂ hp₁ hp₂ h₁ h₂
      exact congrArg Prod.fst (hpair hp₁ hp₂ h₁ h₂)
    · intro p₁ p₂ hp₁ hp₂ h₁ h₂
      exact congrArg Prod.snd (hpair hp₁ hp₂ h₁ h₂)
  · rintro ⟨hA, hB⟩ p₁ p₂ hp₁ hp₂ h₁ h₂
    exact Prod.ext (hA hp₁ hp₂ h₁ h₂) (hB hp₁ hp₂ h₁ h₂)

end ProductSampleConsistent

/-! ## Comparison quotients and score-induced ranking -/

/-- A left item together with two right items, used for pairwise comparisons. -/
structure ComparisonObs (Ω₁ Ω₂ : Type) where
  /-- The left-side item, such as a query. -/
  left : Ω₁
  /-- The first right-side item in the comparison. -/
  first : Ω₂
  /-- The second right-side item in the comparison. -/
  second : Ω₂
deriving DecidableEq

/-- Finite comparison observations are equivalent to left/right/right triples. -/
def comparisonObsEquivProd (Ω₁ Ω₂ : Type) :
    ComparisonObs Ω₁ Ω₂ ≃ Ω₁ × Ω₂ × Ω₂ where
  toFun c := (c.left, c.first, c.second)
  invFun x := {
    left := x.1
    first := x.2.1
    second := x.2.2
  }
  left_inv c := by
    cases c
    rfl
  right_inv x := by
    cases x
    rfl

instance comparisonObsFintype {Ω₁ Ω₂ : Type}
    [Fintype Ω₁] [Fintype Ω₂] : Fintype (ComparisonObs Ω₁ Ω₂) :=
  Fintype.ofEquiv (Ω₁ × Ω₂ × Ω₂) (comparisonObsEquivProd Ω₁ Ω₂).symm

/-- Product quotient for a left item and two right items. -/
def comparisonMap {Ω₁ Ω₂ Z₁ Z₂ : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    ComparisonObs Ω₁ Ω₂ → ComparisonObs Z₁ Z₂ :=
  fun c => {
    left := Q₁ c.left
    first := Q₂ c.first
    second := Q₂ c.second
  }

@[simp]
theorem comparisonMap_left {Ω₁ Ω₂ Z₁ Z₂ : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) (c : ComparisonObs Ω₁ Ω₂) :
    (comparisonMap Q₁ Q₂ c).left = Q₁ c.left :=
  rfl

@[simp]
theorem comparisonMap_first {Ω₁ Ω₂ Z₁ Z₂ : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) (c : ComparisonObs Ω₁ Ω₂) :
    (comparisonMap Q₁ Q₂ c).first = Q₂ c.first :=
  rfl

@[simp]
theorem comparisonMap_second {Ω₁ Ω₂ Z₁ Z₂ : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) (c : ComparisonObs Ω₁ Ω₂) :
    (comparisonMap Q₁ Q₂ c).second = Q₂ c.second :=
  rfl

theorem comparisonMap_eq_iff {Ω₁ Ω₂ Z₁ Z₂ : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (c₁ c₂ : ComparisonObs Ω₁ Ω₂) :
    comparisonMap Q₁ Q₂ c₁ = comparisonMap Q₁ Q₂ c₂ ↔
      Q₁ c₁.left = Q₁ c₂.left ∧
        Q₂ c₁.first = Q₂ c₂.first ∧
          Q₂ c₁.second = Q₂ c₂.second := by
  cases c₁
  cases c₂
  simp [comparisonMap]

/-- A comparison target is invariant under compressed left/right/right codes. -/
def ComparisonFiberInvariant {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (target : ComparisonObs Ω₁ Ω₂ → A) : Prop :=
  ∀ ⦃c₁ c₂ : ComparisonObs Ω₁ Ω₂⦄,
    Q₁ c₁.left = Q₁ c₂.left →
    Q₂ c₁.first = Q₂ c₂.first →
    Q₂ c₁.second = Q₂ c₂.second →
    target c₁ = target c₂

/-- A comparison-factorized target is invariant on comparison quotient fibers. -/
theorem ruleFactorsThrough_comparison_fiberInvariant
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (target : ComparisonObs Ω₁ Ω₂ → A)
    (h : RuleFactorsThrough (comparisonMap Q₁ Q₂) target) :
    ComparisonFiberInvariant Q₁ Q₂ target := by
  rcases h with ⟨targetQ, htarget⟩
  intro c₁ c₂ hleft hfirst hsecond
  have hcode : comparisonMap Q₁ Q₂ c₁ = comparisonMap Q₁ Q₂ c₂ :=
    (comparisonMap_eq_iff Q₁ Q₂ c₁ c₂).mpr ⟨hleft, hfirst, hsecond⟩
  rw [htarget c₁, htarget c₂, hcode]

/-- Score-induced pairwise ordering comparison. -/
def rankByScore {Ω₁ Ω₂ S : Type}
    [LE S] [DecidableRel (fun a b : S => a ≤ b)]
    (score : Ω₁ × Ω₂ → S) :
    ComparisonObs Ω₁ Ω₂ → Bool :=
  fun c => decide (score (c.left, c.first) ≤ score (c.left, c.second))

/--
If a pair score factors through compressed left/right codes, then the
score-induced ordering comparison factors through compressed left/right/right
codes.
-/
theorem rankByScore_factorsThrough_of_score_factorsThrough
    {Ω₁ Ω₂ Z₁ Z₂ S : Type}
    [LE S] [DecidableRel (fun a b : S => a ≤ b)]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂)
    (score : Ω₁ × Ω₂ → S)
    (hscore : RuleFactorsThrough (productMap Q₁ Q₂) score) :
    RuleFactorsThrough (comparisonMap Q₁ Q₂) (rankByScore score) := by
  rcases hscore with ⟨scoreQ, hscoreQ⟩
  refine ⟨fun zc =>
    decide (scoreQ (zc.left, zc.first) ≤ scoreQ (zc.left, zc.second)), ?_⟩
  intro c
  cases c
  simp [rankByScore, comparisonMap, hscoreQ]

/-! ## Comparison image bounds -/

/--
The ambient box of reachable comparison codes induced by one left image and two
right images.
-/
def ComparisonImageBox {Ω₁ Ω₂ Z₁ Z₂ : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) : Finset (ComparisonObs Z₁ Z₂) :=
  ((QuotientImageFinset Q₁).product
      ((QuotientImageFinset Q₂).product (QuotientImageFinset Q₂))).image
    (fun z => {
      left := z.1
      first := z.2.1
      second := z.2.2
    })

/--
The reachable image of a comparison map is contained in the box of reachable
left/right/right component codes.
-/
theorem comparisonMap_image_subset_imageBox
    {Ω₁ Ω₂ Z₁ Z₂ : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    QuotientImageFinset (comparisonMap Q₁ Q₂) ⊆
      ComparisonImageBox Q₁ Q₂ := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨c, _hc, hc⟩
  rw [← hc]
  unfold ComparisonImageBox
  apply Finset.mem_image.mpr
  refine ⟨(Q₁ c.left, (Q₂ c.first, Q₂ c.second)), ?_, rfl⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_image.mpr ⟨c.left, Finset.mem_univ c.left, rfl⟩,
      Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨c.first, Finset.mem_univ c.first, rfl⟩,
          Finset.mem_image.mpr ⟨c.second, Finset.mem_univ c.second, rfl⟩⟩⟩

/--
The reachable image of a comparison map is exactly the box of reachable
left/right/right component codes.
-/
theorem comparisonMap_image_eq_imageBox
    {Ω₁ Ω₂ Z₁ Z₂ : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    QuotientImageFinset (comparisonMap Q₁ Q₂) =
      ComparisonImageBox Q₁ Q₂ := by
  apply Finset.Subset.antisymm
  · exact comparisonMap_image_subset_imageBox Q₁ Q₂
  · intro z hz
    unfold ComparisonImageBox at hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, hpz⟩
    rcases Finset.mem_product.mp hp with ⟨hzleft, hzrights⟩
    rcases Finset.mem_product.mp hzrights with ⟨hzfirst, hzsecond⟩
    rcases Finset.mem_image.mp hzleft with ⟨x, _hxmem, hx⟩
    rcases Finset.mem_image.mp hzfirst with ⟨y₁, _hy₁mem, hy₁⟩
    rcases Finset.mem_image.mp hzsecond with ⟨y₂, _hy₂mem, hy₂⟩
    apply Finset.mem_image.mpr
    refine ⟨{ left := x, first := y₁, second := y₂ }, Finset.mem_univ _, ?_⟩
    rw [← hpz]
    simp [comparisonMap, hx, hy₁, hy₂]

/--
The number of reachable comparison codes is exactly
`|image Q₁| * |image Q₂| * |image Q₂|`.
-/
theorem comparisonMap_image_card_eq_product_images_card
    {Ω₁ Ω₂ Z₁ Z₂ : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    (QuotientImageFinset (comparisonMap Q₁ Q₂)).card =
      (QuotientImageFinset Q₁).card *
        (QuotientImageFinset Q₂).card * (QuotientImageFinset Q₂).card := by
  rw [comparisonMap_image_eq_imageBox Q₁ Q₂]
  unfold ComparisonImageBox
  rw [Finset.card_image_of_injective]
  · simp [mul_assoc]
  · intro p₁ p₂ h
    exact Prod.ext (congrArg ComparisonObs.left h)
      (Prod.ext (congrArg ComparisonObs.first h)
        (congrArg ComparisonObs.second h))

/--
The number of reachable comparison codes is bounded by
`|image Q₁| * |image Q₂| * |image Q₂|`.
-/
theorem comparisonMap_image_card_le_product_images_card
    {Ω₁ Ω₂ Z₁ Z₂ : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    (QuotientImageFinset (comparisonMap Q₁ Q₂)).card ≤
      (QuotientImageFinset Q₁).card *
        (QuotientImageFinset Q₂).card * (QuotientImageFinset Q₂).card := by
  rw [comparisonMap_image_card_eq_product_images_card Q₁ Q₂]

/--
Rules on the reachable comparison image have search-space size
`|A| ^ |image(comparisonMap Q₁ Q₂)|`.
-/
theorem card_comparisonImageQuotientRules
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂] [Fintype A]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    Fintype.card (QuotientImageBucket (comparisonMap Q₁ Q₂) → A) =
      Fintype.card A ^ (QuotientImageFinset (comparisonMap Q₁ Q₂)).card := by
  exact card_quotientImageRules (comparisonMap Q₁ Q₂)

/--
Rules on the reachable comparison image have search-space size
`|A| ^ (|image Q₁| * |image Q₂| * |image Q₂|)`.
-/
theorem card_comparisonImageQuotientRules_eq_product_images
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂] [Fintype A]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    Fintype.card (QuotientImageBucket (comparisonMap Q₁ Q₂) → A) =
      Fintype.card A ^
        ((QuotientImageFinset Q₁).card *
          (QuotientImageFinset Q₂).card * (QuotientImageFinset Q₂).card) := by
  rw [card_comparisonImageQuotientRules Q₁ Q₂,
    comparisonMap_image_card_eq_product_images_card Q₁ Q₂]

/--
Comparison-image quotient rules are bounded by assigning labels to every
left/right/right component-image triple.
-/
theorem card_comparisonImageQuotientRules_le_product_images
    {Ω₁ Ω₂ Z₁ Z₂ A : Type}
    [Fintype Ω₁] [Fintype Ω₂] [DecidableEq Z₁] [DecidableEq Z₂] [Fintype A]
    (Q₁ : Ω₁ → Z₁) (Q₂ : Ω₂ → Z₂) :
    Fintype.card (QuotientImageBucket (comparisonMap Q₁ Q₂) → A) ≤
      Fintype.card A ^
        ((QuotientImageFinset Q₁).card *
          (QuotientImageFinset Q₂).card * (QuotientImageFinset Q₂).card) := by
  rw [card_comparisonImageQuotientRules_eq_product_images Q₁ Q₂]

end OrdvecFormalization
