/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.ConvexFactorSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.ConvexQuotientSplitting
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Domain
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DomainEmbedding

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SubgroupSupport

/-!
# Exponent-domain embeddings of cardinal-bounded Hahn integer parts

An additive order embedding of exponent groups induces embeddings of the cardinal-bounded Hahn
fields and their nonpositive integer parts. Restriction along the exponent embedding is a left
inverse, and a right inverse on series whose support lies in the embedding's range.
-/

open Cardinal

universe u v w

public noncomputable section

namespace HahnSeries

variable {G : Type u} {H : Type u} {R : Type v} {κ : Cardinal.{u}}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [AddCommGroup H] [LinearOrder H] [IsOrderedAddMonoid H]
variable [Field R] [Fact (aleph0 < κ)]

/-- Map a cardinal-bounded Hahn field along an injective additive order embedding. -/
def cardSuppLTFieldMapDomain (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') :
    CardSuppLTField (G := G) (R := R) (κ := κ) →+*
      CardSuppLTField (G := H) (R := R) (κ := κ) where
  toFun x := ⟨HahnSeries.embDomain (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) x, by
    rw [HahnSeries.mem_cardSuppLTSubfield, HahnSeries.cardSupp_embDomain]
    exact x.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (HahnSeries.embDomainRingHom f hfi hf)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (HahnSeries.embDomainRingHom f hfi hf) (x : R⟦G⟧) y
  map_zero' := by
    apply Subtype.ext
    exact map_zero (HahnSeries.embDomainRingHom f hfi hf)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (HahnSeries.embDomainRingHom f hfi hf) (x : R⟦G⟧) y

@[simp]
theorem coe_cardSuppLTFieldMapDomain (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g')
    (x : CardSuppLTField (G := G) (R := R) (κ := κ)) :
    (cardSuppLTFieldMapDomain f hfi hf x : R⟦H⟧) =
      HahnSeries.embDomain (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) (x : R⟦G⟧) :=
  (rfl)

/-- Map a cardinal-bounded Hahn integer part along an injective additive order embedding. -/
def CardSuppLTTruncationIntegerPart.mapDomain (f : G →+ H)
    (hfi : Function.Injective f) (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g')
    (Z : Subring R) :
    cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z →+*
      cardSuppLTTruncationIntegerPart (G := H) (R := R) (κ := κ) Z :=
  ((cardSuppLTFieldMapDomain f hfi hf).domRestrict
    (cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)).codRestrict
      (cardSuppLTTruncationIntegerPart (G := H) (R := R) (κ := κ) Z) (fun x ↦ by
        rw [mem_cardSuppLTTruncationIntegerPart]
        have hx := (mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2
        constructor
        · change (HahnSeries.embDomain
            (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) (x : R⟦G⟧)).support ⊆ Set.Iic 0
          rw [HahnSeries.support_embDomain]
          rintro _ ⟨g, hg, rfl⟩
          change f g ≤ 0
          simpa only [map_zero] using (hf g 0).mpr (hx.1 hg)
        · change (HahnSeries.embDomain
            (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) (x : R⟦G⟧)).coeff 0 ∈ Z
          have h := HahnSeries.embDomain_coeff
            (f := (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H)) (x := (x : R⟦G⟧)) (a := 0)
          have he0 : (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) 0 = 0 := f.map_zero
          rw [he0] at h
          exact h.symm ▸ hx.2
      )

@[simp]
theorem CardSuppLTTruncationIntegerPart.coe_mapDomain
    (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    (((CardSuppLTTruncationIntegerPart.mapDomain f hfi hf Z x :
      cardSuppLTTruncationIntegerPart (G := H) (R := R) (κ := κ) Z) :
        CardSuppLTField (G := H) (R := R) (κ := κ)) : R⟦H⟧) =
      HahnSeries.embDomain (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) (x : R⟦G⟧) :=
  (rfl)

/-- Restrict a cardinal-bounded Hahn integer-part element to an embedded exponent domain. -/
def CardSuppLTTruncationIntegerPart.restrictDomain
    (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := H) (R := R) (κ := κ) Z) :
    cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z := by
  let e : G ↪o H := ⟨⟨f, hfi⟩, hf _ _⟩
  let y : R⟦G⟧ := HahnSeries.restrictDomain e (x : R⟦H⟧)
  have hycard : y.cardSupp < κ := by
    rw [HahnSeries.cardSupp]
    apply (Cardinal.mk_le_of_injective (f := fun g : y.support ↦
      (⟨f g.1, by
        rw [HahnSeries.mem_support]
        have hg := (HahnSeries.mem_support _ _).mp g.2
        change (x : R⟦H⟧).coeff (e g.1) ≠ 0
        simpa only [y, HahnSeries.restrictDomain_coeff] using hg⟩ :
          (x : R⟦H⟧).support)) ?_).trans_lt x.1.2
    intro a b hab
    apply Subtype.ext
    exact hfi (congrArg Subtype.val hab)
  exact ⟨⟨y, hycard⟩, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    have hx := (mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2
    constructor
    · intro g hg
      apply (hf g 0).mp
      have hfg : f g ∈ (x : R⟦H⟧).support := by
        rw [HahnSeries.mem_support]
        have hg' := (HahnSeries.mem_support _ _).mp hg
        change (x : R⟦H⟧).coeff (e g) ≠ 0
        simpa only [y, HahnSeries.restrictDomain_coeff] using hg'
      rw [f.map_zero]
      exact hx.1 hfg
    · change y.coeff 0 ∈ Z
      rw [HahnSeries.restrictDomain_coeff]
      change (x : R⟦H⟧).coeff (f 0) ∈ Z
      rw [f.map_zero]
      exact hx.2⟩

@[simp]
theorem CardSuppLTTruncationIntegerPart.coe_restrictDomain
    (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := H) (R := R) (κ := κ) Z) :
    ((CardSuppLTTruncationIntegerPart.restrictDomain f hfi hf Z x :
      cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) : R⟦G⟧) =
      HahnSeries.restrictDomain (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) (x : R⟦H⟧) :=
  (rfl)

/-- The bundled outer-zero coefficient of convex quotient regrouping is bounded integer-part
restriction to the convex submodule. -/
theorem CardSuppLTTruncationIntegerPart.coeff_zero_convexQuotientSplitRingEquiv
    {K : Type w} [Field K] [Module K H] [Fact κ.IsRegular]
    (P : Submodule K H) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := H) (R := R) (κ := κ) Z) :
    (⟨((cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z x).1.1.coeff 0),
      ((mem_cardSuppLTTruncationIntegerPart
        (Z := cardSuppLTTruncationIntegerPart
          (G := P) (R := R) (κ := κ) Z)).mp
        (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z x).2).2⟩ :
      cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) =
      CardSuppLTTruncationIntegerPart.restrictDomain
        P.toAddSubgroup.subtype Subtype.val_injective (fun _ _ ↦ Iff.rfl) Z x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_restrictDomain]
  ext p
  have hzero :
      ((((cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z x :
        cardSuppLTTruncationIntegerPart (G := H ⧸ P)
          (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)
          (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z)) :
            CardSuppLTField (G := H ⧸ P)
              (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)).1.coeff 0 :
                CardSuppLTField (G := P) (R := R) (κ := κ)) : R⟦P⟧) =
        HahnSeries.restrictDomain (submoduleOrderEmbedding P) (x : R⟦H⟧) := by
    rw [coe_cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv]
    exact coe_coeff_zero_boundedConvexQuotientSplit P x.1
  have hp := congrArg (fun z : R⟦P⟧ ↦ z.coeff p) hzero
  rw [HahnSeries.restrictDomain_coeff] at hp ⊢
  change (↑((cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
    P Z x).1.1.coeff 0) : R⟦P⟧).coeff p = (x : R⟦H⟧).coeff (p : H)
  simpa only [submoduleOrderEmbedding_apply] using hp

@[simp]
theorem CardSuppLTTruncationIntegerPart.restrictDomain_mapDomain
    (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    CardSuppLTTruncationIntegerPart.restrictDomain f hfi hf Z
      (CardSuppLTTruncationIntegerPart.mapDomain f hfi hf Z x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  exact HahnSeries.restrictDomain_embDomain _ _

theorem CardSuppLTTruncationIntegerPart.mapDomain_restrictDomain
    (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := H) (R := R) (κ := κ) Z)
    (hx : (x : R⟦H⟧).support ⊆ Set.range f) :
    CardSuppLTTruncationIntegerPart.mapDomain f hfi hf Z
      (CardSuppLTTruncationIntegerPart.restrictDomain f hfi hf Z x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  exact HahnSeries.embDomain_restrictDomain _ _ hx

open Classical in
/-- Embedding after restriction keeps exactly the exponents in the embedding's range. -/
theorem CardSuppLTTruncationIntegerPart.coe_mapDomain_restrictDomain
    (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := H) (R := R) (κ := κ) Z) :
    ((CardSuppLTTruncationIntegerPart.mapDomain f hfi hf Z
      (CardSuppLTTruncationIntegerPart.restrictDomain f hfi hf Z x) :
        cardSuppLTTruncationIntegerPart (G := H) (R := R) (κ := κ) Z) : R⟦H⟧) =
      HahnSeries.filter (· ∈ f.range) (x : R⟦H⟧) := by
  ext h
  rw [CardSuppLTTruncationIntegerPart.coe_mapDomain,
    CardSuppLTTruncationIntegerPart.coe_restrictDomain]
  let e : G ↪o H := ⟨⟨f, hfi⟩, hf _ _⟩
  change (HahnSeries.embDomain e
    (HahnSeries.restrictDomain e (x : R⟦H⟧))).coeff h = _
  by_cases hh : h ∈ f.range
  · obtain ⟨g, rfl⟩ := hh
    change (HahnSeries.embDomain e
      (HahnSeries.restrictDomain e (x : R⟦H⟧))).coeff (e g) = _
    rw [HahnSeries.embDomain_coeff, HahnSeries.restrictDomain_coeff,
      HahnSeries.coeff_filter, ite_eq_left]
    · rfl
    · exact Set.mem_range_self g
  · rw [HahnSeries.embDomain_of_notMem_range]
    · rw [HahnSeries.coeff_filter, ite_eq_right hh]
    · exact hh

namespace CardSuppLTTruncationIntegerPart

/-- If the image exponent subgroup is convex, primality of an embedded bounded integer-part
element descends to the original exponent domain. -/
theorem isPrimal_of_isPrimal_mapDomain
    (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') (Z : Subring R)
    (hrange : (Set.range f).OrdConnected)
    (a : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (ha : IsPrimal (mapDomain f hfi hf Z a)) : IsPrimal a := by
  let F : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z →+*
      cardSuppLTTruncationIntegerPart (G := H) (R := R) (κ := κ) Z :=
    mapDomain f hfi hf Z
  let C : AddSubgroup H := f.range
  have hC : (C : Set H).OrdConnected := by
    simpa only [C, AddMonoidHom.coe_range] using hrange
  rcases eq_or_ne a 0 with rfl | ha0
  · exact isPrimal_zero
  intro b c ⟨q, hq⟩
  have hdiv : F a ∣ F b * F c := by
    refine ⟨F q, ?_⟩
    rw [← map_mul, hq, map_mul]
  obtain ⟨a₁, a₂, ⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩, ha₁a₂⟩ := ha hdiv
  have hFa0 : F a ≠ 0 := by
    intro h
    apply ha0
    apply Subtype.ext
    apply Subtype.ext
    have hraw := congrArg (fun x : cardSuppLTTruncationIntegerPart
      (G := H) (R := R) (κ := κ) Z ↦ (x : R⟦H⟧)) h
    rw [coe_mapDomain] at hraw
    exact HahnSeries.embDomain_injective (by simpa using hraw)
  have ha₁0 : a₁ ≠ 0 := fun h ↦ hFa0 (by rw [ha₁a₂, h, zero_mul])
  have ha₂0 : a₂ ≠ 0 := fun h ↦ hFa0 (by rw [ha₁a₂, h, mul_zero])
  have ha₁N0 : toNonpositiveRingHom Z a₁ ≠ 0 := by
    intro h
    apply ha₁0
    apply toNonpositiveRingHom_injective Z
    exact h.trans (map_zero _).symm
  have ha₂N0 : toNonpositiveRingHom Z a₂ ≠ 0 := by
    intro h
    apply ha₂0
    apply toNonpositiveRingHom_injective Z
    exact h.trans (map_zero _).symm
  have hFasupp : ((F a : cardSuppLTTruncationIntegerPart
      (G := H) (R := R) (κ := κ) Z) : R⟦H⟧).support ⊆ (C : Set H) := by
    rw [coe_mapDomain, HahnSeries.support_embDomain]
    exact Set.image_subset_range _ _
  have ha₁a₂raw : ((a₁ * a₂ : cardSuppLTTruncationIntegerPart
      (G := H) (R := R) (κ := κ) Z) : R⟦H⟧) = (F a : R⟦H⟧) := by
    exact congrArg (fun x : cardSuppLTTruncationIntegerPart
      (G := H) (R := R) (κ := κ) Z ↦ (x : R⟦H⟧)) ha₁a₂.symm
  have hsuppFactors := HahnSeries.Nonpositive.support_subset_convex_of_mul_support_subset
    hC (a := toNonpositiveRingHom Z a₁) (b := toNonpositiveRingHom Z a₂)
      ha₁N0 ha₂N0 (by
        have heq : (toNonpositiveRingHom Z a₁ * toNonpositiveRingHom Z a₂ :
              HahnSeries.Nonpositive H R) = toNonpositiveRingHom Z (a₁ * a₂) := by
          rw [map_mul]
        rw [heq, coe_toNonpositiveRingHom, ha₁a₂raw]
        exact hFasupp)
  have ha₁supp : (a₁ : R⟦H⟧).support ⊆ (C : Set H) := by
    simpa only [coe_toNonpositiveRingHom] using hsuppFactors.1
  have ha₂supp : (a₂ : R⟦H⟧).support ⊆ (C : Set H) := by
    simpa only [coe_toNonpositiveRingHom] using hsuppFactors.2
  have hq₁supp : (q₁ : R⟦H⟧).support ⊆ (C : Set H) := by
    apply HahnSeries.support_subset_of_mul_eq
      (e := (a₁ : R⟦H⟧)) (u := (q₁ : R⟦H⟧)) (f := (F b : R⟦H⟧))
    · exact ha₁supp
    · exact fun h ↦ ha₁0 (Subtype.ext (Subtype.ext h))
    · rw [coe_mapDomain, HahnSeries.support_embDomain]
      exact Set.image_subset_range _ _
    · exact congrArg (fun x : cardSuppLTTruncationIntegerPart
        (G := H) (R := R) (κ := κ) Z ↦ (x : R⟦H⟧)) hq₁
  have hq₂supp : (q₂ : R⟦H⟧).support ⊆ (C : Set H) := by
    apply HahnSeries.support_subset_of_mul_eq
      (e := (a₂ : R⟦H⟧)) (u := (q₂ : R⟦H⟧)) (f := (F c : R⟦H⟧))
    · exact ha₂supp
    · exact fun h ↦ ha₂0 (Subtype.ext (Subtype.ext h))
    · rw [coe_mapDomain, HahnSeries.support_embDomain]
      exact Set.image_subset_range _ _
    · exact congrArg (fun x : cardSuppLTTruncationIntegerPart
        (G := H) (R := R) (κ := κ) Z ↦ (x : R⟦H⟧)) hq₂
  let A₁ := restrictDomain f hfi hf Z a₁
  let A₂ := restrictDomain f hfi hf Z a₂
  let Q₁ := restrictDomain f hfi hf Z q₁
  let Q₂ := restrictDomain f hfi hf Z q₂
  have hmapA₁ : F A₁ = a₁ := mapDomain_restrictDomain f hfi hf Z a₁ (by
    simpa only [C, AddMonoidHom.coe_range] using ha₁supp)
  have hmapA₂ : F A₂ = a₂ := mapDomain_restrictDomain f hfi hf Z a₂ (by
    simpa only [C, AddMonoidHom.coe_range] using ha₂supp)
  have hmapQ₁ : F Q₁ = q₁ := mapDomain_restrictDomain f hfi hf Z q₁ (by
    simpa only [C, AddMonoidHom.coe_range] using hq₁supp)
  have hmapQ₂ : F Q₂ = q₂ := mapDomain_restrictDomain f hfi hf Z q₂ (by
    simpa only [C, AddMonoidHom.coe_range] using hq₂supp)
  refine ⟨A₁, A₂, ⟨Q₁, ?_⟩, ⟨Q₂, ?_⟩, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    have hF : F b = F (A₁ * Q₁) := by
      rw [map_mul, hmapA₁, hmapQ₁]
      exact hq₁
    have hraw := congrArg (fun x : cardSuppLTTruncationIntegerPart
      (G := H) (R := R) (κ := κ) Z ↦ (x : R⟦H⟧)) hF
    rw [coe_mapDomain, coe_mapDomain] at hraw
    exact HahnSeries.embDomain_injective hraw
  · apply Subtype.ext
    apply Subtype.ext
    have hF : F c = F (A₂ * Q₂) := by
      rw [map_mul, hmapA₂, hmapQ₂]
      exact hq₂
    have hraw := congrArg (fun x : cardSuppLTTruncationIntegerPart
      (G := H) (R := R) (κ := κ) Z ↦ (x : R⟦H⟧)) hF
    rw [coe_mapDomain, coe_mapDomain] at hraw
    exact HahnSeries.embDomain_injective hraw
  · apply Subtype.ext
    apply Subtype.ext
    have hF : F a = F (A₁ * A₂) := by
      rw [map_mul, hmapA₁, hmapA₂]
      exact ha₁a₂
    have hraw := congrArg (fun x : cardSuppLTTruncationIntegerPart
      (G := H) (R := R) (κ := κ) Z ↦ (x : R⟦H⟧)) hF
    rw [coe_mapDomain, coe_mapDomain] at hraw
    exact HahnSeries.embDomain_injective hraw

end CardSuppLTTruncationIntegerPart

end HahnSeries
