/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Domain

/-!
# Embeddings between exponent domains of nonpositive Hahn series

An injective additive order embedding of exponent groups induces a ring embedding between the
corresponding nonpositive Hahn-series rings. This is the nonpositive restriction of Mathlib's
`HahnSeries.embDomainRingHom`.

The construction is used in LM24, Section 6.5 to regard a series with exponents in a subgroup
`H ⊆ ℝ` as a real-exponent Hahn series. The public support formula ensures that later statements
about real suprema refer to the same support, transported along the given embedding.
-/

universe u v w

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {H : Type v} {K : Type w}
  [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
  [LinearOrder H] [AddCommGroup H] [IsOrderedAddMonoid H]
  [CommRing K]

/-- Map a nonpositive Hahn series along an injective additive order embedding of exponent
groups. -/
def mapDomain (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') :
    Nonpositive G K →+* Nonpositive H K :=
  ((HahnSeries.embDomainRingHom f hfi hf).domRestrict
    (HahnSeries.nonpositiveSubring G K)).codRestrict
      (HahnSeries.nonpositiveSubring H K) (fun b ↦ by
        rw [HahnSeries.mem_nonpositiveSubring]
        intro h hh
        change h ∈ (HahnSeries.embDomain
          (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) (b : K⟦G⟧)).support at hh
        obtain ⟨g, hg, rfl⟩ := HahnSeries.support_embDomain_subset hh
        simpa using (hf g 0).mpr (support_subset b hg))

/-- The underlying Hahn series of `mapDomain` is Mathlib's exponent-domain embedding. -/
@[simp]
theorem coe_mapDomain (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g')
    (b : Nonpositive G K) :
    (mapDomain f hfi hf b : K⟦H⟧) =
      HahnSeries.embDomain (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) (b : K⟦G⟧) :=
  (rfl)

/-- Mapping the exponent domain preserves the coefficient at every mapped exponent. -/
theorem mapDomain_coeff_image (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g')
    (b : Nonpositive G K) (g : G) :
    ((mapDomain f hfi hf b : Nonpositive H K) : K⟦H⟧).coeff (f g) =
      (b : K⟦G⟧).coeff g := by
  rw [coe_mapDomain]
  exact HahnSeries.embDomain_coeff

/-- Mapping the exponent domain maps the support pointwise. -/
theorem support_mapDomain (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g')
    (b : Nonpositive G K) :
    (mapDomain f hfi hf b : K⟦H⟧).support = f '' (b : K⟦G⟧).support := by
  rw [coe_mapDomain, HahnSeries.support_embDomain]
  rfl

/-- Mapping along an exponent-domain embedding preserves support order type, after lifting both
ordinals to account for possibly different exponent universes. -/
theorem lift_supportOrderType_mapDomain (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') (b : Nonpositive G K) :
    Ordinal.lift.{u, v}
        (HahnSeries.supportOrderType (mapDomain f hfi hf b : K⟦H⟧)) =
      Ordinal.lift.{v, u} (HahnSeries.supportOrderType (b : K⟦G⟧)) := by
  let e : G ↪o H := ⟨⟨f, hfi⟩, hf _ _⟩
  letI : WellFoundedLT (b : K⟦G⟧).support := ⟨(b : K⟦G⟧).isWF_support⟩
  letI : WellFoundedLT (mapDomain f hfi hf b : K⟦H⟧).support :=
    ⟨(mapDomain f hfi hf b : K⟦H⟧).isWF_support⟩
  let supportEquiv : (mapDomain f hfi hf b : K⟦H⟧).support ≃o
      (b : K⟦G⟧).support :=
    (OrderIso.setCongr _ (f '' (b : K⟦G⟧).support)
      (support_mapDomain f hfi hf b)).trans
        (StrictMonoOn.orderIso e (b : K⟦G⟧).support
          (e.strictMono.strictMonoOn (b : K⟦G⟧).support)).symm
  rw [HahnSeries.supportOrderType_eq_typeLT (OrderIso.refl _),
    HahnSeries.supportOrderType_eq_typeLT (OrderIso.refl _)]
  exact supportEquiv.toRelIsoLT.ordinal_lift_type_eq

/-- Mapping the exponent domain preserves the constant coefficient. -/
theorem constantCoeff_mapDomain (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g')
    (b : Nonpositive G K) :
    constantCoeff (mapDomain f hfi hf b) = constantCoeff b := by
  rw [constantCoeff_apply, constantCoeff_apply, coe_mapDomain, ← f.map_zero]
  exact HahnSeries.embDomain_coeff

/-- Mapping along an injective exponent-domain map is injective on nonpositive series. -/
theorem mapDomain_injective (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') :
    Function.Injective (mapDomain (K := K) f hfi hf) := by
  intro b c hbc
  apply Subtype.ext
  have hbc' := congrArg Subtype.val hbc
  change HahnSeries.embDomain (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) (b : K⟦G⟧) =
    HahnSeries.embDomain (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) (c : K⟦G⟧) at hbc'
  exact HahnSeries.embDomain_injective hbc'

/-- Restrict a nonpositive Hahn series whose support lies in the range of an exponent-domain
embedding. -/
def restrictDomain (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g')
    (b : Nonpositive H K) : Nonpositive G K :=
  ⟨HahnSeries.restrictDomain (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) (b : K⟦H⟧), by
    intro g hg
    have hcoeff : (b : K⟦H⟧).coeff (f g) ≠ 0 := by
      change (HahnSeries.restrictDomain
        (⟨⟨f, hfi⟩, hf _ _⟩ : G ↪o H) (b : K⟦H⟧)).coeff g ≠ 0 at hg
      rw [HahnSeries.restrictDomain_coeff] at hg
      exact hg
    apply (hf g 0).mp
    simpa only [map_zero, Set.mem_Iic] using
      b.property ((HahnSeries.mem_support _ _).mpr hcoeff)⟩

/-- Extending a restricted nonpositive Hahn series recovers the original series. -/
@[simp]
theorem mapDomain_restrictDomain (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g')
    (b : Nonpositive H K) (hb : (b : K⟦H⟧).support ⊆ Set.range f) :
    mapDomain f hfi hf (restrictDomain f hfi hf b) = b := by
  apply Subtype.ext
  rw [coe_mapDomain]
  exact HahnSeries.embDomain_restrictDomain _ _ hb

/-- Mapping the exponent domain sends a monomial to the monomial at the mapped exponent. -/
@[simp]
theorem mapDomain_single (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g')
    (g : G) (k : K) (hg : g ≤ 0) :
    mapDomain f hfi hf (single g k hg) =
      single (f g) k (by simpa only [map_zero] using (hf g 0).mpr hg) := by
  apply Subtype.ext
  rw [coe_mapDomain, coe_single, coe_single, HahnSeries.embDomain_single]
  rfl

/-- Map a finite-support nonpositive Hahn series along an injective additive order embedding of
exponent groups. -/
def mapDomainFiniteSupport (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') :
    (finiteSupportSubring : Subring (Nonpositive G K)) →+*
      (finiteSupportSubring : Subring (Nonpositive H K)) :=
  ((mapDomain (K := K) f hfi hf).domRestrict finiteSupportSubring).codRestrict
    finiteSupportSubring (fun b ↦ by
      rw [mem_finiteSupportSubring_iff]
      change (mapDomain f hfi hf (b : Nonpositive G K) : K⟦H⟧).support.Finite
      rw [support_mapDomain]
      exact ((mem_finiteSupportSubring_iff (b : Nonpositive G K)).mp b.2).image f)

/-- The finite-support exponent-domain map is the restriction of `mapDomain`. -/
@[simp]
theorem coe_mapDomainFiniteSupport (f : G →+ H) (hfi : Function.Injective f)
    (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g')
    (b : (finiteSupportSubring : Subring (Nonpositive G K))) :
    ((mapDomainFiniteSupport f hfi hf b :
        (finiteSupportSubring : Subring (Nonpositive H K))) : Nonpositive H K) =
      mapDomain f hfi hf (b : Nonpositive G K) :=
  (rfl)

/-- Mapping a finite-support series along an injective exponent-domain map is injective. -/
theorem mapDomainFiniteSupport_injective (f : G →+ H)
    (hfi : Function.Injective f) (hf : ∀ g g' : G, f g ≤ f g' ↔ g ≤ g') :
    Function.Injective (mapDomainFiniteSupport (K := K) f hfi hf) := by
  intro b c hbc
  apply Subtype.ext
  exact mapDomain_injective f hfi hf (congrArg Subtype.val hbc)

end HahnSeries.Nonpositive
