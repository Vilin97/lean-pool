/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise315
import LeanPool.DomainTheory.Neighborhood.FunctionSpace

/-!
# Exercise 3.24 (Scott 1981, PRG-19, §3) — function-space isomorphisms

Scott asks to establish further isomorphisms. We formalize **(i)**:

`(𝒟₀ → (𝒟₁ × 𝒟₂)) ≅ (𝒟₀ → 𝒟₁) × (𝒟₀ → 𝒟₂)`.

The crux is the order-isomorphism on the *approximable maps* themselves,
`funProdEquiv : Hom(𝒟₀, 𝒟₁ × 𝒟₂) ≃o Hom(𝒟₀, 𝒟₁) × Hom(𝒟₀, 𝒟₂)`, given by
`h ↦ (p₀ ∘ h, p₁ ∘ h)` with inverse `⟨a, b⟩ ↦ ⟨a, b⟩` (Definition 3.3's
`paired`/`proj`, and the
round-trips `paired_proj` / `proj_comp_paired`). Transporting through Theorem
3.10's `funSpaceEquiv`
and Proposition 3.2's `prodEquiv` gives the domain isomorphism `funProdIso`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.24(i) (Scott 1981, PRG-19).** The order-isomorphism on
approximable maps
`Hom(𝒟₀, 𝒟₁ × 𝒟₂) ≃o Hom(𝒟₀, 𝒟₁) × Hom(𝒟₀, 𝒟₂)`, `h ↦ (p₀ ∘ h, p₁ ∘ h)`. -/
def funProdEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap V₀ (prod V₁ V₂) ≃o (ApproximableMap V₀ V₁ × ApproximableMap V₀ V₂) where
  toFun h := ((proj₀ V₁ V₂).comp h, (proj₁ V₁ V₂).comp h)
  invFun p := paired p.1 p.2
  left_inv h := paired_proj h
  right_inv p := by
    ext1
    · exact proj₀_comp_paired p.1 p.2
    · exact proj₁_comp_paired p.1 p.2
  map_rel_iff' := by
    intro h h'
    constructor
    · rintro ⟨h0, h1⟩
      rw [← paired_proj h, ← paired_proj h']
      intro Z P hrel
      obtain ⟨hP, hfP, hgP⟩ := hrel
      exact ⟨hP, h0 _ _ hfP, h1 _ _ hgP⟩
    · intro hle
      refine ⟨fun X Y hrel => ?_, fun X Y hrel => ?_⟩
      · obtain ⟨W, hW, hYW⟩ := hrel
        exact ⟨W, hle X W hW, hYW⟩
      · obtain ⟨W, hW, hYW⟩ := hrel
        exact ⟨W, hle X W hW, hYW⟩

/-- **Exercise 3.24(i) (Scott 1981, PRG-19).** The domain isomorphism
`|𝒟₀ → (𝒟₁ × 𝒟₂)| ≃o |(𝒟₀ → 𝒟₁) × (𝒟₀ → 𝒟₂)|`. -/
def funProdIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    (funSpace V₀ (prod V₁ V₂)).Element ≃o (prod (funSpace V₀ V₁) (funSpace V₀ V₂)).Element :=
  (funSpaceEquiv V₀ (prod V₁ V₂)).trans <|
    (funProdEquiv V₀ V₁ V₂).trans <|
      (prodCongrOrderIso (funSpaceEquiv V₀ V₁).symm (funSpaceEquiv V₀ V₂).symm).trans
        (prodEquiv (funSpace V₀ V₁) (funSpace V₀ V₂)).symm

/-- **Exercise 3.24(i).** `(𝒟₀ → (𝒟₁ × 𝒟₂)) ≅ (𝒟₀ → 𝒟₁) × (𝒟₀ → 𝒟₂)`. -/
theorem funProd_isomorphic :
    funSpace V₀ (prod V₁ V₂) ≅ᴰ prod (funSpace V₀ V₁) (funSpace V₀ V₂) :=
  ⟨funProdIso V₀ V₁ V₂⟩

end Domain.Neighborhood
