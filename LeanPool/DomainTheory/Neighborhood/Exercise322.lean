/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.FunctionSpace

/-!
# Exercise 3.22 (Scott 1981, PRG-19, §3) — composition is approximable

Scott asks for the approximable composition mapping

`comp : (𝒟₁ → 𝒟₂) × (𝒟₀ → 𝒟₁) → (𝒟₀ → 𝒟₂)`,  `comp(g, f) = g ∘ f`,

and suggests building it from `eval` and `curry`. We follow the hint: the
uncurried form

`compApp : ((𝒟₁ → 𝒟₂) × (𝒟₀ → 𝒟₁)) × 𝒟₀ → 𝒟₂`,  `compApp(⟨⟨g, f⟩, x⟩) = g(f(x))`,

is assembled from the two evaluation maps and the projections/pairing of
Definition 3.3, and then
`compMap = curry compApp` is the desired map. Theorem 3.12's
`toElementMap_curry_apply` and 3.11's
`evalMap_apply` compute `comp(g, f) = g ∘ f` on elements
(`toElementMap_compMap_apply`).

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- The uncurried composition map `((𝒟₁→𝒟₂) × (𝒟₀→𝒟₁)) × 𝒟₀ → 𝒟₂`, `⟨⟨g, f⟩, x⟩ ↦
g(f(x))`,
built from the inner evaluation `(𝒟₀→𝒟₁) × 𝒟₀ → 𝒟₁`, the outer evaluation `(𝒟₁→𝒟₂)
× 𝒟₁ → 𝒟₂`,
and the product projections/pairing (Definition 3.3). -/
def compApp (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀) V₂ :=
  (evalMap V₁ V₂).comp
    (paired
      ((proj₀ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
        (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
      ((evalMap V₀ V₁).comp
        (paired
          ((proj₁ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
            (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
          (proj₁ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))))

/-- `compApp(⟨⟨g, f⟩, x⟩) = g(f(x))`. -/
theorem toElementMap_compApp (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element)
    (x : V₀.Element) :
    (compApp V₀ V₁ V₂).toElementMap (pair (pair Gφ Fφ) x)
      = (toApproxMap Gφ).toElementMap ((toApproxMap Fφ).toElementMap x) := by
  rw [compApp]
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

/-- **Exercise 3.22 (Scott 1981, PRG-19).** The composition mapping
`comp : (𝒟₁ → 𝒟₂) × (𝒟₀ → 𝒟₁) → (𝒟₀ → 𝒟₂)`, `comp = curry(compApp)`. -/
def compMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) (funSpace V₀ V₂) :=
  curry (compApp V₀ V₁ V₂)

/-- **Exercise 3.22 (Scott 1981, PRG-19).** `comp(g, f) = g ∘ f`: applying the
value
`comp(⟨g, f⟩) ∈ |𝒟₀ → 𝒟₂|` to `x` gives `g(f(x))`. -/
theorem toElementMap_compMap_apply (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element)
    (x : V₀.Element) :
    (toApproxMap ((compMap V₀ V₁ V₂).toElementMap (pair Gφ Fφ))).toElementMap x
      = (toApproxMap Gφ).toElementMap ((toApproxMap Fφ).toElementMap x) := by
  rw [compMap, toElementMap_curry_apply, toElementMap_compApp]

/-- **Exercise 3.22 (Scott 1981, PRG-19).** The relational form `comp(g, f) = g ∘
f`: the value of
`comp` at `⟨g, f⟩`, read back as an approximable map, is the composition of the
approximable maps. -/
theorem toApproxMap_compMap (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element) :
    toApproxMap ((compMap V₀ V₁ V₂).toElementMap (pair Gφ Fφ))
      = (toApproxMap Gφ).comp (toApproxMap Fφ) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_compMap_apply, toElementMap_comp]

end Domain.Neighborhood
