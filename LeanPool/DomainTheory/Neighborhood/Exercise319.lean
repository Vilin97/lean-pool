/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Product

/-!
# Exercise 3.19 / 3.20 (Scott 1981, PRG-19, §3) — the product functor `f × g`

Given approximable mappings `f : 𝒟₀ → 𝒟₀'` and `g : 𝒟₁ → 𝒟₁'`, Scott's Exercise
3.19 constructs
the product mapping `f × g : 𝒟₀ × 𝒟₁ → 𝒟₀' × 𝒟₁'` with

* **(i)** `(f × g)(⟨x, y⟩) = ⟨f(x), g(y)⟩`, and
* **(ii)** `f × g = ⟨f ∘ p₀, g ∘ p₁⟩`.

We take (ii) as the definition (`prodMap`, built from Definition 3.3's
`paired`/`proj`), and prove
(i) — indeed the more general `toElementMap_prodMap` (`(f × g)(w) = ⟨f(w₀),
g(w₁)⟩`).

Exercise 3.20 (for category theorists) then follows: `×` is a **functor**
(`prodMap_id`,
`prodMap_comp`), and `prod` with its projections is the **categorical product** —
the universal
property `paired`/`proj` with uniqueness `paired_unique`.

The sum functor `f + g` is treated in `Exercise318.lean`/`Exercise319Sum.lean`
after the sum system
is built. Everything here is **choice-free** (`#print axioms ⊆ {propext,
Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **Exercise 3.19(ii) (Scott 1981, PRG-19).** The product mapping `f × g = ⟨f ∘
p₀, g ∘ p₁⟩`. -/
def prodMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (prod V₀ V₁) (prod V₀' V₁') :=
  paired (f.comp (proj₀ V₀ V₁)) (g.comp (proj₁ V₀ V₁))

/-- **Exercise 3.19 (Scott 1981, PRG-19).** `(f × g)(w) = ⟨f(w₀), g(w₁)⟩` for
every product element
`w` (so in particular `(f × g)(⟨x, y⟩) = ⟨f(x), g(y)⟩`, equation (i)). -/
theorem toElementMap_prodMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁')
    (w : (prod V₀ V₁).Element) :
    (prodMap f g).toElementMap w = pair (f.toElementMap w.fst) (g.toElementMap w.snd) := by
  rw [prodMap, toElementMap_paired, toElementMap_comp, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁]

/-- **Exercise 3.19(i) (Scott 1981, PRG-19).** `(f × g)(⟨x, y⟩) = ⟨f(x), g(y)⟩`. -/
theorem toElementMap_prodMap_pair (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁')
    (x : V₀.Element) (y : V₁.Element) :
    (prodMap f g).toElementMap (pair x y) = pair (f.toElementMap x) (g.toElementMap y) := by
  rw [toElementMap_prodMap, fst_pair, snd_pair]

/-! ### Exercise 3.20 — `×` is a functor. -/

/-- **Exercise 3.20 (Scott 1981, PRG-19).** `×` preserves identities: `I × I = I`. -/
theorem prodMap_id : prodMap (idMap V₀) (idMap V₁) = idMap (prod V₀ V₁) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_prodMap, toElementMap_idMap, toElementMap_idMap, toElementMap_idMap,
    pair_fst_snd]

/-- **Exercise 3.20 (Scott 1981, PRG-19).** `×` preserves composition:
`(f' ∘ f) × (g' ∘ g) = (f' × g') ∘ (f × g)`. -/
theorem prodMap_comp {α'' β'' : Type*}
    {V₀'' : NeighborhoodSystem α''} {V₁'' : NeighborhoodSystem β''}
    (f' : ApproximableMap V₀' V₀'') (f : ApproximableMap V₀ V₀')
    (g' : ApproximableMap V₁' V₁'') (g : ApproximableMap V₁ V₁') :
    prodMap (f'.comp f) (g'.comp g) = (prodMap f' g').comp (prodMap f g) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_prodMap, toElementMap_comp, toElementMap_comp, toElementMap_comp,
    toElementMap_prodMap, toElementMap_prodMap, fst_pair, snd_pair]

/-! ### Exercise 3.20 — `prod` is the categorical product. -/

/-- **Exercise 3.20 (Scott 1981, PRG-19).** The universal property of the product
(existence):
`p₀ ∘ ⟨h₀, h₁⟩ = h₀` and `p₁ ∘ ⟨h₀, h₁⟩ = h₁` (these are Proposition 3.4(i)). -/
theorem proj_paired (h₀ : ApproximableMap V₂ V₀) (h₁ : ApproximableMap V₂ V₁) :
    (proj₀ V₀ V₁).comp (paired h₀ h₁) = h₀ ∧ (proj₁ V₀ V₁).comp (paired h₀ h₁) = h₁ :=
  ⟨proj₀_comp_paired h₀ h₁, proj₁_comp_paired h₀ h₁⟩

/-- **Exercise 3.20 (Scott 1981, PRG-19).** The universal property of the product
(uniqueness):
any `k` with `p₀ ∘ k = h₀` and `p₁ ∘ k = h₁` equals the pairing `⟨h₀, h₁⟩`. Hence
`prod` with
`proj₀`, `proj₁` is the categorical product of `𝒟₀` and `𝒟₁`. -/
theorem paired_unique (h₀ : ApproximableMap V₂ V₀) (h₁ : ApproximableMap V₂ V₁)
    (k : ApproximableMap V₂ (prod V₀ V₁)) (hk₀ : (proj₀ V₀ V₁).comp k = h₀)
    (hk₁ : (proj₁ V₀ V₁).comp k = h₁) : k = paired h₀ h₁ := by
  rw [← hk₀, ← hk₁, paired_proj]

end Domain.Neighborhood
