/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Product

/-!
# Exercise 3.14 (Scott 1981, PRG-19, §3) — the diagonal map

Scott's Exercise 3.14 makes two points.

* **The disjointness of `Δ₀` and `Δ₁` is unnecessary.** Working over a denumerable
token alphabet
  `Σ = {0, 1}`, one may *tag* the two factors, taking the product system over `0Δ₀
  ∪ 1Δ₁` with
  neighbourhoods `0X ∪ 1Y`. Our `Product.lean` already realizes exactly this
  tagging abstractly:
  the disjoint union of token *types* `α ⊕ β` is the type-theoretic incarnation of
  `0Δ₀ ∪ 1Δ₁`, and
  `prodNbhd X Y = Sum.inl '' X ∪ Sum.inr '' Y` is `0X ∪ 1Y`. So no separate
  construction is needed —
  `prod V₀ V₁` *is* the tagged product, and the revised pairing `⟨x, y⟩` is `pair`
  (Definition 3.1).

* **The diagonal `diag : 𝒟 → 𝒟 × 𝒟`, `diag(x) = ⟨x, x⟩`.** This is the paired map
`⟨I, I⟩` of the
  identity with itself (Definition 3.3), so it is approximable for free, and
  `toElementMap_diag` computes `diag(x) = ⟨x, x⟩` from `toElementMap_paired`.

The `n`-fold product `𝒟₀ × ⋯ × 𝒟_{n-1}` over `⋃_{i<n} 1ⁱ0 Δᵢ` is obtained by
iterating the binary
`prod` (it is associative up to isomorphism, Exercise 3.15); the binary diagonal
here is the
`n = 2` instance of the general diagonal `x ↦ ⟨x, …, x⟩`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 3.14 (Scott 1981, PRG-19).** The *diagonal* approximable mapping
`diag : 𝒟 → 𝒟 × 𝒟`, defined as the paired map `⟨I_𝒟, I_𝒟⟩` of the identity with
itself. -/
def diag : ApproximableMap V (prod V V) := paired (idMap V) (idMap V)

@[simp] theorem diag_rel {Z : Set α} {P : Set (α ⊕ α)} :
    (diag V).rel Z P ↔
      (prod V V).mem P ∧ (idMap V).rel Z (Sum.inl ⁻¹' P) ∧ (idMap V).rel Z (Sum.inr ⁻¹' P) :=
  Iff.rfl

/-- **Exercise 3.14 (Scott 1981, PRG-19).** `diag(x) = ⟨x, x⟩` for every `x ∈
|𝒟|`. -/
@[simp] theorem toElementMap_diag (x : V.Element) :
    (diag V).toElementMap x = pair x x := by
  rw [diag, toElementMap_paired, toElementMap_idMap]

/-- **Exercise 3.14 (Scott 1981, PRG-19).** Post-composing the diagonal with the
two projections
returns the identity: `p₀ ∘ diag = I` and `p₁ ∘ diag = I`. -/
theorem proj₀_comp_diag : (proj₀ V V).comp (diag V) = idMap V :=
  proj₀_comp_paired (idMap V) (idMap V)

theorem proj₁_comp_diag : (proj₁ V V).comp (diag V) = idMap V :=
  proj₁_comp_paired (idMap V) (idMap V)

end Domain.Neighborhood
