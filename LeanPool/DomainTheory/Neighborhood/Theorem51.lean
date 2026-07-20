/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Table55

/-!
# Lecture V (§5) — Theorem 5.1 (Scott 1981, PRG-19)

**Theorem 5.1.** Every typed `λ`-term `τ` defines an approximable function of its
free variables.

Scott proves this by induction on the (limited) syntax of `λ`-terms. There are
exactly five cases,
and in the neighbourhood-system framework each is realized by a construction
already shown to be
approximable in Lectures II–III. The interpretation `⟦τ⟧` of a term with free
variables of types
`𝒟₀, …, 𝒟ₙ₋₁` (collected into the context product `Γ = 𝒟₀ × ⋯ × 𝒟ₙ₋₁`) is an
*approximable map*
`Γ → 𝒟'`, built as follows:

| term `τ` | interpretation | approximable by |
| -------- | -------------- | --------------- |
| a variable `xᵢ` | a projection `Γ → 𝒟ᵢ` | Def 3.3 (`proj₀`/`proj₁`) |
| a constant `k` | `constMap` | Lemma 3.6 |
| a tuple `⟨σ₀, σ₁⟩` | `⟨⟦σ₀⟧, ⟦σ₁⟧⟩ = paired` | Prop 3.4 |
| an application `σ₀(σ₁)` | `eval ∘ ⟨⟦σ₀⟧, ⟦σ₁⟧⟩` | Thm 3.11 + Thm 2.5 |
| an abstraction `λx.σ` | `curry ⟦σ⟧` | Thm 3.12 |

Because every one of these lands in `ApproximableMap`, "defines an approximable
function" holds *by
construction* — the content of Theorem 5.1 is that these five closure operations
exist and compute
the intended values, which is what we record here (the value equations `*_apply`).
The genuinely
recursive cases (tuple, application, abstraction) carry the induction hypothesis
that the
subterms `σᵢ` are already approximable.

This module collects the five closure facts as concrete lemmas; everything is
**choice-free**.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₃ : NeighborhoodSystem δ}

namespace Theorem51

/-! ### Case 1 — a variable is a projection (here, the two binary projections of
the context). -/

/-- **Theorem 5.1, variable case (Scott 1981, PRG-19).** A free variable is
interpreted by a
projection of the context; the projections are approximable with `p₀⟨x,y⟩ = x`,
`p₁⟨x,y⟩ = y`. -/
theorem var_fst (x : V₀.Element) (y : V₁.Element) :
    (proj₀ V₀ V₁).toElementMap (pair x y) = x := by rw [toElementMap_proj₀, fst_pair]

theorem var_snd (x : V₀.Element) (y : V₁.Element) :
    (proj₁ V₀ V₁).toElementMap (pair x y) = y := by rw [toElementMap_proj₁, snd_pair]

/-! ### Case 2 — a constant. -/

/-- **Theorem 5.1, constant case (Scott 1981, PRG-19).** A constant `k` is
interpreted by the
constant map, which is approximable with value `k`. -/
theorem const_apply (k : V₁.Element) (x : V₀.Element) :
    (constMap V₀ k).toElementMap x = k := toElementMap_constMap k x

/-! ### Case 3 — a tuple. -/

/-- **Theorem 5.1, tuple case (Scott 1981, PRG-19).** If `⟦σ₀⟧, ⟦σ₁⟧` are
approximable, so is the
tuple `⟨⟦σ₀⟧, ⟦σ₁⟧⟩ = paired`, with value `⟨σ₀(w), σ₁(w)⟩`. -/
theorem tuple_apply (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) (w : V₂.Element) :
    (paired f g).toElementMap w = pair (f.toElementMap w) (g.toElementMap w) :=
  toElementMap_paired f g w

/-! ### Case 4 — an application. -/

/-- **Theorem 5.1, application case (Scott 1981, PRG-19).** If `⟦σ₀⟧ : Γ → (𝒟₀ →
𝒟₁)` and
`⟦σ₁⟧ : Γ → 𝒟₀` are approximable, then `σ₀(σ₁)` is interpreted by `eval ∘ ⟨⟦σ₀⟧,
⟦σ₁⟧⟩`
(approximable by Thm 3.11 and Thm 2.5), with value `(σ₀ w)(σ₁ w)`. -/
theorem app_apply (F : ApproximableMap V₂ (funSpace V₀ V₁)) (G : ApproximableMap V₂ V₀)
    (w : V₂.Element) :
    ((evalMap V₀ V₁).comp (paired F G)).toElementMap w
      = (toApproxMap (F.toElementMap w)).toElementMap (G.toElementMap w) := by
  rw [toElementMap_comp, toElementMap_paired, evalMap_apply]

/-! ### Case 5 — an abstraction. -/

/-- **Theorem 5.1, abstraction case (Scott 1981, PRG-19).** If `⟦σ⟧ : Γ × 𝒟ₙ → 𝒟'`
is approximable,
then `λx.σ` is interpreted by `curry ⟦σ⟧ : Γ → (𝒟ₙ → 𝒟')` (approximable by Thm
3.12), with value
`(λx.σ)(v)(x) = σ(v, x)`. -/
theorem abs_apply (g : ApproximableMap (prod V₀ V₁) V₂) (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry g).toElementMap v)).toElementMap x = g.toElementMap (pair v x) :=
  toElementMap_curry_apply g v x

end Theorem51

end Domain.Neighborhood
