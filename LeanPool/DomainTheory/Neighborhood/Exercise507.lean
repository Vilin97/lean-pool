/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import LeanPool.DomainTheory.Neighborhood.FunctionSpace

/-!
# Exercise 5.7 (Scott 1981, PRG-19, §5) — multi-variable `λ` and application from
one-variable forms

Scott asks for definitions of the two-variable abstraction and application

```
λx, y. τ        and        σ(x, y)
```

that use only the *one-variable* binder `λv` and applications to *one argument at
a time*, with the
combinators `p₀`, `p₁`, `pair` doing the bookkeeping. He then asks to generalise
to many variables.

In the neighbourhood-system framework this is exactly the **curry/uncurry**
isomorphism of
Theorem 3.12 together with **surjective pairing**:

* a two-variable function `σ : D₀ × D₁ → D₂` is applied "one argument at a time"
through its curried
  form, `σ(x, y) = (curry σ)(x)(y)`; conversely `uncurry h` turns
  one-argument-at-a-time application
  back into a single application to a `pair`, and is *literally* built from
  one-argument pieces:
  `uncurry h = eval ∘ ⟨h ∘ p₀, p₁⟩` (`uncurry_eq`), using only `eval`, `p₀`, `p₁`,
  `pair`;
* the two-variable abstraction `λx, y. τ` is `curry`, characterised by `(curry
g)(x)(y) = g⟨x, y⟩`,
  i.e. it binds one variable and returns a one-variable function;
* the projections and pairing are tied together by **surjective pairing** `⟨p₀ z,
p₁ z⟩ = z`, the
  fact that makes `p₀`, `p₁`, `pair` sufficient to encode the product.

We record these as the realisations Scott requests, and give the **three-variable
generalisation**
via nested currying `D₀ × (D₁ × D₂) → D₃`, illustrating the pattern for
arbitrarily many variables.

No new axioms are introduced beyond the project's `Element.ext` /
`ext_of_toElementMap` machinery
already used by `curry`/`uncurry`.
-/

@[expose] public section

namespace Domain.Neighborhood.Exercise507

open Domain.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {V₃ : NeighborhoodSystem δ}

/-! ### Surjective pairing: `p₀`, `p₁`, `pair` recover any element of the product. -/

/-- **Surjective pairing.** Every element `z : D₀ × D₁` is recovered from its
projections:
`⟨p₀(z), p₁(z)⟩ = z`. This is what makes `p₀`, `p₁`, `pair` enough to encode the
product. -/
theorem surjective_pairing (z : (prod V₀ V₁).Element) :
    pair ((proj₀ V₀ V₁).toElementMap z) ((proj₁ V₀ V₁).toElementMap z) = z := by
  rw [toElementMap_proj₀, toElementMap_proj₁, pair_fst_snd]

/-! ### Application to one argument at a time. -/

/-- **One-argument-at-a-time application.** For `h : D₀ → (D₁ → D₂)`, applying the
uncurried map to
a `pair` is the same as applying `h` to `x` and then to `y`:
`(uncurry h)(⟨x, y⟩) = h(x)(y)`. -/
theorem uncurry_apply (h : ApproximableMap V₀ (funSpace V₁ V₂))
    (x : V₀.Element) (y : V₁.Element) :
    (uncurry h).toElementMap (pair x y) =
      (toApproxMap (h.toElementMap x)).toElementMap y := by
  rw [uncurry_eq, toElementMap_comp, toElementMap_paired, toElementMap_comp,
    toElementMap_proj₀, toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]

/-- The combinator `σ(x, y)` (apply `σ : D₀ × D₁ → D₂` to two arguments) is
expressed through the
*one-variable* curried form: `σ(⟨x, y⟩) = (curry σ)(x)(y)`. The right-hand side
uses only
single-variable application. -/
theorem app_two_args (σ : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    σ.toElementMap (pair x y) =
      (toApproxMap ((curry σ).toElementMap x)).toElementMap y := by
  rw [toElementMap_curry_apply]

/-! ### Two-variable abstraction `λx, y. τ`. -/

/-- **Two-variable abstraction.** `λx, y. τ` is `curry`, characterised by `(curry
g)(x)(y) =
g⟨x, y⟩`.
It binds one variable `x` and returns the one-variable function `λy. g⟨x, y⟩`. -/
theorem lam_two_vars (g : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((curry g).toElementMap x)).toElementMap y = g.toElementMap (pair x y) :=
  toElementMap_curry_apply g x y

/-- The two encodings are mutually inverse: uncurrying the two-variable
abstraction returns the
original two-variable function. -/
theorem uncurry_lam_two_vars (g : ApproximableMap (prod V₀ V₁) V₂) : uncurry (curry g) = g :=
  uncurry_curry g

/-! ### Generalisation to three variables (the pattern for many variables). -/

/-- **Three-variable abstraction** `λx, y, z. τ`, via nested currying on `(D₀ ×
D₁) × D₂ → D₃`.
Each `curry` strips one variable, so a function of `n` variables is reached by `n
- 1` curryings —
single-variable binders all the way down. -/
def curry₃ (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃) :
    ApproximableMap V₀ (funSpace V₁ (funSpace V₂ V₃)) :=
  curry (curry g)

/-- The defining equation of `curry₃`: `(λx, y, z. g)(x)(y)(z) = g⟨⟨x, y⟩, z⟩`. -/
theorem curry₃_apply (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃)
    (x : V₀.Element) (y : V₁.Element) (z : V₂.Element) :
    (toApproxMap ((toApproxMap ((curry₃ g).toElementMap x)).toElementMap y)).toElementMap z =
      g.toElementMap (pair (pair x y) z) := by
  rw [curry₃, toElementMap_curry_apply, toElementMap_curry_apply]

end Domain.Neighborhood.Exercise507
