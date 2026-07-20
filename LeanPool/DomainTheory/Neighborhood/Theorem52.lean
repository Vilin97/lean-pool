/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Table55

/-!
# Lecture V (§5) — Theorem 5.2 (Scott 1981, PRG-19)

**Theorem 5.2.** For suitably typed `λ`-terms the following equation is true:

`(λx₀, …, xₙ₋₁. τ)(σ₀, …, σₙ₋₁) = τ[σ₀/x₀, …, σₙ₋₁/xₙ₋₁].`

This is the fundamental **conversion (β-substitution) rule**. Scott proves it by
induction on `τ`,
reducing to the one-variable case and using three "true equations" along the way.
In the
neighbourhood-system framework, where a term-in-context is an approximable map,
the one-variable
rule is exactly the computation law of `curry`/`eval` from Theorem 3.12, and the
inductive helper
equations are the corresponding combinator identities:

* **β (one variable, in context).** With `⟦τ⟧ = g : Γ × 𝒟ₓ → 𝒟'`, the term `λx.τ`
is `curry g` and
  applying it to a constant `σ` substitutes `σ` for `x`:
  `eval ∘ ⟨curry g, const σ⟩ = g ∘ ⟨I, const σ⟩`   (`beta`).
* **tuple.** `(λx.⟨τ₀, τ₁⟩)(σ) = ⟨(λx.τ₀)(σ), (λx.τ₁)(σ)⟩`   (`beta_tuple`).
* **abstraction (Scott's `inv` step).** `(λx.λy.τ)(σ)(y) = τ[σ/x]` evaluated, i.e.
the double-curry
  application law   (`beta_abs`).

The base value law `(λx.τ)(σ) = τ[σ/x]` evaluated pointwise is
`toElementMap_curry_apply`.
Everything here is at the level of approximable maps; the *map equation* `beta`
uses the permitted
`ext_of_toElementMap`, the *value* equations are choice-free.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₃ : NeighborhoodSystem δ}

namespace Theorem52

/-- **Theorem 5.2, base value law (Scott 1981, PRG-19).** `(λx.τ)(σ) = τ[σ/x]`
evaluated: applying
the abstraction `curry g` (in free-variable context `v`) to `x` substitutes,
giving `g(v, x)`. -/
theorem subst_value (g : ApproximableMap (prod V₀ V₁) V₂) (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry g).toElementMap v)).toElementMap x = g.toElementMap (pair v x) :=
  toElementMap_curry_apply g v x

/-- **Theorem 5.2 (Scott 1981, PRG-19) — β as a map equation.** Substituting the
constant `σ` for
the bound variable: `(λx.τ)(σ) = τ[σ/x]`, where the left side first abstracts
(`curry g`) then
applies to the constant `σ`, and the right side substitutes `σ` directly. Both are
approximable
maps `Γ → 𝒟'` and they are equal. -/
theorem beta (g : ApproximableMap (prod V₀ V₁) V₂) (σ : V₁.Element) :
    (evalMap V₁ V₂).comp (paired (curry g) (constMap V₀ σ))
      = g.comp (paired (idMap V₀) (constMap V₀ σ)) := by
  apply ext_of_toElementMap
  intro v
  rw [toElementMap_comp, toElementMap_paired, evalMap_apply, toElementMap_curry_apply,
    toElementMap_constMap, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap]

/-- **Theorem 5.2 (Scott 1981, PRG-19) — tuple case.**
`(λx.⟨τ₀, τ₁⟩)(σ) = ⟨(λx.τ₀)(σ), (λx.τ₁)(σ)⟩`: abstraction distributes over a
tuple. -/
theorem beta_tuple (g₀ : ApproximableMap (prod V₀ V₁) V₂) (g₁ : ApproximableMap (prod V₀ V₁) V₃)
    (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry (paired g₀ g₁)).toElementMap v)).toElementMap x
      = pair ((toApproxMap ((curry g₀).toElementMap v)).toElementMap x)
          ((toApproxMap ((curry g₁).toElementMap v)).toElementMap x) := by
  rw [toElementMap_curry_apply, toElementMap_paired, toElementMap_curry_apply,
    toElementMap_curry_apply]

/-- **Theorem 5.2 (Scott 1981, PRG-19) — abstraction case (`inv` step).**
`(λx.λy.τ)(σ)(y) = τ[σ/x]` evaluated at `y`: the double-curry application law. The
bound `y` is
carried inert past the substitution of `σ` for `x`, exactly Scott's
`(λx.λy.τ)(σ)(y) = (λx.τ)(σ)`. -/
theorem beta_abs (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃) (v : V₀.Element) (σ : V₁.Element)
    (y : V₂.Element) :
    (toApproxMap ((toApproxMap ((curry (curry g)).toElementMap v)).toElementMap σ)).toElementMap y
      = g.toElementMap (pair (pair v σ) y) := by
  rw [toElementMap_curry_apply, toElementMap_curry_apply]

end Theorem52

end Domain.Neighborhood
