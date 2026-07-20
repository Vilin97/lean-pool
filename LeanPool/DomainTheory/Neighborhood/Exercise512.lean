/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Theorem41
import LeanPool.DomainTheory.Neighborhood.Exercise326

/-!
# Exercise 5.12 (Scott 1981, PRG-19, §5) — the `while` combinator

Given a domain `D`, a *predicate* `p : D → T` (into the truth domain of Example
1.2) and an
*update* `f : D → D`, Scott's `while`-loop

```
while p do f
```

is the function `D → D` that keeps applying `f` while `p` holds. It is
characterised as the least
solution `w : D → D` of the recursion

```
w(x) = cond(p(x), w(f(x)), x).
```

We realise this *semantically* inside the approximable-map framework: the
right-hand side, read as
a function of the unknown `w`, is an approximable operator

```
Wop : (D → D) → (D → D),   Wop(w) = λx. cond(p(x), w(f(x)), x),
```

built from the conditional `cond` of Exercise 3.26, evaluation `eval`, the
projections, pairing and
composition. The loop is then `whileFix = fixElement Wop`, the least fixed point
of `Wop`
(Theorem 4.1), and `whileMap = toApproxMap whileFix : D → D` the approximable
function it denotes.

We prove:

* `whileMap_rec` — the defining recursion `w(x) = cond(p(x), w(f(x)), x)`;
* `whileMap_true`  — if `p(x) = true`  then `w(x) = w(f(x))` (loop body runs);
* `whileMap_false` — if `p(x) = false` then `w(x) = x` (loop exits);
* `whileMap_bot`   — if `p(x) = ⊥`     then `w(x) = ⊥` (divergent test diverges);
* `whileMap_least` — leastness: any `w'` satisfying the recursion dominates
`whileMap`.

Everything is choice-free in spirit; the only classical input is inherited from
`cond`/`T`
(Example 1.2) and the project's `Element.ext` / `ext_of_toElementMap` machinery.
-/

namespace Domain.Neighborhood.Exercise512

open Domain.Neighborhood NeighborhoodSystem ApproximableMap
open Domain.Neighborhood.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- The body of the loop as a two-argument map `M : (D → D) × D → D`,
`M(w, x) = cond(p(x), w(f(x)), x)`. It is assembled from `cond`, `eval`, the
projections,
pairing and composition, hence approximable. -/
def bodyMap : ApproximableMap (prod (funSpace V V) V) V :=
  (cond V).comp
    (paired (p.comp (proj₁ (funSpace V V) V))
      (paired
        ((evalMap V V).comp
          (paired (proj₀ (funSpace V V) V) (f.comp (proj₁ (funSpace V V) V))))
        (proj₁ (funSpace V V) V)))

/-- Value of the loop body: `M(w, x) = cond(p(x), w(f(x)), x)`. -/
theorem bodyMap_apply (w : (funSpace V V).Element) (x : V.Element) :
    (bodyMap V p f).toElementMap (pair w x) =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((toApproxMap w).toElementMap (f.toElementMap x)) x)) := by
  rw [bodyMap, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

/-- The loop operator `Wop : (D → D) → (D → D)`, `Wop(w) = λx. cond(p(x), w(f(x)),
x)`. -/
def Wop : ApproximableMap (funSpace V V) (funSpace V V) := curry (bodyMap V p f)

/-- `Wop(w)(x) = cond(p(x), w(f(x)), x)`. -/
theorem Wop_apply (w : (funSpace V V).Element) (x : V.Element) :
    (toApproxMap ((Wop V p f).toElementMap w)).toElementMap x =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((toApproxMap w).toElementMap (f.toElementMap x)) x)) := by
  rw [Wop, toElementMap_curry_apply, bodyMap_apply]

/-- The `while`-loop element of the function space `D → D`: the least fixed point
of `Wop`. -/
def whileFix : (funSpace V V).Element := (Wop V p f).fixElement

/-- The approximable function `while p do f : D → D` denoted by `whileFix`. -/
def whileMap : ApproximableMap V V := toApproxMap (whileFix V p f)

/-- **Exercise 5.12 (Scott 1981, PRG-19).** The defining recursion of the
`while`-loop:
`w(x) = cond(p(x), w(f(x)), x)`. -/
theorem whileMap_rec (x : V.Element) :
    (whileMap V p f).toElementMap x =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((whileMap V p f).toElementMap (f.toElementMap x)) x)) := by
  have hfix : (Wop V p f).toElementMap (whileFix V p f) = whileFix V p f :=
    toElementMap_fixElement (Wop V p f)
  have := Wop_apply V p f (whileFix V p f) x
  rw [hfix] at this
  exact this

/-- If the test holds (`p(x) = true`), the loop runs the body: `w(x) = w(f(x))`. -/
theorem whileMap_true {x : V.Element} (hx : p.toElementMap x = Example23.trueElt) :
    (whileMap V p f).toElementMap x = (whileMap V p f).toElementMap (f.toElementMap x) := by
  rw [whileMap_rec, hx, Exercise326.cond_true]

/-- If the test fails (`p(x) = false`), the loop exits: `w(x) = x`. -/
theorem whileMap_false {x : V.Element} (hx : p.toElementMap x = Example23.falseElt) :
    (whileMap V p f).toElementMap x = x := by
  rw [whileMap_rec, hx, Exercise326.cond_false]

/-- If the test diverges (`p(x) = ⊥`), the loop diverges: `w(x) = ⊥`. -/
theorem whileMap_bot {x : V.Element} (hx : p.toElementMap x = Example23.botElt) :
    (whileMap V p f).toElementMap x = V.bot := by
  rw [whileMap_rec, hx, Exercise326.cond_bot]

/-- **Leastness.** Any `w'` satisfying the `while`-recursion `w'(x) = cond(p(x),
w'(f(x)), x)`
dominates the least solution `whileMap`. -/
theorem whileMap_least (w' : (funSpace V V).Element)
    (hw' : ∀ x : V.Element, (toApproxMap w').toElementMap x =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((toApproxMap w').toElementMap (f.toElementMap x)) x))) :
    whileFix V p f ≤ w' := by
  apply fixElement_le_of_toElementMap_le
  apply le_of_eq
  apply (funSpaceEquiv V V).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply]
  apply ext_of_toElementMap
  intro x
  rw [Wop_apply]
  exact (hw' x).symm

end Domain.Neighborhood.Exercise512
