/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Theorem41

/-!
# Exercise 4.23 (Scott 1981, PRG-19, Lecture IV) — Eilenberg's uniqueness
criterion

(Suggested by S. Eilenberg.) Let `f : 𝒟 → 𝒟` be approximable, and let `aₙ : 𝒟 → 𝒟`
be a sequence of
approximable maps with

* (i)   `a₀(x) = ⊥` for all `x`;
* (ii)  `aₙ ⊑ aₙ₊₁` in `𝒟 → 𝒟`;
* (iii) `⊔ₙ aₙ = I_𝒟` (the identity);
* (iv)  `aₙ₊₁ ∘ f = aₙ₊₁ ∘ f ∘ aₙ`.

**Then `f` has a unique fixed point** (`f_unique_fixedPoint`).

Existence is the Fixed-point Theorem 4.1 (`fix f = ⊔ₙ fⁿ(⊥)`). For uniqueness,
suppose `x = f(x)`.
Following Scott's hint, one shows by induction on `n` that

  `aₙ(x) ⊑ aₙ(fix f)`            (`approx_le`),

the step using (iv) twice and `x = f(x)`, `fix = f(fix)`:
`aₙ₊₁(x) = aₙ₊₁(f(x)) = aₙ₊₁(f(aₙ(x))) ⊑ aₙ₊₁(f(aₙ(fix))) = aₙ₊₁(f(fix)) =
aₙ₊₁(fix)`.
Then, since `⊔ₙ aₙ = I` evaluates pointwise to `x = ⊔ₙ aₙ(x)` and `aₙ(x) ⊑ aₙ(fix)
⊑ fix`, the least
upper bound `x` lies below `fix`; together with `fix ⊑ x` (minimality of the least
fixed point) this
forces `x = fix`. Hence the fixed point is unique.

We phrase conditions (ii)+(iii) together in the pointwise form `IsLUB {aₙ(x)} x`
(equivalent to
`⊔ₙ aₙ = I` via the pointwise suprema of the function space `𝒟 → 𝒟`, Theorem
3.10): that `x` is the
*least upper bound* of the family `{aₙ(x)}` already records both that the family
is bounded by `x`
(absorbing (ii)'s monotonicity into the LUB) and that nothing smaller bounds it.
The argument uses
only the project's permitted element-extensionality through `Theorem41`.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 4.23 (Scott 1981, PRG-19) — Eilenberg.** If `f` is approximable and
`aₙ` is an
*approximation scheme* — (i) `a₀ = ⊥`, (ii) increasing, (iii) `⊔ₙ aₙ = I`
(pointwise `IsLUB`),
(iv) `aₙ₊₁ ∘ f = aₙ₊₁ ∘ f ∘ aₙ` — then `f` has a **unique** fixed point.

The unique fixed point is `fix f` (Theorem 4.1). -/
theorem f_unique_fixedPoint (f : ApproximableMap V V) (a : ℕ → ApproximableMap V V)
    (ha0 : ∀ x, (a 0).toElementMap x = V.bot)
    (hlub : ∀ x, IsLUB {y | ∃ n, y = (a n).toElementMap x} x)
    (hcomm : ∀ n x, (a (n + 1)).toElementMap (f.toElementMap x) =
      (a (n + 1)).toElementMap (f.toElementMap ((a n).toElementMap x))) :
    ∃! x, f.toElementMap x = x := by
  set fix := f.fixElement with hfixdef
  have hfixed : f.toElementMap fix = fix := toElementMap_fixElement f
  refine ⟨fix, hfixed, ?_⟩
  intro x hx
  -- `fix ⊑ x`: minimality of the least fixed point.
  have hle : fix ≤ x := fixElement_le_of_toElementMap_le f (le_of_eq hx)
  -- `aₙ(x) ⊑ aₙ(fix)` by induction on `n` (Scott's hint).
  have approx_le : ∀ n, (a n).toElementMap x ≤ (a n).toElementMap fix := by
    intro n
    induction n with
    | zero => rw [ha0 x]; exact bot_le
    | succ k ih =>
      have h1 : (a (k + 1)).toElementMap x =
          (a (k + 1)).toElementMap (f.toElementMap ((a k).toElementMap x)) := by
        rw [← hcomm k x, hx]
      have h2 : (a (k + 1)).toElementMap (f.toElementMap ((a k).toElementMap fix)) =
          (a (k + 1)).toElementMap fix := by
        rw [← hcomm k fix, hfixed]
      rw [h1, ← h2]
      exact toElementMap_mono (a (k + 1)) (toElementMap_mono f ih)
  -- each `aₙ(fix) ⊑ fix` (since `fix` is an upper bound of its own scheme).
  have hfix_ub : ∀ n, (a n).toElementMap fix ≤ fix := fun n => (hlub fix).1 ⟨n, rfl⟩
  -- so `fix` is an upper bound of `{aₙ(x)}`, hence `x = ⊔ₙ aₙ(x) ⊑ fix`.
  have hge : x ≤ fix := by
    apply (hlub x).2
    rintro y ⟨n, rfl⟩
    exact le_trans (approx_le n) (hfix_ub n)
  exact le_antisymm hge hle

end ApproximableMap

end Domain.Neighborhood
