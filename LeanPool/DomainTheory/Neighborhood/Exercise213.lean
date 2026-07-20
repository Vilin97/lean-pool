/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.ApproximableExercises
import LeanPool.DomainTheory.Neighborhood.Exercise122

/-!
# Exercise 2.13 (Scott 1981, PRG-19, §2) — approximable maps **are** the
continuous functions

> **EXERCISE 2.13.** (For topologists.) Recall Exercise 1.22 where it was shown
that any domain
> `|𝒟|` is a topological space. Prove from Exercise 2.9 that the functions `f :
|𝒟₀| → |𝒟₁|`
> determined by approximable mappings are exactly *the continuous functions
between these spaces.*

This file closes the loop between the §2 theory of approximable mappings
(`Approximable.lean`,
`ApproximableExercises.lean`) and the Exercise 1.22 topology on `|𝒟|`
(`Exercise122.lean`):

* **`continuous_toElementMap`** — every approximable mapping `f` induces a
*continuous* function
  `x ↦ f(x)`. Scott's hint: by Exercise 2.9, `f⁻¹[Y] = ⋃ {[X] ∣ Y ∈ f(↑X)}`, so
  the inverse image
  of a basic open is a union of basic opens, hence open.
* **`continuous_monotone`** — a continuous `c : |𝒟₀| → |𝒟₁|` is monotone for `⊑`
(the order is the
  specialization order, `le_iff_isOpen_imp`).
* **`mem_iff_principal_of_continuous`** — Scott's union formula for a *continuous*
`c`:
  `Y ∈ c(x) ↔ ∃ X ∈ x, Y ∈ c(↑X)`. (Forward: `c⁻¹[X]` open ∋ `x`; reverse: `↑X ⊑
  x` + monotone.)
* **`ofContinuous`** — the approximable mapping of a continuous function, built
from `ofMono` on the
  finite elements `↑X ↦ c(↑X)` (monotone by `continuous_monotone`).
* **`toElementMap_ofContinuous`** — the round trip: `ofContinuous c hc` induces
exactly `c`
  (`(ofContinuous c hc)(x) = c(x)`), combining Exercise 2.9 with the union
  formula.

Together: `f ↦ toElementMap f` and `c ↦ ofContinuous c` exhibit approximable
mappings `𝒟₀ → 𝒟₁`
and continuous functions `|𝒟₀| → |𝒟₁|` as the same thing.

Choice-free apart from the `ofMono`/Exercise-2.9 ingredients (whose uniqueness
companions are the
only classical pieces). -/

namespace Domain.Neighborhood

open NeighborhoodSystem

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

/-- **Exercise 2.13 (forward).** The elementwise function of an approximable
mapping is continuous.
For an open `U` and `x` with `f(x) ∈ U`, openness gives `Y` with `Y ∈ f(x)` and
`[Y] ⊆ U`; unfolding
`Y ∈ f(x)` produces `X ∈ x` with `X f Y`; then `[X] ⊆ f⁻¹U`, since any `x' ∈ [X]`
has `Y ∈ f(x')`
(via `X f Y`). -/
theorem continuous_toElementMap (f : ApproximableMap V₀ V₁) :
    Continuous (fun x => f.toElementMap x) := by
  rw [continuous_def]
  intro U hU
  change V₀.IsOpenFilter _
  intro x hx
  obtain ⟨Y, hY, hYU⟩ := hU (f.toElementMap x) hx
  obtain ⟨X, hxX, hrel⟩ := hY
  exact ⟨X, hxX, fun x' hx' => hYU ⟨X, hx', hrel⟩⟩

end ApproximableMap

namespace NeighborhoodSystem

/-- A continuous function between domains is monotone for the approximation order
`⊑`: this is
because `⊑` is recoverable from the topology (`le_iff_isOpen_imp`) and continuous
preimages of opens
are open and upward closed (`isOpen_isUpperSet`). -/
theorem continuous_monotone {c : V₀.Element → V₁.Element} (hc : Continuous c) : Monotone c := by
  intro x y hxy
  rw [V₁.le_iff_isOpen_imp]
  intro U hU hxU
  exact V₀.isOpen_isUpperSet (hU.preimage hc) hxU hxy

/-- **Exercise 2.13 — Scott's union formula for a continuous map.** For continuous
`c` and any
`x ∈ |𝒟₀|`: `Y ∈ c(x) ↔ ∃ X ∈ x, Y ∈ c(↑X)`.

* `→` : `c⁻¹[[Y]]` is open and contains `x`, so it contains a basic neighbourhood
`[X]` with `X ∈ x`;
  since `↑X ∈ [X]`, `Y ∈ c(↑X)`.
* `←` : `↑X ⊑ x` and `c` monotone (`continuous_monotone`) give `c(↑X) ⊑ c(x)`,
transporting `Y`. -/
theorem mem_iff_principal_of_continuous {c : V₀.Element → V₁.Element} (hc : Continuous c)
    (x : V₀.Element) {Y : Set β} :
    (c x).mem Y ↔ ∃ (X : Set α) (hx : x.mem X), (c (V₀.principal (x.sub hx))).mem Y := by
  constructor
  · intro hY
    have hxpre : x ∈ c ⁻¹' V₁.basicOpen Y := hY
    have hopen : IsOpen (c ⁻¹' V₁.basicOpen Y) := (V₁.isOpen_basicOpen Y).preimage hc
    obtain ⟨X, hxX, hXU⟩ := hopen x hxpre
    refine ⟨X, hxX, ?_⟩
    exact hXU (show V₀.principal (x.sub hxX) ∈ V₀.basicOpen X from ⟨x.sub hxX, subset_rfl⟩)
  · rintro ⟨X, hxX, hY⟩
    have hple : V₀.principal (x.sub hxX) ≤ x := fun Z hZ => x.up_mem hxX hZ.1 hZ.2
    exact (continuous_monotone hc hple) Y hY

end NeighborhoodSystem

namespace ApproximableMap

/-- **Exercise 2.13 (reverse).** The approximable mapping determined by a
continuous function `c`:
its action on the finite element `↑X` is the value `c(↑X)`, extended to all of
`𝒟₀` via `ofMono`.
Monotonicity of `X ↦ c(↑X)` is `continuous_monotone` together with the
inclusion-reversal
`X' ⊆ X ↔ ↑X ⊑ ↑X'`. -/
def ofContinuous (c : V₀.Element → V₁.Element) (hc : Continuous c) : ApproximableMap V₀ V₁ :=
  ofMono (fun _X hX => c (V₀.principal hX))
    (fun _X _X' hX hX' hX'X =>
      NeighborhoodSystem.continuous_monotone hc ((V₀.principal_le_iff hX hX').mpr hX'X))

/-- **Exercise 2.13 — the round trip.** `ofContinuous c hc` induces exactly `c`:
`(ofContinuous c hc)(x) = c(x)` for all `x`. Exercise 2.9 reduces `f(x)` to a
union over finite
approximants `↑X` (`X ∈ x`), where `ofMono` evaluates to `c(↑X)`; the union
formula
`mem_iff_principal_of_continuous` then re-assembles `c(x)`. -/
theorem toElementMap_ofContinuous (c : V₀.Element → V₁.Element) (hc : Continuous c)
    (x : V₀.Element) : (ofContinuous c hc).toElementMap x = c x := by
  apply Element.ext
  intro Y
  rw [toElementMap_mem_iff_principal, NeighborhoodSystem.mem_iff_principal_of_continuous hc]
  constructor
  · rintro ⟨X, hxX, hmem⟩
    refine ⟨X, hxX, ?_⟩
    rwa [ofContinuous, toElementMap_ofMono_principal] at hmem
  · rintro ⟨X, hxX, hmem⟩
    refine ⟨X, hxX, ?_⟩
    rwa [ofContinuous, toElementMap_ofMono_principal]

end ApproximableMap

end Domain.Neighborhood
