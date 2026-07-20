/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Basic
import Mathlib.Order.Zorn

/-!
# Exercise 1.24 (Scott 1981, PRG-19, §1) — every partial element extends to a
total one (AC)

Scott (for set theorists): using the Axiom of Choice, prove that in every domain a
partial element
can always be extended to a total element. (Hint: the union of every transfinite
chain of filters
is again a filter.)

This file formalizes:

* `chainUnion C hne hchain` — the union `⋃ C` of a non-empty **chain** `C` of
filters is itself a
  filter (`V.Element`); the only non-trivial axiom is `inter_mem`, which uses
  chain-directedness to
  find a single member of `C` containing both factors. Plus `le_chainUnion` (every
  member of the
  chain is `⊑` the union).
* `exists_total_ge x` — **with Zorn's lemma** (`zorn_le_nonempty_Ici₀`), every
element `x` has a
  *total* element `t` above it (`x ⊑ t ∧ IsTotal t`). The chains in `Ici x` are
  bounded above by
  their `chainUnion`, so Zorn produces a maximal — i.e. total — element.

Whether this is *equivalent* to AC is left as prose (Scott's question); we do not
formalize the
reversal. This is the explicitly **classical** exercise: `exists_total_ge`
legitimately uses
`Classical.choice` through `zorn_le_nonempty_Ici₀`. The `chainUnion`
*construction* is choice-free
(`[propext, Quot.sound]`). -/

namespace Domain.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.24 — the union of a chain of filters is a filter.** For a
non-empty chain `C` of
filters, `⋃ C = {X ∣ ∃ x ∈ C, X ∈ x}` is again a filter. The intersection axiom
uses chain
totality: given `X ∈ x` and `Y ∈ y` with `x, y ∈ C`, one of `x ⊑ y`, `y ⊑ x`
holds, and the larger
filter contains both `X` and `Y`, hence `X ∩ Y`. -/
def chainUnion (C : Set V.Element) (hne : C.Nonempty) (hchain : IsChain (· ≤ ·) C) : V.Element where
  mem X := ∃ x ∈ C, x.mem X
  sub := by rintro X ⟨x, _, hxX⟩; exact x.sub hxX
  master_mem := by obtain ⟨x, hxC⟩ := hne; exact ⟨x, hxC, x.master_mem⟩
  inter_mem := by
    rintro X Y ⟨x, hxC, hxX⟩ ⟨y, hyC, hyY⟩
    rcases hchain.total hxC hyC with hxy | hyx
    · exact ⟨y, hyC, y.inter_mem (hxy X hxX) hyY⟩
    · exact ⟨x, hxC, x.inter_mem hxX (hyx Y hyY)⟩
  up_mem := by
    rintro X Y ⟨x, hxC, hxX⟩ hY hXY
    exact ⟨x, hxC, x.up_mem hxX hY hXY⟩

/-- Every member of the chain approximates the union `⋃ C`. -/
theorem le_chainUnion (C : Set V.Element) (hne : C.Nonempty) (hchain : IsChain (· ≤ ·) C)
    {x : V.Element} (hx : x ∈ C) : x ≤ V.chainUnion C hne hchain :=
  fun _ hX => ⟨x, hx, hX⟩

/-- **Exercise 1.24 — partial elements extend to total ones (AC).** Using Zorn's
lemma, every
element `x` admits a *total* element `t` with `x ⊑ t`. The upper bound of any
non-empty chain in
`Ici x` is its `chainUnion`, so a maximal element exists; maximality is exactly
totality
(`IsMax = IsTotal`). -/
theorem exists_total_ge (x : V.Element) : ∃ t, V.IsTotal t ∧ x ≤ t := by
  obtain ⟨m, hxm, hmax⟩ :=
    zorn_le_nonempty_Ici₀ x
      (fun c _ hchain y hy =>
        ⟨V.chainUnion c ⟨y, hy⟩ hchain, fun z hz => V.le_chainUnion c ⟨y, hy⟩ hchain hz⟩)
      x le_rfl
  exact ⟨m, fun y hy => hmax hy, hxm⟩

end NeighborhoodSystem

end Domain.Neighborhood
