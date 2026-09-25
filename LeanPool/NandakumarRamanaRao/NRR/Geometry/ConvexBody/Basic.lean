/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Topology.Closure

/-!
# `NRR.Geometry.ConvexBody` — bundled compact convex bodies with nonempty interior

This module introduces the central bundled object

```
NRR.Geometry.ConvexBody E
```

a **compact convex** subset of a topological `ℝ`-module `E` with **nonempty interior**.
downstream modules are expected to use `ConvexBody` through the accessor/extensionality API below
without ever unfolding its fields.

## Relationship to Mathlib's `ConvexBody`

Mathlib already ships a bundled

```
_root_.ConvexBody V -- carrier, convex', isCompact', nonempty'
```

(see `Mathlib.Analysis.Convex.Body`), but its solidity requirement is only that the carrier be
**nonempty** (`nonempty'`), *not* that the interior be nonempty. The fair-partition
development needs the stronger *solid* condition (nonempty interior, hence positive
Lebesgue measure in finite dimensions), so we introduce a dedicated bundled structure whose
proof field is `interior_nonempty'`. To avoid clashing with the root `ConvexBody` used
elsewhere in the library, this structure lives in the `NRR.Geometry` namespace; the two
never collide because that namespace is not opened by the modules that use Mathlib's
`_root_.ConvexBody`.

## Design notes

* Typeclasses are kept minimal: the whole API only needs `[TopologicalSpace E]`,
 `[AddCommMonoid E]`, `[Module ℝ E]` (enough to state `Convex ℝ`, `IsCompact`, and `interior`).
 Finite dimensionality / inner-product structure is intentionally *not* required here and is
 added by downstream modules where genuinely needed.
* We coerce to `Set E` (via a `Coe` instance) and provide a `Membership` instance, but do not
 coerce `ConvexBody` to a type.
* No area/perimeter/measure fields, and no separate full-dimensionality field: nonempty
 interior already encodes solidity.

## Import policy

Following the library-wide policy fixed in `AI_CONTEXT.md`, this file
uses the whole-library `import Mathlib`. The concrete dependencies are lightweight
(`Convex`, `IsCompact`, `interior`, `Set` membership/extensionality).
-/

@[expose] public section

namespace NRR.Geometry

variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-- A **convex body** (in the solid sense used throughout this development): a compact convex
subset of a topological `ℝ`-module with nonempty interior. -/
structure ConvexBody (E : Type*) [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] where
  /-- The underlying set of points of the convex body. -/
  carrier : Set E
  /-- The carrier is convex. -/
  convex' : Convex ℝ carrier
  /-- The carrier is compact. -/
  isCompact' : IsCompact carrier
  /-- The carrier has nonempty interior (solidity). -/
  interior_nonempty' : (interior carrier).Nonempty

namespace ConvexBody

/-- Coercion of a convex body to its underlying set of points. -/
instance : Coe (ConvexBody E) (Set E) := ⟨carrier⟩

/-- Membership `x ∈ K` unfolds to membership in the carrier. -/
instance : Membership E (ConvexBody E) := ⟨fun K x => x ∈ K.carrier⟩


@[simp] theorem mem_coe (K : ConvexBody E) (x : E) :
    x ∈ (K : Set E) ↔ x ∈ K := Iff.rfl

/-- The carrier of a convex body is convex. -/
theorem convex (K : ConvexBody E) : Convex ℝ (K : Set E) := K.convex'

/-- The carrier of a convex body is compact. -/
theorem isCompact (K : ConvexBody E) : IsCompact (K : Set E) := K.isCompact'

/-- The carrier of a convex body has nonempty interior. -/
theorem interior_nonempty (K : ConvexBody E) : (interior (K : Set E)).Nonempty :=
  K.interior_nonempty'

/-- A convex body is nonempty (its interior is nonempty and the interior is contained in it). -/
theorem nonempty (K : ConvexBody E) : (K : Set E).Nonempty :=
  K.interior_nonempty.mono interior_subset

/-- **Extensionality**: two convex bodies with equal carriers are equal. The remaining proof
fields are equal by proof irrelevance. -/
@[ext] theorem ext {K L : ConvexBody E} (h : (K : Set E) = (L : Set E)) : K = L := by
  cases K; cases L; congr

/-- Membership extensionality: two convex bodies are equal iff they have the same points. -/
theorem ext_iff_mem {K L : ConvexBody E} :
    K = L ↔ ∀ x : E, x ∈ (K : Set E) ↔ x ∈ (L : Set E) := by
  rw [ConvexBody.ext_iff, Set.ext_iff]

@[simp] theorem coe_mk (s : Set E) (hconv hcomp hint) :
    ((ConvexBody.mk s hconv hcomp hint : ConvexBody E) : Set E) = s := rfl

end ConvexBody

end NRR.Geometry
