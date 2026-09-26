/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.InteriorScriptTransport
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSpec

/-!
# Localizing a guarding picture to one chip-free component

`AtanasovRanganathan.Guarding.GuardingSet` asks, for every chip-free core
vertex `v` and every degenerate spec `d` over the core, for

    Reaches d.graph (d.coreClassDivisor chips) (d.coreVertex v).

Every picture in the library discharges that by exhibiting a firing script on
the whole of `d.graph` and checking its residual there.  That is why the
library's pictures are indexed by the *ambient* core and not by the shape of
the component being guarded: a component of four vertices sitting in a
ten-vertex core has to have its Dhar arithmetic rewritten from scratch.

This file supplies the alternative.  `reaches_coreVertex_of_induced_script`
is the same conclusion, but its arithmetic hypothesis lives on the induced
subgraph cut out by a vertex set `A` -- typically the component together with
the chip vertices it hangs from.  The only extra obligation is that the script
vanish at the vertices of `A` which have an edge leaving `A`.

`interior_of_steps` is the combinatorial criterion which discharges the
interiority obligation on a subdivision: a vertex is interior to `A` as soon
as every unit step touching it has its other end in `A`.

## What this buys

A component's picture becomes a statement about the component, provable once
and reusable in every ambient core the shape occurs in.  Concretely, the
genus-six "two-banana chain" (auxiliary calculations Sec. 5a)
occupies six of core 46's ten vertices; localizing to it replaces a genus-six
Dhar calculation by a genus-two one with two frozen endpoints.

## Layering

`Utilities` only: `DegSpec` already lives here, so `LowGenus` picture files
may use this directly.
-/

@[expose] public section

namespace Utilities.Gluing

open Utilities.Certificate.StrongSeparator
open Utilities.Certificate.DegenerateSpec

universe u

variable {n p : ℕ}

namespace DegSpec

open Utilities.Certificate.DegenerateSpec.DegSpec

/-- **Interiority on a subdivision is a statement about unit steps.**  If every
unit step with an end at `x` has its other end inside `A`, then no edge at `x`
leaves `A`. -/
theorem interior_of_steps (d : DegSpec n p) (A : Finset d.Vertex) (x : d.Vertex)
    (hLeft : ∀ s : d.Step, d.stepLeft s.1 s.2 = x → d.stepRight s.1 s.2 ∈ A)
    (hRight : ∀ s : d.Step, d.stepRight s.1 s.2 = x → d.stepLeft s.1 s.2 ∈ A) :
    Interior d.graph A x := by
  classical
  intro w hw
  rw [d.num_edges_eq_card_filter_steps]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s _
  rintro (hEdge | hEdge)
  · have hL : d.stepLeft s.1 s.2 = x := congrArg Prod.fst hEdge
    have hR : d.stepRight s.1 s.2 = w := congrArg Prod.snd hEdge
    exact hw (hR ▸ hLeft s hL)
  · have hL : d.stepLeft s.1 s.2 = w := congrArg Prod.fst hEdge
    have hR : d.stepRight s.1 s.2 = x := congrArg Prod.snd hEdge
    exact hw (hL ▸ hRight s hR)

/-- **The shape of a guarding discharge, localized.**

This is `GuardingSet.guard`'s conclusion, obtained from a local Dhar move
computed inside the induced subgraph on `A`.  `hOff` is free for a chip
assignment, since `coreClassDivisor` of nonnegative weights is effective. -/
theorem reaches_coreVertex_of_induced_script (d : DegSpec n p)
    (weight : Fin n → ℤ) (hWeight : ∀ v, 0 ≤ weight v)
    {A : Finset d.Vertex} (hA : A.Nonempty)
    {v : Fin n} (hv : d.coreVertex v ∈ A)
    {t : firingScript (inducedSubgraph d.graph A hA)} (ht : SupportInterior t)
    (hEff : effective
      ((fun x : (inducedSubgraph d.graph A hA).V => d.coreClassDivisor weight x.val)
        - oneChip (⟨d.coreVertex v, hv⟩ : (inducedSubgraph d.graph A hA).V)
        + prin (inducedSubgraph d.graph A hA) t)) :
    Reaches d.graph (d.coreClassDivisor weight) (d.coreVertex v) :=
  reaches_of_induced_script hA
    (fun x _ => d.coreClassDivisor_effective weight hWeight x) hv ht hEff

end DegSpec

end Utilities.Gluing
