/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.Round
public import LeanPool.AsymptoticTrianglePacking.Internal.Conflict

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — Module C4b-0' : round-matching membership via
conflicts (deterministic bridge)

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

Bridges the round's matching (`roundMatching`, module C1) with the conflict structure (module
C4b-0): an edge is in the round's matching exactly when it is retained and none of its conflicting
edges is retained. This is the deterministic identity that lets the survival probability
`p·(1-p)^{c(e)}` (module C4b-1) be attached to actual matching membership.

Definitions come from `LeanPool.AsymptoticTrianglePacking.Internal.Basic`,
`LeanPool.AsymptoticTrianglePacking.Internal.Round`,
`LeanPool.AsymptoticTrianglePacking.Internal.Conflict`. Must be placeholder-free and
axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- **C4b-0' — survival iff retained with no retained conflict.** For a retained set `R ⊆ H`, an
edge `e` is in the round's matching iff `e ∈ R` and none of its conflicting edges lies in `R`. -/
theorem mem_roundMatching_iff_conflicts {H R : Finset (Finset V)} (hRH : R ⊆ H)
    {e : Finset V} :
    e ∈ roundMatching R ↔ e ∈ R ∧ ∀ f ∈ conflicts H e, f ∉ R := by
  rw [roundMatching, Finset.mem_filter]
  constructor
  · rintro ⟨heR, hdis⟩
    refine ⟨heR, ?_⟩
    intro f hf hfR
    rw [conflicts, Finset.mem_filter] at hf
    obtain ⟨_, hfe, hne⟩ := hf
    exact hne.ne_empty (Finset.disjoint_iff_inter_eq_empty.mp (hdis f hfR hfe))
  · rintro ⟨heR, hconf⟩
    refine ⟨heR, ?_⟩
    intro f hfR hfe
    by_contra hnd
    rw [Finset.not_disjoint_iff_nonempty_inter] at hnd
    exact hconf f (Finset.mem_filter.mpr ⟨hRH hfR, hfe, hnd⟩) hfR

end Hypergraph
