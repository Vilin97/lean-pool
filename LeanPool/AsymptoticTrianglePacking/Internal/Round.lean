/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — Module C1 : one nibble round (deterministic scaffolding)

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

A *nibble round* takes a set `R` of "retained" edges (in the probabilistic argument `R` is a
random subset of `H`, but every structural fact here is deterministic and holds for *any* `R`):

* `roundMatching R` — the retained edges that are isolated, i.e. disjoint from every other
  retained edge. These form a genuine matching.
* `covered R` — the vertices used by that matching.
* `residual H R` — the edges of `H` that avoid the covered vertices; the hypergraph the next
  round works on.

Results:
* `roundMatching_isMatching` — `roundMatching R` is a matching of the ambient `H` (when `R ⊆ H`).
* `residual_subset`, `residual_uniform` — the residual hypergraph is a sub-hypergraph of `H`
  and stays `r`-uniform.
* `residual_disjoint_covered` — every residual edge avoids the covered set (well-formedness of
  the iteration invariant).

The probabilistic content (expected sizes, concentration) is Layer C2/C3 and consumes Layer B.
Definitions (`degree`, `IsUniform`, `IsMatching`, `support`) come from `LeanPool.AsymptoticTrianglePacking.Internal.Basic` /
`LeanPool.AsymptoticTrianglePacking.Internal.Greedy`. Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import LeanPool.AsymptoticTrianglePacking.Internal.Greedy

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- The matching induced by a retained set `R`: the retained edges that are disjoint from every
other retained edge. -/
def roundMatching (R : Finset (Finset V)) : Finset (Finset V) :=
  R.filter (fun e => ∀ f ∈ R, f ≠ e → Disjoint e f)

/-- The vertices covered by the round's matching. -/
def covered (R : Finset (Finset V)) : Finset V := support (roundMatching R)

/-- The residual hypergraph: edges of `H` that avoid the covered vertices. -/
def residual (H R : Finset (Finset V)) : Finset (Finset V) :=
  H.filter (fun e => Disjoint e (covered R))

@[simp] theorem roundMatching_subset (R : Finset (Finset V)) : roundMatching R ⊆ R :=
  Finset.filter_subset _ _

/-- **C1a — the round's matching is a matching.** For `R ⊆ H`, `roundMatching R` is a matching
of `H`. -/
theorem roundMatching_isMatching {H R : Finset (Finset V)} (hRH : R ⊆ H) :
    IsMatching H (roundMatching R) where
  subset := (roundMatching_subset R).trans hRH
  disjoint := by
    intro e he f hf hef
    rw [roundMatching, Finset.mem_filter] at he
    exact he.2 f (roundMatching_subset R hf) (fun h => hef h.symm)

@[simp] theorem residual_subset (H R : Finset (Finset V)) : residual H R ⊆ H :=
  Finset.filter_subset _ _

/-- **C1b — residual stays `r`-uniform.** -/
theorem residual_uniform {H : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r)
    (R : Finset (Finset V)) : IsUniform (residual H R) r :=
  fun e he => hr e (residual_subset H R he)

/-- **C1c — residual edges avoid the covered vertices.** -/
theorem residual_disjoint_covered {H R : Finset (Finset V)} {e : Finset V}
    (he : e ∈ residual H R) : Disjoint e (covered R) := by
  rw [residual, Finset.mem_filter] at he
  exact he.2

end Hypergraph
