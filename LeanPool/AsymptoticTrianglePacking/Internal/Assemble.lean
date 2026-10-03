/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.Greedy
public import LeanPool.AsymptoticTrianglePacking.Internal.Round
public import LeanPool.AsymptoticTrianglePacking.Internal.Assembly
public import LeanPool.AsymptoticTrianglePacking.Internal.IterationSeq


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — Module D1 : iteration of nibble rounds
(deterministic scaffolding)

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

Given a per-round retention strategy `R` (a function assigning to the current hypergraph the set
of retained edges), `nibbleIter R H k` runs `k` rounds starting from `H`, returning the pair
`(accumulated matching, current residual hypergraph)`. Each round adds the round's matching and
passes to the residual (edges avoiding the covered vertices).

Deterministic invariants proved here (they hold for *any* strategy `R`):
* `nibbleResidual_subset` — the residual after `k` rounds is a sub-hypergraph of `H`.
* `nibbleResidual_uniform` — the residual stays `r`-uniform.

The probabilistic per-round shrinkage of the uncovered set (C4b-2 / C4) and the final assembly of
the accumulated matching (D2 / D3) build on top of this scaffolding.

Definitions come from `LeanPool.AsymptoticTrianglePacking.Internal.Basic` /
`LeanPool.AsymptoticTrianglePacking.Internal.Round`. Must be placeholder-free and axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

public section

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- Run `k` nibble rounds from `H` under retention strategy `R`, returning
`(accumulated matching, current residual)`. -/
def nibbleIter (R : Finset (Finset V) → Finset (Finset V)) (H : Finset (Finset V)) :
    ℕ → Finset (Finset V) × Finset (Finset V) :=
  nibbleIterSeq (fun _ => R) H

/-- The constant strategy sequence is the fixed-strategy iteration. -/
theorem nibbleIterSeq_const (R : Finset (Finset V) → Finset (Finset V)) (H : Finset (Finset V)) :
    ∀ k, nibbleIterSeq (fun _ => R) H k = nibbleIter R H k := by
  intro k
  rfl

/-- The residual hypergraph after `k` rounds. -/
def nibbleResidual (R : Finset (Finset V) → Finset (Finset V)) (H : Finset (Finset V)) (k : ℕ) :
    Finset (Finset V) := (nibbleIter R H k).2

/-- The matching accumulated over `k` rounds. -/
def nibbleMatching (R : Finset (Finset V) → Finset (Finset V)) (H : Finset (Finset V)) (k : ℕ) :
    Finset (Finset V) := (nibbleIter R H k).1

/-- **D1a — the residual is a sub-hypergraph of `H`.** -/
theorem nibbleResidual_subset (R : Finset (Finset V) → Finset (Finset V))
    (H : Finset (Finset V)) (k : ℕ) : nibbleResidual R H k ⊆ H := by
  change nibbleResidualSeq (fun _ => R) H k ⊆ H
  exact nibbleResidualSeq_subset (fun _ => R) H k

/-- **D1b — the residual stays `r`-uniform.** -/
theorem nibbleResidual_uniform {H : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r)
    (R : Finset (Finset V) → Finset (Finset V)) (k : ℕ) :
    IsUniform (nibbleResidual R H k) r := by
  change IsUniform (nibbleResidualSeq (fun _ => R) H k) r
  exact nibbleResidualSeq_uniform hr (fun _ => R) k

end Hypergraph

end


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — D3 assembly : the accumulated matching is a matching

Standalone, Mathlib-only. The accumulated matching after `k` nibble rounds (`nibbleMatching`, D1) is
a genuine matching of `H`. The key is a cross-round invariant: the residual hypergraph after `k`
rounds is disjoint from the support of the accumulated matching (each round only matches edges that
avoid all previously covered vertices). Hence the round matchings have pairwise-disjoint supports
and their union is a matching — the assembly step of T3.

Definitions from `LeanPool.AsymptoticTrianglePacking.Internal.Basic` /
`LeanPool.AsymptoticTrianglePacking.Internal.Greedy` /
`LeanPool.AsymptoticTrianglePacking.Internal.Round` /
`LeanPool.AsymptoticTrianglePacking.Internal.Iteration`.
Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- **D3a — accumulated matching stays inside `H`.** -/
theorem nibbleMatching_subset {R : Finset (Finset V) → Finset (Finset V)}
    (hR : ∀ H', R H' ⊆ H') (H : Finset (Finset V)) (k : ℕ) :
    nibbleMatching R H k ⊆ H := by
  change nibbleMatchingSeq (fun _ => R) H k ⊆ H
  exact nibbleMatchingSeq_subset (fun _ H' => hR H') H k

/-- **D3b — cross-round invariant.** Every edge of the residual after `k` rounds is disjoint from
the support of the accumulated matching. -/
theorem nibbleResidual_disjoint_support {R : Finset (Finset V) → Finset (Finset V)}
    (H : Finset (Finset V)) (k : ℕ) :
    ∀ e ∈ nibbleResidual R H k, Disjoint e (support (nibbleMatching R H k)) := by
  change ∀ e ∈ nibbleResidualSeq (fun _ => R) H k,
    Disjoint e (support (nibbleMatchingSeq (fun _ => R) H k))
  exact nibbleResidualSeq_disjoint_support (R := fun _ => R) H k

/-- **D3 — the accumulated matching is a matching of `H`.** -/
theorem nibbleMatching_isMatching {R : Finset (Finset V) → Finset (Finset V)}
    (hR : ∀ H', R H' ⊆ H') (H : Finset (Finset V)) (k : ℕ) :
    IsMatching H (nibbleMatching R H k) := by
  change IsMatching H (nibbleMatchingSeq (fun _ => R) H k)
  exact nibbleMatchingSeq_isMatching (fun _ H' => hR H') H k

end Hypergraph
