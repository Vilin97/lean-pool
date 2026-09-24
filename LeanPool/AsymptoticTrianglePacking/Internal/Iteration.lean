/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

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

@[expose] public section

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
