/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.Greedy
public import LeanPool.AsymptoticTrianglePacking.Internal.Round
public import LeanPool.AsymptoticTrianglePacking.Internal.Iteration
public import LeanPool.AsymptoticTrianglePacking.Internal.Assembly

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
