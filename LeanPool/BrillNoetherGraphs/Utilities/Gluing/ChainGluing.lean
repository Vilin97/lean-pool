/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionWedgeDemazure
import LeanPool.BrillNoetherGraphs.Utilities.Grassmannian.OnceMarked

/-!
# Iterated vertex gluing and the chain transmission theorem

This is the assembly layer for Section 6 of the twice-marked banana paper: the
iterated vertex gluing of a chain of twice-marked graphs, and the transport of
`TransmissionExistence` along it.

## What is here and what it rests on

`TransmissionWedgeDemazure` already proves the two-factor step: opposite-side
wedge addition composes two transmission witnesses by the Demazure product
(`satisfiesTransmission_wedgeAddDivisor_star`, the paper's `eq:tauGlued`), and
the existential form of the same
(`transmissionExistence_vertexWedge_opposite_of_factorizations`) is conditional
on one named input, `HasBoundedDemazureFactorizations`: every finite ASP
permutation whose inversion length fits inside `gG + gH` splits as a Demazure
product of two factors of lengths at most `gG` and `gH`.

This file iterates that step along a chain, so the chain theorem is reduced to
exactly the same single input and nothing else.  `chainTransmissionExistence`
below is the ℓ-fold statement; the two-factor case is the existing theorem.

The bounded factorization property is an explicit hypothesis of this module's
general gluing theorem. `Demazure.Avoiding321.dprod_eq_iff` supplies the
factorization criterion used by its consumers.

## Universes

`vertexWedge` lands in `CFGraph.{max u v}`, so iterating it in full universe
generality would raise the level at every step.  Everything here therefore
works with all factors in a single fixed universe, where the wedge is closed.
-/

namespace Utilities

universe u

/-- A twice-marked graph, bundled so that an iterated wedge can change the
vertex type at every step. -/
structure MarkedGraph where
  graph : CFGraph.{u}
  left : graph.V
  right : graph.V

namespace MarkedGraph

/-- Glue the right mark of `M` to the left mark of `N`.  The result keeps the
left mark of `M` and the right mark of `N`, which is the marking the Demazure
composition theorem produces. -/
def wedge (M N : MarkedGraph.{u}) : MarkedGraph.{u} where
  graph := vertexWedge M.graph N.graph M.right N.left
  left := Sum.inl M.left
  right := wedgeRightVertex M.graph N.graph M.right N.left N.right

@[simp] theorem genus_wedge (M N : MarkedGraph.{u}) :
    genus (M.wedge N).graph = genus M.graph + genus N.graph :=
  genus_vertexWedge _ _ _ _

/-- The left-associated iterated vertex gluing of a chain, growing to the
right.  `chain M []` is `M`, and each further factor is glued onto the
accumulated right mark. -/
def chain (M : MarkedGraph.{u}) : List MarkedGraph.{u} → MarkedGraph.{u}
  | [] => M
  | N :: rest => chain (M.wedge N) rest

@[simp] theorem chain_nil (M : MarkedGraph.{u}) : M.chain [] = M := rfl

@[simp] theorem chain_cons (M N : MarkedGraph.{u}) (rest : List MarkedGraph.{u}) :
    M.chain (N :: rest) = (M.wedge N).chain rest := rfl

/-- Genera add along a chain: vertex identification creates no cycle. -/
theorem genus_chain (M : MarkedGraph.{u}) (L : List MarkedGraph.{u}) :
    genus (M.chain L).graph =
      genus M.graph + (L.map fun N => genus N.graph).sum := by
  induction L generalizing M with
  | nil => simp
  | cons N rest ih =>
      rw [chain_cons, ih, genus_wedge]
      simp only [List.map_cons, List.sum_cons]
      ring

end MarkedGraph

/-- The bounded Demazure factorization input, at every pair of budgets.

`HasBoundedDemazureFactorizations` is stated for one pair `(gG, gH)`; the
chain induction meets a new pair at every step, so it needs the uniform
version. -/
def HasAllBoundedDemazureFactorizations : Prop :=
  ∀ gG gH : ℤ, HasBoundedDemazureFactorizations gG gH

/-- **Chain gluing for transmission existence.**

If every factor of a chain has transmission existence at its own two marks,
then so does the whole chain at the two outer marks.  This is the ℓ-fold form
of `transmissionExistence_vertexWedge_opposite_of_factorizations`, and rests on
the same single input.

This is the transmission half of `thm:bngChain` (Theorem 1.13). -/
theorem chainTransmissionExistence
    (hFactor : HasAllBoundedDemazureFactorizations)
    (M : MarkedGraph.{u}) (L : List MarkedGraph.{u})
    (hM : TransmissionExistence M.graph M.left M.right)
    (hL : ∀ N ∈ L, TransmissionExistence N.graph N.left N.right) :
    TransmissionExistence (M.chain L).graph (M.chain L).left
      (M.chain L).right := by
  induction L generalizing M with
  | nil => simpa using hM
  | cons N rest ih =>
      rw [MarkedGraph.chain_cons]
      refine ih (M.wedge N) ?_ ?_
      · exact transmissionExistence_vertexWedge_opposite_of_factorizations
          M.graph N.graph M.right N.left M.left N.right hM
          (hL N (by simp)) (hFactor _ _)
      · intro P hP
        exact hL P (by simp [hP])

/-- **Chain gluing for once-marked Brill--Noether existence.**

The once-marked corollary of the chain theorem: if the chain's transmission
existence holds and the ASP permutation attached to a partition has the
Grassmannian profile, then the glued graph realizes that partition at its left
mark.

This is the shape in which `thm:bngChain` is used downstream — the partition
side is supplied by `transmissionExists_iff_onceMarkedBNExists`, the chain side
by `chainTransmissionExistence`. -/
theorem onceMarkedBNExists_chain
    (hFactor : HasAllBoundedDemazureFactorizations)
    (M : MarkedGraph.{u}) (L : List MarkedGraph.{u})
    (hM : TransmissionExistence M.graph M.left M.right)
    (hL : ∀ N ∈ L, TransmissionExistence N.graph N.left N.right)
    (hconn : graphConnected (M.chain L).graph)
    (tau : AspPerm) (lambda : YoungDiagram)
    (hProfile : GrassmannianPartitionProfile tau lambda)
    (hFinite : FiniteTransmissionPerm tau)
    (hLength : ((invSet tau).ncard : ℤ) ≤ genus (M.chain L).graph) :
    OnceMarkedBNExists (M.chain L).graph (M.chain L).left lambda := by
  refine (transmissionExists_iff_onceMarkedBNExists hconn (M.chain L).left
    (M.chain L).right tau lambda hProfile).mp ?_
  exact chainTransmissionExistence hFactor M L hM hL tau hFinite hLength

end Utilities
