/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Plane
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Topology of the plane: the gaps Mathlib leaves

Appendix C of the blueprint lists the topology imported without proof. Almost all of it is in
Mathlib: compactness and Heine–Borel, the compact-to-Hausdorff homeomorphism criterion,
connectedness and its stability under images, unions through a common point, adjoining closure
points (`IsPreconnected.subset_closure`), a connected set inside a disjoint union of two opens
(`IsPreconnected.subset_left_of_subset_union`), `Metric.diam_closure`, thickenings, and the
two-piece pasting lemma (`continuousOn_union_iff_of_isClosed`).

This module collects the few that are not stated in the form the development uses.

## Blueprint

* `isOpen_connectedComponentIn` — Appendix C item 4: components of open subsets of the plane
  are open. The plane is locally connected, so this is Mathlib's, restated at `Plane` so that
  the instance is found once here rather than at every call site.
* `frontier_connectedComponentIn_compl_subset` — Appendix C item 5: the boundary of a component
  of the complement of a closed set lies in that closed set. This is the form Part I uses to
  recognize that a region's frontier sits on the curve.
* `continuousOn_union_of_isClosed` — Appendix C item 6, the pasting lemma, in the two-piece
  form the development pastes with.
-/

@[expose] public section

open Metric Set

namespace Schoenflies

namespace Plane

variable {U K : Set Plane} {x : Plane}

/-- Components of an open subset of the plane are open. The plane is locally connected. -/
theorem isOpen_connectedComponentIn (hU : IsOpen U) : IsOpen (connectedComponentIn U x) :=
  hU.connectedComponentIn

/-- Appendix C item 5. The frontier of a component of the complement of a closed set lies in
that closed set.

A frontier point off `K` would be a point of the open set `Kᶜ` in the closure of the
component; adjoining it keeps the component connected, so it was in the component already. -/
theorem frontier_connectedComponentIn_compl_subset (hK : IsClosed K) (x : Plane) :
    frontier (connectedComponentIn Kᶜ x) ⊆ K := by
  set C := connectedComponentIn Kᶜ x with hC
  have hCopen : IsOpen C := isOpen_connectedComponentIn hK.isOpen_compl
  intro z hz
  by_contra hzK
  -- `z` is a frontier point of the open set `C`, so it lies in `closure C` but not in `C`.
  rw [hCopen.frontier_eq] at hz
  obtain ⟨hzclosure, hzC⟩ := hz
  -- `C` is nonempty, since it has a frontier point in its closure.
  have hxU : x ∈ Kᶜ := by
    by_contra hx
    rw [hC, connectedComponentIn_eq_empty hx] at hzclosure
    simp at hzclosure
  -- Adjoining `z` keeps it connected and inside `Kᶜ`, so `z` was in the component already.
  have hsub : C ∪ {z} ⊆ Kᶜ := by
    refine union_subset (connectedComponentIn_subset _ _) ?_
    simpa using hzK
  have hconn : IsPreconnected (C ∪ {z}) :=
    (isPreconnected_connectedComponentIn (F := Kᶜ) (x := x)).subset_closure
      subset_union_left (union_subset subset_closure (by simpa using hzclosure))
  have : C ∪ {z} ⊆ C :=
    hconn.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hxU)) hsub
  exact hzC (this (Or.inr rfl))

/-- Appendix C item 6, the pasting lemma, two closed pieces. -/
theorem continuousOn_union_of_isClosed {f : Plane → Plane} {s t : Set Plane}
    (hs : IsClosed s) (ht : IsClosed t) (hfs : ContinuousOn f s) (hft : ContinuousOn f t) :
    ContinuousOn f (s ∪ t) :=
  (continuousOn_union_iff_of_isClosed hs ht).2 ⟨hfs, hft⟩

end Plane

end Schoenflies
