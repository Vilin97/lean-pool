/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
import Mathlib.Tactic

/-!
# Kernel-cheap spanning-tree connectivity certificates

The cut checker for a finite core enumerates every vertex subset.  Generated
cores can instead display a root, one parent and incident parent-edge slot for
every vertex, and a strictly decreasing rank along parent links.  Checking
those local facts is linear in the number of vertices.

The parent/rank argument is proved once below: in either side of a nontrivial
cut not containing the root, a minimum-rank vertex has its parent outside that
side, so its displayed parent edge crosses the cut.  The external program
which chooses this data is not trusted.
-/

-- The `Certificate` structure deliberately lives inside a namespace that already
-- ends in `Certificate`; renaming either would ripple through every consumer.
-- Lean v4.33 added `linter.dupNamespace`, which flags exactly this shape.
namespace MarkedGraphs.Certificate.SpanningTreeConnectivity
open Utilities.Certificate

open Utilities

open Finset

variable {n p : Nat}

/-- An unordered edge slot joins the displayed pair of vertices. -/
def EdgeJoins (core : ExplicitPotential.Core n p) (edge : Fin p)
    (first second : Fin n) : Prop :=
  (core.tail edge = first ∧ core.head edge = second) ∨
  (core.tail edge = second ∧ core.head edge = first)

/-- Proof-free rooted parent data for an ordered finite multigraph core. -/
structure Certificate (core : ExplicitPotential.Core n p) where
  root : Fin n
  parent : Fin n → Fin n
  parentEdge : Fin n → Fin p
  rank : Fin n → Nat

namespace Certificate

variable {core : ExplicitPotential.Core n p}

/-- Mathematical validity of every non-root parent link. -/
def Valid (data : Certificate core) : Prop :=
  ∀ vertex : Fin n,
    vertex = data.root ∨
      (data.rank (data.parent vertex) < data.rank vertex ∧
        EdgeJoins core (data.parentEdge vertex)
          vertex (data.parent vertex))

/-- Linear-time exact checker for rooted parent data. -/
def check (data : Certificate core) : Bool :=
  AffineCover.allFin fun vertex : Fin n =>
    decide (vertex = data.root) ||
      (decide (data.rank (data.parent vertex) < data.rank vertex) &&
        ((decide (core.tail (data.parentEdge vertex) = vertex) &&
            decide (core.head (data.parentEdge vertex) = data.parent vertex)) ||
          (decide (core.tail (data.parentEdge vertex) = data.parent vertex) &&
            decide (core.head (data.parentEdge vertex) = vertex))))

@[simp] theorem check_eq_true_iff (data : Certificate core) :
    data.check = true ↔ data.Valid := by
  simp [check, Valid, EdgeJoins]

private theorem edge_crosses_of_joins
    {edge : Fin p} {first second : Fin n} {S : Finset (Fin n)}
    (hJoin : EdgeJoins core edge first second)
    (hFirst : first ∈ S) (hSecond : second ∉ S) :
    (core.tail edge ∈ S ∧ core.head edge ∉ S) ∨
      (core.head edge ∈ S ∧ core.tail edge ∉ S) := by
  rcases hJoin with ⟨hTail, hHead⟩ | ⟨hTail, hHead⟩
  · left
    simpa [hTail, hHead] using And.intro hFirst hSecond
  · right
    simpa [hTail, hHead] using And.intro hFirst hSecond

private theorem edgeJoins_comm
    {edge : Fin p} {first second : Fin n}
    (hJoin : EdgeJoins core edge first second) :
    EdgeJoins core edge second first := by
  simpa [EdgeJoins, or_comm] using hJoin

/-- Valid rooted parent data imply the exact cut-connectedness predicate used
by explicit-potential cores. -/
theorem coreConnected_of_valid (data : Certificate core)
    (hValid : data.Valid) :
    core.Connected := by
  intro S hSplit
  obtain ⟨inside, outside, hInside, hOutside⟩ := hSplit
  by_cases hRoot : data.root ∈ S
  · let complement : Finset (Fin n) := Finset.univ \ S
    have hComplementNonempty : complement.Nonempty := by
      refine ⟨outside, ?_⟩
      simp [complement, hOutside]
    obtain ⟨vertex, hVertexComplement, hMinimal⟩ :=
      complement.exists_min_image data.rank hComplementNonempty
    have hVertexOutside : vertex ∉ S := by
      simpa [complement] using hVertexComplement
    have hVertexNeRoot : vertex ≠ data.root := by
      intro hEqual
      subst vertex
      exact hVertexOutside hRoot
    rcases hValid vertex with hEqual | ⟨hRank, hJoin⟩
    · exact (hVertexNeRoot hEqual).elim
    · have hParentNotComplement : data.parent vertex ∉ complement := by
        intro hParentComplement
        have hLe := hMinimal (data.parent vertex) hParentComplement
        omega
      have hParentInside : data.parent vertex ∈ S := by
        simpa [complement] using hParentNotComplement
      refine ⟨data.parentEdge vertex, ?_⟩
      exact edge_crosses_of_joins
        (edgeJoins_comm hJoin) hParentInside hVertexOutside
  · have hSNonempty : S.Nonempty := ⟨inside, hInside⟩
    obtain ⟨vertex, hVertexInside, hMinimal⟩ :=
      S.exists_min_image data.rank hSNonempty
    have hVertexNeRoot : vertex ≠ data.root := by
      intro hEqual
      subst vertex
      exact hRoot hVertexInside
    rcases hValid vertex with hEqual | ⟨hRank, hJoin⟩
    · exact (hVertexNeRoot hEqual).elim
    · have hParentOutside : data.parent vertex ∉ S := by
        intro hParentInside
        have hLe := hMinimal (data.parent vertex) hParentInside
        omega
      refine ⟨data.parentEdge vertex, ?_⟩
      exact edge_crosses_of_joins hJoin hVertexInside hParentOutside

/-- Checker acceptance implies exact ordered-core connectedness. -/
theorem coreConnected_of_check_eq_true (data : Certificate core)
    (hCheck : data.check = true) :
    core.Connected :=
  data.coreConnected_of_valid ((data.check_eq_true_iff).mp hCheck)

end Certificate

namespace SubdivisionGraph.Spec

/-- A checked parent certificate on the ordered core proves connectivity of
every positive subdivision as a chip-firing graph. -/
theorem graph_connected_of_spanningCheck
    (spec : SubdivisionGraph.Spec n p)
    (data : Certificate spec.core)
    (hCheck : data.check = true) :
    graph_connected spec.graph :=
  spec.graph_connected_of_coreConnected
    (data.coreConnected_of_check_eq_true hCheck)

end SubdivisionGraph.Spec

/-! ## Closed ordinary-kernel regressions -/

namespace Examples

def pathCore : ExplicitPotential.Core 3 2 where
  tail := ![0, 1]
  head := ![1, 2]

def pathCertificate : Certificate pathCore where
  root := 0
  parent := ![0, 0, 1]
  parentEdge := ![0, 0, 1]
  rank := ![0, 1, 2]

example : pathCertificate.check = true := by
  decide

theorem pathCore_connected : pathCore.Connected :=
  pathCertificate.coreConnected_of_check_eq_true (by decide)

def badRankCertificate : Certificate pathCore where
  root := 0
  parent := ![0, 0, 1]
  parentEdge := ![0, 0, 1]
  rank := ![0, 0, 0]

example : badRankCertificate.check = false := by
  decide

end Examples

end MarkedGraphs.Certificate.SpanningTreeConnectivity
