/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.OneEdgeSplitRefinement

/-!
# Iterated canonical bivalent splits

This module packages a finite sequence of the canonical positive one-edge
splits from `OneEdgeSplitRefinement`.  The numbers of core vertices and edge
slots change at every step, so `PackedSpec` hides those indices while each
`CanonicalSplitStep` retains the split occurrence, its two positive lengths,
and the required length sum.

Composing the checked one-edge `LaplacianEquiv`s gives a reusable transport
from the original subdivision presentation to any presentation obtained by a
finite chain of positive bivalent refinements.  In particular, Brill--Noether
existence is invariant along the whole chain.
-/

@[expose] public section

namespace Utilities.Certificate.IteratedSplitRefinement

open ExplicitPotential SubdivisionGraph
open Utilities.Certificate.OneEdgeSplitRefinement

/-- A subdivision specification together with its dependent core sizes. -/
structure PackedSpec where
  /-- The number of core vertices in the packed subdivision specification. -/
  n : ℕ
  /-- The number of ordered core slots in the packed subdivision specification. -/
  p : ℕ
  /-- The positive-length subdivision specification with the stored vertex and slot counts. -/
  spec : SubdivisionGraph.Spec n p

namespace PackedSpec

/-- The finite graph presented by a packed subdivision specification. -/
abbrev graph (packed : PackedSpec) : CFGraph := packed.spec.graph

/-- Its subdivision vertices. -/
abbrev Vertex (packed : PackedSpec) : Type := packed.spec.Vertex

end PackedSpec

/-- The target presentation produced by one canonical bivalent split. -/
def splitPacked (source : PackedSpec) (split : Fin source.p)
    (first second : ℕ) (hFirst : 0 < first) (hSecond : 0 < second) :
    PackedSpec where
  n := source.n + 1
  p := source.p + 1
  spec := splitSpec source.spec split first second hFirst hSecond

/-- A proof-carrying canonical bivalent split between packed presentations.

`target_eq` makes the target exactly the canonical split.  Relabeling a
separately generated presentation remains a subsequent `LaplacianEquiv`
obligation. -/
structure CanonicalSplitStep (source target : PackedSpec) where
  /-- The source slot divided by this canonical split step. -/
  splitSlot : Fin source.p
  /-- The positive length of the first segment created by the split. -/
  firstLength : ℕ
  /-- The positive length of the second segment, completing the original slot length. -/
  secondLength : ℕ
  firstLength_pos : 0 < firstLength
  secondLength_pos : 0 < secondLength
  length_sum : source.spec.length splitSlot = firstLength + secondLength
  target_eq : target = splitPacked source splitSlot firstLength secondLength
    firstLength_pos secondLength_pos

namespace CanonicalSplitStep

variable {source target : PackedSpec}

/-- The checked one-edge equivalence attached to a canonical split step. -/
def laplacianEquiv (step : CanonicalSplitStep source target) :
    LaplacianEquiv source.graph target.graph := by
  obtain ⟨splitSlot, firstLength, secondLength, firstLength_pos,
    secondLength_pos, length_sum, rfl⟩ := step
  exact canonicalSplitLaplacianEquiv source.spec splitSlot
    firstLength secondLength firstLength_pos secondLength_pos length_sum

end CanonicalSplitStep

/-- A data-carrying reflexive-transitive closure of canonical split steps.

Unlike `Relation.ReflTransGen`, this lives in `Type`: the endpoint graph
equivalence retains the concrete split data instead of eliminating a
proposition into computational data. -/
inductive CanonicalSplitChain (source : PackedSpec) : PackedSpec → Type
  | refl : CanonicalSplitChain source source
  | tail {middle target : PackedSpec} :
      CanonicalSplitChain source middle → CanonicalSplitStep middle target →
        CanonicalSplitChain source target

namespace CanonicalSplitChain

variable {source target : PackedSpec}

/-- Regard one canonical split as a one-step chain. -/
def single (step : CanonicalSplitStep source target) :
    CanonicalSplitChain source target :=
  .tail .refl step

/-- Concatenate two canonical split chains. -/
def append (first : CanonicalSplitChain source target) :
    ∀ {final : PackedSpec}, CanonicalSplitChain target final →
      CanonicalSplitChain source final
  | _, .refl => first
  | _, .tail chain step => .tail (append first chain) step

/-- Compose the one-edge equivalences along a split chain. -/
def laplacianEquivAux (source : PackedSpec) :
    ∀ {target : PackedSpec}, CanonicalSplitChain source target →
      LaplacianEquiv source.graph target.graph
  | _, .refl => identityLaplacianEquiv source.spec
  | _, .tail chain step =>
      (laplacianEquivAux source chain).trans step.laplacianEquiv

/-- Compose the one-edge equivalences along a split chain. -/
def laplacianEquiv (chain : CanonicalSplitChain source target) :
    LaplacianEquiv source.graph target.graph :=
  laplacianEquivAux source chain

/-- The vertex transport determined by a split chain. -/
def vertexEquiv (chain : CanonicalSplitChain source target) :
    source.Vertex ≃ target.Vertex :=
  chain.laplacianEquiv.toEquiv

/-- Iterated positive bivalent splitting preserves Brill--Noether
existence, in both directions and for every rank and degree. -/
theorem bnExists_iff (chain : CanonicalSplitChain source target) (r d : ℤ) :
    BNExists source.graph r d ↔ BNExists target.graph r d :=
  chain.laplacianEquiv.bnExists_iff r d

end CanonicalSplitChain

end Utilities.Certificate.IteratedSplitRefinement
