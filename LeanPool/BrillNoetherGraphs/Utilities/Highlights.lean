/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gonality.LegalFiring
public import LeanPool.BrillNoetherGraphs.Utilities.Gonality.DivisorialGonality
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.UnderlyingSimpleGraph
public import LeanPool.BrillNoetherGraphs.Utilities.Iso.FossilTopology
public import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphIso

/-!
# Highlights of the `Utilities` library

**A public interface, in one file.**  Every main theorem of this library is
restated below as an `example` whose type is written out in full and whose
proof is the real theorem.  Nothing here is new mathematics — there is not a
single new definition or theorem in this file.

The point is twofold.

* **For a reader.**  The complete statement of each headline result is visible
  here, with all of its binders and hypotheses, without navigating ninety
  modules.
* **For the build.**  Because each `example` is checked by the kernel against
  the real declaration, a refactor that silently changes a statement — weakens
  a hypothesis, strengthens a conclusion, renames a definition — breaks *this*
  file loudly, in seconds.  That is the whole reason the statements are spelled
  out rather than abbreviated.

`Utilities` is **infrastructure**: it holds only what more than one downstream
programme uses.  Its headline content is accordingly an API rather than a
single named theorem — the divisorial gonality interface (attainment, the
agreement of the two gonality conventions, the nested legal chain to a
`q`-reduced form) and the transport of Brill–Noether data along a relabelling.

The named theorems that *used* to head this file now head their own libraries,
because each is an application of this infrastructure rather than a piece of
it:

* `treewidth ≤ gonality` (van Dobben de Bruyn–Gijswijt) — `TreewidthGonality/`,
  restated in `TreewidthGonality/Highlights.lean`;
* the discrete/metric gonality gap (van Dobben de Bruyn–Smit–van der Wegen) —
  `Tricycle/`, restated in `Tricycle/Highlights.lean`.
-/

@[expose] public section

namespace Utilities.Highlights

open Utilities Utilities.Gonality

universe u

/-! ## The key definitions

Re-exported here so that the statements below read without qualification. -/

/-- The simple graph underlying a chip-firing multigraph: `v` and `w` are
adjacent when `numEdges G v w > 0`.  "The treewidth of a multigraph" means the
treewidth of this graph — parallel edges do not change it.
(`Utilities/Foundations/UnderlyingSimpleGraph.lean`) -/
alias underlyingSimpleGraph := Utilities.underlyingSimpleGraph

/-- The degrees of the effective divisors of rank at least one.
(`Utilities/Gonality/DivisorialGonality.lean`) -/
alias gonalitySet := Utilities.Gonality.gonalitySet

/-- **Divisorial gonality**: the least degree of an effective divisor of rank
at least one, as a natural number.  An `Nat.sInf`, so it is attained whenever
`gonalitySet` is nonempty — which it is on a connected graph.
(`Utilities/Gonality/DivisorialGonality.lean`) -/
alias divisorialGonality := Utilities.Gonality.divisorialGonality

/-- Iterated set firing: `fireChain G D U i` fires `U 0, …, U (i-1)` in turn.
(`Utilities/Gonality/LegalFiring.lean`) -/
alias fireChain := Utilities.Gonality.fireChain

/-- An **isomorphism of chip-firing graphs**: a vertex bijection preserving
every edge multiplicity.  (`Utilities/Iso/GraphIso.lean`) -/
alias CFGraphIso := Utilities.CFGraphIso

/-- There is a divisor of degree `d` and rank at least `r` on `G`.
(`Utilities/Foundations/Parameters.lean`) -/
alias BNExists := Utilities.BNExists

/-- The **fossil**: the library's short name for the degree-one Abel--Jacobi
image, equivalently the 2-edge-connectivization of a connected graph.
(`Utilities/Iso/Fossil.lean`) -/
alias fossil := Utilities.fossil

/-! ## The gonality API

This is what every downstream gonality argument in the repository runs on. -/

/-- The two gonalities agree: the dependency's `ℤ`-valued `gonality` is the
coercion of the `ℕ`-valued `divisorialGonality`. -/
example (G : CFGraph) (h_conn : graphConnected G) :
    gonality h_conn = (divisorialGonality G : ℤ) :=
  Utilities.Gonality.gonality_eq_divisorialGonality h_conn

/-- The gonality is **attained** by an actual divisor. -/
example (G : CFGraph) (h_conn : graphConnected G) :
    ∃ D : CFDiv G, effective D ∧ deg D = (divisorialGonality G : ℤ) ∧
      rank G D ≥ 1 :=
  Utilities.Gonality.exists_divisor_of_divisorialGonality h_conn

/-! ## The Abel--Jacobi image / fossil -/

/-- Passing to the fossil preserves genus and divisorial gonality. -/
example (G : CFGraph) (h_conn : graphConnected G) :
    genus (fossil G) = genus G ∧
      divisorialGonality (fossil G) = divisorialGonality G :=
  ⟨Utilities.genus_fossil G h_conn,
    Utilities.divisorialGonality_fossil G h_conn⟩

/-- The fossil has no one-edge cut: it is the 2-edge-connectivization in the
literal cut-multiplicity sense. -/
example (G : CFGraph) (h_conn : graphConnected G) :
    TwoEdgeCutCondition (fossil G) :=
  Utilities.twoEdgeCutCondition_fossil G h_conn

/-- Every-rank Brill--Noether existence is invariant under fossilization. -/
example (G : CFGraph) (h_conn : graphConnected G) (r d : ℤ) :
    BNExists G r d ↔ BNExists (fossil G) r d :=
  Utilities.BNExists_fossil_iff G h_conn r d

/-- **The nested legal chain** (van Dobben de Bruyn–Gijswijt, Lemma 1.3): an
effective divisor reaches its `q`-reduced form through legal firings whose
fired sets are nested and avoid `q`. -/
example (G : CFGraph) (h_conn : graphConnected G) (q : G.V)
    {D : CFDiv G} (hD : effective D) :
    ∃ (k : ℕ) (U : ℕ → Finset G.V),
      (∀ i, i < k → U i ⊆ Finset.univ.erase q) ∧
      (∀ i, i < k → (U i).Nonempty) ∧
      (∀ i j, i ≤ j → j < k → U i ⊆ U j) ∧
      (∀ i, i < k → legalSet G (fireChain G D U i) (U i)) ∧
      qReduced G q (fireChain G D U k) :=
  Utilities.Gonality.exists_nested_legal_chain h_conn q hD

/-! ## Transport along a relabelling -/

/-- Brill–Noether existence is invariant under graph isomorphism. -/
example {G H : CFGraph} (φ : CFGraphIso G H) (r d : ℤ) :
    BNExists H r d ↔ BNExists G r d :=
  φ.BNExists_iff r d

/-- Baker–Norine rank is invariant under relabelling. -/
example {G H : CFGraph} (φ : CFGraphIso G H) (D : CFDiv G) :
    rank H (φ.mapDiv D) = rank G D :=
  φ.rank_mapDiv D

end Utilities.Highlights
