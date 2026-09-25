/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSeparator

/-!
# The common closing step of an Atanasov--Ranganathan closed-face row

Every completed genus-five row ends with the same four moves: the displayed
degree-four divisor reaches every contracted core class, hence has rank at
least one by the closed-face separator theorem, hence is a
`DegreeFourDharPencil`, hence witnesses a
`ClosedSubdivisionDharConstruction`.

Only the middle statement is row specific.  This file packages the other three
once, so that a row's closing theorem is a single application.
-/

@[expose] public section

namespace AtanasovRanganathan.Configurations

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral

/-- **The closing wrapper.**  A family of effective degree-four divisors, one
for each degenerate spec on a fixed connected core, which reaches every
contracted core class, is a closed-orthant AR construction.

The `reaches` hypothesis is stated on an arbitrary `DegSpec` with the two
facts a face proof actually uses: its core is the fixed one, and its
representative map is exactly reachability through the zero-length slots.
That is the shape the row lemmas already have, so each row's tail becomes one
application of this theorem. -/
theorem ClosedSubdivisionDharConstruction.ofReachesCoreClasses
    {n p : ℕ} {core : Certificate.ExplicitPotential.Core n p}
    (core_nonempty : 0 < n) (core_connected : core.Connected)
    (divisor : ∀ d : DegSpec n p, CFDiv d.graph)
    (divisor_effective : ∀ d : DegSpec n p, effective (divisor d))
    (divisor_degree : ∀ d : DegSpec n p, deg (divisor d) = 4)
    (reaches : ∀ d : DegSpec n p, d.core = core →
      (∀ x y : Fin n,
        d.rep x = d.rep y ↔ ReachIn core (zeroSlots d.length) x y) →
      ∀ center : Fin n,
        Reaches d.graph (divisor d) (d.coreVertex center)) :
    ClosedSubdivisionDharConstruction core core_nonempty := by
  intro length forest not_loopy
  let d := faceSpec core core_nonempty length forest not_loopy
  have hCore : d.core = core := rfl
  have hRepReach : ∀ x y : Fin n,
      d.rep x = d.rep y ↔ ReachIn core (zeroSlots d.length) x y := by
    intro x y
    exact compFold_iff core (zeroSlots length) x y
  refine ⟨DegreeFourDharPencil.ofEffectiveRankOne (divisor d)
    (divisor_effective d) (divisor_degree d) ?_⟩
  refine d.rank_ge_one_of_reaches_coreVertices ?_ (divisor d)
    (reaches d hCore hRepReach)
  rw [hCore]
  exact core_connected

/-- **The face-indexed closing wrapper.**

`ofReachesCoreClasses` instantiates its `reaches` hypothesis at exactly one
`DegSpec` — the canonical `faceSpec` of the face it is looking at.  Asking for
`reaches` at an *arbitrary* `DegSpec` is therefore strictly more than the proof
uses.  That extra generality is free for a row that builds its script by hand,
and expensive for one that wants to move a picture along a core symmetry: the
symmetry transport (`ClosedOrbit.relabeling`) is a relabeling *between two
`faceSpec`s*, and there is no corresponding datum for a bare `DegSpec` with an
unconstrained representative map.

This variant asks only for the face-indexed statement.  It is the entry point
`Guarding.OrbitGuard` uses; `ofReachesCoreClasses` is unchanged and remains the
entry point for every row that already exists. -/
theorem ClosedSubdivisionDharConstruction.ofReachesFaceClasses
    {n p : ℕ} {core : Certificate.ExplicitPotential.Core n p}
    (core_nonempty : 0 < n) (core_connected : core.Connected)
    (divisor : ∀ d : DegSpec n p, CFDiv d.graph)
    (divisor_effective : ∀ d : DegSpec n p, effective (divisor d))
    (divisor_degree : ∀ d : DegSpec n p, deg (divisor d) = 4)
    (reaches : ∀ (length : Fin p → ℕ)
      (forest : IsForest core (zeroSlots length))
      (not_loopy : ¬ IsLoopy core (zeroSlots length)) (center : Fin n),
      Reaches (faceSpec core core_nonempty length forest not_loopy).graph
        (divisor (faceSpec core core_nonempty length forest not_loopy))
        ((faceSpec core core_nonempty length forest not_loopy).coreVertex center)) :
    ClosedSubdivisionDharConstruction core core_nonempty := by
  intro length forest not_loopy
  let d := faceSpec core core_nonempty length forest not_loopy
  refine ⟨DegreeFourDharPencil.ofEffectiveRankOne (divisor d)
    (divisor_effective d) (divisor_degree d) ?_⟩
  refine d.rank_ge_one_of_reaches_coreVertices ?_ (divisor d)
    (reaches length forest not_loopy)
  exact core_connected

/-- Combine a positive-subdivision proof with proofs only for the proper
boundary faces.  This lets a shared positive construction become the
load-bearing interior proof while retaining an existing row's contraction
arguments.  Both branches produce the same closed-orthant obligation. -/
theorem ClosedSubdivisionDharConstruction.ofPositiveAndBoundary
    {n p : ℕ} {core : Certificate.ExplicitPotential.Core n p}
    (core_nonempty : 0 < n)
    (positive : ∀ spec : SubdivisionGraph.Spec n p, spec.core = core →
      BNExists spec.graph 1 4)
    (boundary : ∀ (length : Fin p → ℕ)
      (forest : IsForest core (zeroSlots length))
      (not_loopy : ¬ IsLoopy core (zeroSlots length)),
      (∃ edge : Fin p, length edge = 0) →
      Nonempty (DegreeFourDharPencil
        (faceSpec core core_nonempty length forest not_loopy).graph)) :
    ClosedSubdivisionDharConstruction core core_nonempty := by
  classical
  intro length forest not_loopy
  by_cases hpos : ∀ edge : Fin p, 0 < length edge
  · let d := faceSpec core core_nonempty length forest not_loopy
    have hExists : BNExists (d.toSpec hpos).graph 1 4 :=
      positive (d.toSpec hpos) rfl
    exact DegreeFourDharPencil.nonempty_ofBNExists
      ((d.bnExists_toSpec_iff hpos 1 4).mp hExists)
  · apply boundary length forest not_loopy
    by_contra hzero
    apply hpos
    intro edge
    apply Nat.pos_of_ne_zero
    intro he
    exact hzero ⟨edge, he⟩

end AtanasovRanganathan.Configurations
