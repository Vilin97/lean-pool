/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/
module

public import LeanPool.Erdos137.Finiteness
public import LeanPool.Erdos137.Base
public import LeanPool.Erdos137.BlockFramework
public import LeanPool.Erdos137.RefinedOverlap
public import LeanPool.Erdos137.JointFiniteness
public import LeanPool.Erdos137.SmoothRefinement
public import LeanPool.Erdos137.TaoPoint
public import LeanPool.Erdos137.RoughPartStructure
public import LeanPool.Erdos137.SpliceFiniteness
public import LeanPool.Erdos137.QuarticCrude
public import LeanPool.Erdos137.SexticCrude
public import LeanPool.Erdos137.SquarefreeCapacity
public import LeanPool.Erdos137.CombinedSplice

/-!
# Axiom audit

This module aggregates every route of the Erdős #137 development so that the
axioms underlying each theorem can be inspected in one place. Every theorem in
the project depends only on `propext`, `Classical.choice`, and `Quot.sound` —
no `sorryAx`, no `native_decide`/`Lean.ofReduceBool`.

The routes assembled here are:
* the triple-tiling route (`JointFiniteness`, `g = 3`);
* the smooth-part radical refinement (`Base` + `SmoothRefinement`);
* the Tao "very bad interval" elementary structure (`TaoPoint`);
* the honest `g = 5` finiteness and abstract splice machine (`SpliceFiniteness`);
* the parametric `g`-block framework (`BlockFramework`);
* the crude (non-smooth) route, including `g = 4` and `g = 6` (`QuarticCrude`,
  `SexticCrude`);
* the refined deterministic overlap bound (`RefinedOverlap`);
* the deterministic squarefree-capacity reduction (`SquarefreeCapacity`);
* the combined four-range splice (`CombinedSplice`);
* the term-level rough-part anatomy (`RoughPartStructure`).
-/

@[expose] public section
