/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import LeanPool.Erdos137.Finiteness
import LeanPool.Erdos137.Base
import LeanPool.Erdos137.BlockFramework
import LeanPool.Erdos137.RefinedOverlap
import LeanPool.Erdos137.JointFiniteness
import LeanPool.Erdos137.SmoothRefinement
import LeanPool.Erdos137.TaoPoint
import LeanPool.Erdos137.RoughPartStructure
import LeanPool.Erdos137.SpliceFiniteness
import LeanPool.Erdos137.QuarticCrude
import LeanPool.Erdos137.SexticCrude
import LeanPool.Erdos137.SquarefreeCapacity
import LeanPool.Erdos137.CombinedSplice

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
