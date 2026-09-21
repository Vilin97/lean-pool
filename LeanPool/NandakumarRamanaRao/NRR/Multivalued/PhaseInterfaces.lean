/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.BodySpace
import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody

/-!
# `NRR.Multivalued.PhaseInterfaces` — prerequisite interface for the separator phase

This module is the single compatibility import through which the nice-multivalued-function and
separator development consumes the earlier convex-body and variable-power-partition theory. It
re-exports the two prerequisite public surfaces:

* the convex-body hyperspace layer `NRR.BodySpace`, providing the lower-area hyperspace
  `NRR.BodySpace`, its solid bridge `NRR.BodySpace.toGeometryConvexBody`, and the
  continuity of the planar perimeter `NRR.BodySpace.continuous_perimeter`;

* the variable-body weighted-Voronoi layer `NRR.EMP.VariableBody`, providing the site
  family `NRR.EMP.VariableBody.SiteFamily`, the canonical children
  `NRR.EMP.VariableBody.child` with their continuity
  (`NRR.EMP.VariableBody.continuous_child`,
  `NRR.EMP.VariableBody.continuous_children`,
  `NRR.EMP.VariableBody.continuous_child_perimeter`), and the equal-area partition witness
  `NRR.EMP.VariableBody.witness`.

Every declaration named above already exists under exactly the name used here, so no renaming
alias is required; downstream separator modules import this file rather than reaching into the
individual prerequisite modules.
-/
