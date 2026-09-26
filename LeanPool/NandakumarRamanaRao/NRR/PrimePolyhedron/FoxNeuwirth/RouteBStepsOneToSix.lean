/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBFullBadSetNullity
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBSmallGenericPerturbation

/-!
# Route B, Steps 1--6

Single import point for the audited finite-dimensional perturbation layer.

The imported development contains:

* finite avoidance of null sets;
* the movable parameter space and exact frozen-coordinate reconstruction;
* finite mixed-face incidence cases;
* the scalar fixed-witness calculation;
* the canonical selected `p`-vector coordinate split;
* measurability and full nullity of every existential mixed-face bad set;
* selection of a small endpoint-relative perturbation satisfying direct
  positive-ray general position, under the explicit origin-margin,
  frozen-support safety, and facet-neighborhood inputs.
-/

@[expose] public section
