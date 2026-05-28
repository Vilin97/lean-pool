/-
Copyright (c) 2026 Abdullah Uyu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdullah Uyu
-/

import LeanPool.Desargues.Basic
import LeanPool.Desargues.Morphism
import LeanPool.Desargues.PV
import LeanPool.Desargues.Structure

/-!
# Projective geometry and central projection (toward Desargues' theorem)

Source: url:https://github.com/oneofvalts/desargues
Authors: Abdullah Uyu
Status: verified
Main declarations: `Basic.ProjectiveGeometry`, `Basic.central_projection`
Tags: projective-geometry, incidence-geometry, geometry
MSC: 51A05, 51A30
-/

/-!
## Mathematical overview

A formalization following Faure and Frölicher's *Modern Projective Geometry* of
the axiomatic theory of projective geometries and central projections — the
framework in which Desargues' theorem is proved.

- `Basic.ProjectiveGeometry`: the projective-geometry axioms as a typeclass on a
  collinearity relation.
- `Basic.central_projection` and `Basic.cen_proj_bij`: the central projection
  map between lines and the proof that it is a bijection.
- `Structure.Subspace` / `Structure.ProjectiveSubgeometry`: subspaces and
  subgeometries; `PV` exhibits every Mathlib `Projectivization` as a
  `ProjectiveGeometry`.
-/
