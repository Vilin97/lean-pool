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
# Axiomatic projective geometry (Faure–Frölicher)

Source: doi:10.1007/978-94-015-9590-2
Authors: Abdullah Uyu
Status: verified
Main declarations: `Basic.ProjectiveGeometry`, `Basic.centralProjection`, `Basic.cen_proj_bij`
Tags: projective-geometry, incidence-geometry, geometry
MSC: 51A05, 51A30
-/

/-!
## Mathematical overview

An axiomatic development, following Faure and Frölicher's *Modern Projective
Geometry* (Kluwer, 2000), of projective geometries given by a ternary
collinearity relation. The headline theorem is `Basic.cen_proj_bij`: the
central projection between two lines is a bijection. Desargues' theorem itself
is not formalized — this is the upstream `desargues` repository's groundwork in
the setting where that theorem is classically stated.

- `Basic.ProjectiveGeometry`: the projective-geometry axioms `L₁`–`L₃` as a
  typeclass on a collinearity relation, with the line operator `Basic.star`.
- `Basic.centralProjection` and `Basic.cen_proj_bij`: the central projection
  map between lines and the proof that it is a bijection.
- `Structure.Subspace` / `Structure.ProjectiveSubgeometry`: subspaces and
  subgeometries; `PV` exhibits every Mathlib `Projectivization` as a
  `ProjectiveGeometry`.
-/
