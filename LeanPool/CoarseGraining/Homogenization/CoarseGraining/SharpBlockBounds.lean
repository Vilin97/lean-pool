/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.SharpBlockBounds.Basic
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich

/-!
# Sharp-constant pointwise block bounds (Proposition 2.1)

Facade for the sharp-constant pointwise block-matrix algebra of Proposition 2.1
of the high-moment paper (Armstrong–Kuusi–Loher, to appear):

* `SharpBlockBounds.Basic` — the ellipticity-class quadratic identities and the
  upper diagonal sandwich (items A4–A8-upper);
* `SharpBlockBounds.DiagonalSandwich` — the block Fenchel/reflection inverse,
  the lower diagonal sandwich (A8-lower), and the two-field comparison (A9).

All matrix/vector work is on `Vec d = Fin d → ℝ` / `Mat d`; no `EuclideanSpace`.
-/
