/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.WindingWeights.I
import LeanPool.LeanModularForms.ValenceFormula.WindingWeights.Rho
import LeanPool.LeanModularForms.ValenceFormula.WindingWeights.RhoPlusOne

/-!
# Winding Number Weights at Elliptic Points

Explicit computation of generalized winding numbers of the
fundamental domain boundary around the elliptic points i, ρ, ρ+1.

## Main Results

* `gWN_fdBoundary_H_at_i` — gWN = -1/2 at i
* `gWN_fdBoundary_H_at_rho` — gWN = -1/6 at ρ
* `gWN_fdBoundary_H_at_rho_plus_one` — gWN = -1/6 at ρ+1
* `effectiveWinding_rho_eq_neg_gWN` — 1/3 = -(gWN(ρ) + gWN(ρ+1))
* `effectiveWinding_i_eq_neg_gWN` — 1/2 = -gWN(i)
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

theorem effectiveWinding_rho_eq_neg_gWN (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    (1 : ℚ) / 3 = -(generalizedWindingNumber' (fdBoundaryH H) 0 5 ellipticPointRho +
      generalizedWindingNumber' (fdBoundaryH H) 0 5 ellipticPointRhoPlusOne) := by
  rw [gWN_fdBoundary_H_at_rho H hH, gWN_fdBoundary_H_at_rho_plus_one H hH]
  push_cast; ring

theorem effectiveWinding_i_eq_neg_gWN (H : ℝ) (hH : 1 < H) :
    (1 : ℚ) / 2 = -(generalizedWindingNumber' (fdBoundaryH H) 0 5 I) := by
  rw [gWN_fdBoundary_H_at_i H hH]
  push_cast; ring

end
