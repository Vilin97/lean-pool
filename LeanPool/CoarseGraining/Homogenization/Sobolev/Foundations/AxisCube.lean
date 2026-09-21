/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain

/-! # Axis Cube -/

namespace Homogenization

open MeasureTheory
open scoped BigOperators

/-!
# Axis-aligned cube domains

An axis cube `z + (0,L)^d` is the open box obtained by translating the product
of the open intervals `(0,L)` by a corner point `z`.  This file records that
these boxes fit the ambient Sobolev geometry API: they are open, bounded,
convex, and hence open bounded convex domains.  These are the reference domains
for the interior harmonic estimates.
-/

noncomputable section

/-- The open axis cube `z + (0,L)^d`. -/
def axisCube {d : ℕ} (z : Vec d) (L : ℝ) : Set (Vec d) :=
  Set.pi Set.univ fun j => Set.Ioo (z j) (z j + L)

/-- Axis cubes are open finite products of open intervals. -/
theorem isOpen_axisCube {d : ℕ} (z : Vec d) (L : ℝ) :
    IsOpen (axisCube z L) := by
  dsimp [axisCube]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

/-- Axis cubes are bounded, even in the degenerate or empty cases. -/
theorem isBoundedDomain_axisCube {d : ℕ} (z : Vec d) (L : ℝ) :
    IsBoundedDomain (axisCube z L) := by
  dsimp [axisCube]
  exact Bornology.IsBounded.isBoundedDomain <|
    Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _

/-- Axis cubes are convex finite products of convex intervals. -/
theorem convex_axisCube {d : ℕ} (z : Vec d) (L : ℝ) :
    Convex ℝ (axisCube z L) := by
  dsimp [axisCube]
  refine convex_pi ?_
  intro _ _
  exact convex_Ioo _ _

/-- Axis cubes are bounded open convex domains in the Sobolev geometry API. -/
theorem isOpenBoundedConvexDomain_axisCube
    {d : ℕ} (z : Vec d) (L : ℝ) :
    IsOpenBoundedConvexDomain (axisCube z L) :=
  ⟨isOpen_axisCube z L, isBoundedDomain_axisCube z L, convex_axisCube z L⟩

end

end Homogenization
