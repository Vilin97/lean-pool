/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.PrincipalIdealGE

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.LoweringDerivation

/-!
# API checks for the filtration `I_{≥•}`

The approach-zero class gives a nonzero homogeneous element of degree one in `I_{≥1} \ I_{≥2}`;
its square gives one in `I_{≥2} \ I_{≥3}`. Adding a nonzero scalar component to the degree-one
element produces an element outside `I_{≥1}`, which distinguishes the filtration from a cutoff
determined by the largest visible homogeneous degree.
-/

open scoped DirectSum HahnSeries NatOrdinal

public noncomputable section

namespace Tests

open Berarducci

private theorem approachZero_ordinalValue_bound_for_idealGE :
    Berarducci.ordinalValue approachZeroNonpositive <
      ω^ (((1 : ℕ) : NatOrdinal) + 1) := by
  rw [Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
    approachZero_degree_eq_one]
  simpa only [Nat.cast_one] using
    NatOrdinal.wpow_lt_wpow.mpr (lt_add_one (1 : NatOrdinal))

/-- The approach-zero series represented in the homogeneous component `P_1`. -/
def idealGEApproachZeroLayer :
    Berarducci.PrincipalComponent ℚ ((1 : ℕ) : NatOrdinal) :=
  Berarducci.principalComponentMk ((1 : ℕ) : NatOrdinal)
    approachZeroNonpositive approachZero_ordinalValue_bound_for_idealGE

/-- The approach-zero class used by the filtration fixture is nonzero. -/
theorem idealGEApproachZeroLayer_ne_zero :
    idealGEApproachZeroLayer ≠ 0 := by
  intro hzero
  have hlower := (Berarducci.principalComponentMk_eq_zero_iff
    ((1 : ℕ) : NatOrdinal) approachZeroNonpositive
      approachZero_ordinalValue_bound_for_idealGE).mp hzero
  rw [Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
    approachZero_degree_eq_one] at hlower
  have : ω^ (1 : NatOrdinal) < ω^ (1 : NatOrdinal) := by
    simpa only [Nat.cast_one] using hlower
  exact (lt_irrefl _) this

/-- The approach-zero class placed homogeneously in `P̂`. -/
def idealGEApproachZeroElement : Berarducci.PrincipalSubring ℚ :=
  DirectSum.of (Berarducci.PrincipalComponent ℚ) ((1 : ℕ) : NatOrdinal)
    idealGEApproachZeroLayer

/-- The degree-one fixture lies in `I_{≥1}` but not in `I_{≥2}`. -/
theorem idealGEApproachZeroElement_mem_one_not_mem_two :
    idealGEApproachZeroElement ∈ principalIdealGE ℚ 1 ∧
      idealGEApproachZeroElement ∉ principalIdealGE ℚ 2 := by
  constructor
  · exact principalIdealGEGenerator_mem (le_refl 1)
      idealGEApproachZeroLayer
  · intro hmem
    apply idealGEApproachZeroLayer_ne_zero
    apply eq_zero_of_homogeneous_mem_principalIdealGE
      (j := 2) (δ := ((1 : ℕ) : NatOrdinal)) (by
        rw [NatOrdinal.constantCoeff_natCast]
        decide)
    exact hmem

/-- The square of the approach-zero class in the homogeneous component `P_2`. -/
def idealGEApproachZeroSquare :
    Berarducci.PrincipalComponent ℚ ((2 : ℕ) : NatOrdinal) :=
  principalComponentMulNat ℚ 1 1
    idealGEApproachZeroLayer idealGEApproachZeroLayer

/-- The square of the approach-zero class is nonzero. -/
theorem idealGEApproachZeroSquare_ne_zero :
    idealGEApproachZeroSquare ≠ 0 :=
  principalComponentMulNat_ne_zero
    idealGEApproachZeroLayer_ne_zero
    idealGEApproachZeroLayer_ne_zero

/-- The approach-zero square placed homogeneously in `P̂`. -/
def idealGEApproachZeroSquareElement : Berarducci.PrincipalSubring ℚ :=
  DirectSum.of (Berarducci.PrincipalComponent ℚ) ((2 : ℕ) : NatOrdinal)
    idealGEApproachZeroSquare

/-- The degree-two fixture lies in `I_{≥2}` but not in `I_{≥3}`. -/
theorem idealGEApproachZeroSquareElement_mem_two_not_mem_three :
    idealGEApproachZeroSquareElement ∈ principalIdealGE ℚ 2 ∧
      idealGEApproachZeroSquareElement ∉ principalIdealGE ℚ 3 := by
  constructor
  · exact principalIdealGEGenerator_mem (le_refl 2)
      idealGEApproachZeroSquare
  · intro hmem
    apply idealGEApproachZeroSquare_ne_zero
    apply eq_zero_of_homogeneous_mem_principalIdealGE
      (j := 3) (δ := ((2 : ℕ) : NatOrdinal)) (by
        rw [NatOrdinal.constantCoeff_natCast]
        decide)
    exact hmem

/-- The sum of scalar one and the homogeneous degree-one fixture. -/
def idealGEScalarPlusApproachZero : Berarducci.PrincipalSubring ℚ :=
  1 + idealGEApproachZeroElement

/-- A nonzero scalar component prevents the mixed fixture from belonging to `I_{≥1}`. -/
theorem idealGEScalarPlusApproachZero_not_mem_one :
    idealGEScalarPlusApproachZero ∉ principalIdealGE ℚ 1 := by
  intro hmem
  have hzero := principalIdealGE_component_eq_zero
    idealGEScalarPlusApproachZero hmem (δ := 0) (by simp)
  have hscalar : (1 : Berarducci.PrincipalSubring ℚ) 0 ≠ 0 := by
    intro hone
    have hone' : GradedMonoid.GOne.one =
        (0 : Berarducci.PrincipalComponent ℚ 0) := by
      simpa only [DirectSum.one_def, DirectSum.of_apply, dite_true] using hone
    apply (one_ne_zero : (1 : Berarducci.PrincipalSubring ℚ) ≠ 0)
    rw [DirectSum.one_def, hone', map_zero]
  apply hscalar
  simpa [idealGEScalarPlusApproachZero, idealGEApproachZeroElement,
    DirectSum.add_apply, DirectSum.of_apply] using hzero

end Tests
