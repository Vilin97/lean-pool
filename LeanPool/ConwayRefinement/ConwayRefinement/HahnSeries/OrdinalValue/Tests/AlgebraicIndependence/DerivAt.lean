/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponent
public import LeanPool.ConwayRefinement.ConwayRefinement.Order.Filter.FunAtZeroMinus
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.LoweringDerivation
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.FinitePart

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Tests.Fixtures.ApproachZero
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.DerivAtInjective

/-!
# API checks for `∂` on `P_α`

The degree-one approach-zero series gives a nonzero class in the homogeneous component `P_1`.
Injectivity of `∂`
on `P_1` (D3) sends it to a nonzero element of `Fun_{0⁻}(P_0)`, and the derivation
`∂ : P̂ → Fun_{0⁻}(P̂)` sends its homogeneous inclusion to a nonzero function at `0⁻`. These
checks distinguish both maps from zero on a class represented by a series with infinite support
cofinal below zero.
-/

open Filter Topology
open scoped HahnSeries NatOrdinal TensorProduct

public noncomputable section

namespace Tests

open Berarducci

private theorem approachZero_ordinalValue_bound_for_lowering :
    Berarducci.ordinalValue approachZeroNonpositive <
      ω^ ((1 : NatOrdinal) + 1) := by
  rw [Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
    approachZero_degree_eq_one]
  exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one (1 : NatOrdinal))

private theorem one_constantCoeff_pos :
    0 < (1 : NatOrdinal).constantCoeff := by
  have hcoeff : (1 : NatOrdinal).constantCoeff = 1 := by
    simpa only [Nat.cast_one] using NatOrdinal.constantCoeff_natCast (1 : ℕ)
  rw [hcoeff]
  decide

/-- `∂(B)` for the class `B ∈ P_1` of the degree-one approach-zero series. -/
def approachZeroDerivAt :
    FunAtZeroMinus (Berarducci.PrincipalComponent ℚ
      ((1 : NatOrdinal).removeNat 1)) :=
  principalComponentDerivAt ℚ 1 one_constantCoeff_pos
    (Berarducci.principalComponentMk 1 approachZeroNonpositive
      approachZero_ordinalValue_bound_for_lowering)

private theorem approachZeroPrincipalClass_ne_zero :
    Berarducci.principalComponentMk 1 approachZeroNonpositive
      approachZero_ordinalValue_bound_for_lowering ≠ 0 := by
  intro hzero
  have hlower := (Berarducci.principalComponentMk_eq_zero_iff 1
    approachZeroNonpositive approachZero_ordinalValue_bound_for_lowering).mp hzero
  rw [Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
    approachZero_degree_eq_one] at hlower
  exact lt_irrefl _ hlower

private theorem approachZero_ordinalValue_bound_for_natCast_one :
    Berarducci.ordinalValue approachZeroNonpositive <
      ω^ (((1 : ℕ) : NatOrdinal) + 1) := by
  simpa only [Nat.cast_one] using approachZero_ordinalValue_bound_for_lowering

private theorem approachZeroPrincipalClassNatCast_ne_zero :
    Berarducci.principalComponentMk ((1 : ℕ) : NatOrdinal)
      approachZeroNonpositive approachZero_ordinalValue_bound_for_natCast_one ≠ 0 := by
  intro hzero
  have hlower := (Berarducci.principalComponentMk_eq_zero_iff
    ((1 : ℕ) : NatOrdinal) approachZeroNonpositive
      approachZero_ordinalValue_bound_for_natCast_one).mp hzero
  rw [Berarducci.ordinalValue_eq_wpow_of_isPrincipal approachZero_isPrincipal
    approachZero_degree_eq_one] at hlower
  have : ω^ (1 : NatOrdinal) < ω^ (1 : NatOrdinal) := by
    simpa only [Nat.cast_one] using hlower
  exact lt_irrefl _ this

/-- `∂(B) ≠ 0` for the approach-zero class `B`, because support cutoffs remain cofinal at
zero. -/
theorem approachZeroDerivAt_ne_zero :
    approachZeroDerivAt ≠ 0 := by
  rw [approachZeroDerivAt]
  exact principalComponentDerivAt_ne_zero 1
    one_constantCoeff_pos approachZeroPrincipalClass_ne_zero

/-- The homogeneous inclusion of the approach-zero class in `P̂`. -/
def approachZeroPrincipalElement : Berarducci.PrincipalSubring ℚ :=
  DirectSum.of (Berarducci.PrincipalComponent ℚ) 1
    (Berarducci.principalComponentMk 1 approachZeroNonpositive
      approachZero_ordinalValue_bound_for_lowering)

/-- The derivation `∂` of `P̂` detects the approach-zero element: `∂` is injective on `P_1`. -/
theorem principalSubringDerivation_approachZero_ne_zero :
    principalSubringDerivation ℚ approachZeroPrincipalElement ≠ 0 := by
  intro hzero
  have h := (principalSubringDerivation_isLoweringDerivation ℚ).injective
    one_constantCoeff_pos (of_mem_principalGrading 1 _) hzero
  exact approachZeroPrincipalClass_ne_zero
    (DirectSum.of_injective 1 (h.trans (map_zero _).symm))

end Tests
