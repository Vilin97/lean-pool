/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Boundedness of smooth Jordan domains

The boundary representation in `SmoothJordanDomain`, together with convexity,
forces the represented carrier to be the bounded side of its Jordan trace.
Canonical orientation supplies winding number one throughout the carrier;
the scalar Cauchy transform then tends to zero at infinity, ruling out an
unbounded carrier.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCauchyKernelWinding
import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanionRadial

open Complex Metric Set

/-- Every represented smooth convex Jordan carrier is bounded. -/
theorem SmoothJordanDomain.isBounded_carrier
    (Omega : SmoothJordanDomain) :
    Bornology.IsBounded Omega.carrier := by
  let Psi := Omega.canonicalOrientation
  obtain ⟨c, hc, hc0⟩ := Omega.exists_oriented_point_canonicalOrientation
  have hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Psi.boundaryParam t) *
        (c - Psi.boundaryParam t)).re ≤ 0 :=
    Psi.canonicalNormal_support_all_of_support_at c hc 0 hc0
  have hkernel : ∀ z ∈ Psi.carrier,
      crouzeixScalarCauchyKernel Psi z = 1 :=
    crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
      Psi c hc hcside
  have hbounded : Bornology.IsBounded Psi.carrier :=
    Psi.isBounded_carrier_of_cauchyKernel_eq_one hkernel
  simpa only [Psi, SmoothJordanDomain.canonicalOrientation_carrier] using hbounded

/-- The closure of every represented smooth convex Jordan carrier is compact. -/
theorem SmoothJordanDomain.isCompact_closure
    (Omega : SmoothJordanDomain) :
    IsCompact (closure Omega.carrier) :=
  Omega.isBounded_carrier.isCompact_closure

/-- Around any chosen center, the closed carrier of a smooth Jordan domain is
contained in a ball of some positive radius. -/
theorem SmoothJordanDomain.exists_pos_radius_closure_subset_ball
    (Omega : SmoothJordanDomain) (c : ℂ) :
    ∃ R : ℝ, 0 < R ∧ closure Omega.carrier ⊆ Metric.ball c R :=
  Omega.isCompact_closure.isBounded.subset_ball_lt 0 c

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
