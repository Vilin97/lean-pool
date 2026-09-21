/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom

/-!
# Boundary reduction for the scalar Crouzeix companion

The scalar companion is holomorphic in the interior of a smooth Jordan
domain, but its defining contour integral is singular on the boundary.  The
Plemelj step therefore naturally supplies a separate continuous extension to
the closed domain.  This file proves that any such extension automatically
inherits the companion's interior differentiability.  The maximum-modulus
principle then reduces the sharp interior contraction entirely to a frontier
bound for the extension.

No boundary-value theorem is assumed implicitly: both continuity on the
closure and the frontier estimate remain explicit hypotheses.

## Main declarations

* `crouzeixPolynomialScalarCompanionClosedExtension` -- the canonical
  limit-based extension from the open carrier.
* `continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_tendsto`
  -- pointwise interior limits on the frontier make that extension continuous.
* `diffContOnCl_crouzeixPolynomialScalarCompanion_extension` -- a continuous
  closed-domain extension is differentiable in the interior.
* `norm_crouzeixPolynomialScalarCompanion_extension_le_of_boundary` -- a
  frontier bound propagates across the closed domain.
* `norm_crouzeixPolynomialScalarCompanion_le_of_boundary_extension` -- the
  resulting bound for the actual interior companion.
* `norm_crouzeixPolynomialScalarCompanion_le_of_boundary_tendsto` -- the same
  sharp reduction stated directly in terms of Plemelj boundary limits.
-/

open Complex Filter Set

/-- The canonical closed-domain candidate obtained by taking limits of the
interior scalar companion.  Its useful properties are proved below from the
existence of the relevant frontier limits. -/
noncomputable def crouzeixPolynomialScalarCompanionClosedExtension
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) : ℂ → ℂ :=
  extendFrom Omega.carrier (crouzeixPolynomialScalarCompanion Omega p)

/-- The canonical limit extension agrees with the scalar companion at every
interior point, independently of any boundary-value theorem. -/
theorem crouzeixPolynomialScalarCompanionClosedExtension_eq
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p z =
      crouzeixPolynomialScalarCompanion Omega p z := by
  apply extendFrom_extends
    (analyticOn_crouzeixPolynomialScalarCompanion Omega p).continuousOn z hz

/-- If `b z` is the interior limit of the scalar companion at every frontier
point, the canonical extension is continuous on the whole closed domain. -/
theorem
    continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_tendsto
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (b : ℂ → ℂ)
    (hlim : ∀ z ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanion Omega p)
        (nhdsWithin z Omega.carrier) (nhds (b z))) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      (closure Omega.carrier) := by
  apply continuousOn_extendFrom (fun _ hz ↦ hz)
  intro z hz
  rw [closure_eq_self_union_frontier] at hz
  rcases hz with hz | hz
  · exact ⟨crouzeixPolynomialScalarCompanion Omega p z,
      (analyticOn_crouzeixPolynomialScalarCompanion Omega p).continuousOn z hz⟩
  · exact ⟨b z, hlim z hz⟩

/-- The canonical extension takes the prescribed Plemelj limit on the
frontier. -/
theorem crouzeixPolynomialScalarCompanionClosedExtension_eq_boundary_of_tendsto
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (b : ℂ → ℂ)
    (hlim : ∀ z ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanion Omega p)
        (nhdsWithin z Omega.carrier) (nhds (b z)))
    {z : ℂ} (hz : z ∈ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p z = b z := by
  exact extendFrom_eq (frontier_subset_closure hz) (hlim z hz)

/-- A function continuous on the closed smooth Jordan domain and equal to the
scalar companion in the interior is complex differentiable in the interior.
Thus it has the exact regularity required by the maximum-modulus principle. -/
theorem diffContOnCl_crouzeixPolynomialScalarCompanion_extension
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (g : ℂ → ℂ)
    (hcont : ContinuousOn g (closure Omega.carrier))
    (heq : Set.EqOn g (crouzeixPolynomialScalarCompanion Omega p)
      Omega.carrier) :
    DiffContOnCl ℂ g Omega.carrier := by
  refine ⟨?_, hcont⟩
  intro z hz
  have hev : g =ᶠ[nhds z]
      crouzeixPolynomialScalarCompanion Omega p := by
    filter_upwards [Omega.isOpen_carrier.mem_nhds hz] with w hw
    exact heq hw
  exact ((hasDerivAt_crouzeixPolynomialScalarCompanion Omega p hz).congr_of_eventuallyEq
    hev).differentiableAt.differentiableWithinAt

/-- On a bounded smooth Jordan domain, a frontier norm bound for a continuous
extension of the scalar companion propagates to the entire closed domain. -/
theorem norm_crouzeixPolynomialScalarCompanion_extension_le_of_boundary
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (g : ℂ → ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hcont : ContinuousOn g (closure Omega.carrier))
    (heq : Set.EqOn g (crouzeixPolynomialScalarCompanion Omega p)
      Omega.carrier)
    {C : ℝ} (hC : ∀ z ∈ frontier Omega.carrier, ‖g z‖ ≤ C)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖g z‖ ≤ C := by
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hbounded
    (diffContOnCl_crouzeixPolynomialScalarCompanion_extension
      Omega p g hcont heq) hC hz

/-- A continuous boundary extension with norm at most `C` on the frontier
gives the same sharp bound for the actual scalar companion at every interior
point.  Consequently, the remaining contraction input is precisely the
Plemelj extension and its boundary estimate. -/
theorem norm_crouzeixPolynomialScalarCompanion_le_of_boundary_extension
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (g : ℂ → ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hcont : ContinuousOn g (closure Omega.carrier))
    (heq : Set.EqOn g (crouzeixPolynomialScalarCompanion Omega p)
      Omega.carrier)
    {C : ℝ} (hC : ∀ z ∈ frontier Omega.carrier, ‖g z‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by
  rw [← heq hz]
  exact norm_crouzeixPolynomialScalarCompanion_extension_le_of_boundary
    Omega p g hbounded hcont heq hC (subset_closure hz)

/-- Pointwise Plemelj limits with frontier norm at most `C` imply the sharp
interior companion bound.  The continuous closed-domain extension is
constructed canonically, so no separate extension function or compatibility
proof is required. -/
theorem norm_crouzeixPolynomialScalarCompanion_le_of_boundary_tendsto
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (b : ℂ → ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hlim : ∀ z ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanion Omega p)
        (nhdsWithin z Omega.carrier) (nhds (b z)))
    {C : ℝ} (hC : ∀ z ∈ frontier Omega.carrier, ‖b z‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by
  apply norm_crouzeixPolynomialScalarCompanion_le_of_boundary_extension
    Omega p (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      hbounded
      (continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_tendsto
        Omega p b hlim)
      (fun w hw ↦ crouzeixPolynomialScalarCompanionClosedExtension_eq Omega p hw)
      (fun w hw ↦ ?_) hz
  rw [crouzeixPolynomialScalarCompanionClosedExtension_eq_boundary_of_tendsto
    Omega p b hlim hw]
  exact hC w hw

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
