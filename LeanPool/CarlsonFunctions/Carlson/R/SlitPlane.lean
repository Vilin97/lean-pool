/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.Basic
public import Mathlib.Analysis.Complex.Convex

/-! # Slit-plane domains for Carlson's R-function

The product slit plane is star-convex about the constant node vector `1`. The segment
from `1` to each node stays on the principal branch, as required by the single-integral
construction in Carlson's Section 6.8. Arbitrary convex combinations of nodes need not
stay on this branch; the original simplex integral is therefore not used on this domain.
-/

open Complex
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The full principal-branch node domain for Carlson's `R`-function. -/
def carlsonRSlitDomain : Set (ι → ℂ) := {z | ∀ i, z i ∈ slitPlane}

omit [Fintype ι] in
theorem carlsonRVariableDomain_subset_slitDomain :
    (carlsonRVariableDomain : Set (ι → ℂ)) ⊆ carlsonRSlitDomain :=
  fun _ hz i => carlsonRightHalfPlane_subset_slitPlane (hz i)

theorem isOpen_carlsonRSlitDomain : IsOpen (carlsonRSlitDomain : Set (ι → ℂ)) := by
  rw [show carlsonRSlitDomain (ι := ι) =
    ⋂ i, {z : ι → ℂ | z i ∈ slitPlane} by ext z; simp [carlsonRSlitDomain]]
  exact isOpen_iInter_of_finite fun i => isOpen_slitPlane.preimage (continuous_apply i)

omit [Fintype ι] in
theorem one_mem_carlsonRSlitDomain : (fun _ : ι => (1 : ℂ)) ∈ carlsonRSlitDomain :=
  fun _ => by simp

omit [Fintype ι] in
theorem starConvex_one_carlsonRSlitDomain :
    StarConvex ℝ (fun _ : ι => (1 : ℂ)) carlsonRSlitDomain := by
  intro z hz a b ha hb hab i
  exact starConvex_one_slitPlane (hz i) ha hb hab

omit [Fintype ι] in
theorem isPreconnected_carlsonRSlitDomain :
    IsPreconnected (carlsonRSlitDomain : Set (ι → ℂ)) :=
  (starConvex_one_carlsonRSlitDomain.isPathConnected
    one_mem_carlsonRSlitDomain).isConnected.isPreconnected

omit [Fintype ι] in
/-- Each factor of the single-integral kernel avoids the branch cut on the closed interval. -/
theorem carlsonRSegment_mem_slitPlane {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain)
    {u : ℝ} (hu : u ∈ Set.Icc 0 1) (i : ι) :
    (1 - u : ℂ) + (u : ℂ) * z i ∈ slitPlane := by
  have h := starConvex_one_slitPlane (hz i) (sub_nonneg.mpr hu.2) hu.1
    (sub_add_cancel 1 u)
  simpa [Complex.real_smul, Complex.ofReal_sub] using h

omit [Fintype ι] in
/-- Taking coordinatewise reciprocals preserves the full principal-branch node domain. -/
theorem carlsonRSlitDomain_inv {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    (fun i => (z i)⁻¹) ∈ carlsonRSlitDomain := by
  intro i
  have hn := normSq_pos.mpr (slitPlane_ne_zero (hz i))
  rcases mem_slitPlane_iff.mp (hz i) with h | h
  · exact mem_slitPlane_iff.mpr (Or.inl (by rw [inv_re]; exact div_pos h hn))
  · exact mem_slitPlane_iff.mpr (Or.inr (by rw [inv_im]; exact div_ne_zero (neg_ne_zero.mpr h) hn.ne'))

end DirichletTransform
