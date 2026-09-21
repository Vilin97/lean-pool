/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HolomorphicConvexity.Hull

/-!
# Boundary distance and compactness of holomorphic hulls

Distance is taken to the complement and valued in `ℝ≥0∞`. In particular, `boundaryEDistance U ∅
= ∞` and `boundaryEDistance univ K = ∞`. On finite complex coordinate spaces the norm is the
supremum norm, so the balls here are equal-radius polydiscs.

The radius formulation of hull-distance preservation implies holomorphic convexity by relative
closedness, boundedness, and positive distance from the complement. These purely topological
implications do not depend on Cartan–Thullen or Taylor continuation.

## Main results

`HasHolomorphicHullRadiusProperty` is uniform polydisc-radius preservation on hulls.
`HasHolomorphicHullDistanceProperty` is exact preservation of extended boundary distance. Each
implies the other, and each implies `IsHolomorphicallyConvex`.
-/

public noncomputable section

open Set Metric
open scoped ENNReal

namespace SeveralComplexVariables

/-- The extended distance of a set to the complement of an ambient set. -/
@[expose] noncomputable def boundaryEDistance {X : Type*} [PseudoMetricSpace X] (U K : Set X)
    : ℝ≥0∞ :=
  ⨅ x ∈ K, infEDist x Uᶜ

/-- Empty compact sets have infinite boundary distance. -/
@[simp] theorem boundaryEDistance_empty {X : Type*} [PseudoMetricSpace X] (U : Set X) :
    boundaryEDistance U ∅ = ⊤ := by simp [boundaryEDistance]

/-- In the whole ambient space every set has infinite boundary distance. -/
@[simp] theorem boundaryEDistance_univ {X : Type*} [PseudoMetricSpace X] (K : Set X) :
    boundaryEDistance univ K = ⊤ := by simp [boundaryEDistance]

/-- Enlarging a set decreases its distance to the complement. -/
theorem boundaryEDistance_anti {X : Type*} [PseudoMetricSpace X] {U K L : Set X}
    (hKL : K ⊆ L) : boundaryEDistance U L ≤ boundaryEDistance U K := by
  exact le_iInf fun x => le_iInf fun hx => iInf₂_le x (hKL hx)

/-- A lower bound for boundary distance means that all corresponding open balls stay inside the
ambient set. This formulation includes nonpositive radii and empty sets. -/
theorem ofReal_le_boundaryEDistance_iff {X : Type*} [PseudoMetricSpace X]
    {U K : Set X} {r : ℝ} :
    ENNReal.ofReal r ≤ boundaryEDistance U K ↔ ∀ x ∈ K, ball x r ⊆ U := by
  simp only [boundaryEDistance, le_iInf_iff, le_infEDist]
  constructor
  · intro h x hx y hy
    by_contra hn
    have hle := h x hx y hn
    have hlt : edist x y < ENNReal.ofReal r := edist_lt_ofReal.mpr
      (by simpa only [mem_ball, dist_comm] using hy)
    exact (not_lt_of_ge hle) hlt
  · intro h x hx y hy
    apply le_of_not_gt
    intro hlt
    exact hy (h x hx (by simpa only [mem_ball, dist_comm] using edist_lt_ofReal.mp hlt))

variable {ι : Type*} [Fintype ι]

/-- Uniform polydisc radii available on a compact set remain available on its holomorphic hull.
Openness is separate from this property. -/
@[expose] def HasHolomorphicHullRadiusProperty (U : Set (ι → ℂ)) : Prop :=
  ∀ K, IsCompact K → K ⊆ U → ∀ r : ℝ, 0 < r →
    (∀ x ∈ K, ball x r ⊆ U) → ∀ a ∈ holomorphicHull U K, ball a r ⊆ U

/-- Preservation of the extended boundary distance under taking holomorphic hulls. -/
@[expose] def HasHolomorphicHullDistanceProperty (U : Set (ι → ℂ)) : Prop :=
  ∀ K, IsCompact K → K ⊆ U →
    boundaryEDistance U (holomorphicHull U K) = boundaryEDistance U K

/-- The radius property implies exact boundary-distance preservation. -/
theorem HasHolomorphicHullRadiusProperty.hasHolomorphicHullDistanceProperty {U : Set (ι → ℂ)}
    (h : HasHolomorphicHullRadiusProperty U) : HasHolomorphicHullDistanceProperty U := by
  intro K hK hKU
  apply le_antisymm (boundaryEDistance_anti (subset_holomorphicHull hKU))
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r hr hrK
  have hball : ∀ x ∈ K, ball x (r : ℝ) ⊆ U :=
    ofReal_le_boundaryEDistance_iff.mp (by simpa using hrK.le)
  have hh := h K hK hKU r hr hball
  simpa using ofReal_le_boundaryEDistance_iff.mpr hh

/-- Boundary-distance preservation implies the uniform radius property. -/
theorem HasHolomorphicHullDistanceProperty.hasHolomorphicHullRadiusProperty {U : Set (ι → ℂ)}
    (h : HasHolomorphicHullDistanceProperty U) : HasHolomorphicHullRadiusProperty U := by
  intro K hK hKU r _ hr
  apply ofReal_le_boundaryEDistance_iff.mp
  rw [h K hK hKU]
  exact ofReal_le_boundaryEDistance_iff.mpr hr

/-- Uniform preservation of positive hull radii makes every compact hull compact. -/
theorem HasHolomorphicHullRadiusProperty.isHolomorphicallyConvex
    {U : Set (ι → ℂ)} (h : HasHolomorphicHullRadiusProperty U) (ho : IsOpen U) :
    IsHolomorphicallyConvex U := by
  intro K hK hKU
  obtain ⟨r, hr, hthick⟩ := hK.exists_thickening_subset_open ho hKU
  have hb : ∀ x ∈ K, ball x r ⊆ U := by
    intro x hx y hy
    exact hthick (mem_thickening_iff.mpr ⟨x, hx, hy⟩)
  have hH := h K hK hKU r hr hb
  have hcl : closure (holomorphicHull U K) ⊆ U := by
    intro a ha
    obtain ⟨z, hz, hza⟩ := Metric.mem_closure_iff.mp ha r hr
    exact hH z hz (by simpa only [mem_ball, dist_comm] using hza)
  exact isCompact_holomorphicHull_of_subset_compact
    (isBounded_holomorphicHull U hK.isBounded).isCompact_closure hcl subset_closure

/-- The boundary-distance characterization implies holomorphic convexity. -/
theorem HasHolomorphicHullDistanceProperty.isHolomorphicallyConvex
    {U : Set (ι → ℂ)} (h : HasHolomorphicHullDistanceProperty U) (ho : IsOpen U) :
    IsHolomorphicallyConvex U := h.hasHolomorphicHullRadiusProperty.isHolomorphicallyConvex ho

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
