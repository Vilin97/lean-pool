/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Segments.SeamCalculus
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgeGenusOne

/-!
# Degree-one rigidity from two-edge-connected cuts

For the pointed genus-one wedge argument, the remaining cycle input is that
distinct vertices determine distinct degree-one divisor classes.  This file
proves a graph-level sufficient condition: every nonempty proper vertex cut
has total outgoing multiplicity at least two.

If `(y) - (p)` were principal, choose the maximum level set of a firing script
with principal divisor `(p) - (y)`.  The vertex `p` cannot lie in that set.
At every other maximum except possibly `y`, the level-set inequality forces
out-degree zero; at `y` it forces out-degree at most one.  Thus the whole cut
has size at most one, contradicting the hypothesis.
-/

namespace Utilities

open Finset

universe uTwoEdgeRigidity

variable {H : CFGraph.{uTwoEdgeRigidity}}

/-- Total edge multiplicity crossing from `S` to its complement, counted at
the endpoint in `S`. -/
def cutMultiplicity (H : CFGraph) (S : Finset H.V) : ℤ :=
  ∑ v ∈ S, outdeg_S H S v

/-- Every nonempty proper vertex set has at least two outgoing edges, counted
with multiplicity.  For a connected loopless multigraph this is the usual
absence of bridges. -/
def TwoEdgeCutCondition (H : CFGraph) : Prop :=
  ∀ S : Finset H.V, S.Nonempty → S ≠ Finset.univ →
    2 ≤ cutMultiplicity H S

/-- The cut leaving a singleton has multiplicity equal to the valence of its
unique vertex. -/
@[simp] theorem cutMultiplicity_singleton (H : CFGraph) (v : H.V) :
    cutMultiplicity H {v} = vertex_degree H v := by
  unfold cutMultiplicity vertex_degree outdeg_S
  simp

/-- A graph satisfying the two-edge cut condition has no degree-one
vertices. -/
theorem vertex_degree_ne_one_of_twoEdgeCutCondition
    (hCut : TwoEdgeCutCondition H) (v : H.V) :
    vertex_degree H v ≠ 1 := by
  intro hDegree
  have hNeighbor : ∃ w : H.V, 0 < num_edges H v w := by
    by_contra h
    push Not at h
    have hZero : ∀ w : H.V, num_edges H v w = 0 := by
      intro w
      have hw := h w
      omega
    simp [vertex_degree, hZero] at hDegree
  obtain ⟨w, hvw⟩ := hNeighbor
  have hvwNe : w ≠ v := by
    intro h
    subst w
    simp at hvw
  have hProper : ({v} : Finset H.V) ≠ Finset.univ := by
    intro h
    have : w ∈ ({v} : Finset H.V) := by rw [h]; simp
    exact hvwNe (by simpa using this)
  have hLower := hCut {v} (by simp) hProper
  rw [cutMultiplicity_singleton, hDegree] at hLower
  omega

theorem cutMultiplicity_nonneg (H : CFGraph) (S : Finset H.V) :
    0 ≤ cutMultiplicity H S := by
  exact Finset.sum_nonneg fun v _ => outdeg_S_nonneg H S v

/-- A maximum-level vertex whose principal coefficient is zero has no edge
leaving the maximum-level set. -/
theorem outdeg_S_topSet_eq_zero_of_prin_eq_zero
    {g : firing_script H} {v : H.V} (hv : v ∈ topSet g)
    (hPrin : prin H g v = 0) :
    outdeg_S H (topSet g) v = 0 := by
  have hUpper := prin_le_neg_outdeg_S hv
  have hNonnegative := outdeg_S_nonneg H (topSet g) v
  omega

/-- A maximum-level vertex with principal coefficient `-1` has at most one
edge leaving the maximum-level set. -/
theorem outdeg_S_topSet_le_one_of_prin_eq_neg_one
    {g : firing_script H} {v : H.V} (hv : v ∈ topSet g)
    (hPrin : prin H g v = -1) :
    outdeg_S H (topSet g) v ≤ 1 := by
  have hUpper := prin_le_neg_outdeg_S hv
  omega

/-- Distinct vertices cannot be linearly equivalent in degree one when every
proper cut has multiplicity at least two.  Connectedness is retained in the
interface expected by the genus-one application; the cut hypothesis already
contains the part of connectedness used by this extremal-set proof. -/
theorem not_linear_equiv_one_chip_sub_of_twoEdgeCutCondition
    (_hConnected : graph_connected H) (hCut : TwoEdgeCutCondition H)
    {p y : H.V} (hpy : p ≠ y) :
    ¬ linear_equiv H (one_chip y - one_chip p) 0 := by
  intro hEquivalent
  unfold linear_equiv at hEquivalent
  obtain ⟨g, hg⟩ :=
    (principal_iff_eq_prin H (0 - (one_chip y - one_chip p))).mp
      hEquivalent
  have hPrincipal : prin H g = one_chip p - one_chip y := by
    calc
      prin H g = 0 - (one_chip y - one_chip p) := hg.symm
      _ = one_chip p - one_chip y := by abel
  let S : Finset H.V := topSet g
  have hSNonempty : S.Nonempty := by
    exact topSet_nonempty g
  have hpNotS : p ∉ S := by
    intro hpS
    have hAtP : prin H g p = 1 := by
      rw [hPrincipal]
      simp [one_chip, hpy]
    have hUpper := prin_le_neg_outdeg_S (H := H) (g := g) (v := p) hpS
    have hNonnegative := outdeg_S_nonneg H (topSet g) p
    omega
  have hSProper : S ≠ Finset.univ := by
    intro hUniv
    apply hpNotS
    rw [hUniv]
    simp
  have hZeroAwayY : ∀ v ∈ S, v ≠ y → outdeg_S H S v = 0 := by
    intro v hvS hvy
    have hvp : v ≠ p := by
      intro hvp
      subst v
      exact hpNotS hvS
    have hAtV : prin H g v = 0 := by
      rw [hPrincipal]
      simp [one_chip, hvp, hvy]
    exact outdeg_S_topSet_eq_zero_of_prin_eq_zero
      (H := H) (g := g) (v := v) hvS hAtV
  have hCutUpper : cutMultiplicity H S ≤ 1 := by
    by_cases hyS : y ∈ S
    · have hAtY : prin H g y = -1 := by
        rw [hPrincipal]
        simp [one_chip, hpy.symm]
      have hYUpper : outdeg_S H S y ≤ 1 :=
        outdeg_S_topSet_le_one_of_prin_eq_neg_one
          (H := H) (g := g) (v := y) hyS hAtY
      have hSum : cutMultiplicity H S = outdeg_S H S y := by
        unfold cutMultiplicity
        apply Finset.sum_eq_single y
        · intro v hvS hvy
          exact hZeroAwayY v hvS hvy
        · intro hyNot
          exact (hyNot hyS).elim
      rw [hSum]
      exact hYUpper
    · have hSum : cutMultiplicity H S = 0 := by
        unfold cutMultiplicity
        apply Finset.sum_eq_zero
        intro v hvS
        exact hZeroAwayY v hvS (by
          intro hvy
          subst v
          exact hyS hvS)
      rw [hSum]
      omega
  have hCutLower := hCut S hSNonempty hSProper
  omega

/-- A connected genus-one graph with a second vertex and no one-edge cut is
a pointed rigid genus-one block. -/
theorem pointedGenusOneRigid_of_twoEdgeCutCondition
    (y : H.V) (hConnected : graph_connected H) (hGenus : genus H = 1)
    (hExists : ∃ p : H.V, p ≠ y) (hCut : TwoEdgeCutCondition H) :
    PointedGenusOneRigid H y where
  connected := hConnected
  genus_one := hGenus
  exists_ne := hExists
  nontrivial := by
    intro p hp
    exact not_linear_equiv_one_chip_sub_of_twoEdgeCutCondition
      hConnected hCut hp

end Utilities
