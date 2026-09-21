/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Opening.FiniteOrbit
import LeanPool.MarkoffModP.BGS.Markoff.Core.ConicParametrization

namespace BGS.Markoff

universe u

variable {R : Type u} [Field R] [DecidableEq R] [Invertible (3 : R)]

/-- The finite segment of normalized surface iterates cut out by the matrix rotation order. -/
noncomputable def normalizedSurfaceRotationCycle (x : NormalizedMarkoffSurface R) :
    Finset (NormalizedMarkoffSurface R) := by
  classical
  exact (Finset.range (rotationOrder x.1.u1)).image fun n =>
    (normalizedRotate1Surface^[n]) x

/-- Every point of the normalized rotation cycle belongs to the full transported Gamma orbit. -/
theorem normalizedSurfaceRotationCycle_subset_normalizedGammaOrbit
    (x : NormalizedMarkoffSurface R) :
    (normalizedSurfaceRotationCycle x : Set (NormalizedMarkoffSurface R)) ⊆
      normalizedGammaOrbit x := by
  classical
  intro y hy
  rw [Finset.mem_coe, normalizedSurfaceRotationCycle, Finset.mem_image] at hy
  obtain ⟨n, _hn, rfl⟩ := hy
  exact (sameNormalizedComponent_iff_mem_normalizedGammaOrbit x _).mp
    (sameNormalizedComponent_iterate_normalizedRotate1Surface x n)

omit [Invertible (3 : R)] in
/-- Forgetting the surface proof identifies the surface cycle with the existing point cycle. -/
theorem normalizedSurfaceRotationCycle_image_val
    (x : NormalizedMarkoffSurface R) :
    (normalizedSurfaceRotationCycle x).image Subtype.val =
      normalizedRotationCycle x.1.u1 x.1 := by
  classical
  ext y
  simp only [normalizedSurfaceRotationCycle, normalizedRotationCycle, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨z, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨n, hn, (coe_iterate_normalizedRotate1Surface x n).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨(normalizedRotate1Surface^[n]) x, ⟨n, hn, rfl⟩,
      coe_iterate_normalizedRotate1Surface x n⟩

omit [Invertible (3 : R)] in
/-- Surface and point rotation cycles have the same cardinality. -/
theorem normalizedSurfaceRotationCycle_card
    (x : NormalizedMarkoffSurface R) :
    (normalizedSurfaceRotationCycle x).card =
      (normalizedRotationCycle x.1.u1 x.1).card := by
  rw [← normalizedSurfaceRotationCycle_image_val x]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

/-- A normalized rotation cycle injects into the full Gamma orbit, so its cardinality is an
honest lower bound for the orbit cardinality. -/
theorem normalizedRotationCycle_card_le_normalizedGammaOrbit_ncard
    [Fintype R] (x : NormalizedMarkoffSurface R) :
    (normalizedRotationCycle x.1.u1 x.1).card ≤ (normalizedGammaOrbit x).ncard := by
  rw [← normalizedSurfaceRotationCycle_card x, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (normalizedSurfaceRotationCycle_subset_normalizedGammaOrbit x)

end BGS.Markoff
