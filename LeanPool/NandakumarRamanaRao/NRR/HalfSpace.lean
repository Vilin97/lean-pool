/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.HalfspaceCut

/-!
# `NRR.HalfSpace` — public halfspace definitions

Provides the set-theoretic lower and upper halfspaces used throughout the cut and power-diagram
layers. Measure-theoretic and continuity results live in the dedicated halfspace-cut modules.
-/

open NRR
open scoped RealInnerProductSpace

namespace NRR.Halfspace

/-- The public closed half‑space with inner normal `u` and offset `c`, defined as a direct
wrapper around the implemented geometry half‑space `Geometry.lowerClosedHalfspace u c`, i.e.
`{x : E2 | ⟪u, x⟫ ≤ c}`. (`E2` is a definitional alias of `Geometry.Plane`.) -/
def of (u : E2) (c : ℝ) : Set E2 :=
  Geometry.lowerClosedHalfspace u c

@[simp] theorem of_eq_lowerClosedHalfspace (u : E2) (c : ℝ) :
    Halfspace.of u c = Geometry.lowerClosedHalfspace u c := rfl

/-- A half‑space is convex. -/
theorem convex (u : E2) (c : ℝ) : Convex ℝ (Halfspace.of u c) :=
  Geometry.lowerClosedHalfspace_convex u c

/-- A half‑space is closed. -/
theorem isClosed (u : E2) (c : ℝ) : IsClosed (Halfspace.of u c) :=
  Geometry.lowerClosedHalfspace_isClosed u c

@[simp] theorem mem_halfspace (u x : E2) (c : ℝ) :
    x ∈ Halfspace.of u c ↔ ⟪u, x⟫ ≤ c :=
  Geometry.mem_lowerClosedHalfspace u c x

/-- An affine hyperplane `{x | ⟪u, x⟫ = c}` in the plane, with nonzero normal `u`, has
Lebesgue measure zero. The hyperplane is a translate of the kernel of the (nonzero) linear
functional `⟪u, ·⟫`, which is a proper submodule and hence Haar-null. -/
theorem hyperplane_null {u : E2} (hu : u ≠ 0) (c : ℝ) :
    MeasureTheory.volume {x : E2 | ⟪u, x⟫ = c} = 0 := by
  by_contra h_nonzero
  -- The set `{x | ⟪u, x⟫ = c}` is a translate of the kernel of `⟪u, ·⟫`.
  have hnorm : ‖u‖ ^ 2 ≠ 0 := by
    have : ‖u‖ ≠ 0 := by simpa [norm_eq_zero] using hu
    positivity
  have h_translate :
      {x : E2 | ⟪u, x⟫ = c}
        = (fun y => (c / ‖u‖ ^ 2) • u + y) '' {x | ⟪u, x⟫ = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hx
      refine ⟨x - (c / ‖u‖ ^ 2) • u, ?_, by abel⟩
      rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hx]
      field_simp
      ring
    · rintro ⟨y, hy, rfl⟩
      rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hy]
      field_simp
      ring
  -- The kernel of `⟪u, ·⟫` is a proper submodule.
  have h_kernel :
      ∃ s : Submodule ℝ E2, s ≠ ⊤ ∧ {x : E2 | ⟪u, x⟫ = 0} = s := by
    refine ⟨LinearMap.ker (innerₛₗ ℝ u), ?_, ?_⟩
    · have hmem : u ∉ LinearMap.ker (innerₛₗ ℝ u) := by
        simp [LinearMap.mem_ker, hu]
      exact fun htop => hmem (htop ▸ Submodule.mem_top)
    · ext x; simp [LinearMap.mem_ker]
  obtain ⟨s, hs₁, hs₂⟩ := h_kernel
  rw [h_translate, hs₂, Set.image_add_left] at h_nonzero
  refine h_nonzero ?_
  rw [MeasureTheory.measure_preimage_add]
  exact MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume s hs₁

end NRR.Halfspace

namespace NRR.Geometry.ConvexBody

/-- Intersecting a convex body `K` with the public closed half‑space `Halfspace.of u c` yields
a compact convex set; when it retains nonempty interior it is again a (solid) convex body.
This bundles the intersection as a `ConvexBody`, requiring the nonempty‑interior hypothesis
`hInt` explicitly (solidity is not automatic). It is a thin wrapper around the geometry
primitive `ConvexBody.cutLowerClosed`. -/
noncomputable def interHalfspace
    (K : ConvexBody Plane) (u : Plane) (c : ℝ)
    (hInt : (interior ((K : Set Plane) ∩ NRR.Halfspace.of u c)).Nonempty) :
    ConvexBody Plane :=
  K.cutLowerClosed u c hInt

/-- The carrier of `interHalfspace` is the set intersection with the public half‑space. -/
@[simp] theorem coe_interHalfspace
    (K : ConvexBody Plane) (u : Plane) (c : ℝ)
    (hInt : (interior ((K : Set Plane) ∩ NRR.Halfspace.of u c)).Nonempty) :
    (K.interHalfspace u c hInt : Set Plane) =
      (K : Set Plane) ∩ NRR.Halfspace.of u c := rfl

end NRR.Geometry.ConvexBody
