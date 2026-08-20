/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.PolygonalQuotient
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Radial extension of circle homeomorphisms

Every `PolygonCell n` has the closed unit disk as its carrier. This file implements the radial
extension (Alexander trick) of a homeomorphism of the unit circle. The extension preserves the
norm exactly, is continuous at the origin by that norm identity, and restricts to the selected
circle homeomorphism on the boundary.

The side-count indices of the source and target cells are independent phantom parameters. A
later boundary reparameterization only needs to construct a circle homeomorphism with the desired
action on marked arcs; `PolygonCell.radialHomeomorph` then supplies the disk homeomorphism.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex

namespace Circle

/-- The direction of a nonzero complex number as a point of the unit circle. -/
noncomputable def direction (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / ‖z‖, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_norm]
    exact div_self (norm_ne_zero_iff.mpr hz)⟩

@[simp]
theorem coe_direction (z : ℂ) (hz : z ≠ 0) :
    (direction z hz : ℂ) = z / ‖z‖ :=
  rfl

theorem continuous_direction :
    Continuous (fun w : {w : ℂ // w ≠ 0} =>
      direction (w : ℂ) w.property) := by
  apply continuous_induced_rng.2
  change Continuous (fun w : {w : ℂ // w ≠ 0} =>
    (w : ℂ) / ‖(w : ℂ)‖)
  have hnorm : Continuous (fun w : {w : ℂ // w ≠ 0} =>
      (‖(w : ℂ)‖ : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_subtype_val.norm
  exact continuous_subtype_val.div₀ hnorm fun w =>
    ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr w.property)

/-- Radially extend a circle homeomorphism to the complex plane, fixing the origin. -/
noncomputable def radialMap (h : Circle ≃ₜ Circle) (z : ℂ) : ℂ :=
  if hz : z = 0 then 0
  else (‖z‖ : ℂ) * (h (direction z hz) : ℂ)

@[simp]
theorem radialMap_zero (h : Circle ≃ₜ Circle) :
    radialMap h 0 = 0 := by
  simp [radialMap]

theorem radialMap_of_ne (h : Circle ≃ₜ Circle) {z : ℂ} (hz : z ≠ 0) :
    radialMap h z = (‖z‖ : ℂ) * (h (direction z hz) : ℂ) := by
  simp [radialMap, hz]

/-- Radial extension preserves distance from the origin exactly. -/
@[simp]
theorem norm_radialMap (h : Circle ≃ₜ Circle) (z : ℂ) :
    ‖radialMap h z‖ = ‖z‖ := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [radialMap_of_ne h hz, norm_mul, Circle.norm_coe]
    simp

theorem radialMap_ne_zero (h : Circle ≃ₜ Circle) {z : ℂ} (hz : z ≠ 0) :
    radialMap h z ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_radialMap]
  exact norm_ne_zero_iff.mpr hz

/-- The direction of a radial image is the selected image direction. -/
theorem direction_radialMap (h : Circle ≃ₜ Circle) {z : ℂ} (hz : z ≠ 0) :
    direction (radialMap h z) (radialMap_ne_zero h hz) =
      h (direction z hz) := by
  apply Subtype.ext
  rw [coe_direction, radialMap_of_ne h hz]
  simp only [norm_mul, Circle.norm_coe, mul_one, norm_real,
    Real.norm_eq_abs, abs_norm]
  field_simp [norm_ne_zero_iff.mpr hz]

/-- Extending the inverse circle homeomorphism gives the inverse radial map. -/
theorem radialMap_symm_apply (h : Circle ≃ₜ Circle) (z : ℂ) :
    radialMap h.symm (radialMap h z) = z := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [radialMap_of_ne h.symm (radialMap_ne_zero h hz),
      direction_radialMap h hz, h.symm_apply_apply, norm_radialMap,
      coe_direction]
    field_simp [norm_ne_zero_iff.mpr hz]

theorem continuousAt_radialMap_zero (h : Circle ≃ₜ Circle) :
    ContinuousAt (radialMap h) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro z hz
  rw [radialMap_zero, dist_zero_right, norm_radialMap,
    ← dist_zero_right]
  exact hz

theorem continuousAt_radialMap_of_ne (h : Circle ≃ₜ Circle)
    {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (radialMap h) z := by
  have hrestrict :
      Continuous (fun w : {w : ℂ // w ≠ 0} => radialMap h w) := by
    have heq :
        (fun w : {w : ℂ // w ≠ 0} => radialMap h w) =
          fun w : {w : ℂ // w ≠ 0} => (‖(w : ℂ)‖ : ℂ) *
            (h (direction (w : ℂ) w.property) : ℂ) := by
      funext w
      exact radialMap_of_ne h w.property
    rw [heq]
    have hnorm : Continuous (fun w : {w : ℂ // w ≠ 0} =>
        (‖(w : ℂ)‖ : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_subtype_val.norm
    exact hnorm.mul
      (continuous_subtype_val.comp
        (h.continuous.comp continuous_direction))
  have hOn : ContinuousOn (radialMap h) ({0}ᶜ : Set ℂ) := by
    rw [continuousOn_iff_continuous_restrict]
    exact hrestrict
  exact (hOn z hz).continuousAt (isOpen_compl_singleton.mem_nhds hz)

theorem continuous_radialMap (h : Circle ≃ₜ Circle) :
    Continuous (radialMap h) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    exact continuousAt_radialMap_zero h
  · exact continuousAt_radialMap_of_ne h hz

/-- On the unit circle, radial extension is exactly the original homeomorphism. -/
@[simp]
theorem radialMap_coe (h : Circle ≃ₜ Circle) (z : Circle) :
    radialMap h (z : ℂ) = (h z : ℂ) := by
  rw [radialMap_of_ne h z.coe_ne_zero, z.norm_coe]
  have hdirection : direction (z : ℂ) z.coe_ne_zero = z := by
    apply Circle.ext
    rw [coe_direction, z.norm_coe]
    simp
  rw [hdirection]
  simp

end Circle

namespace PolygonCell

/-- Radially extend a circle homeomorphism between closed polygon-cell carriers. -/
noncomputable def radialHomeomorph {n m : ℕ} (h : Circle ≃ₜ Circle) :
    PolygonCell n ≃ₜ PolygonCell m where
  toFun z := ⟨Circle.radialMap h z.val, by
    rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_radialMap]
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property⟩
  invFun z := ⟨Circle.radialMap h.symm z.val, by
    rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_radialMap]
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property⟩
  left_inv := by
    intro z
    apply PolygonCell.ext
    exact Circle.radialMap_symm_apply h z.val
  right_inv := by
    intro z
    apply PolygonCell.ext
    exact Circle.radialMap_symm_apply h.symm z.val
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact Circle.continuous_radialMap h |>.comp PolygonCell.continuous_val
  continuous_invFun := by
    apply continuous_induced_rng.2
    exact Circle.continuous_radialMap h.symm |>.comp PolygonCell.continuous_val

@[simp]
theorem radialHomeomorph_apply_val {n m : ℕ} (h : Circle ≃ₜ Circle)
    (z : PolygonCell n) :
    (radialHomeomorph (n := n) (m := m) h z).val =
      Circle.radialMap h z.val :=
  rfl

/-- The radial cell homeomorphism restricts to the selected circle homeomorphism. -/
@[simp]
theorem radialHomeomorph_ofCircle {n m : ℕ} (h : Circle ≃ₜ Circle)
    (z : Circle) :
    radialHomeomorph h (ofCircle n z) = ofCircle m (h z) := by
  apply PolygonCell.ext
  exact Circle.radialMap_coe h z

end PolygonCell

end LeanEval.Topology.ClassificationOfSurfaces
