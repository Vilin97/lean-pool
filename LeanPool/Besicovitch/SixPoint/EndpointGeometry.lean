/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.Configuration

/-!
# Coordinate-free endpoint geometry

After translating the red root to the origin, the blue children are pulled back toward their own
root. The resulting vectors are the `e`, `p`, and `w` variables in the nine-packing proof.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

namespace SixPointConfiguration

/-- The displacement from the red root to the blue root. -/
def rootDisplacement (configuration : SixPointConfiguration) : (EuclideanSpace ℝ (Fin 2)) :=
  configuration .blue .root - configuration .red .root

/-- A red point, translated relative to the red root. -/
def redDisplacement (configuration : SixPointConfiguration) (label : SixPointLabel) :
    (EuclideanSpace ℝ (Fin 2)) :=
  configuration .red label - configuration .red .root

/-- A blue point pulled back from the blue root into the red child disk. -/
def bluePullback (configuration : SixPointConfiguration) (label : SixPointLabel) :
    (EuclideanSpace ℝ (Fin 2)) :=
  configuration .blue .root - configuration .blue label

/-- The root displacement of an admissible configuration has unit norm. -/
theorem norm_rootDisplacement {configuration : SixPointConfiguration} {s : ℝ}
    (h : configuration.IsAdmissibleAt s) : ‖configuration.rootDisplacement‖ = 1 := by
  rw [rootDisplacement, norm_sub_rev]
  simpa [dist_eq_norm] using h.root_distance

/-- Red child displacements have norm at most one. -/
theorem norm_redDisplacement_le_one {configuration : SixPointConfiguration} {s : ℝ}
    (h : configuration.IsAdmissibleAt s) {label : SixPointLabel} (hlabel : label ≠ .root) :
    ‖configuration.redDisplacement label‖ ≤ 1 := by
  rw [redDisplacement, norm_sub_rev]
  simpa [dist_eq_norm] using h.child_distance .red label hlabel

/-- Pulled-back blue child displacements have norm at most one. -/
theorem norm_bluePullback_le_one {configuration : SixPointConfiguration} {s : ℝ}
    (h : configuration.IsAdmissibleAt s) {label : SixPointLabel} (hlabel : label ≠ .root) :
    ‖configuration.bluePullback label‖ ≤ 1 := by
  simpa [bluePullback, dist_eq_norm] using h.child_distance .blue label hlabel

/-- The distance between red children is their displacement-vector distance. -/
theorem dist_redDisplacement (configuration : SixPointConfiguration)
    (label₁ label₂ : SixPointLabel) :
    dist (configuration.redDisplacement label₁) (configuration.redDisplacement label₂) =
      dist (configuration .red label₁) (configuration .red label₂) := by
  simp [redDisplacement, dist_eq_norm]

/-- Pulling back both blue children preserves their distance. -/
theorem dist_bluePullback (configuration : SixPointConfiguration)
    (label₁ label₂ : SixPointLabel) :
    dist (configuration.bluePullback label₁) (configuration.bluePullback label₂) =
      dist (configuration .blue label₁) (configuration .blue label₂) := by
  simp only [bluePullback, dist_eq_norm]
  rw [show
    (configuration .blue .root - configuration .blue label₁) -
        (configuration .blue .root - configuration .blue label₂) =
      configuration .blue label₂ - configuration .blue label₁ by abel]
  exact norm_sub_rev _ _

/-- Admissibility gives the endpoint lower bound for the red displacement pair. -/
theorem two_mul_le_dist_redDisplacement {configuration : SixPointConfiguration} {s : ℝ}
    (h : configuration.IsAdmissibleAt s) :
    2 * s ≤ dist (configuration.redDisplacement .left)
      (configuration.redDisplacement .right) := by
  rw [configuration.dist_redDisplacement]
  exact h.sibling_distance .red

/-- Admissibility gives the endpoint lower bound for the pulled-back blue pair. -/
theorem two_mul_le_dist_bluePullback {configuration : SixPointConfiguration} {s : ℝ}
    (h : configuration.IsAdmissibleAt s) :
    2 * s ≤ dist (configuration.bluePullback .left)
      (configuration.bluePullback .right) := by
  rw [configuration.dist_bluePullback]
  exact h.sibling_distance .blue

/-- A red-blue child distance is the norm of `e - p - w`. -/
theorem dist_red_blue_eq_norm (configuration : SixPointConfiguration)
    (redLabel blueLabel : SixPointLabel) :
    dist (configuration .red redLabel) (configuration .blue blueLabel) =
      ‖configuration.rootDisplacement - configuration.redDisplacement redLabel -
        configuration.bluePullback blueLabel‖ := by
  simp only [rootDisplacement, redDisplacement, bluePullback, dist_eq_norm]
  rw [show
    (configuration .blue .root - configuration .red .root) -
        (configuration .red redLabel - configuration .red .root) -
          (configuration .blue .root - configuration .blue blueLabel) =
      configuration .blue blueLabel - configuration .red redLabel by abel]
  exact norm_sub_rev _ _

end SixPointConfiguration

end LeanPool.Besicovitch
