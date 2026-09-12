/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Statement

/-!
# Two-color six-point configurations

This file records exactly the metric assumptions in the finite six-point problem.
-/

@[expose] public section

namespace LeanPool.Besicovitch

/-- The two colors in a six-point configuration. -/
inductive SixPointColor
  | red
  | blue
  deriving DecidableEq

instance : Fintype SixPointColor where
  elems := {.red, .blue}
  complete := by intro color; cases color <;> simp

/-- The root and two child labels belonging to each color. -/
inductive SixPointLabel
  | root
  | left
  | right
  deriving DecidableEq

instance : Fintype SixPointLabel where
  elems := {.root, .left, .right}
  complete := by intro label; cases label <;> simp

/-- A label for one of the six points. -/
abbrev SixPointIndex := SixPointColor × SixPointLabel

/-- A two-color six-point configuration in the Euclidean plane. -/
abbrev SixPointConfiguration := SixPointColor → SixPointLabel → (EuclideanSpace ℝ (Fin 2))

namespace SixPointConfiguration

/-- The labelled configuration determined by two roots and two children of each color. -/
def ofPoints (redRoot redLeft redRight blueRoot blueLeft blueRight : (EuclideanSpace ℝ (Fin 2))) :
    SixPointConfiguration
  | .red, .root => redRoot
  | .red, .left => redLeft
  | .red, .right => redRight
  | .blue, .root => blueRoot
  | .blue, .left => blueLeft
  | .blue, .right => blueRight

/-- A normalized configuration at separation parameter `s`. -/
structure IsAdmissibleAt (configuration : SixPointConfiguration) (s : ℝ) : Prop where
  root_distance : dist (configuration .red .root) (configuration .blue .root) = 1
  child_distance : ∀ color label, label ≠ .root →
    dist (configuration color .root) (configuration color label) ≤ 1
  sibling_distance : ∀ color,
    2 * s ≤ dist (configuration color .left) (configuration color .right)

/-- Raising the separation parameter only shrinks the admissible configuration class. -/
theorem IsAdmissibleAt.mono {configuration : SixPointConfiguration} {s t : ℝ}
    (hst : s ≤ t) (h : configuration.IsAdmissibleAt t) : configuration.IsAdmissibleAt s where
  root_distance := h.root_distance
  child_distance := h.child_distance
  sibling_distance color := (mul_le_mul_of_nonneg_left hst (by norm_num)).trans
    (h.sibling_distance color)

end SixPointConfiguration

end LeanPool.Besicovitch
