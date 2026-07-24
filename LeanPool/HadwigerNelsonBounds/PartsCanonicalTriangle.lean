/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsRootDecision
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# The canonical non-monochromatic sqrt-three triangle

The checked Parts certificate rules out a monochromatic copy of its canonical
equilateral triangle in every proper four-coloring of the plane.
-/

namespace HadwigerNelsonBounds

/-- Rename a distinguished color to zero and a different color to three. -/
def partsColorEquiv (triple center : Fin 4) : Fin 4 ≃ Fin 4 :=
  (Equiv.swap triple 0).trans
    (Equiv.swap ((Equiv.swap triple 0) center) 3)

lemma partsColorEquiv_spec {triple center : Fin 4} (hne : triple ≠ center) :
    partsColorEquiv triple center triple = 0 ∧
      partsColorEquiv triple center center = 3 := by
  fin_cases triple <;> fin_cases center <;> revert hne <;> decide

/-- First vertex of the canonical equilateral triangle in the Parts graph. -/
noncomputable def partsTriangleA : R2 := (partsPoint 195).toR2

/-- Second vertex of the canonical equilateral triangle in the Parts graph. -/
noncomputable def partsTriangleB : R2 := (partsPoint 205).toR2

/-- Third vertex of the canonical equilateral triangle in the Parts graph. -/
noncomputable def partsTriangleC : R2 := (partsPoint 215).toR2

/-- The origin, adjacent to all three canonical triangle vertices. -/
noncomputable def partsTriangleCenter : R2 := (partsPoint 0).toR2

/-- The full Parts certificate: its canonical sqrt-three triangle is never
monochromatic in a proper four-coloring of the unit-distance graph. -/
theorem parts_canonical_triangle_not_monochromatic
    (planeColoring : unitDistanceGraph.Coloring (Fin 4)) :
    ¬(planeColoring partsTriangleA = planeColoring partsTriangleB ∧
      planeColoring partsTriangleB = planeColoring partsTriangleC) := by
  rintro ⟨hab, hbc⟩
  let triple := planeColoring partsTriangleA
  let center := planeColoring partsTriangleCenter
  have hadj : partsAdjacent 0 195 = true := by decide
  have hcenter : center ≠ triple := by
    exact planeColoring.valid (unitDistanceGraph_adj_of_partsAdjacent hadj)
  let rename := partsColorEquiv triple center
  have hrename := partsColorEquiv_spec hcenter.symm
  let coloring : Fin 481 → Fin 4 := fun vertex =>
    rename (planeColoring (partsPoint vertex).toR2)
  have hproper : PartsProper coloring := by
    intro v w hvw heq
    apply planeColoring.valid (unitDistanceGraph_adj_of_partsAdjacent hvw)
    exact rename.injective heq
  have hroots : PartsExtends coloring partsNormalizedRootPath := by
    intro assignment hin
    simp only [partsNormalizedRootPath, List.mem_cons] at hin
    rcases hin with rfl | rfl | rfl | rfl | hin
    · exact hrename.2
    · exact hrename.1
    · exact (congrArg rename hab).symm.trans hrename.1
    · exact (congrArg rename (hab.trans hbc)).symm.trans hrename.1
    · simp at hin
  exact no_parts_coloring_of_normalized_root hproper hroots

end HadwigerNelsonBounds
