/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.HumanVerification.EqualAreaEqualPerimeterPartitionWrapper

/-! # Main -/

noncomputable section

namespace HumanVerification

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A nondegenerate compact convex figure in the Euclidean plane. -/
structure ConvexFigure where
  carrier : Set Plane
  isConvex : Convex ℝ carrier
  isCompact : IsCompact carrier
  hasNonemptyInterior : (interior carrier).Nonempty

namespace ConvexFigure

def area (F : ConvexFigure) : ENNReal :=
  MeasureTheory.volume F.carrier

def perimeter (F : ConvexFigure) : ENNReal :=
  (MeasureTheory.Measure.hausdorffMeasure (1 : ℝ) :
      MeasureTheory.Measure Plane)
    (frontier F.carrier)

end ConvexFigure

def IsConvexPartition {n : ℕ}
    (F : ConvexFigure) (pieces : Fin n → ConvexFigure) : Prop :=
  F.carrier = ⋃ i, (pieces i).carrier ∧
  ∀ i j, i ≠ j →
    Disjoint
      (interior (pieces i).carrier)
      (interior (pieces j).carrier)

/--
Every nondegenerate compact convex figure can be partitioned into `n > 0`
compact convex figures having equal areas and equal perimeters.
-/
theorem equalAreaEqualPerimeterPartition
    (F : ConvexFigure) (n : ℕ) (hn : 0 < n) :
    ∃ pieces : Fin n → ConvexFigure,
      IsConvexPartition F pieces ∧
      (∀ i j, (pieces i).area = (pieces j).area) ∧
      (∀ i j, (pieces i).perimeter = (pieces j).perimeter) := by
  let model : NRR.HumanExport.ConvexFigureModel ConvexFigure :=
    { carrier := ConvexFigure.carrier
      isConvex := ConvexFigure.isConvex
      isCompact := ConvexFigure.isCompact
      hasNonemptyInterior := ConvexFigure.hasNonemptyInterior
      ofBody := fun K =>
        { carrier := K
          isConvex := K.convex
          isCompact := K.isCompact
          hasNonemptyInterior := K.interior_nonempty }
      carrier_ofBody := by
        intro K
        rfl }
  exact @equalAreaEqualPerimeterPartitionWrapper ConvexFigure model F n hn

end HumanVerification
