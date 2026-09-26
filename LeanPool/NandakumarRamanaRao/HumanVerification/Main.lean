/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Tactic
public import LeanPool.NandakumarRamanaRao.HumanVerification.EqualAreaEqualPerimeterPartitionWrapper

/-! # Main -/

@[expose] public section

noncomputable section

namespace HumanVerification

/-- The real Euclidean plane, with its standard inner product and measure. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A nondegenerate compact convex figure in the Euclidean plane. -/
structure ConvexFigure where
  /-- The set of points belonging to the figure. -/
  carrier : Set Plane
  isConvex : Convex ℝ carrier
  isCompact : IsCompact carrier
  hasNonemptyInterior : (interior carrier).Nonempty

namespace ConvexFigure

/-- Convert a public figure to the solid convex-body type used by the proof. -/
def toBody (F : ConvexFigure) : NRR.Geometry.ConvexBody Plane where
  carrier := F.carrier
  convex' := F.isConvex
  isCompact' := F.isCompact
  interior_nonempty' := F.hasNonemptyInterior

/-- Present an internal solid convex body as a public figure. -/
def ofBody (K : NRR.Geometry.ConvexBody Plane) : ConvexFigure where
  carrier := K
  isConvex := K.convex
  isCompact := K.isCompact
  hasNonemptyInterior := K.interior_nonempty

@[simp] theorem toBody_carrier (F : ConvexFigure) :
    (F.toBody : Set Plane) = F.carrier := rfl

@[simp] theorem ofBody_carrier (K : NRR.Geometry.ConvexBody Plane) :
    (ofBody K).carrier = (K : Set Plane) := rfl

@[simp] theorem ofBody_toBody (F : ConvexFigure) : ofBody F.toBody = F := by
  cases F
  rfl

@[simp] theorem toBody_ofBody (K : NRR.Geometry.ConvexBody Plane) :
    (ofBody K).toBody = K := by
  exact NRR.Geometry.ConvexBody.ext rfl

/-- Public figures and internal solid convex bodies carry exactly the same data. -/
def equivBody : ConvexFigure ≃ NRR.Geometry.ConvexBody Plane where
  toFun := toBody
  invFun := ofBody
  left_inv := by exact ofBody_toBody
  right_inv := by exact toBody_ofBody

/-- The reusable proof-export model induced by the public body conversion. -/
instance instConvexFigureModel : NRR.HumanExport.ConvexFigureModel ConvexFigure where
  carrier := ConvexFigure.carrier
  isConvex := ConvexFigure.isConvex
  isCompact := ConvexFigure.isCompact
  hasNonemptyInterior := ConvexFigure.hasNonemptyInterior
  ofBody := ofBody
  carrier_ofBody := by exact ofBody_carrier

/-- Lebesgue area of the figure's carrier. -/
def area (F : ConvexFigure) : ENNReal :=
  MeasureTheory.volume F.carrier

/-- One-dimensional Hausdorff measure of the figure's boundary. -/
def perimeter (F : ConvexFigure) : ENNReal :=
  (MeasureTheory.Measure.hausdorffMeasure (1 : ℝ) :
      MeasureTheory.Measure Plane)
    (frontier F.carrier)

end ConvexFigure

/-- A finite family covers the figure and has pairwise disjoint interiors. -/
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
  exact equalAreaEqualPerimeterPartitionWrapper F n hn

end HumanVerification
