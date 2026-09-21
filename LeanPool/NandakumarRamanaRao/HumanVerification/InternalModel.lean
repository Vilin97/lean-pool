/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.PlanarPerimeter
import LeanPool.NandakumarRamanaRao.NRR.Partition.ConvexPartition
import LeanPool.NandakumarRamanaRao.NRR.FairPartition.Predicates

/-! # Internal Model -/

open Set MeasureTheory

noncomputable section

namespace NRR.HumanExport

/-- The Euclidean plane used by the internal proof-export layer. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/--
A type-level interface used by the proof wrapper.

The human-facing structure is deliberately declared later, in
`HumanVerification/Main.lean`.  This interface lets the wrapper be imported
before that declaration, avoiding an import cycle while keeping all public
definitions in the human-facing file.
-/
class ConvexFigureModel (α : Type) where
  carrier : α → Set Plane
  isConvex : ∀ F, Convex ℝ (carrier F)
  isCompact : ∀ F, IsCompact (carrier F)
  hasNonemptyInterior : ∀ F, (interior (carrier F)).Nonempty
  ofBody : NRR.Geometry.ConvexBody Plane → α
  carrier_ofBody : ∀ K, carrier (ofBody K) = (K : Set Plane)

namespace ConvexFigureModel

variable {α : Type} [ConvexFigureModel α]

/-- Convert any model value into the convex-body type used by NRR. -/
def toBody (F : α) : NRR.Geometry.ConvexBody Plane where
  carrier := ConvexFigureModel.carrier F
  convex' := ConvexFigureModel.isConvex F
  isCompact' := ConvexFigureModel.isCompact F
  interior_nonempty' := ConvexFigureModel.hasNonemptyInterior F

@[simp] theorem toBody_carrier (F : α) :
    ((toBody F : NRR.Geometry.ConvexBody Plane) : Set Plane) =
      ConvexFigureModel.carrier F := rfl

@[simp] theorem carrier_ofBody_apply
    (K : NRR.Geometry.ConvexBody Plane) :
    ConvexFigureModel.carrier (α := α) (ConvexFigureModel.ofBody K) =
      (K : Set Plane) :=
  ConvexFigureModel.carrier_ofBody K

end ConvexFigureModel

/-- Generic area used internally by the wrapper. -/
abbrev area {α : Type} [ConvexFigureModel α] (F : α) : ENNReal :=
  volume (ConvexFigureModel.carrier F)

/-- Generic Hausdorff perimeter used internally by the wrapper. -/
abbrev perimeter {α : Type} [ConvexFigureModel α] (F : α) : ENNReal :=
  (μH[1] : Measure Plane) (frontier (ConvexFigureModel.carrier F))

/-- Generic partition predicate used internally by the wrapper. -/
abbrev IsConvexPartition {α : Type} [ConvexFigureModel α] {n : ℕ}
    (F : α) (pieces : Fin n → α) : Prop :=
  ConvexFigureModel.carrier F =
      ⋃ i, ConvexFigureModel.carrier (pieces i) ∧
  ∀ i j, i ≠ j →
    Disjoint
      (interior (ConvexFigureModel.carrier (pieces i)))
      (interior (ConvexFigureModel.carrier (pieces j)))

end NRR.HumanExport
