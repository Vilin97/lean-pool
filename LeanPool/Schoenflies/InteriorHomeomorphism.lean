/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.InitialGenerated
public import LeanPool.Schoenflies.InitialOuterCycle
public import LeanPool.Schoenflies.QuantitativeRecursion

/-!
# The interior homeomorphism

This module starts the quantitative recursion at the canonical initial matched pair.  It closes
the construction of the nested stage sequence and therefore obtains the limit homeomorphism
between the inside of an arbitrary Jordan curve and the open square.
-/

@[expose] public section

open Set

namespace Schoenflies

variable {C : Set Plane}

/-- The initial-pair interface and the endgame interface express the same restricted
homeomorphism data with fields in a different order. -/
theorem IsHomeoOn.toIsSetHomeoOn {u v : Plane → Plane} {X Y : Set Plane}
    (h : IsHomeoOn u v X Y) : IsSetHomeoOn u v X Y where
  continuousOn := h.continuousOn
  continuousOn_inv := h.continuousOn_inv
  mapsTo := h.mapsTo
  mapsTo_inv := h.mapsTo_inv
  leftInvOn := h.invOn.1
  rightInvOn := h.invOn.2

/-- The anchored initial pair using the boundary homeomorphism supplied by the caller. -/
noncomputable def prescribedAnchoredInitialData (hC : IsJordanCurve C)
    (u v : Plane → Plane) (hu : IsHomeoOn u v C modelCurve) :
    AnchoredInitialData C (anchorSet hC) :=
  (exists_anchoredInitialData_of_homeo hC (anchorSet hC) u v
    hu.toIsSetHomeoOn).choose

theorem prescribedAnchoredInitialData_u (hC : IsJordanCurve C)
    (u v : Plane → Plane) (hu : IsHomeoOn u v C modelCurve) :
    (prescribedAnchoredInitialData hC u v hu).toInitialData.u = u :=
  (exists_anchoredInitialData_of_homeo hC (anchorSet hC) u v
    hu.toIsSetHomeoOn).choose_spec.1

/-- The quantitative sequence starting with a prescribed boundary homeomorphism. -/
noncomputable def prescribedJordanStageSequence (hC : IsJordanCurve C)
    (u v : Plane → Plane) (hu : IsHomeoOn u v C modelCurve) :
    StageSequence InitialCell initialStructure C :=
  denseQuantitativeStageSequence
    (prescribedAnchoredInitialData hC u v hu).generatedPair
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
      combInvariants_initialStructure

/-- The canonical, fully quantitative sequence of matched subdivisions associated with a
Jordan curve. -/
noncomputable def jordanStageSequence (hC : IsJordanCurve C) :
    StageSequence InitialCell initialStructure C :=
  denseQuantitativeStageSequence (initialData hC).generatedPair
    (jordan_curve_theorem hC) outerEdgesFormCycle_initialStructure
      combInvariants_initialStructure

/-- **`prop:interior-homeomorphism`.** Every Jordan curve bounds a domain homeomorphic to the
open square. -/
theorem exists_isHomeoOn_inside_openSquare (hC : IsJordanCurve C) :
    ∃ F G : Plane → Plane,
      IsHomeoOn F G (inside C) (Plane.openSquare 0 1) := by
  let T := jordanStageSequence hC
  exact ⟨T.limitTower.F, T.limitTower.inv, T.isHomeoOn_F⟩

/-- The selected limit map on the open Jordan domain. -/
noncomputable def jordanInteriorMap (hC : IsJordanCurve C) : Plane → Plane :=
  (jordanStageSequence hC).limitTower.F

/-- The selected inverse limit map on the open square. -/
noncomputable def jordanInteriorInv (hC : IsJordanCurve C) : Plane → Plane :=
  (jordanStageSequence hC).limitTower.inv

theorem jordanInteriorMap_isHomeoOn (hC : IsJordanCurve C) :
    IsHomeoOn (jordanInteriorMap hC) (jordanInteriorInv hC)
      (inside C) (Plane.openSquare 0 1) :=
  (jordanStageSequence hC).isHomeoOn_F

/-- The limit map already agrees with the prescribed initial boundary homeomorphism wherever
the latter is evaluated on the Jordan curve. `Schoenflies/BoundaryAnchors.lean` supplies the
additional data used to prove boundary continuity. -/
theorem jordanInteriorMap_eq_initialData_u (hC : IsJordanCurve C) :
    EqOn (jordanInteriorMap hC) (initialData hC).u C := by
  intro x hx
  let T := jordanStageSequence hC
  have hxskel : x ∈ (T.stage 0).src.skeletonSet := by
    change x ∈ (initialData hC).sourceRealization.skeletonSet
    rw [(initialData hC).sourceRealization_skeletonSet]
    exact Or.inl hx
  calc
    jordanInteriorMap hC x = (T.stage 0).homeo.toFun x :=
      T.F_eq_skelHomeo hxskel (Or.inl hx)
    _ = (initialData hC).skeletonHomeo.toFun x := by rfl
    _ = (initialData hC).u x := (initialData hC).skeletonHomeo_eq_u hx

/-- The limit map selected from the prescribed initial pair agrees pointwise with the caller's
boundary homeomorphism. -/
theorem prescribedJordanStageSequence_F_eq_boundary (hC : IsJordanCurve C)
    (u v : Plane → Plane) (hu : IsHomeoOn u v C modelCurve) :
    EqOn (prescribedJordanStageSequence hC u v hu).limitTower.F u C := by
  intro x hx
  let D := prescribedAnchoredInitialData hC u v hu
  let T := prescribedJordanStageSequence hC u v hu
  have hxskel : x ∈ (T.stage 0).src.skeletonSet := by
    change x ∈ D.toInitialData.sourceRealization.skeletonSet
    rw [D.toInitialData.sourceRealization_skeletonSet]
    exact Or.inl hx
  calc
    T.limitTower.F x = (T.stage 0).homeo.toFun x :=
      T.F_eq_skelHomeo hxskel (Or.inl hx)
    _ = D.toInitialData.skeletonHomeo.toFun x := by rfl
    _ = D.toInitialData.u x := D.toInitialData.skeletonHomeo_eq_u hx
    _ = u x := by rw [prescribedAnchoredInitialData_u hC u v hu]

end Schoenflies
