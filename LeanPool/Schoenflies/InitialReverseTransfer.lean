/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.FiniteTransferTargetMesh
import LeanPool.Schoenflies.InitialGenerated
import LeanPool.Schoenflies.InitialOuterCycle

/-!
# Reverse square-mesh transfer over the initial cell-name type

The concrete square mesh uses segments (`Piece`) as edge names, whereas every generated pair
over the initial hexagon uses `InitialCell`.  Only the finitely many mesh edges matter, so they
can be injectively renamed into the spare `InitialCell.aux` supply while avoiding every current
cell name.  Edge relabelling preserves the ambient boundary geometry used by reverse transfer.

## Blueprint

* `Schoenflies.exists_initialCell_squareMesh_edgeRelabeling` — choose fresh `InitialCell` names
  for all edges of one finite square mesh.
* `Schoenflies.finite_transfer_toward_source_initial_relabelledSquareMesh` — direction (b) for
  the relabelled mesh, with the initial outer-cycle base case discharged.
* `Schoenflies.exists_finite_transfer_toward_source_initial_squareMesh` — the bare-square-mesh
  specialization: choose the fresh names, assemble the extension from the three explicit
  subdivision hypotheses, and run reverse transfer.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph

/-- Every finite square mesh can be renamed into currently unused `InitialCell` names. -/
theorem exists_initialCell_squareMesh_edgeRelabeling
    {srcOuter srcDom tgtDom : Set Plane}
    (P : GeneratedPair initialStructure srcOuter srcDom modelCurve tgtDom)
    (delta : ℝ) (fresh anchors : List Plane) :
    ∃ name : Piece → InitialCell,
      InjOn name E(squareMesh delta fresh anchors) ∧
      ∀ e ∈ E(squareMesh delta fresh anchors), name e ∉ P.str.cells :=
  exists_squareMesh_edgeRelabeling_avoiding InitialCell delta fresh anchors
    P.str.cells P.str.finite_cells

/-- **Finite transfer, direction (b), over the concrete initial naming type.**  Once the stage
constructor supplies the relabelled square mesh as a target extension, the reverse transfer is
available directly: boundary anchoring, boundary-edge uniqueness, and the initial outer cycle are
all discharged here. -/
theorem finite_transfer_toward_source_initial_relabelledSquareMesh
    {srcOuter srcDom tgtDom : Set Plane}
    (P : GeneratedPair initialStructure srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (delta : ℝ) (name : Piece → InitialCell)
    (hname : InjOn name E(squareMesh delta fresh anchors))
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      ((squareMesh delta fresh anchors).relabelEdges name hname)
      ((squareMesh delta fresh anchors).relabelDrawing name segmentDrawing)) :
    ∃ (T : GeneratedPair initialStructure srcOuter srcDom modelCurve tgtDom)
        (par : InitialCell → InitialCell),
      IsTargetTransferOf T P
        ((squareMesh delta fresh anchors).relabelEdges name hname)
        ((squareMesh delta fresh anchors).relabelDrawing name segmentDrawing) par :=
  finite_transfer_toward_source_relabelledSquareMesh_of_outerCycle
    P hfresh hstrong delta name hname hH outerEdgesFormCycle_initialStructure

/-- **Reverse transfer specialized to a bare square mesh.**  Fresh abstract edge names are
chosen automatically.  The square-mesh theorems discharge finiteness, drawing, 2-connectivity,
domain containment, boundary-edge geometry, and connectedness off the model curve.  The three
remaining hypotheses assert that this particular mesh subdivides the current target skeleton;
they need not hold for an arbitrary current polygonal skeleton, whose stage construction uses
the combined overlay in `Schoenflies.TargetOverlay`. -/
theorem exists_finite_transfer_toward_source_initial_squareMesh
    {srcOuter srcDom : Set Plane}
    (P : GeneratedPair initialStructure srcOuter srcDom modelCurve
      (Plane.closedSquare 0 1))
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    {delta : ℝ} (hdense : FreshDense fresh delta) (hdelta : delta < 4)
    (hvertices : V(P.tgt.graph) ⊆ V(squareMesh delta fresh anchors))
    (hskeleton : P.tgt.skeletonSet ⊆
      Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing)
    (hedge : ∀ ⦃e : InitialCell⦄, e ∈ E(P.str.skel) → ∀ ⦃f : Piece⦄,
      f ∈ E(squareMesh delta fresh anchors) →
      (edgeArc segmentDrawing f ∩
        (P.tgt.cell e \ V(squareMesh delta fresh anchors))).Nonempty →
      edgeArc segmentDrawing f ⊆ edgeArc P.tgt.drawing e) :
    ∃ (name : Piece → InitialCell)
        (hname : InjOn name E(squareMesh delta fresh anchors))
        (T : GeneratedPair initialStructure srcOuter srcDom modelCurve
          (Plane.closedSquare 0 1)) (par : InitialCell → InitialCell),
      IsTargetTransferOf T P
        ((squareMesh delta fresh anchors).relabelEdges name hname)
        ((squareMesh delta fresh anchors).relabelDrawing name segmentDrawing) par := by
  obtain ⟨name, hname, -⟩ :=
    exists_initialCell_squareMesh_edgeRelabeling P delta fresh anchors
  have hH := isSourceExtension_relabelledSquareMesh_closedSquare
    P hfresh hdense hdelta name hname hvertices hskeleton hedge
  obtain ⟨T, par, hT⟩ := finite_transfer_toward_source_initial_relabelledSquareMesh
    P hfresh hstrong delta name hname hH
  exact ⟨name, hname, T, par, hT⟩

end Schoenflies
