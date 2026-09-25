/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Classification.BridgelessGenusTwoKGeneralReduction
public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaKGeneralClassification
public import LeanPool.BrillNoetherGraphs.Bananas.Wedge.WedgeKGeneralClassification

/-!
# Theorem 4.13, bundled

The structural seam `marked_bridgelessGenusTwo_coreNormalForm`
(`Bananas/BridgelessGenusTwoPseudocore.lean`) reduces any nontrivial
bridgeless genus-two twice-marked graph, up to a certified graph
isomorphism carrying the two marks, to either a `Banana 2` theta
presentation or a vertex wedge of two `PointedGenusOneRigid` factors. The
two branch classifiers `theta_kGeneral_iff_coordinates_nonRecurrent`
(`ThetaKGeneralClassification.lean`) and `kGeneral_iff_wedge_placement`
(`WedgeKGeneralClassification.lean`) then pin down `k`-general
transmission on each normal form exactly.

This file bundles the three into one biconditional: `KGeneralTransmission`
on the original marked graph holds iff *some* certified isomorphism
exhibits it as a theta graph with non-recurrent coordinates in one of the
three admissible families, or as a rigid wedge with an admissible
placement.  The graph isomorphism has to be retained explicitly in the
right-hand side (rather than existentially discarding it, as the raw
`coreNormalForm` seam does) so that the statement is actually about
`(G, u, v)` and not vacuously true of every graph.  Transport of
`KGeneralTransmission`, `IsTorsionOrder`, and `TwoEdgeCutCondition` along a
`CFGraphIso` is already available
(`kGeneralTransmission_map_of_marks_iff`, `isTorsionOrder_map_of_marks_iff`
in `Bananas/MarkedIso.lean`; `twoEdgeCutCondition_map_iff` in
`Bananas/GraphIsoCuts.lean`), so no new transport lemma is needed here.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- **Theorem 4.13** (`thm:g2general`), bundled single-theorem form.

The right-hand side packages the paper's three cases (theta with
non-recurrent coordinates in one of three families; vertex gluing of two
equal-torsion-order cycles; vertex gluing of a length-two cycle at both its
vertices) as an isomorphism-transported disjunction between the theta and
wedge normal forms. -/
def BridgelessGenusTwoKGeneralCharacterization
    (G : CFGraph.{0}) (u v : G.V) (k : ℕ) : Prop :=
  (∃ (B : Banana 2) (φ : CFGraphIso G B.graph)
      (alpha beta : Fin 3) (i : B.PathPosition alpha) (j : B.PathPosition beta),
      φ.vertexEquiv u = strandVertex B alpha i ∧
      φ.vertexEquiv v = strandVertex B beta j ∧
      ThetaKGeneralCoordinates (k := k) B alpha beta i j) ∨
  (∃ (base factor : CFGraph.{0}) (attachment : base.V) (root : factor.V)
      (φ : CFGraphIso G (vertexWedge base factor attachment root)),
      PointedGenusOneRigid base attachment ∧
      PointedGenusOneRigid factor root ∧
      TwoEdgeCutCondition base ∧ TwoEdgeCutCondition factor ∧
      TwoEdgeCutCondition (vertexWedge base factor attachment root) ∧
      WedgeKGeneralPlacement base factor attachment root
        (φ.vertexEquiv u) (φ.vertexEquiv v) k)

/-- **Theorem 4.13** (`thm:g2general`), bundled. Section 4.

For a connected bridgeless twice-marked genus-two graph with distinct
marks and torsion order `k`, `k`-general transmission is equivalent to the
paper's structural characterization. -/
theorem kGeneralTransmission_bridgelessGenusTwo_iff
    (G : CFGraph.{0}) (u v : G.V) (k : ℕ)
    (hConnected : _root_.graphConnected G) (hCut : TwoEdgeCutCondition G)
    (huv : u ≠ v) (hGenus : genus G = 2)
    (hTO : IsTorsionOrder (mark G u v) k) :
    KGeneralTransmission (mark G u v) k ↔
      BridgelessGenusTwoKGeneralCharacterization G u v k := by
  constructor
  · intro hKGT
    cases marked_bridgelessGenusTwo_coreNormalForm G u v hConnected hCut
        ⟨u, v, huv⟩ hGenus with
    | theta B u' v' φ hu hv =>
        have hKGT' : KGeneralTransmission (mark B.graph u' v') k :=
          (kGeneralTransmission_map_of_marks_iff φ hu hv k).mpr hKGT
        have hTO' : IsTorsionOrder (mark B.graph u' v') k :=
          (isTorsionOrder_map_of_marks_iff φ hu hv k).mpr hTO
        obtain ⟨alpha, i, hi⟩ := strandVertex_surjective B u'
        obtain ⟨beta, j, hj⟩ := strandVertex_surjective B v'
        rw [← hi] at hKGT' hTO'
        rw [← hj] at hKGT' hTO'
        have hcoord := (theta_kGeneral_iff_coordinates_nonRecurrent B alpha beta i j
          hTO').mp hKGT'
        exact Or.inl ⟨B, φ, alpha, beta, i, j, hu.trans hi.symm, hv.trans hj.symm, hcoord⟩
    | rigidWedge base factor attachment root u' v' _hBaseConnected _hBaseGenus
        hBaseCut hFactorCut hWedgeCut hBaseRigid hFactorRigid φ hu hv =>
        have hKGT' : KGeneralTransmission
            (mark (vertexWedge base factor attachment root) u' v') k :=
          (kGeneralTransmission_map_of_marks_iff φ hu hv k).mpr hKGT
        have huv' : u' ≠ v' := by
          rw [← hu, ← hv]
          exact fun h => huv (φ.vertexEquiv.injective h)
        have hplace := wedge_kGeneral_placement base factor attachment root u' v' k
          hBaseRigid hFactorRigid hBaseCut hFactorCut hWedgeCut huv' hKGT'
        refine Or.inr ⟨base, factor, attachment, root, φ, hBaseRigid, hFactorRigid,
          hBaseCut, hFactorCut, hWedgeCut, ?_⟩
        rw [hu, hv]
        exact hplace
  · rintro (⟨B, φ, alpha, beta, i, j, hu, hv, hcoord⟩ |
      ⟨base, factor, attachment, root, φ, hBaseRigid, hFactorRigid, hBaseCut, hFactorCut,
        _hWedgeCut, hplace⟩)
    · have hTO' : IsTorsionOrder
          (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) k :=
        (isTorsionOrder_map_of_marks_iff φ hu hv k).mpr hTO
      have hKGT' := (theta_kGeneral_iff_coordinates_nonRecurrent B alpha beta i j
        hTO').mpr hcoord
      exact (kGeneralTransmission_map_of_marks_iff φ hu hv k).mp hKGT'
    · have hKGT' : KGeneralTransmission
          (mark (vertexWedge base factor attachment root)
            (φ.vertexEquiv u) (φ.vertexEquiv v)) k :=
        kGeneral_of_wedge_placement base factor attachment root
          (φ.vertexEquiv u) (φ.vertexEquiv v) k hBaseRigid hFactorRigid hBaseCut hFactorCut
          hplace
      exact (kGeneralTransmission_map_of_marks_iff φ rfl rfl k).mp hKGT'

end Bananas
