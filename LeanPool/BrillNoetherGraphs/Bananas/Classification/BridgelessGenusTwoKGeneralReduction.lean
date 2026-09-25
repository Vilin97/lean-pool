/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Classification.BridgelessGenusTwoPseudocore
public import LeanPool.BrillNoetherGraphs.Bananas.Basics.MarkedIso

/-!
# Reducing bridgeless genus-two general transmission to core normal forms

This is the marked, transmission-theoretic form of the pseudocore reduction.
It keeps the remaining work in Theorem 4.13 genuinely algebraic: after this
theorem, there is no bivalent-path suppression or graph-isomorphism transport
left to prove.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- A `k`-general transmission instance on a nontrivial bridgeless genus-two
graph has a theta or a two pointed-rigid-genus-one-factor wedge presentation,
with the ordered marks and the `k`-general-transmission assertion transported
to that presentation. -/
theorem kGeneralTransmission_bridgelessGenusTwo_coreNormalForm
    (G : CFGraph.{0}) (u v : G.V) (k : ℕ)
    (hConnected : _root_.graphConnected G)
    (hCut : TwoEdgeCutCondition G) (hNontrivial : ∃ p q : G.V, p ≠ q)
    (hGenus : genus G = 2)
    (hKGT : KGeneralTransmission (mark G u v) k) :
    (∃ (B : Banana 2) (u' v' : B.graph.V),
      KGeneralTransmission (mark B.graph u' v') k) ∨
    (∃ (base factor : CFGraph.{0}) (attachment : base.V) (root : factor.V)
      (u' v' : (vertexWedge base factor attachment root).V),
      PointedGenusOneRigid base attachment ∧
      PointedGenusOneRigid factor root ∧
      TwoEdgeCutCondition base ∧ TwoEdgeCutCondition factor ∧
      TwoEdgeCutCondition (vertexWedge base factor attachment root) ∧
      KGeneralTransmission
        (mark (vertexWedge base factor attachment root) u' v') k) := by
  cases marked_bridgelessGenusTwo_coreNormalForm G u v hConnected hCut
    hNontrivial hGenus with
  | theta B u' v' equivalence hu hv =>
      left
      refine ⟨B, u', v', ?_⟩
      exact (kGeneralTransmission_map_of_marks_iff equivalence hu hv k).mpr hKGT
  | rigidWedge base factor attachment root u' v' _baseConnected _baseGenus
      baseCut factorCut wedgeCut baseRigid factorRigid equivalence hu hv =>
      right
      refine ⟨base, factor, attachment, root, u', v', baseRigid, factorRigid,
        baseCut, factorCut, wedgeCut, ?_⟩
      exact (kGeneralTransmission_map_of_marks_iff equivalence hu hv k).mpr hKGT

end Bananas
