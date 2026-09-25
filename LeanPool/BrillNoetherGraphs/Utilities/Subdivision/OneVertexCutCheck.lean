/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexCutConnectivity

/-!
# Finite checking for one-vertex cuts

This is a passive boundary for finite cut data emitted by an external search.
Every condition of `OneVertexCut` is replayed by a transparent computation.
-/

namespace Utilities.Certificate

universe u

namespace OneVertexCutCheck

variable {K : CFGraph.{u}}

/-- The proof-free part of a proposed one-vertex cut. -/
structure Data (K : CFGraph.{u}) where
  left : Finset K.V
  right : Finset K.V
  glue : K.V

namespace Data

/-- The exact conditions required by `OneVertexCut`. -/
def Valid (c : Data K) : Prop :=
  c.glue ∈ c.left ∧
  c.glue ∈ c.right ∧
  (∀ z : K.V, z ∈ c.left ∨ z ∈ c.right) ∧
  (∀ z : K.V, z ∈ c.left → z ∈ c.right → z = c.glue) ∧
  ∀ a : K.V, a ∈ c.left → a ≠ c.glue →
    ∀ b : K.V, b ∈ c.right → b ≠ c.glue → numEdges K a b = 0

/-- Executable replay of `Valid`. -/
def check (c : Data K) : Bool :=
  decide (c.glue ∈ c.left) &&
  decide (c.glue ∈ c.right) &&
  (@decide (∀ z : K.V, z ∈ c.left ∨ z ∈ c.right)
    Fintype.decidableForallFintype) &&
  (@decide (∀ z : K.V, z ∈ c.left → z ∈ c.right → z = c.glue)
    Fintype.decidableForallFintype) &&
  (@decide (∀ a : K.V, a ∈ c.left → a ≠ c.glue →
    ∀ b : K.V, b ∈ c.right → b ≠ c.glue → numEdges K a b = 0)
    Fintype.decidableForallFintype)

@[simp] theorem check_eq_true_iff (c : Data K) : c.check = true ↔ c.Valid := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq]
  simp [Valid, and_assoc]

/-- Turn verified finite data into the corresponding mathematical cut. -/
def toOneVertexCut (c : Data K) (h : c.Valid) : OneVertexCut K where
  left := c.left
  right := c.right
  glue := c.glue
  glue_mem_left := h.1
  glue_mem_right := h.2.1
  vertex_cover := h.2.2.1
  only_overlap := h.2.2.2.1
  no_cross := h.2.2.2.2

/-- An accepted finite check constructs the corresponding one-vertex cut. -/
def cutOfCheck (c : Data K) (h : c.check = true) : OneVertexCut K :=
  c.toOneVertexCut (c.check_eq_true_iff.mp h)

/-- The vertex-wedge presentation extracted from accepted cut data. -/
noncomputable def presentationOfCheck (c : Data K) (h : c.check = true) :=
  (c.cutOfCheck h).presentation

/-- The occurrence-safe graph isomorphism extracted from accepted cut data. -/
noncomputable def graphIsoOfCheck (c : Data K) (h : c.check = true) :
    CFGraphIso
      (vertexWedge (c.cutOfCheck h).leftGraph (c.cutOfCheck h).rightGraph
        (c.cutOfCheck h).leftGlue (c.cutOfCheck h).rightGlue) K :=
  (c.cutOfCheck h).graphIso

/-- Connectedness of the ambient graph automatically supplies connectedness
of both checked induced factors. -/
theorem graph_connected_factors_of_check
    (c : Data K) (h : c.check = true) (hK : graphConnected K) :
    graphConnected (c.cutOfCheck h).leftGraph ∧
      graphConnected (c.cutOfCheck h).rightGraph :=
  (c.cutOfCheck h).graph_connected_factors hK

/-- Brill--Noether existence transfers across an accepted cut check. -/
@[simp] theorem BNExists_iff_of_check (c : Data K) (h : c.check = true) (r d : ℤ) :
    BNExists K r d ↔
      BNExists
        (vertexWedge (c.cutOfCheck h).leftGraph (c.cutOfCheck h).rightGraph
          (c.cutOfCheck h).leftGlue (c.cutOfCheck h).rightGlue) r d :=
  (c.cutOfCheck h).BNExists_iff r d

/-- An arbitrary-ASP wedge profile transfers to the ambient graph after an
accepted cut check. -/
theorem transmissionExists_of_profile_of_check
    (c : Data K) (h : c.check = true)
    (u : (c.cutOfCheck h).leftGraph.V) (v : (c.cutOfCheck h).rightGraph.V)
    (tau : AspPerm) (D : CFDiv (c.cutOfCheck h).leftGraph)
    (E : CFDiv (c.cutOfCheck h).rightGraph)
    (hProfile : WedgeTransmissionProfile (c.cutOfCheck h).leftGraph
      (c.cutOfCheck h).rightGraph (c.cutOfCheck h).leftGlue
      (c.cutOfCheck h).rightGlue D E u v tau) :
    TransmissionExists K u.val v.val tau :=
  (c.cutOfCheck h).transmissionExists_of_profile u v tau D E hProfile

/-- A checked cut transports a same-left arbitrary-ASP factor profile to the
ambient graph. -/
theorem transmissionExists_sameLeft_of_profile_of_check
    (c : Data K) (h : c.check = true)
    (p q : (c.cutOfCheck h).leftGraph.V) (tau : AspPerm)
    (D : CFDiv (c.cutOfCheck h).leftGraph)
    (E : CFDiv (c.cutOfCheck h).rightGraph)
    (hProfile : WedgeSameLeftTransmissionProfile
      (c.cutOfCheck h).leftGraph (c.cutOfCheck h).rightGraph
      (c.cutOfCheck h).leftGlue (c.cutOfCheck h).rightGlue
      D E p q tau) :
    TransmissionExists K p.val q.val tau :=
  (c.cutOfCheck h).transmissionExists_sameLeft_of_profile
    p q tau D E hProfile

/-- Explicit ambient divisor supplied by a same-left profile after a checked
cut. -/
theorem satisfiesTransmission_map_wedgeAddDivisor_sameLeft_of_profile_of_check
    (c : Data K) (h : c.check = true)
    (p q : (c.cutOfCheck h).leftGraph.V) (tau : AspPerm)
    (D : CFDiv (c.cutOfCheck h).leftGraph)
    (E : CFDiv (c.cutOfCheck h).rightGraph)
    (hProfile : WedgeSameLeftTransmissionProfile
      (c.cutOfCheck h).leftGraph (c.cutOfCheck h).rightGraph
      (c.cutOfCheck h).leftGlue (c.cutOfCheck h).rightGlue
      D E p q tau) :
    SatisfiesTransmission K p.val q.val tau
      ((c.cutOfCheck h).graphIso.mapDiv
        (wedgeAddDivisor
          (c.cutOfCheck h).leftGraph (c.cutOfCheck h).rightGraph
          (c.cutOfCheck h).leftGlue (c.cutOfCheck h).rightGlue D E)) :=
  (c.cutOfCheck h).satisfiesTransmission_map_wedgeAddDivisor_sameLeft_of_profile
      p q tau D E hProfile

/-- A checked cut transports a same-right arbitrary-ASP factor profile to the
ambient graph. -/
theorem transmissionExists_sameRight_of_profile_of_check
    (c : Data K) (h : c.check = true)
    (p q : (c.cutOfCheck h).rightGraph.V) (tau : AspPerm)
    (D : CFDiv (c.cutOfCheck h).leftGraph)
    (E : CFDiv (c.cutOfCheck h).rightGraph)
    (hProfile : WedgeSameRightTransmissionProfile
      (c.cutOfCheck h).leftGraph (c.cutOfCheck h).rightGraph
      (c.cutOfCheck h).leftGlue (c.cutOfCheck h).rightGlue
      D E p q tau) :
    TransmissionExists K p.val q.val tau :=
  (c.cutOfCheck h).transmissionExists_sameRight_of_profile
    p q tau D E hProfile

/-- Explicit ambient divisor supplied by a same-right profile after a checked
cut. -/
theorem satisfiesTransmission_map_wedgeAddDivisor_sameRight_of_profile_of_check
    (c : Data K) (h : c.check = true)
    (p q : (c.cutOfCheck h).rightGraph.V) (tau : AspPerm)
    (D : CFDiv (c.cutOfCheck h).leftGraph)
    (E : CFDiv (c.cutOfCheck h).rightGraph)
    (hProfile : WedgeSameRightTransmissionProfile
      (c.cutOfCheck h).leftGraph (c.cutOfCheck h).rightGraph
      (c.cutOfCheck h).leftGlue (c.cutOfCheck h).rightGlue
      D E p q tau) :
    SatisfiesTransmission K p.val q.val tau
      ((c.cutOfCheck h).graphIso.mapDiv
        (wedgeAddDivisor
          (c.cutOfCheck h).leftGraph (c.cutOfCheck h).rightGraph
          (c.cutOfCheck h).leftGlue (c.cutOfCheck h).rightGlue D E)) :=
  (c.cutOfCheck h).satisfiesTransmission_map_wedgeAddDivisor_sameRight_of_profile
      p q tau D E hProfile

/-! ## Closed regression -/

private def threeVertexPath : CFGraph where
  V := Fin 3
  edges := {(0, 1), (1, 2)}
  loopless := by decide

private def threeVertexPathData : Data threeVertexPath where
  left := ({0, 1} : Finset (Fin 3))
  right := ({1, 2} : Finset (Fin 3))
  glue := (1 : Fin 3)

private theorem threeVertexPath_check : threeVertexPathData.check = true := by
  decide

end Data

end OneVertexCutCheck

end Utilities.Certificate
