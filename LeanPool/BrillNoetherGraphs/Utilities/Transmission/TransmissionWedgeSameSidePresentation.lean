/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionIso
public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionWedgeSameSide
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgePresentation

/-!
# Same-side transmission through a presented vertex wedge

This file transports the exact same-left and same-right profiles from the
concrete vertex wedge to any ambient graph equipped with a
`VertexWedgePresentation`.  It supplies both existential interfaces and the
explicit mapped divisors needed when wedge decompositions are used
recursively.
-/

@[expose] public section

namespace Utilities

namespace VertexWedgePresentation

universe u v w

variable {K : CFGraph.{w}} {G : CFGraph.{u}} {H : CFGraph.{v}}
  {x : G.V} {y : H.V}

/-- Same-left transmission existence on a presented graph is exactly
existence on its concrete vertex-wedge model. -/
@[simp] theorem transmissionExists_sameLeft_iff
    (P : VertexWedgePresentation K G H x y)
    (p q : G.V) (tau : AspPerm) :
    TransmissionExists K (P.leftMap p) (P.leftMap q) tau ↔
      TransmissionExists (vertexWedge G H x y) (Sum.inl p) (Sum.inl q) tau := by
  simpa only [P.graphIso_apply_left, P.graphIso_apply_wedgeRightVertex] using
    P.graphIso.transmissionExists_map_iff
    (Sum.inl p) (Sum.inl q) tau

/-- A same-left factor profile gives a transmission witness on any graph
carrying the corresponding wedge presentation. -/
theorem transmissionExists_sameLeft_of_profile
    (P : VertexWedgePresentation K G H x y)
    (p q : G.V) (tau : AspPerm) (D : CFDiv G) (E : CFDiv H)
    (hProfile : WedgeSameLeftTransmissionProfile
      G H x y D E p q tau) :
    TransmissionExists K (P.leftMap p) (P.leftMap q) tau := by
  apply (P.transmissionExists_sameLeft_iff p q tau).mpr
  exact transmissionExists_vertexWedge_sameLeft_of_profile
    G H x y p q tau D E hProfile

/-- Explicit ambient divisor constructed from a same-left factor profile. -/
theorem satisfiesTransmission_map_wedgeAddDivisor_sameLeft_of_profile
    (P : VertexWedgePresentation K G H x y)
    (p q : G.V) (tau : AspPerm) (D : CFDiv G) (E : CFDiv H)
    (hProfile : WedgeSameLeftTransmissionProfile
      G H x y D E p q tau) :
    SatisfiesTransmission K (P.leftMap p) (P.leftMap q) tau
      (P.graphIso.mapDiv (wedgeAddDivisor G H x y D E)) := by
  have hWedge :=
    (satisfiesTransmission_wedgeAddDivisor_sameLeft_iff_profile
      G H x y D E p q tau).mpr hProfile
  simpa only [P.graphIso_apply_left, P.graphIso_apply_wedgeRightVertex] using
    P.graphIso.satisfiesTransmission_mapDiv
    (Sum.inl p) (Sum.inl q) tau (wedgeAddDivisor G H x y D E) hWedge

/-- Same-right transmission existence on a presented graph is exactly
existence on its concrete vertex-wedge model. -/
@[simp] theorem transmissionExists_sameRight_iff
    (P : VertexWedgePresentation K G H x y)
    (p q : H.V) (tau : AspPerm) :
    TransmissionExists K (P.rightMap p) (P.rightMap q) tau ↔
      TransmissionExists (vertexWedge G H x y)
        (wedgeRightVertex G H x y p) (wedgeRightVertex G H x y q) tau := by
  simpa only [P.graphIso_apply_left, P.graphIso_apply_wedgeRightVertex] using
    P.graphIso.transmissionExists_map_iff
    (wedgeRightVertex G H x y p) (wedgeRightVertex G H x y q) tau

/-- A same-right factor profile gives a transmission witness on any graph
carrying the corresponding wedge presentation. -/
theorem transmissionExists_sameRight_of_profile
    (P : VertexWedgePresentation K G H x y)
    (p q : H.V) (tau : AspPerm) (D : CFDiv G) (E : CFDiv H)
    (hProfile : WedgeSameRightTransmissionProfile
      G H x y D E p q tau) :
    TransmissionExists K (P.rightMap p) (P.rightMap q) tau := by
  apply (P.transmissionExists_sameRight_iff p q tau).mpr
  exact transmissionExists_vertexWedge_sameRight_of_profile
    G H x y p q tau D E hProfile

/-- Explicit ambient divisor constructed from a same-right factor profile. -/
theorem satisfiesTransmission_map_wedgeAddDivisor_sameRight_of_profile
    (P : VertexWedgePresentation K G H x y)
    (p q : H.V) (tau : AspPerm) (D : CFDiv G) (E : CFDiv H)
    (hProfile : WedgeSameRightTransmissionProfile
      G H x y D E p q tau) :
    SatisfiesTransmission K (P.rightMap p) (P.rightMap q) tau
      (P.graphIso.mapDiv (wedgeAddDivisor G H x y D E)) := by
  have hWedge :=
    (satisfiesTransmission_wedgeAddDivisor_sameRight_iff_profile
      G H x y D E p q tau).mpr hProfile
  simpa only [P.graphIso_apply_left, P.graphIso_apply_wedgeRightVertex] using
    P.graphIso.satisfiesTransmission_mapDiv
    (wedgeRightVertex G H x y p) (wedgeRightVertex G H x y q) tau
      (wedgeAddDivisor G H x y D E) hWedge

end VertexWedgePresentation

end Utilities
