/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionIso
import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionWedge
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedgePresentation

/-!
# Transmission through a presented vertex wedge

This file joins the abstract factor-profile theorem for a vertex wedge to the
presentation interface for an ambient graph.  It is deliberately valid for
an arbitrary ASP permutation and arbitrary factor divisors.
-/

namespace Utilities

namespace VertexWedgePresentation

universe u v w

variable {K : CFGraph.{w}} {G : CFGraph.{u}} {H : CFGraph.{v}}
  {x : G.V} {y : H.V}

/-- Transmission existence on a presented graph is exactly transmission
existence on its concrete vertex-wedge model. -/
@[simp] theorem transmissionExists_iff
    (P : VertexWedgePresentation K G H x y)
    (u : G.V) (v : H.V) (tau : AspPerm) :
    TransmissionExists K (P.leftMap u) (P.rightMap v) tau ↔
      TransmissionExists (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v) tau := by
  simpa only [P.graphIso_apply_left, P.graphIso_apply_wedgeRightVertex] using P.graphIso.transmissionExists_map_iff
    (Sum.inl u) (wedgeRightVertex G H x y v) tau

/-- A pair of factor divisors satisfying the exact wedge rank profile gives
a transmission witness on any graph carrying the corresponding wedge
presentation. -/
theorem transmissionExists_of_profile
    (P : VertexWedgePresentation K G H x y)
    (u : G.V) (v : H.V) (tau : AspPerm)
    (D : CFDiv G) (E : CFDiv H)
    (hProfile : WedgeTransmissionProfile G H x y D E u v tau) :
    TransmissionExists K (P.leftMap u) (P.rightMap v) tau := by
  apply (P.transmissionExists_iff u v tau).mpr
  exact transmissionExists_vertexWedge_of_profile
    G H x y u v tau D E hProfile

/-- Explicit-divisor form of `transmissionExists_of_profile`: the witness on
the ambient graph is the relabeling of the wedge-additive factor divisor. -/
theorem satisfiesTransmission_map_wedgeAddDivisor_of_profile
    (P : VertexWedgePresentation K G H x y)
    (u : G.V) (v : H.V) (tau : AspPerm)
    (D : CFDiv G) (E : CFDiv H)
    (hProfile : WedgeTransmissionProfile G H x y D E u v tau) :
    SatisfiesTransmission K (P.leftMap u) (P.rightMap v) tau
      (P.graphIso.mapDiv (wedgeAddDivisor G H x y D E)) := by
  have hWedge := satisfiesTransmission_wedgeAddDivisor_of_profile
    G H x y D E u v tau hProfile
  simpa only [P.graphIso_apply_left, P.graphIso_apply_wedgeRightVertex] using P.graphIso.satisfiesTransmission_mapDiv
    (Sum.inl u) (wedgeRightVertex G H x y v) tau
      (wedgeAddDivisor G H x y D E) hWedge

end VertexWedgePresentation

end Utilities
