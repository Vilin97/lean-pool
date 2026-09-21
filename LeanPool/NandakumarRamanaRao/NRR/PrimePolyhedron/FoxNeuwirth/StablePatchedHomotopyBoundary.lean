/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableEndpointBridges
/-!
# Patched endpoint homotopy and exact frozen-boundary samples

The endpoint bridges provide genuine zero-free equivariant maps whose refined vertex values are
exactly the two stable regular approximations.  This file concatenates those bridges with the
original zero-free homotopy and defines the corresponding relative-collar vertex assignment.

The assignment samples the patched homotopy at every nonhorizontal vertex and stores the supplied
stable approximation values on the two horizontal layers.  Exact endpoint fixing is therefore
literal.  On every vertex of an identified external endpoint facet, the stored value is also the
actual value of the continuous patched homotopy; this follows from endpoint identification,
prime equivariance, and the refined-vertex interpolation theorem.
-/

namespace NRR

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StablePatchedHomotopyBoundary

open EquivariantCoordinateHomotopy
open RefinedAffineMap
open StableCollarRelativeSubdivisionExact
open StableEndpointBridges
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap

variable {p : Nat}

/-- The continuous zero-free homotopy obtained by adjoining the two endpoint bridges to the
original homotopy. -/
noncomputable def stablePatchedHomotopy
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    ZeroFreeHomotopy hp
      (StableEndpointBridges.endpointInterpolant hp F₀ A₀).map
      (StableEndpointBridges.endpointInterpolant hp F₁ A₁).map :=
  patchedHomotopy
    (StableEndpointBridges.endpointInterpolant hp F₀ A₀)
    H
    (StableEndpointBridges.endpointInterpolant hp F₁ A₁)

/-- At every lower refined endpoint vertex, the patched homotopy starts at exactly the stored
stable approximation sample. -/
theorem stablePatchedHomotopy_zero_refinedVertex
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (q : TopCell hp A₀.toRegularApproximation.level)
    (i : Fin (p - 1 + 1)) :
    (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
        (vertex hp A₀.toRegularApproximation.level q i, ⟨0, by simp⟩) =
      A₀.toRegularApproximation.map
        (vertex hp A₀.toRegularApproximation.level q i) := by
  rw [(stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map_zero]
  exact StableEndpointBridges.endpointInterpolant_refinedVertex hp F₀ A₀ q i

/-- At every upper refined endpoint vertex, the patched homotopy ends at exactly the stored
stable approximation sample. -/
theorem stablePatchedHomotopy_one_refinedVertex
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (q : TopCell hp A₁.toRegularApproximation.level)
    (i : Fin (p - 1 + 1)) :
    (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
        (vertex hp A₁.toRegularApproximation.level q i, ⟨1, by simp⟩) =
      A₁.toRegularApproximation.map
        (vertex hp A₁.toRegularApproximation.level q i) := by
  rw [(stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map_one]
  exact StableEndpointBridges.endpointInterpolant_refinedVertex hp F₁ A₁ q i

/-- Scalar value used by the boundary-compatible sampling assignment.  The horizontal values are
stored literally from the stable approximations; every nonhorizontal value is sampled from the
continuous patched homotopy. -/
noncomputable def patchedBoundarySiteValue
    {N₀ N₁ M L : Nat}
    (hp : Nat.Prime p)
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (s : ScalarSite hp C) : Real :=
  if h₀ : (globalPoint hp C s.1).time.1 = 0 then
    A₀.toRegularApproximation.map (globalPoint hp C s.1).spatial s.2
  else if h₁ : (globalPoint hp C s.1).time.1 = 1 then
    A₁.toRegularApproximation.map (globalPoint hp C s.1).spatial s.2
  else
    (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
      (EquivariantPrismVertexParameters.CylinderPoint.toProd (globalPoint hp C s.1)) s.2

/-- Boundary-compatible patched samples are constant on diagonal prime orbits. -/
theorem patchedBoundarySiteValue_eq_of_orbitRel
    {N₀ N₁ M L : Nat}
    (hp : Nat.Prime p)
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    {a b : ScalarSite hp C}
    (hab : MulAction.orbitRel (PrimeSymmetry p) (ScalarSite hp C) a b) :
    patchedBoundarySiteValue hp C F₀ F₁ H A₀ A₁ a =
      patchedBoundarySiteValue hp C F₀ F₁ H A₀ A₁ b := by
  rw [MulAction.orbitRel_apply] at hab
  rcases hab with ⟨g, hgab⟩
  subst a
  simp only [patchedBoundarySiteValue, Prod.smul_fst, Prod.smul_snd, globalPoint_smul,
    EquivariantPrismVertexParameters.CylinderPoint.smul_time, EquivariantPrismVertexParameters.CylinderPoint.smul_spatial]
  split_ifs
  · have heq := A₀.toRegularApproximation.equivariant g (globalPoint hp C b.1).spatial
    have hj := congrFun heq (g • b.2)
    simpa [PrimeSymmetry.smul_coordinate_apply, PrimeSymmetry.smul_label] using hj
  · have heq := A₁.toRegularApproximation.equivariant g (globalPoint hp C b.1).spatial
    have hj := congrFun heq (g • b.2)
    simpa [PrimeSymmetry.smul_coordinate_apply, PrimeSymmetry.smul_label] using hj
  · have heq := (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).equivariant g
      (globalPoint hp C b.1).spatial (globalPoint hp C b.1).time
    have hj := congrFun heq (g • b.2)
    simpa [EquivariantPrismVertexParameters.CylinderPoint.toProd, PrimeSymmetry.smul_coordinate_apply,
      PrimeSymmetry.smul_label] using hj

/-- The boundary-compatible assignment associated with the patched homotopy. -/
noncomputable def patchedBoundaryAssignment
    {N₀ N₁ M L : Nat}
    (hp : Nat.Prime p)
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) : Assignment hp C :=
  fun q => Quotient.liftOn q (patchedBoundarySiteValue hp C F₀ F₁ H A₀ A₁) (by
    intro a b hab
    exact patchedBoundarySiteValue_eq_of_orbitRel hp C F₀ F₁ H A₀ A₁ hab)

/-- The patched assignment equals the lower stable approximation at every lower horizontal
collar vertex. -/
theorem vectorValue_patchedBoundaryAssignment_lower
    {N₀ N₁ M L : Nat}
    (hp : Nat.Prime p)
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (x : GlobalVertex hp C)
    (hx : (globalPoint hp C x).time.1 = 0) :
    vectorValue hp C (patchedBoundaryAssignment hp C F₀ F₁ H A₀ A₁) x =
      A₀.toRegularApproximation.map (globalPoint hp C x).spatial := by
  funext j
  simp [vectorValue, scalarValue, patchedBoundaryAssignment,
    patchedBoundarySiteValue, hx]

/-- The patched assignment equals the upper stable approximation at every upper horizontal
collar vertex. -/
theorem vectorValue_patchedBoundaryAssignment_upper
    {N₀ N₁ M L : Nat}
    (hp : Nat.Prime p)
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (x : GlobalVertex hp C)
    (hx : (globalPoint hp C x).time.1 = 1) :
    vectorValue hp C (patchedBoundaryAssignment hp C F₀ F₁ H A₀ A₁) x =
      A₁.toRegularApproximation.map (globalPoint hp C x).spatial := by
  have hx₀ : (globalPoint hp C x).time.1 ≠ 0 := by
    rw [hx]
    norm_num
  funext j
  simp [vectorValue, scalarValue, patchedBoundaryAssignment,
    patchedBoundarySiteValue, hx, hx₀]

/-- At every nonhorizontal sampled vertex, the patched assignment is the actual value of the
continuous patched homotopy. -/
theorem vectorValue_patchedBoundaryAssignment_interior
    {N₀ N₁ M L : Nat}
    (hp : Nat.Prime p)
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (x : GlobalVertex hp C)
    (hx₀ : (globalPoint hp C x).time.1 ≠ 0)
    (hx₁ : (globalPoint hp C x).time.1 ≠ 1) :
    vectorValue hp C (patchedBoundaryAssignment hp C F₀ F₁ H A₀ A₁) x =
      (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
        (EquivariantPrismVertexParameters.CylinderPoint.toProd (globalPoint hp C x)) := by
  funext j
  simp [vectorValue, scalarValue, patchedBoundaryAssignment,
    patchedBoundarySiteValue, hx₀, hx₁]

/-- Exact frozen-boundary matching for every horizontal vertex slot of an endpoint-identified
relative collar. -/
theorem horizontalVertexFixed_patchedBoundaryAssignment
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    {M L : Nat}
    (C : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L) :
    HorizontalVertexFixed hp A₀ A₁ C
      (patchedBoundaryAssignment hp C.cells F₀ F₁ H A₀ A₁) := by
  constructor
  · intro s hs
    simpa using vectorValue_patchedBoundaryAssignment_lower
      hp C.cells F₀ F₁ H A₀ A₁ (sampleVertex hp C.cells s) (by simpa using hs)
  · intro s hs
    simpa using vectorValue_patchedBoundaryAssignment_upper
      hp C.cells F₀ F₁ H A₀ A₁ (sampleVertex hp C.cells s) (by simpa using hs)

/-- Replacing only movable parameters preserves the exact patched horizontal boundary values. -/
theorem horizontalVertexFixed_replaceMovable_patchedBoundaryAssignment
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    {M L : Nat}
    (C : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L)
    (move : MovableParameter hp C.cells → Real) :
    HorizontalVertexFixed hp A₀ A₁ C
      (replaceMovable hp C.cells
        (patchedBoundaryAssignment hp C.cells F₀ F₁ H A₀ A₁) move) := by
  constructor
  · intro s hs
    rw [replaceMovable_horizontal_localValue hp C.cells
      (patchedBoundaryAssignment hp C.cells F₀ F₁ H A₀ A₁)
      move s (Or.inl hs)]
    exact (horizontalVertexFixed_patchedBoundaryAssignment
      hp F₀ F₁ H A₀ A₁ C).lowerValue s hs
  · intro s hs
    rw [replaceMovable_horizontal_localValue hp C.cells
      (patchedBoundaryAssignment hp C.cells F₀ F₁ H A₀ A₁)
      move s (Or.inr hs)]
    exact (horizontalVertexFixed_patchedBoundaryAssignment
      hp F₀ F₁ H A₀ A₁ C).upperValue s hs

/-- On every lower external endpoint-facet vertex, the exact stored boundary value is also the
actual value of the continuous patched homotopy. -/
theorem lowerFacetVertex_eq_patchedHomotopySample
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    {M L : Nat}
    (C : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L)
    (q : TopCell hp A₀.toRegularApproximation.level)
    (o : C.cells.FacetOccurrence)
    (ho : C.cells.facetClass o = C.lowerFacet q)
    (i : Fin p) :
    facetValue
        (localVertexMap hp C.cells
          (patchedBoundaryAssignment hp C.cells F₀ F₁ H A₀ A₁) o.1)
        o.2 i =
      (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
        (EquivariantPrismVertexParameters.CylinderPoint.toProd (C.cells.facetSignature o i)) := by
  rcases C.lowerFacetOccurrenceVertex_eq q o ho with ⟨g, hg⟩
  let s : C.cells.VertexSlot := (o.1, o.2.succAbove i)
  have hpoint : C.cells.slotPoint s =
      g • lowerCylinderPoint
        (vertex hp A₀.toRegularApproximation.level q (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
    simpa [s, RelativeAffineCellSystem.facetSignature,
      RelativeAffineCellSystem.slotPoint] using hg i
  change vectorValue hp C.cells
      (patchedBoundaryAssignment hp C.cells F₀ F₁ H A₀ A₁)
      (sampleVertex hp C.cells s) = _
  calc
    vectorValue hp C.cells
        (patchedBoundaryAssignment hp C.cells F₀ F₁ H A₀ A₁)
        (sampleVertex hp C.cells s) =
        A₀.toRegularApproximation.map (C.cells.slotPoint s).spatial :=
      vectorValue_patchedBoundaryAssignment_lower
        hp C.cells F₀ F₁ H A₀ A₁ (sampleVertex hp C.cells s) (by
          rw [globalPoint_sampleVertex, hpoint]
          simp [lowerCylinderPoint])
    _ = g • A₀.toRegularApproximation.map
        (vertex hp A₀.toRegularApproximation.level q (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
      rw [hpoint]
      exact A₀.toRegularApproximation.equivariant g _
    _ = g • (StableEndpointBridges.endpointInterpolant hp F₀ A₀).map.map
        (vertex hp A₀.toRegularApproximation.level q (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
      rw [StableEndpointBridges.endpointInterpolant_refinedVertex hp F₀ A₀ q (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)]
    _ = (StableEndpointBridges.endpointInterpolant hp F₀ A₀).map.map
        (g • vertex hp A₀.toRegularApproximation.level q (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
      rw [(StableEndpointBridges.endpointInterpolant hp F₀ A₀).map.equivariant g]
    _ = (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
        (g • vertex hp A₀.toRegularApproximation.level q (Fin.cast (Nat.sub_add_cancel hp.pos).symm i), ⟨0, by simp⟩) := by
      symm
      exact (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map_zero _
    _ = (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
        (EquivariantPrismVertexParameters.CylinderPoint.toProd (C.cells.facetSignature o i)) := by
      rw [hg i]
      rfl

/-- On every upper external endpoint-facet vertex, the exact stored boundary value is also the
actual value of the continuous patched homotopy. -/
theorem upperFacetVertex_eq_patchedHomotopySample
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    {M L : Nat}
    (C : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L)
    (q : TopCell hp A₁.toRegularApproximation.level)
    (o : C.cells.FacetOccurrence)
    (ho : C.cells.facetClass o = C.upperFacet q)
    (i : Fin p) :
    facetValue
        (localVertexMap hp C.cells
          (patchedBoundaryAssignment hp C.cells F₀ F₁ H A₀ A₁) o.1)
        o.2 i =
      (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
        (EquivariantPrismVertexParameters.CylinderPoint.toProd (C.cells.facetSignature o i)) := by
  rcases C.upperFacetOccurrenceVertex_eq q o ho with ⟨g, hg⟩
  let s : C.cells.VertexSlot := (o.1, o.2.succAbove i)
  have hpoint : C.cells.slotPoint s =
      g • upperCylinderPoint
        (vertex hp A₁.toRegularApproximation.level q (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
    simpa [s, RelativeAffineCellSystem.facetSignature,
      RelativeAffineCellSystem.slotPoint] using hg i
  change vectorValue hp C.cells
      (patchedBoundaryAssignment hp C.cells F₀ F₁ H A₀ A₁)
      (sampleVertex hp C.cells s) = _
  calc
    vectorValue hp C.cells
        (patchedBoundaryAssignment hp C.cells F₀ F₁ H A₀ A₁)
        (sampleVertex hp C.cells s) =
        A₁.toRegularApproximation.map (C.cells.slotPoint s).spatial :=
      vectorValue_patchedBoundaryAssignment_upper
        hp C.cells F₀ F₁ H A₀ A₁ (sampleVertex hp C.cells s) (by
          rw [globalPoint_sampleVertex, hpoint]
          simp [upperCylinderPoint])
    _ = g • A₁.toRegularApproximation.map
        (vertex hp A₁.toRegularApproximation.level q (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
      rw [hpoint]
      exact A₁.toRegularApproximation.equivariant g _
    _ = g • (StableEndpointBridges.endpointInterpolant hp F₁ A₁).map.map
        (vertex hp A₁.toRegularApproximation.level q (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
      rw [StableEndpointBridges.endpointInterpolant_refinedVertex hp F₁ A₁ q (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)]
    _ = (StableEndpointBridges.endpointInterpolant hp F₁ A₁).map.map
        (g • vertex hp A₁.toRegularApproximation.level q (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
      rw [(StableEndpointBridges.endpointInterpolant hp F₁ A₁).map.equivariant g]
    _ = (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
        (g • vertex hp A₁.toRegularApproximation.level q (Fin.cast (Nat.sub_add_cancel hp.pos).symm i), ⟨1, by simp⟩) := by
      symm
      exact (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map_one _
    _ = (stablePatchedHomotopy hp F₀ F₁ H A₀ A₁).map
        (EquivariantPrismVertexParameters.CylinderPoint.toProd (C.cells.facetSignature o i)) := by
      rw [hg i]
      rfl

end StablePatchedHomotopyBoundary
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
