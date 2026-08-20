/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP1Realization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP2Realization

/-!
# Realization invariance for finite cyclic move closures

This file closes the geometric proof obligations parameterizing `FiniteCyclicMoves`. Signed
presentation isomorphisms, P1 subdivisions, and genuine P2 face subdivisions all preserve the
faithful polygonal quotient. Consequently, clients of directed chains and common-subdivision
certificates do not need to pass the primitive invariance proofs explicitly.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

/-- Every elementary directed subdivision step preserves the faithful polygonal realization. -/
theorem subdivisionStep_preservesPolygonalRealization :
    SubdivisionStep.PreservesPolygonalRealization :=
  SubdivisionStep.preservesPolygonalRealization
    P1Subdivision.preservesPolygonalRealization
    P2Subdivision.preservesPolygonalRealization

/-- A directed chain of signed isomorphisms and P1/P2 subdivisions preserves the faithful
polygonal realization. -/
theorem Subdivides.toPolygonallyEquivalent
    {P Q : FiniteCyclicPresentation} (hPQ : Subdivides P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  hPQ.polygonallyEquivalent
    subdivisionStep_preservesPolygonalRealization validP validQ

/-- A common directed subdivision gives a homeomorphism of the two faithful polygonal
realizations. -/
theorem HasCommonSubdivision.toPolygonallyEquivalent
    {P Q : FiniteCyclicPresentation} (hPQ : HasCommonSubdivision P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  hPQ.polygonallyEquivalent
    subdivisionStep_preservesPolygonalRealization validP validQ

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
