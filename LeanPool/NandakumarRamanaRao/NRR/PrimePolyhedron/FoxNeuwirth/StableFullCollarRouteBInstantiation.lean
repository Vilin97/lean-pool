/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableFullCollarRouteBComplete

/-!
# Concrete Route B assignment on the affine-pullback full collar

This module turns the unconditional existence theorem from
`StableFullCollarRouteBComplete` into a canonical selected perturbation and a
concrete perturbed assignment.  The exported lemmas expose exactly the data
needed by downstream collar/Stokes constructions:

* quantitative closeness to the Step 4 base assignment;
* literal preservation of every frozen parameter, hence both horizontal ends;
* prime equivariance;
* retention of half of the positive origin margin;
* cellwise facet regularity, codimension-two positive-ray avoidance,
  origin avoidance, and full positive-ray general position.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableFullCollarRouteBInstantiation

open EquivariantCoordinateHomotopy
open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open ExplicitAffineRelativeCollar.RelativeGenericity
open ExplicitAffineRelativeCollar.RouteB
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open EquivariantPrismGenericPerturbation
open StableFullCollarOriginMargin
open StableFullCollarRouteB
open StableFullCollarRouteBComplete

variable {p : Nat}

/-- A canonical Route B perturbation selected from the unconditional existence
result for the concrete affine-pullback collar. -/
noncomputable def routeBPerturbation
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (eps : Real) (heps : 0 < eps) :
    SmallGenericPerturbationResult hp
      (baseData hp F0 F1 H A0 A1).collar.cells
      (baseData hp F0 F1 H A0 A1).assignment eps
      (baseData hp F0 F1 H A0 A1).margin :=
  Classical.choice
    (exists_smallGenericPerturbation_affinePullback_unconditional
      hp F0 F1 H A0 A1 heps)

/-- The full collar assignment obtained by replacing exactly the movable
parameters with the selected Route B perturbation. -/
noncomputable def perturbedAssignment
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (eps : Real) (heps : 0 < eps) :
    Assignment hp (baseData hp F0 F1 H A0 A1).collar.cells :=
  assignmentOfMovableParameters hp
    (baseData hp F0 F1 H A0 A1).collar.cells
    (baseData hp F0 F1 H A0 A1).assignment
    (routeBPerturbation hp F0 F1 H A0 A1 eps heps).move

/-- The selected assignment is pointwise `eps`-close to the Step 4 base
assignment. -/
theorem perturbedAssignment_closeToBase
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (eps : Real) (heps : 0 < eps) :
    AssignmentClose
      (perturbedAssignment hp F0 F1 H A0 A1 eps heps)
      (baseData hp F0 F1 H A0 A1).assignment eps :=
  (routeBPerturbation hp F0 F1 H A0 A1 eps heps).closeToBase

/-- Every frozen parameter is preserved literally. -/
theorem perturbedAssignment_fixesFrozen
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (eps : Real) (heps : 0 < eps)
    {s : Parameter hp (baseData hp F0 F1 H A0 A1).collar.cells}
    (hs : IsFrozenParameter hp
      (baseData hp F0 F1 H A0 A1).collar.cells s) :
    perturbedAssignment hp F0 F1 H A0 A1 eps heps s =
      (baseData hp F0 F1 H A0 A1).assignment s :=
  (routeBPerturbation hp F0 F1 H A0 A1 eps heps).fixesFrozen hs

/-- The selected full assignment remains prime-equivariant. -/
theorem perturbedAssignment_equivariant
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (eps : Real) (heps : 0 < eps)
    (g : PrimeSymmetry p)
    (v : GlobalVertex hp (baseData hp F0 F1 H A0 A1).collar.cells) :
    vectorValue hp (baseData hp F0 F1 H A0 A1).collar.cells
        (perturbedAssignment hp F0 F1 H A0 A1 eps heps) (g • v) =
      g • vectorValue hp (baseData hp F0 F1 H A0 A1).collar.cells
        (perturbedAssignment hp F0 F1 H A0 A1 eps heps) v :=
  (routeBPerturbation hp F0 F1 H A0 A1 eps heps).equivariant g v

/-- Half of the Step 2 origin margin is retained by the selected assignment. -/
theorem perturbedAssignment_retainedMargin
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (eps : Real) (heps : 0 < eps) :
    LocalAffineCoordinateNormMargin hp
      (baseData hp F0 F1 H A0 A1).collar.cells
      (perturbedAssignment hp F0 F1 H A0 A1 eps heps)
      ((baseData hp F0 F1 H A0 A1).margin / 2) :=
  (routeBPerturbation hp F0 F1 H A0 A1 eps heps).retainedMargin

/-- Every local cell is facet-regular after perturbation. -/
theorem perturbedAssignment_facetRegular
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (eps : Real) (heps : 0 < eps)
    (q : (baseData hp F0 F1 H A0 A1).collar.cells.Cell) :
    FacetRegular hp
      (localVertexMap hp (baseData hp F0 F1 H A0 A1).collar.cells
        (perturbedAssignment hp F0 F1 H A0 A1 eps heps) q) :=
  (routeBPerturbation hp F0 F1 H A0 A1 eps heps).facetRegular q

/-- Every local cell avoids the codimension-two positive-ray degeneracies. -/
theorem perturbedAssignment_avoidsPositiveRayCodimTwo
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (eps : Real) (heps : 0 < eps)
    (q : (baseData hp F0 F1 H A0 A1).collar.cells.Cell) :
    AvoidsPositiveRayCodimTwo hp
      (localVertexMap hp (baseData hp F0 F1 H A0 A1).collar.cells
        (perturbedAssignment hp F0 F1 H A0 A1 eps heps) q) :=
  (routeBPerturbation hp F0 F1 H A0 A1 eps heps).avoidsPositiveRayCodimTwo q

/-- Every local affine cell remains origin-free. -/
theorem perturbedAssignment_avoidsOrigin
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (eps : Real) (heps : 0 < eps)
    (q : (baseData hp F0 F1 H A0 A1).collar.cells.Cell) :
    AvoidsOrigin
      (localVertexMap hp (baseData hp F0 F1 H A0 A1).collar.cells
        (perturbedAssignment hp F0 F1 H A0 A1 eps heps) q) :=
  (routeBPerturbation hp F0 F1 H A0 A1 eps heps).avoidsOrigin q

/-- The selected assignment is in full positive-ray general position on every
cell of the new full collar. -/
theorem perturbedAssignment_positiveRayGeneralPosition
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (eps : Real) (heps : 0 < eps)
    (q : (baseData hp F0 F1 H A0 A1).collar.cells.Cell) :
    PositiveRayGeneralPosition hp
      (localVertexMap hp (baseData hp F0 F1 H A0 A1).collar.cells
        (perturbedAssignment hp F0 F1 H A0 A1 eps heps) q) :=
  (routeBPerturbation hp F0 F1 H A0 A1 eps heps).positiveRayGeneralPosition q

end StableFullCollarRouteBInstantiation
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
