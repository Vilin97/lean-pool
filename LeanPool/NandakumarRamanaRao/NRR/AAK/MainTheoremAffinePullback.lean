/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.AAK.SimplestRouteS6Refined
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableHomotopyInvarianceAffinePullback

/-!
# Unconditional AAK theorem from the affine-pullback stable collar

The exact relative stable-collar construction supplies the stable homotopy-invariance input required
by the refined S6 route.  This module provides the final adapter and exports the arbitrary-
`n` fair-partition theorem without a theorem-provider argument.
-/

@[expose] public section

namespace NRR
namespace AAK

open Geometry
open FoxNeuwirthOrderComplex
open FoxNeuwirthOrderComplex.EquivariantPrismStableRelativeBoundary

/-- Unconditional arbitrary-`n` Akopyan--Avvakumov--Karasev theorem obtained from the concrete
 affine-pullback collar, Route B perturbation, finite Stokes comparison, and the stable refined S6
 obstruction. -/
theorem avvakumov_akopyan_karasev :
    ∀ (K : Geometry.ConvexBody Plane) (n : Nat), 0 < n →
      ∃ P : ConvexPartition K n, P.IsFair :=
  avvakumov_akopyan_karasev_of_stableRefinedPL
    StableHomotopyInvarianceAffinePullback.stableHomotopyInvariance_affinePullback

end AAK

/-- Canonical top-level public theorem. The conditional theorem-provider form is available as
`avvakumov_akopyan_karasev_of_primeRefinement`. -/
theorem avvakumov_akopyan_karasev :
    ∀ (K : Geometry.ConvexBody Geometry.Plane) (n : Nat), 0 < n →
      ∃ P : ConvexPartition K n, P.IsFair :=
  AAK.avvakumov_akopyan_karasev

/-- Route-specific alias for the unconditional affine-pullback proof. -/
theorem avvakumov_akopyan_karasev_affinePullback :
    ∀ (K : Geometry.ConvexBody Geometry.Plane) (n : Nat), 0 < n →
      ∃ P : ConvexPartition K n, P.IsFair :=
  avvakumov_akopyan_karasev

end NRR
