/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableExactRelativeCollarConstructionAffinePullback

/-!
# Stable homotopy invariance from the exact affine-pullback collar

This module is the focused Step 6 adapter.  The exact relative collar certificate constructed from
Step 4 and Route B identifies the stable zero counts of any two endpoint approximations joined by a
zero-free equivariant homotopy.  The pointwise equality is then packaged into the project-level
`StableHomotopyInvarianceTheorem` interface.
-/

@[expose] public section

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableHomotopyInvarianceAffinePullback

open EquivariantCoordinateHomotopy
open RefinedAffineMap
open StableCollarRelativeSubdivisionExact
open StableExactRelativeCollarConstructionAffinePullback

variable {p : Nat}

/-- The exact affine-pullback collar identifies the stable endpoint zero counts. -/
theorem zeroCount_eq
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    A₀.zeroCount = A₁.zeroCount :=
  exactRelativeStableCollarData_affinePullback_zeroCount_eq hp F₀ F₁ H A₀ A₁

/-- Stable zero count is invariant under zero-free equivariant homotopy. -/
theorem stableHomotopyInvariance_affinePullback :
    StableHomotopyInvarianceTheorem := by
  intro p hp F₀ F₁ H A₀ A₁
  exact zeroCount_eq hp F₀ F₁ H A₀ A₁

end StableHomotopyInvarianceAffinePullback
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
