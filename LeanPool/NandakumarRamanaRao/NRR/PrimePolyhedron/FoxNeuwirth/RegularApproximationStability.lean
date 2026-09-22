/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantCoordinateHomotopy
/-!
# Stable regular approximations for endpoint cobordism

The raw `RegularApproximation` interface records top-simplex determinant regularity but permits a
positive-ray intersection on a proper face of the chosen refined triangulation.  Since
`RegularApproximation.zeroCount` counts only relative-interior intersections, that datum is not
sufficient for a boundary-relative prism comparison.

This module introduces the transversality condition required by the endpoint-comparison stage.
Existence and comparison are established by the downstream collar modules.
-/

namespace NRR

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace RefinedAffineMap

variable {p : Nat}

/-- The sampled affine map has no positive-ray intersection on the boundary of any refined top
simplex.  Equivalently, every positive deviation-zero barycentric point is in the relative
interior. -/
def PositiveRaySkeletonFree
    (hp : Nat.Prime p) (N : Nat) (F : ContinuousCoordinateMap p) : Prop :=
  ∀ (q : TopCell hp N) (w : StandardSimplex (p - 1)),
    (∀ r : Fin (p - 1),
      value hp N F q w (ReferenceAffineOrbitCount.coordinateLabel hp r) =
        value hp N F q w (ReferenceAffineOrbitCount.lastLabel hp)) →
    0 < coordinateMean p (value hp N F q w) →
    StandardSimplex.IsInterior w

/-- A regular approximation whose positive-ray intersections are transverse to the chosen
triangulation skeleton.  This is the appropriate endpoint object for a boundary-relative prism
cobordism. -/
structure StableRegularApproximation
    (hp : Nat.Prime p) (F : ContinuousCoordinateMap p)
    extends RegularApproximation hp F where
  positiveRaySkeletonFree :
    PositiveRaySkeletonFree hp toRegularApproximation.level toRegularApproximation.map

namespace StableRegularApproximation

/-- The stable count is the existing refined count; stability is supplied by the additional
transversality field, not by changing the numerical definition. -/
noncomputable def zeroCount
    {hp : Nat.Prime p} {F : ContinuousCoordinateMap p}
    (A : StableRegularApproximation hp F) : ZMod p :=
  A.toRegularApproximation.zeroCount

/-- A positive-ray intersection of a stable approximation cannot have a zero barycentric
coordinate. -/
theorem positive_coordinate
    {hp : Nat.Prime p} {F : ContinuousCoordinateMap p}
    (A : StableRegularApproximation hp F)
    (q : TopCell hp A.toRegularApproximation.level)
    (w : StandardSimplex (p - 1))
    (hdev : ∀ r : Fin (p - 1),
      value hp A.toRegularApproximation.level A.toRegularApproximation.map q w
          (ReferenceAffineOrbitCount.coordinateLabel hp r) =
        value hp A.toRegularApproximation.level A.toRegularApproximation.map q w
          (ReferenceAffineOrbitCount.lastLabel hp))
    (hmean : 0 < coordinateMean p
      (value hp A.toRegularApproximation.level A.toRegularApproximation.map q w))
    (i : Fin p) :
    0 < w (Fin.cast (FoxNeuwirthChain.maximalIndex_eq hp).symm i) := by
  exact A.positiveRaySkeletonFree q w hdev hmean
    (Fin.cast (FoxNeuwirthChain.maximalIndex_eq hp).symm i)

end StableRegularApproximation

/-- Finite-PL endpoint comparison proposition.  This proposition requires boundary-transverse endpoint approximations. -/
def StableHomotopyInvarianceTheorem : Prop :=
  ∀ {p : Nat} (hp : Nat.Prime p)
    (F₀ F₁ : EquivariantCoordinateHomotopy.ZeroFreeMap hp)
    (H : EquivariantCoordinateHomotopy.ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map),
      A₀.zeroCount = A₁.zeroCount

end RefinedAffineMap
end FoxNeuwirthOrderComplex
end NRR
