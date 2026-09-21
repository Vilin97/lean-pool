/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.AAK.SimplestRoute
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ChildMapLocalHomotopy
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ChildReferenceHomotopy
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableCollarRelativeSubdivision

/-!
# Stable refined S6 obstruction

This is the S6 endpoint.  Endpoint counts are taken only from
`StableRegularApproximation`s, so a positive-ray intersection cannot be lost on a triangulation
face.  The finite relative-collar theorem supplies stable homotopy invariance.  The positive
reference endpoint is discharged explicitly at level zero by the reference-map skeleton
transversality theorem.
-/

namespace NRR
namespace AAK

open Geometry
open FoxNeuwirthOrderComplex
open FoxNeuwirthOrderComplex.EquivariantCoordinateHomotopy
open FoxNeuwirthOrderComplex.EquivariantPLPositiveRay
open FoxNeuwirthOrderComplex.RefinedAffineMap

variable {p : Nat}

/-- Stable obstruction value of the frozen child map. -/
noncomputable def stableRefinedChildObstructionValue
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (z : BodySpace K A × SignedInterval)
    (hz : z ∈ ((orderComplexModel hp).projectedAllChildrenZeroSet hA phi)ᶜ) : ZMod p :=
  stableObstructionValue hp (childZeroFreeMap hp hA phi z hz)

/-- The stable child obstruction is locally constant on the complement. -/
theorem stableRefinedChildObstructionValue_locally_constant
    {K : Geometry.ConvexBody Plane} {A : Real}
    (HPL : StableHomotopyInvarianceTheorem)
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (z : BodySpace K A × SignedInterval)
    (hz : z ∈ ((orderComplexModel hp).projectedAllChildrenZeroSet hA phi)ᶜ) :
    ∃ (U : Set (BodySpace K A × SignedInterval))
      (hUout : U ⊆ ((orderComplexModel hp).projectedAllChildrenZeroSet hA phi)ᶜ),
      IsOpen U ∧ z ∈ U ∧
        ∀ (w : BodySpace K A × SignedInterval) (hw : w ∈ U),
          stableRefinedChildObstructionValue hp hA phi w (hUout hw) =
            stableRefinedChildObstructionValue hp hA phi z hz := by
  obtain ⟨U, hUout, hUopen, hzU, hhom⟩ :=
    exists_local_zeroFreeHomotopy hp hA phi z hz
  refine ⟨U, hUout, hUopen, hzU, ?_⟩
  intro w hw
  exact stableObstructionValue_homotopy HPL hp
    (Classical.choice (hhom w hw)) |>.symm

/-- The stable obstruction vanishes on the lower endpoint. -/
theorem stableRefinedChildObstructionValue_left_eq_zero
    {K : Geometry.ConvexBody Plane} {A : Real}
    (HPL : StableHomotopyInvarianceTheorem)
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (C : BodySpace K A) :
    stableRefinedChildObstructionValue hp hA phi (C, SignedInterval.left)
      ((orderComplexModel hp).not_mem_projectedAllChildrenZeroSet_left hA phi C) = 0 := by
  rw [show stableRefinedChildObstructionValue hp hA phi (C, SignedInterval.left)
      ((orderComplexModel hp).not_mem_projectedAllChildrenZeroSet_left hA phi C) =
      stableObstructionValue hp (negativeReferenceZeroFreeMap hp) by
    exact stableObstructionValue_homotopy HPL hp
      (childLeftToNegativeReference hp hA phi C)]
  exact negativeReference_stableObstructionValue_eq_zero HPL hp

/-- The stable obstruction is nonzero on the upper endpoint. -/
theorem stableRefinedChildObstructionValue_right_ne_zero
    {K : Geometry.ConvexBody Plane} {A : Real}
    (HPL : StableHomotopyInvarianceTheorem)
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (C : BodySpace K A) :
    stableRefinedChildObstructionValue hp hA phi (C, SignedInterval.right)
      ((orderComplexModel hp).not_mem_projectedAllChildrenZeroSet_right hA phi C) ≠ 0 := by
  rw [show stableRefinedChildObstructionValue hp hA phi (C, SignedInterval.right)
      ((orderComplexModel hp).not_mem_projectedAllChildrenZeroSet_right hA phi C) =
      stableObstructionValue hp (positiveReferenceZeroFreeMap hp) by
    exact stableObstructionValue_homotopy HPL hp
      (childRightToPositiveReference hp hA phi C)]
  exact positiveReference_stableObstructionValue_ne_zero HPL hp

/-- The stable finite-PL theorem produces the exact complement obstruction needed by the simplest
route. -/
noncomputable def stableRefinedComplementObstructionValue
    {K : Geometry.ConvexBody Plane} {A : Real}
    (HPL : StableHomotopyInvarianceTheorem)
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real)))) :
    ComplementObstructionValue
      (BodySpace K A)
      ((orderComplexModel hp).projectedAllChildrenZeroSet hA phi)
      (ZMod p) where
  value := stableRefinedChildObstructionValue hp hA phi
  lowerValue := 0
  locally_constant := stableRefinedChildObstructionValue_locally_constant HPL hp hA phi
  bottom_outside := by
    rintro ⟨C, t⟩ ht
    change t = SignedInterval.left at ht
    subst t
    exact (orderComplexModel hp).not_mem_projectedAllChildrenZeroSet_left hA phi C
  top_outside := by
    rintro ⟨C, t⟩ ht
    change t = SignedInterval.right at ht
    subst t
    exact (orderComplexModel hp).not_mem_projectedAllChildrenZeroSet_right hA phi C
  bottom_value := stableRefinedChildObstructionValue_left_eq_zero HPL hp hA phi
  top_value_ne := stableRefinedChildObstructionValue_right_ne_zero HPL hp hA phi

/-- Stable homotopy invariance implies the simplest-route obstruction statement. -/
theorem stableRefinedPL_implies_simplestRouteObstruction
    (HPL : StableHomotopyInvarianceTheorem) :
    SimplestRouteObstructionTheorem := by
  intro p hp K A hA _ phi
  exact ⟨stableRefinedComplementObstructionValue HPL hp hA phi⟩

/-- Conditional arbitrary-`n` AAK endpoint.  This statement does not assume equality of counts for arbitrary raw regular approximations. -/
theorem avvakumov_akopyan_karasev_of_stableRefinedPL
    (HPL : StableHomotopyInvarianceTheorem) :
    ∀ (K : Geometry.ConvexBody Plane) (n : Nat), 0 < n →
      ∃ P : ConvexPartition K n, P.IsFair :=
  avvakumov_akopyan_karasev_of_simplestRoute
    (stableRefinedPL_implies_simplestRouteObstruction HPL)

/-- Relative stable-collar existence supplies the stable homotopy-invariance input used to prove the arbitrary-`n` AAK endpoint. -/
theorem avvakumov_akopyan_karasev_of_relativeStableCollar
    (HC : EquivariantPrismStableRelativeBoundary.StableCollarRelativeSubdivision.RelativeStableCollarExistenceTheorem) :
    ∀ (K : Geometry.ConvexBody Plane) (n : Nat), 0 < n →
      ∃ P : ConvexPartition K n, P.IsFair :=
  avvakumov_akopyan_karasev_of_stableRefinedPL
    (EquivariantPrismStableRelativeBoundary.StableCollarRelativeSubdivision.stableHomotopyInvariance_of_relative_collarExistence
      HC)

/-- Fully geometric S6 reduction.  It is enough to construct the endpoint-identified collar,
prove that its endpoint-adjusted affine cells avoid the origin, provide nonhorizontal
facet/minor witnesses, and identify purely horizontal codimension-two faces with the supplied
stable endpoint skeletons.  Compactness, horizontal facet regularity, polynomial nontriviality,
relative perturbation, and finite Stokes are then automatic. -/
theorem avvakumov_akopyan_karasev_of_relativeStableCollarConstruction
    (HC : EquivariantPrismStableRelativeBoundary.StableCollarRelativeSubdivision.RelativeStableCollarConstructionTheorem) :
    ∀ (K : Geometry.ConvexBody Plane) (n : Nat), 0 < n →
      ∃ P : ConvexPartition K n, P.IsFair :=
  avvakumov_akopyan_karasev_of_relativeStableCollar
    (EquivariantPrismStableRelativeBoundary.StableCollarRelativeSubdivision.relativeStableCollarExistence_of_construction
      HC)

end AAK
end NRR
