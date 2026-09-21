/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableCollarExistenceAudit
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarGenericity
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarMiddlePrismEndpoints
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionIter

/-!
# Relative subdivision cobordisms for stable endpoint counts

The relative stable-collar construction allows the lower and upper horizontal boundaries to use
independently chosen barycentric-subdivision levels. It is represented by a relative finite-chain
cobordism.  For a cycle `c`, the difference of the two accumulated barycentric-subdivision
homotopies has boundary

```
sd^N₀(c) - sd^N₁(c).
```

Thus the two horizontal chains retain their independently chosen levels.  The module also defines
a proof-carrying relative stable-collar certificate: a linear positive-ray boundary functional
which vanishes on the collar boundary and evaluates to the two supplied stable counts on the two
horizontal chains.  Finite Stokes then proves equality of the endpoint counts without assuming
that the endpoint levels coincide.

The geometric construction realizes the finite
support of the relative chain by compatible prime-equivariant affine cells, freeze the two
horizontal parameter subsets, and use strong general position only on movable interior and side
cells.  The fixed horizontal boundaries require only the `PositiveRaySkeletonFree` property
already carried by `StableRegularApproximation`.
-/

namespace NRR

open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits
open FoxNeuwirthOrderComplex
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableCollarRelativeSubdivision

open EquivariantCoordinateHomotopy
open RefinedAffineMap

variable {p : Nat}

/-- The accumulated barycentric-subdivision homotopy has boundary `c - sd^N(c)` on a cycle. -/
theorem iterHomotopy_boundary_of_cycle
    (R : Type) [CommRing R] (X : TopCat.{0})
    (N n : Nat) (c : singularChainGroup R X n)
    (hc : match n with
      | 0 => True
      | m + 1 => (singularBoundary R X m).hom c = 0) :
    (singularBoundary R X n).hom
        (barycentricSubdivisionIterHomotopyLinearMap R X N n c) =
      c - barycentricSubdivisionIterLinearMap R X N n c := by
  have h := barycentricSubdivisionIter_boundary_formula R X N n c
  have hboundary :
      barycentricSubdivisionIterHomotopyBoundaryTerm R X N n c = 0 := by
    cases n with
    | zero =>
        simp [barycentricSubdivisionIterHomotopyBoundaryTerm_zero]
    | succ m =>
        simp only [barycentricSubdivisionIterHomotopyBoundaryTerm_succ]
        rw [hc, map_zero]
  rw [hboundary, add_zero] at h
  exact h.symm

/-- Relative subdivision collar between two independently chosen subdivision levels.  Its order is
chosen so that the boundary is `sd^N₀(c) - sd^N₁(c)`. -/
noncomputable def relativeSubdivisionChain
    (R : Type) [CommRing R] (X : TopCat.{0})
    (N₀ N₁ n : Nat) (c : singularChainGroup R X n) :
    singularChainGroup R X (n + 1) :=
  barycentricSubdivisionIterHomotopyLinearMap R X N₁ n c -
    barycentricSubdivisionIterHomotopyLinearMap R X N₀ n c

/-- Boundary formula for the relative subdivision collar.  Neither horizontal chain is replaced by
an additional common refinement. -/
theorem relativeSubdivisionChain_boundary
    (R : Type) [CommRing R] (X : TopCat.{0})
    (N₀ N₁ n : Nat) (c : singularChainGroup R X n)
    (hc : match n with
      | 0 => True
      | m + 1 => (singularBoundary R X m).hom c = 0) :
    (singularBoundary R X n).hom
        (relativeSubdivisionChain R X N₀ N₁ n c) =
      barycentricSubdivisionIterLinearMap R X N₀ n c -
        barycentricSubdivisionIterLinearMap R X N₁ n c := by
  rw [relativeSubdivisionChain, map_sub,
    iterHomotopy_boundary_of_cycle R X N₁ n c hc,
    iterHomotopy_boundary_of_cycle R X N₀ n c hc]
  abel

/-- Proof-carrying relative boundary chain.  This is the algebraic domain required by a stable
collar whose endpoint triangulations may have distinct levels. -/
structure RelativeSubdivisionBoundary
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : Nat) where
  baseCycle : singularChainGroup R X n
  baseCycle_closed : match n with
    | 0 => True
    | m + 1 => (singularBoundary R X m).hom baseCycle = 0
  lowerLevel : Nat
  upperLevel : Nat
  collarChain : singularChainGroup R X (n + 1) :=
    relativeSubdivisionChain R X lowerLevel upperLevel n baseCycle
  collar_boundary :
    (singularBoundary R X n).hom collarChain =
      barycentricSubdivisionIterLinearMap R X lowerLevel n baseCycle -
        barycentricSubdivisionIterLinearMap R X upperLevel n baseCycle := by
    simpa using relativeSubdivisionChain_boundary R X lowerLevel upperLevel n
      baseCycle baseCycle_closed

/-- Canonical relative boundary object associated with a cycle and two subdivision levels. -/
noncomputable def RelativeSubdivisionBoundary.ofCycle
    (R : Type) [CommRing R] (X : TopCat.{0})
    (n : Nat) (c : singularChainGroup R X n)
    (hc : match n with
      | 0 => True
      | m + 1 => (singularBoundary R X m).hom c = 0)
    (N₀ N₁ : Nat) : RelativeSubdivisionBoundary R X n where
  baseCycle := c
  baseCycle_closed := hc
  lowerLevel := N₀
  upperLevel := N₁
  collarChain := relativeSubdivisionChain R X N₀ N₁ n c
  collar_boundary := relativeSubdivisionChain_boundary R X N₀ N₁ n c hc

namespace RelativeSubdivisionBoundary

variable {R : Type} [CommRing R] {X : TopCat.{0}} {n : Nat}

/-- Lower horizontal chain of a relative subdivision boundary. -/
noncomputable def lowerChain (B : RelativeSubdivisionBoundary R X n) :
    singularChainGroup R X n :=
  barycentricSubdivisionIterLinearMap R X B.lowerLevel n B.baseCycle

/-- Upper horizontal chain of a relative subdivision boundary. -/
noncomputable def upperChain (B : RelativeSubdivisionBoundary R X n) :
    singularChainGroup R X n :=
  barycentricSubdivisionIterLinearMap R X B.upperLevel n B.baseCycle

/-- The collar boundary is lower minus upper. -/
theorem collar_boundary_eq_lower_sub_upper
    (B : RelativeSubdivisionBoundary R X n) :
    (singularBoundary R X n).hom B.collarChain = B.lowerChain - B.upperChain := by
  simpa [lowerChain, upperChain] using B.collar_boundary

end RelativeSubdivisionBoundary

/-- A linear boundary functional which vanishes on the boundary of a relative collar.  In the
geometric application this functional is obtained by summing the local positive-ray facet indices.
Interior and side general position are used to prove `collarBoundaryWeightZero`; no stronger
transversality is required on the two fixed horizontal chains. -/
structure RelativeBoundaryFunctional
    {R : Type} [CommRing R] {X : TopCat.{0}} {n : Nat}
    (B : RelativeSubdivisionBoundary R X n) where
  weight : singularChainGroup R X n →ₗ[R] R
  collarBoundaryWeightZero :
    weight ((singularBoundary R X n).hom B.collarChain) = 0

namespace RelativeBoundaryFunctional

variable {R : Type} [CommRing R] {X : TopCat.{0}} {n : Nat}
variable {B : RelativeSubdivisionBoundary R X n}

/-- Relative finite Stokes: a boundary functional vanishing on the collar boundary takes the same
value on the independently subdivided lower and upper chains. -/
theorem lower_eq_upper (W : RelativeBoundaryFunctional B) :
    W.weight B.lowerChain = W.weight B.upperChain := by
  have h := W.collarBoundaryWeightZero
  rw [B.collar_boundary_eq_lower_sub_upper] at h
  have hsub : W.weight B.lowerChain - W.weight B.upperChain = 0 := by
    simpa using h
  exact sub_eq_zero.mp hsub

end RelativeBoundaryFunctional

/-- Finite-chain replacement for the old common-level `StableCollar`.  The two endpoint levels are
independent.  The structure contains no endpoint count equality field: equality follows from the
relative boundary formula and the vanishing boundary functional.

A geometric constructor must realize `boundary.collarChain` by compatible affine cells.  The
supplied stable approximations already provide the only fixed-boundary condition needed here,
namely positive-ray skeleton transversality. -/
structure RelativeStableCollarCertificate
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (X : TopCat.{0}) (n : Nat) where
  boundary : RelativeSubdivisionBoundary (ZMod p) X n
  lowerLevel_eq : boundary.lowerLevel = A₀.toRegularApproximation.level
  upperLevel_eq : boundary.upperLevel = A₁.toRegularApproximation.level
  functional : RelativeBoundaryFunctional boundary
  lowerWeight_eq : functional.weight boundary.lowerChain = A₀.zeroCount
  upperWeight_eq : functional.weight boundary.upperChain = A₁.zeroCount

namespace RelativeStableCollarCertificate

/-- A relative finite-chain stable collar compares arbitrary stable endpoint levels. -/
theorem zeroCount_eq
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    {X : TopCat.{0}} {n : Nat}
    (C : RelativeStableCollarCertificate hp H A₀ A₁ X n) :
    A₀.zeroCount = A₁.zeroCount := by
  rw [← C.lowerWeight_eq, ← C.upperWeight_eq]
  exact C.functional.lower_eq_upper

end RelativeStableCollarCertificate

/-! ## Geometric relative-collar certificate

The singular-chain certificate above records the algebraic Stokes pattern, but by itself it does
not require its abstract chain or functional to arise from the Fox--Neuwirth collar.  The main
formalization therefore uses the following geometric certificate instead.  Its finite affine
cells have exactly the two prescribed refined endpoint boundaries, and count equality is derived
from the actual local affine boundary theorem and the actual signed facet-incidence formula.
-/

open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open ExplicitAffineRelativeCollar.RelativeGenericity
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap

/-- A genuine boundary-fixed relative affine collar between two supplied stable approximations.
The base assignment is no longer arbitrary: it is the endpoint-adjusted homotopy assignment.  The
certificate chooses only the movable parameter values, so exact agreement with both horizontal
endpoint approximations follows automatically from the parameter construction.  The comparison
itself is proved by finite affine Stokes and is not stored as data. -/
structure ExplicitRelativeStableCollarCertificate
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) where
  commonLevel : Nat
  timeLevel : Nat
  collar : EndpointIdentifiedRelativeAffineCollar hp
    A₀.toRegularApproximation.level A₁.toRegularApproximation.level
    commonLevel timeLevel
  movableAssignment : MovableParameter hp collar.cells → Real
  localPositiveRayStokes :
    collar.toFoxNeuwirthRelativeAffineCollar.LocalPositiveRayStokes hp
      (replaceMovable hp collar.cells
        (endpointAdjustedAssignment hp collar.cells H
          A₀.toRegularApproximation A₁.toRegularApproximation)
        movableAssignment)

namespace ExplicitRelativeStableCollarCertificate

/-- Build a stable-collar certificate from the boundary-restricted polynomial package, horizontal
endpoint safety, and local origin avoidance. -/
noncomputable def ofRelativeGeneric
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (commonLevel timeLevel : Nat)
    (collar : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level A₁.toRegularApproximation.level
      commonLevel timeLevel)
    (move : MovableParameter hp collar.cells → Real)
    (hgeneric : IsRelativeGeneric hp collar.cells
      (endpointAdjustedAssignment hp collar.cells H
        A₀.toRegularApproximation A₁.toRegularApproximation) move)
    (hhorizontal : HorizontalPositiveRayCodimTwoSafe hp collar.cells
      (replaceMovable hp collar.cells
        (endpointAdjustedAssignment hp collar.cells H
          A₀.toRegularApproximation A₁.toRegularApproximation) move))
    (havoid : ∀ q : collar.cells.Cell,
      AvoidsOrigin
        (localVertexMap hp collar.cells
          (replaceMovable hp collar.cells
            (endpointAdjustedAssignment hp collar.cells H
              A₀.toRegularApproximation A₁.toRegularApproximation) move) q)) :
    ExplicitRelativeStableCollarCertificate hp H A₀ A₁ where
  commonLevel := commonLevel
  timeLevel := timeLevel
  collar := collar
  movableAssignment := move
  localPositiveRayStokes :=
    localPositiveRayStokes_of_relativeGeneric hp
      collar.toFoxNeuwirthRelativeAffineCollar
      (endpointAdjustedAssignment hp collar.cells H
        A₀.toRegularApproximation A₁.toRegularApproximation)
      move hgeneric hhorizontal havoid

/-- The actual compatible assignment represented by a geometric stable-collar certificate. -/
noncomputable def assignment
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (C : ExplicitRelativeStableCollarCertificate hp H A₀ A₁) :
    Assignment hp C.collar.cells :=
  replaceMovable hp C.collar.cells
    (endpointAdjustedAssignment hp C.collar.cells H
      A₀.toRegularApproximation A₁.toRegularApproximation)
    C.movableAssignment

/-- The represented assignment fixes both horizontal endpoint approximations automatically. -/
theorem horizontalVertexFixed
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (C : ExplicitRelativeStableCollarCertificate hp H A₀ A₁) :
    HorizontalVertexFixed hp A₀ A₁ C.collar C.assignment := by
  exact horizontalVertexFixed_replaceMovable_endpointAdjustedAssignment hp H A₀ A₁
    C.collar C.movableAssignment

/-- Finite affine Stokes compares the two prescribed stable endpoint counts. -/
theorem zeroCount_eq
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (C : ExplicitRelativeStableCollarCertificate hp H A₀ A₁) :
    A₀.zeroCount = A₁.zeroCount := by
  let B : EndpointBoundaryFixed hp A₀ A₁ C.collar C.assignment :=
    C.horizontalVertexFixed.toEndpointBoundaryFixed hp A₀ A₁ C.collar C.assignment
  rw [← B.lowerHorizontalContribution_eq_zeroCount,
    ← B.upperHorizontalContribution_eq_zeroCount]
  exact FoxNeuwirthRelativeAffineCollar.lowerHorizontalContribution_eq_upperHorizontalContribution_of_localPositiveRayStokes
      hp C.collar.toFoxNeuwirthRelativeAffineCollar C.assignment C.localPositiveRayStokes

end ExplicitRelativeStableCollarCertificate

/-! ## Concrete construction package -/

/-- Geometric data for a stable relative collar.

The base assignment is forced to be the endpoint-adjusted sampling of the supplied homotopy.  The
proof fields record the required geometry: cellwise origin avoidance,
a geometric movable-assignment witness for every nonhorizontal genericity condition, and exact
representation of every purely horizontal codimension-two point on the frozen endpoint skeletons.
Horizontal facet regularity, polynomial nontriviality, finite perturbation, and finite Stokes are
consequences, not additional assumptions. -/
structure RelativeStableCollarConstructionData
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) where
  commonLevel : Nat
  timeLevel : Nat
  collar : EndpointIdentifiedRelativeAffineCollar hp
    A₀.toRegularApproximation.level A₁.toRegularApproximation.level
    commonLevel timeLevel
  baseAvoidsOrigin : ∀ q : collar.cells.Cell,
    AvoidsOrigin
      (localVertexMap hp collar.cells
        (endpointAdjustedAssignment hp collar.cells H
          A₀.toRegularApproximation A₁.toRegularApproximation) q)
  requiredGenericityWitness :
    ∀ i : RelativeGenericityIndex hp collar.cells,
      RequiresMovableGenericityWitness hp collar.cells i →
      ∃ move : MovableParameter hp collar.cells → Real,
        genericityValue hp collar.cells
          (replaceMovable hp collar.cells
            (endpointAdjustedAssignment hp collar.cells H
              A₀.toRegularApproximation A₁.toRegularApproximation) move) i ≠ 0
  horizontalEndpointRepresentation : HorizontalEndpointSkeletonRepresentation hp A₀ A₁ collar
    (endpointAdjustedAssignment hp collar.cells H
      A₀.toRegularApproximation A₁.toRegularApproximation)

namespace RelativeStableCollarConstructionData

/-- A geometric construction package yields a boundary-fixed generic collar certificate.  The
movable perturbation is chosen automatically, retains a positive compactness-derived norm margin, and cannot
change the horizontal positive-ray safety condition. -/
theorem certificate_nonempty
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (D : RelativeStableCollarConstructionData hp H A₀ A₁) :
    Nonempty (ExplicitRelativeStableCollarCertificate hp H A₀ A₁) := by
  let base : Assignment hp D.collar.cells :=
    endpointAdjustedAssignment hp D.collar.cells H
      A₀.toRegularApproximation A₁.toRegularApproximation
  obtain ⟨m, hm, hmargin⟩ :=
    exists_positive_localAffineCoordinateNormMargin hp D.collar.cells base
      (by simpa [base] using D.baseAvoidsOrigin)
  have hwitness : ∀ i : RelativeGenericityIndex hp D.collar.cells,
      ∃ move : MovableParameter hp D.collar.cells → Real,
        genericityValue hp D.collar.cells
          (replaceMovable hp D.collar.cells base move) i ≠ 0 := by
    simpa [base] using all_relativeGenericityWitnesses_of_required
      hp H A₀ A₁ D.collar D.requiredGenericityWitness
  have hpoly : ∀ i : RelativeGenericityIndex hp D.collar.cells,
      restrictedGenericityPolynomial hp D.collar.cells base i ≠ 0 :=
    restrictedGenericityPolynomial_ne_zero_of_witnesses
      hp D.collar.cells base hwitness
  obtain ⟨P⟩ := exists_relativeGeneric_perturbation hp D.collar.cells base
    hpoly hm hmargin
  refine ⟨ExplicitRelativeStableCollarCertificate.ofRelativeGeneric
    H A₀ A₁ D.commonLevel D.timeLevel D.collar P.move
    (by simpa [base] using P.relativeGeneric) ?_
    (by simpa [base] using P.avoidsOrigin)⟩
  apply horizontalPositiveRayCodimTwoSafe_replaceMovable hp D.collar.cells base P.move
  apply horizontalPositiveRayCodimTwoSafe_of_endpointRepresentation hp A₀ A₁ D.collar base
  simpa [base] using D.horizontalEndpointRepresentation

end RelativeStableCollarConstructionData

/-- Existence of the explicit geometric construction package for every stable pair of endpoints. -/
def RelativeStableCollarConstructionTheorem : Prop :=
  ∀ {p : Nat} (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map),
      Nonempty (RelativeStableCollarConstructionData hp H A₀ A₁)

/-- Arbitrary-endpoint existence proposition. A witness contains a finite endpoint-identified affine
collar and movable parameter data whose assignment satisfies the exact cellwise positive-ray
Stokes identity. Horizontal boundary fixing is derived from the certificate. -/
def RelativeStableCollarExistenceTheorem : Prop :=
  ∀ {p : Nat} (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map),
      Nonempty (ExplicitRelativeStableCollarCertificate hp H A₀ A₁)

/-- The concrete geometric construction package implies the stable-collar existence theorem. -/
theorem relativeStableCollarExistence_of_construction
    (HC : RelativeStableCollarConstructionTheorem) :
    RelativeStableCollarExistenceTheorem := by
  intro p hp F₀ F₁ H A₀ A₁
  exact (Classical.choice (HC hp F₀ F₁ H A₀ A₁)).certificate_nonempty

/-- Relative stable-collar existence implies stable homotopy invariance. -/
theorem stableHomotopyInvariance_of_relative_collarExistence
    (HC : RelativeStableCollarExistenceTheorem) :
    StableHomotopyInvarianceTheorem := by
  intro p hp F₀ F₁ H A₀ A₁
  exact (Classical.choice (HC hp F₀ F₁ H A₀ A₁)).zeroCount_eq

end StableCollarRelativeSubdivision
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
