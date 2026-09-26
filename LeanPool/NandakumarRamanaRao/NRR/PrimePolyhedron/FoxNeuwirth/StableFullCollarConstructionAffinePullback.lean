/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EndpointStackIteratedAffinePullback
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableFullCollarRelativeMesh
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarComposeDescribed
/-!
# Concrete fine full-collar construction by affine pullback

This module closes Step 4.  The collar is assembled from three regions:

1. an iterated affine-pullback stack from the lower endpoint level to a common refined level;
2. a sufficiently fine staircase prism sampling the PL-ended compatible chart homotopy; and
3. the reversal of an iterated affine-pullback stack from the upper endpoint level to the same
   common refined level.

All three assignments use the original endpoint PL chart maps as their seam invariants.  The
carrier theorem therefore gives literal equality on both composition seams.  Endpoint stacks avoid
the origin exactly, while the middle prism avoids it by the compactness/oscillation estimate.
The external horizontal values are the supplied stable approximation samples.

The endpoint stacks are produced at the level `A.level + (k + 1)` while the middle prism lives at
`baseLevel A0 A1 + L`.  These two natural numbers are equal but not definitionally equal, so the
stacks are transported with `castEndpointCollar`; `castEndpoint_property` moves every property of
a collar together with its assignment across such a transport.
-/

@[expose] public section

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableFullCollarConstructionAffinePullback

open RefinedAffineMap
open EquivariantCoordinateHomotopy
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open ExplicitAffineRelativeCollarCompose
open ExplicitAffineRelativeCollarReverse
open ExplicitAffineRelativeCollarAssignmentCompose
open ExplicitAffineRelativeCollarAssignmentReverse
open ExplicitAffineRelativeCollarComposeDescribed
open CompatibleRefinedChartHomotopy
open CompatibleRefinedChartHomotopyPrism
open ChartMapCollarRepresentation
open EndpointStackIteratedAffinePullback
open RelativeSubdivisionEndpointCollar
open RelativeCollarMiddlePrismEndpoints
open StableFullCollarOriginMargin
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap

variable {p : Nat}

/-! ### Transport of collar data along equal spatial levels -/

section LevelTransport

variable {hp : Nat.Prime p}

/-- Transport an endpoint-identified collar along equalities of its two endpoint levels. -/
noncomputable def castEndpointCollar
    {N₀ N₀' N₁ N₁' M T : Nat} (h₀ : N₀ = N₀') (h₁ : N₁ = N₁')
    (C : EndpointIdentifiedRelativeAffineCollar hp N₀ N₁ M T) :
    EndpointIdentifiedRelativeAffineCollar hp N₀' N₁' M T := by
  subst h₀
  subst h₁
  exact C

@[simp] theorem castEndpointCollar_rfl
    {N₀ N₁ M T : Nat} (C : EndpointIdentifiedRelativeAffineCollar hp N₀ N₁ M T) :
    castEndpointCollar (rfl : N₀ = N₀) (rfl : N₁ = N₁) C = C := rfl

/-- Transport an assignment along the same equalities of endpoint levels. -/
noncomputable def castEndpointAssignment
    {N₀ N₀' N₁ N₁' M T : Nat} (h₀ : N₀ = N₀') (h₁ : N₁ = N₁')
    (C : EndpointIdentifiedRelativeAffineCollar hp N₀ N₁ M T)
    (a : Assignment hp C.cells) :
    Assignment hp (castEndpointCollar h₀ h₁ C).cells := by
  subst h₀
  subst h₁
  exact a

/-- Every property of a collar together with its assignment survives the level transport. -/
theorem castEndpoint_property
    {N₀ N₀' N₁ N₁' M T : Nat}
    (P : ∀ A B : Nat, (D : EndpointIdentifiedRelativeAffineCollar hp A B M T) →
      Assignment hp D.cells → Prop)
    (h₀ : N₀ = N₀') (h₁ : N₁ = N₁')
    (C : EndpointIdentifiedRelativeAffineCollar hp N₀ N₁ M T)
    (a : Assignment hp C.cells) (h : P N₀ N₁ C a) :
    P N₀' N₁' (castEndpointCollar h₀ h₁ C) (castEndpointAssignment h₀ h₁ C a) := by
  subst h₀
  subst h₁
  exact h

end LevelTransport

/-! ### Prism boundary representation at a transported level -/

/-- Lower prism boundary representation when the homotopy is stated at a level equal, but not
definitionally equal, to the refined endpoint level. -/
theorem lower_boundary_represents_base_cast
    (hp : Nat.Prime p) {N0 d M : Nat} (K : ChartMap hp N0) (h : N0 + d = M)
    {K1 : ChartMap hp M}
    (J : ChartHomotopy hp M (ChartMap.castLevel h (K.refine d)) K1) (L : Nat) :
    RepresentsAtTime
      (RelativeCollarMiddlePrism.cellSystem hp M L) K
      (vectorValue hp (RelativeCollarMiddlePrism.cellSystem hp M L)
        (CompatibleRefinedChartHomotopyPrism.assignment hp J L)) 0 := by
  subst h
  exact lower_boundary_represents_base hp K J L

/-- Upper prism boundary representation when the homotopy is stated at a level equal, but not
definitionally equal, to the refined endpoint level. -/
theorem upper_boundary_represents_base_cast
    (hp : Nat.Prime p) {N0 d M : Nat} (K : ChartMap hp N0) (h : N0 + d = M)
    {K0 : ChartMap hp M}
    (J : ChartHomotopy hp M K0 (ChartMap.castLevel h (K.refine d))) (L : Nat) :
    RepresentsAtTime
      (RelativeCollarMiddlePrism.cellSystem hp M L) K
      (vectorValue hp (RelativeCollarMiddlePrism.cellSystem hp M L)
        (CompatibleRefinedChartHomotopyPrism.assignment hp J L)) 1 := by
  subst h
  exact upper_boundary_represents_base hp K J L

/-! ### The three collar regions -/

/-- Base level at which the PL-ended chart homotopy is defined. -/
def baseLevel
    {hp : Nat.Prime p} {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) : Nat :=
  A0.toRegularApproximation.level + A1.toRegularApproximation.level + 1

/-- Number of one-step layers below a middle prism with additional refinement `L`. -/
def lowerStackIndex
    {hp : Nat.Prime p} {F1 : ZeroFreeMap hp}
    (A1 : StableRegularApproximation hp F1.map) (L : Nat) : Nat :=
  A1.toRegularApproximation.level + L

/-- Number of one-step layers above a middle prism with additional refinement `L`. -/
def upperStackIndex
    {hp : Nat.Prime p} {F0 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (L : Nat) : Nat :=
  A0.toRegularApproximation.level + L

/-- The lower stack reaches exactly the middle prism level. -/
theorem lowerLevel_eq
    {hp : Nat.Prime p} {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) (L : Nat) :
    A0.toRegularApproximation.level + (lowerStackIndex A1 L + 1) = baseLevel A0 A1 + L := by
  simp only [baseLevel, lowerStackIndex]
  omega

/-- The upper stack reaches exactly the middle prism level. -/
theorem upperLevel_eq
    {hp : Nat.Prime p} {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) (L : Nat) :
    A1.toRegularApproximation.level + (upperStackIndex A0 L + 1) = baseLevel A0 A1 + L := by
  simp only [baseLevel, upperStackIndex]
  omega

/-- The PL-ended chart homotopy used in the middle region. -/
noncomputable def middleHomotopy
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) :=
  plEndedHomotopy hp F0 F1 H A0 A1

/-- Chosen fine prism level for the middle region. -/
noncomputable def middleRefinement
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) : Nat :=
  Classical.choose
    (exists_refinement_avoidsOrigin hp (middleHomotopy hp F0 F1 H A0 A1))

/-- Origin avoidance for the chosen middle refinement. -/
theorem middleRefinement_avoidsOrigin
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) :
    ∀ q : SubdivisionPrismCharts.PrismCell hp
      (baseLevel A0 A1) (middleRefinement hp F0 F1 H A0 A1),
      AvoidsOrigin
        (localVertexMap hp
          (RelativeCollarMiddlePrism.cellSystem hp (baseLevel A0 A1)
            (middleRefinement hp F0 F1 H A0 A1))
          (CompatibleRefinedChartHomotopyPrism.assignment hp
            (middleHomotopy hp F0 F1 H A0 A1)
            (middleRefinement hp F0 F1 H A0 A1)) q) := by
  exact Classical.choose_spec
    (exists_refinement_avoidsOrigin hp (middleHomotopy hp F0 F1 H A0 A1))

/-- Lower endpoint stack, transported to the common middle level. -/
noncomputable def lowerCollar
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    EndpointIdentifiedRelativeAffineCollar hp
      A0.toRegularApproximation.level (baseLevel A0 A1 + L)
      (positiveWitness hp A0.toRegularApproximation.level
        (lowerStackIndex A1 L)).commonLevel
      (positiveWitness hp A0.toRegularApproximation.level
        (lowerStackIndex A1 L)).timeLevel :=
  castEndpointCollar rfl (lowerLevel_eq A0 A1 L)
    (positiveWitness hp A0.toRegularApproximation.level
      (lowerStackIndex A1 L)).collar

/-- Upper endpoint stack, reversed and transported from the common middle level. -/
noncomputable def upperCollar
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    EndpointIdentifiedRelativeAffineCollar hp
      (baseLevel A0 A1 + L) A1.toRegularApproximation.level
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).commonLevel
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).timeLevel :=
  castEndpointCollar (upperLevel_eq A0 A1 L) rfl
    (reverseEndpointCollar
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar)

/-- The transported lower stack assignment. -/
noncomputable def lowerAssignment
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    Assignment hp (lowerCollar hp A0 A1 L).cells :=
  castEndpointAssignment rfl (lowerLevel_eq A0 A1 L)
    (positiveWitness hp A0.toRegularApproximation.level
      (lowerStackIndex A1 L)).collar
    (build hp A0.toRegularApproximation (lowerStackIndex A1 L)).assignment

/-- The transported reversed upper stack assignment. -/
noncomputable def upperAssignment
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    Assignment hp (upperCollar hp A0 A1 L).cells :=
  castEndpointAssignment (upperLevel_eq A0 A1 L) rfl
    (reverseEndpointCollar
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar)
    (reverseAssignment
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar.cells
      (build hp A1.toRegularApproximation (upperStackIndex A0 L)).assignment)

/-- Fine common-level middle prism with all seam data, but without the unnecessary standalone
horizontal-facet exhaustiveness requirement. -/
noncomputable def middleCollar
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    EndpointDescribedRelativeAffineCollar hp
      (baseLevel A0 A1 + L) (baseLevel A0 A1 + L)
      (baseLevel A0 A1 + L) L where
  toFoxNeuwirthRelativeAffineCollar :=
    RelativeCollarMiddlePrismBoundary.collar hp (baseLevel A0 A1) L
  lowerFacet := RelativeCollarMiddlePrismEndpoints.lowerFacet hp (baseLevel A0 A1) L
  upperFacet := RelativeCollarMiddlePrismEndpoints.upperFacet hp (baseLevel A0 A1) L
  lowerFacet_isLower :=
    RelativeCollarMiddlePrismEndpoints.lowerFacet_isLower hp (baseLevel A0 A1) L
  upperFacet_isUpper :=
    RelativeCollarMiddlePrismEndpoints.upperFacet_isUpper hp (baseLevel A0 A1) L
  lowerBoundaryPairing_eq :=
    RelativeCollarMiddlePrismEndpoints.lowerBoundaryPairing_eq hp (baseLevel A0 A1) L
  upperBoundaryPairing_eq :=
    RelativeCollarMiddlePrismEndpoints.upperBoundaryPairing_eq hp (baseLevel A0 A1) L
  lowerFacetOccurrenceVertex_eq :=
    RelativeCollarMiddlePrismEndpoints.lowerFacetOccurrenceVertex_eq hp (baseLevel A0 A1) L
  upperFacetOccurrenceVertex_eq :=
    RelativeCollarMiddlePrismEndpoints.upperFacetOccurrenceVertex_eq hp (baseLevel A0 A1) L

/-! ### The assembled three-region collar -/

/-- The middle prism assignment sampled from the PL-ended chart homotopy. -/
noncomputable def middleAssignment
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    Assignment hp (middleCollar hp A0 A1 L).cells :=
  CompatibleRefinedChartHomotopyPrism.assignment hp
    (middleHomotopy hp F0 F1 H A0 A1) L

/-- The lower stack represents the lower original PL chart map. -/
theorem lower_represents
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    Represents (lowerCollar hp A0 A1 L).cells
      (baseOriginalPLMap hp A0.toRegularApproximation)
      (vectorValue hp (lowerCollar hp A0 A1 L).cells (lowerAssignment hp A0 A1 L)) :=
  castEndpoint_property
    (P := fun _ _ D b =>
      Represents D.cells (baseOriginalPLMap hp A0.toRegularApproximation)
        (vectorValue hp D.cells b))
    rfl (lowerLevel_eq A0 A1 L)
    (positiveWitness hp A0.toRegularApproximation.level
      (lowerStackIndex A1 L)).collar
    (build hp A0.toRegularApproximation (lowerStackIndex A1 L)).assignment
    (build hp A0.toRegularApproximation (lowerStackIndex A1 L)).represents

/-- The reversed upper stack represents the upper original PL chart map. -/
theorem upper_represents
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    Represents (upperCollar hp A0 A1 L).cells
      (baseOriginalPLMap hp A1.toRegularApproximation)
      (vectorValue hp (upperCollar hp A0 A1 L).cells (upperAssignment hp A0 A1 L)) :=
  castEndpoint_property
    (P := fun _ _ D b =>
      Represents D.cells (baseOriginalPLMap hp A1.toRegularApproximation)
        (vectorValue hp D.cells b))
    (upperLevel_eq A0 A1 L) rfl
    (reverseEndpointCollar
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar)
    (reverseAssignment
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar.cells
      (build hp A1.toRegularApproximation (upperStackIndex A0 L)).assignment)
    (reverseAssignment_represents
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar.cells
      (baseOriginalPLMap hp A1.toRegularApproximation)
      (build hp A1.toRegularApproximation (upperStackIndex A0 L)).assignment
      (build hp A1.toRegularApproximation (upperStackIndex A0 L)).represents)

/-- At time zero the middle prism represents the lower original PL chart map. -/
theorem middle_represents_lower
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    RepresentsAtTime (middleCollar hp A0 A1 L).cells
      (baseOriginalPLMap hp A0.toRegularApproximation)
      (vectorValue hp (middleCollar hp A0 A1 L).cells
        (middleAssignment hp F0 F1 H A0 A1 L)) 0 :=
  lower_boundary_represents_base_cast hp
    (baseOriginalPLMap hp A0.toRegularApproximation)
    (d := A1.toRegularApproximation.level + 1) rfl
    (middleHomotopy hp F0 F1 H A0 A1) L

/-- At time one the middle prism represents the upper original PL chart map. -/
theorem middle_represents_upper
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    RepresentsAtTime (middleCollar hp A0 A1 L).cells
      (baseOriginalPLMap hp A1.toRegularApproximation)
      (vectorValue hp (middleCollar hp A0 A1 L).cells
        (middleAssignment hp F0 F1 H A0 A1 L)) 1 :=
  upper_boundary_represents_base_cast hp
    (baseOriginalPLMap hp A1.toRegularApproximation)
    (d := A0.toRegularApproximation.level + 1)
    (upperLevel_eq_baseCommonLevel A0 A1)
    (middleHomotopy hp F0 F1 H A0 A1) L

/-- The lower seam of the three-region decomposition. -/
theorem lowerSeam
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    SeamCompatible (lowerCollar hp A0 A1 L).cells (middleCollar hp A0 A1 L).cells
      (vectorValue hp (lowerCollar hp A0 A1 L).cells (lowerAssignment hp A0 A1 L))
      (vectorValue hp (middleCollar hp A0 A1 L).cells
        (middleAssignment hp F0 F1 H A0 A1 L)) :=
  seamCompatible_of_boundary (lowerCollar hp A0 A1 L).cells
    (middleCollar hp A0 A1 L).cells
    (baseOriginalPLMap hp A0.toRegularApproximation)
    (vectorValue hp (lowerCollar hp A0 A1 L).cells (lowerAssignment hp A0 A1 L))
    (vectorValue hp (middleCollar hp A0 A1 L).cells
      (middleAssignment hp F0 F1 H A0 A1 L))
    ((lower_represents hp A0 A1 L).atTime 1)
    (middle_represents_lower hp F0 F1 H A0 A1 L)

/-- The lower stack composed with the middle prism. -/
noncomputable def lowerMiddleCollar
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    EndpointDescribedRelativeAffineCollar hp
      A0.toRegularApproximation.level (baseLevel A0 A1 + L)
      (max
        (positiveWitness hp A0.toRegularApproximation.level
          (lowerStackIndex A1 L)).commonLevel
        (baseLevel A0 A1 + L))
      ((positiveWitness hp A0.toRegularApproximation.level
        (lowerStackIndex A1 L)).timeLevel + L + 1) :=
  describedCollar
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified (lowerCollar hp A0 A1 L))
    (middleCollar hp A0 A1 L)

/-- The assignment of the lower two regions. -/
noncomputable def lowerMiddleAssignment
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    Assignment hp (lowerMiddleCollar hp A0 A1 L).cells :=
  combinedAssignment (lowerCollar hp A0 A1 L).cells (middleCollar hp A0 A1 L).cells
    (lowerAssignment hp A0 A1 L) (middleAssignment hp F0 F1 H A0 A1 L)
    (lowerSeam hp F0 F1 H A0 A1 L)

/-- The upper seam of the three-region decomposition. -/
theorem upperSeam
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    SeamCompatible (lowerMiddleCollar hp A0 A1 L).cells (upperCollar hp A0 A1 L).cells
      (vectorValue hp (lowerMiddleCollar hp A0 A1 L).cells
        (lowerMiddleAssignment hp F0 F1 H A0 A1 L))
      (vectorValue hp (upperCollar hp A0 A1 L).cells (upperAssignment hp A0 A1 L)) :=
  seamCompatible_of_boundary (lowerMiddleCollar hp A0 A1 L).cells
    (upperCollar hp A0 A1 L).cells
    (baseOriginalPLMap hp A1.toRegularApproximation)
    (vectorValue hp (lowerMiddleCollar hp A0 A1 L).cells
      (lowerMiddleAssignment hp F0 F1 H A0 A1 L))
    (vectorValue hp (upperCollar hp A0 A1 L).cells (upperAssignment hp A0 A1 L))
    (combinedAssignment_upper_represents_right (lowerCollar hp A0 A1 L).cells
      (middleCollar hp A0 A1 L).cells
      (baseOriginalPLMap hp A1.toRegularApproximation)
      (lowerAssignment hp A0 A1 L) (middleAssignment hp F0 F1 H A0 A1 L)
      (lowerSeam hp F0 F1 H A0 A1 L)
      (middle_represents_upper hp F0 F1 H A0 A1 L))
    ((upper_represents hp A0 A1 L).atTime 0)

/-- External lower facets of the composed lower region are exhaustive. -/
theorem lowerMiddle_lowerFacet_exhaustive
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    ∀ s, (lowerMiddleCollar hp A0 A1 L).cells.IsLowerFacet s →
      ∃ q, (lowerMiddleCollar hp A0 A1 L).lowerFacet q = s :=
  lowerFacet_exhaustive_of_left
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified (lowerCollar hp A0 A1 L))
    (middleCollar hp A0 A1 L) (lowerCollar hp A0 A1 L).lowerFacet_exhaustive

/-- External upper facets of the upper region are exhaustive. -/
theorem upperDescribed_upperFacet_exhaustive
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    ∀ s, (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified
        (upperCollar hp A0 A1 L)).cells.IsUpperFacet s →
      ∃ q, (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified
        (upperCollar hp A0 A1 L)).upperFacet q = s :=
  (upperCollar hp A0 A1 L).upperFacet_exhaustive

/-- The complete three-region collar. -/
noncomputable def fullCollar
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    EndpointIdentifiedRelativeAffineCollar hp
      A0.toRegularApproximation.level A1.toRegularApproximation.level
      (max
        (max
          (positiveWitness hp A0.toRegularApproximation.level
            (lowerStackIndex A1 L)).commonLevel
          (baseLevel A0 A1 + L))
        (positiveWitness hp A1.toRegularApproximation.level
          (upperStackIndex A0 L)).commonLevel)
      (((positiveWitness hp A0.toRegularApproximation.level
          (lowerStackIndex A1 L)).timeLevel + L + 1) +
        (positiveWitness hp A1.toRegularApproximation.level
          (upperStackIndex A0 L)).timeLevel + 1) :=
  ExplicitAffineRelativeCollarComposeDescribed.endpointIdentifiedCollar
    (lowerMiddleCollar hp A0 A1 L)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified (upperCollar hp A0 A1 L))
    (lowerMiddle_lowerFacet_exhaustive hp A0 A1 L)
    (upperDescribed_upperFacet_exhaustive hp A0 A1 L)

/-- The complete three-region assignment. -/
noncomputable def fullAssignment
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    Assignment hp (fullCollar hp A0 A1 L).cells :=
  combinedAssignment (lowerMiddleCollar hp A0 A1 L).cells (upperCollar hp A0 A1 L).cells
    (lowerMiddleAssignment hp F0 F1 H A0 A1 L) (upperAssignment hp A0 A1 L)
    (upperSeam hp F0 F1 H A0 A1 L)

/-! ### Origin avoidance and horizontal endpoint values -/

/-- The lower stack avoids the origin cellwise. -/
theorem lower_avoidsOrigin
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    ∀ q : (lowerCollar hp A0 A1 L).cells.Cell,
      AvoidsOrigin
        (localVertexMap hp (lowerCollar hp A0 A1 L).cells
          (lowerAssignment hp A0 A1 L) q) :=
  castEndpoint_property
    (P := fun _ _ D b => ∀ q : D.cells.Cell,
      AvoidsOrigin (localVertexMap hp D.cells b q))
    rfl (lowerLevel_eq A0 A1 L)
    (positiveWitness hp A0.toRegularApproximation.level
      (lowerStackIndex A1 L)).collar
    (build hp A0.toRegularApproximation (lowerStackIndex A1 L)).assignment
    (build hp A0.toRegularApproximation (lowerStackIndex A1 L)).avoidsOrigin

/-- The reversed upper stack avoids the origin cellwise. -/
theorem upper_avoidsOrigin
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    ∀ q : (upperCollar hp A0 A1 L).cells.Cell,
      AvoidsOrigin
        (localVertexMap hp (upperCollar hp A0 A1 L).cells
          (upperAssignment hp A0 A1 L) q) :=
  castEndpoint_property
    (P := fun _ _ D b => ∀ q : D.cells.Cell,
      AvoidsOrigin (localVertexMap hp D.cells b q))
    (upperLevel_eq A0 A1 L) rfl
    (reverseEndpointCollar
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar)
    (reverseAssignment
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar.cells
      (build hp A1.toRegularApproximation (upperStackIndex A0 L)).assignment)
    (reverseAssignment_avoidsOrigin
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar.cells
      (build hp A1.toRegularApproximation (upperStackIndex A0 L)).assignment
      (build hp A1.toRegularApproximation (upperStackIndex A0 L)).avoidsOrigin)

/-- The full collar avoids the origin cellwise. -/
theorem full_avoidsOrigin
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) :
    ∀ q : (fullCollar hp A0 A1 (middleRefinement hp F0 F1 H A0 A1)).cells.Cell,
      AvoidsOrigin
        (localVertexMap hp
          (fullCollar hp A0 A1 (middleRefinement hp F0 F1 H A0 A1)).cells
          (fullAssignment hp F0 F1 H A0 A1
            (middleRefinement hp F0 F1 H A0 A1)) q) :=
  combinedAssignment_avoidsOrigin
    (lowerMiddleCollar hp A0 A1 (middleRefinement hp F0 F1 H A0 A1)).cells
    (upperCollar hp A0 A1 (middleRefinement hp F0 F1 H A0 A1)).cells
    (lowerMiddleAssignment hp F0 F1 H A0 A1 (middleRefinement hp F0 F1 H A0 A1))
    (upperAssignment hp A0 A1 (middleRefinement hp F0 F1 H A0 A1))
    (upperSeam hp F0 F1 H A0 A1 (middleRefinement hp F0 F1 H A0 A1))
    (combinedAssignment_avoidsOrigin
      (lowerCollar hp A0 A1 (middleRefinement hp F0 F1 H A0 A1)).cells
      (middleCollar hp A0 A1 (middleRefinement hp F0 F1 H A0 A1)).cells
      (lowerAssignment hp A0 A1 (middleRefinement hp F0 F1 H A0 A1))
      (middleAssignment hp F0 F1 H A0 A1 (middleRefinement hp F0 F1 H A0 A1))
      (lowerSeam hp F0 F1 H A0 A1 (middleRefinement hp F0 F1 H A0 A1))
      (lower_avoidsOrigin hp A0 A1 (middleRefinement hp F0 F1 H A0 A1))
      (fun q => middleRefinement_avoidsOrigin hp F0 F1 H A0 A1 q))
    (upper_avoidsOrigin hp A0 A1 (middleRefinement hp F0 F1 H A0 A1))

/-- Exact lower endpoint samples on the lower stack. -/
theorem lower_lowerFixed
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    ∀ s : (lowerCollar hp A0 A1 L).cells.VertexSlot,
      ((lowerCollar hp A0 A1 L).cells.slotPoint s).time.1 = 0 →
        vectorValue hp (lowerCollar hp A0 A1 L).cells (lowerAssignment hp A0 A1 L)
            (sampleVertex hp (lowerCollar hp A0 A1 L).cells s) =
          A0.toRegularApproximation.map
            ((lowerCollar hp A0 A1 L).cells.slotPoint s).spatial :=
  castEndpoint_property
    (P := fun _ _ D b => ∀ s : D.cells.VertexSlot,
      (D.cells.slotPoint s).time.1 = 0 →
        vectorValue hp D.cells b (sampleVertex hp D.cells s) =
          A0.toRegularApproximation.map (D.cells.slotPoint s).spatial)
    rfl (lowerLevel_eq A0 A1 L)
    (positiveWitness hp A0.toRegularApproximation.level
      (lowerStackIndex A1 L)).collar
    (build hp A0.toRegularApproximation (lowerStackIndex A1 L)).assignment
    (build hp A0.toRegularApproximation (lowerStackIndex A1 L)).lowerFixed

/-- Exact upper endpoint samples on the reversed upper stack. -/
theorem upper_upperFixed
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    ∀ s : (upperCollar hp A0 A1 L).cells.VertexSlot,
      ((upperCollar hp A0 A1 L).cells.slotPoint s).time.1 = 1 →
        vectorValue hp (upperCollar hp A0 A1 L).cells (upperAssignment hp A0 A1 L)
            (sampleVertex hp (upperCollar hp A0 A1 L).cells s) =
          A1.toRegularApproximation.map
            ((upperCollar hp A0 A1 L).cells.slotPoint s).spatial :=
  castEndpoint_property
    (P := fun _ _ D b => ∀ s : D.cells.VertexSlot,
      (D.cells.slotPoint s).time.1 = 1 →
        vectorValue hp D.cells b (sampleVertex hp D.cells s) =
          A1.toRegularApproximation.map (D.cells.slotPoint s).spatial)
    (upperLevel_eq A0 A1 L) rfl
    (reverseEndpointCollar
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar)
    (reverseAssignment
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar.cells
      (build hp A1.toRegularApproximation (upperStackIndex A0 L)).assignment)
    (reverse_build_upperFixed hp A1.toRegularApproximation
      (upperStackIndex A0 L))

/-- Exact lower endpoint samples on the full collar. -/
theorem full_lowerFixed
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    ∀ s : (fullCollar hp A0 A1 L).cells.VertexSlot,
      ((fullCollar hp A0 A1 L).cells.slotPoint s).time.1 = 0 →
        vectorValue hp (fullCollar hp A0 A1 L).cells (fullAssignment hp F0 F1 H A0 A1 L)
            (sampleVertex hp (fullCollar hp A0 A1 L).cells s) =
          A0.toRegularApproximation.map
            ((fullCollar hp A0 A1 L).cells.slotPoint s).spatial :=
  combinedAssignment_lowerFixed (lowerMiddleCollar hp A0 A1 L).cells
    (upperCollar hp A0 A1 L).cells
    (lowerMiddleAssignment hp F0 F1 H A0 A1 L) (upperAssignment hp A0 A1 L)
    (upperSeam hp F0 F1 H A0 A1 L) A0.toRegularApproximation.map
    (combinedAssignment_lowerFixed (lowerCollar hp A0 A1 L).cells
      (middleCollar hp A0 A1 L).cells
      (lowerAssignment hp A0 A1 L) (middleAssignment hp F0 F1 H A0 A1 L)
      (lowerSeam hp F0 F1 H A0 A1 L) A0.toRegularApproximation.map
      (lower_lowerFixed hp A0 A1 L))

/-- Exact upper endpoint samples on the full collar. -/
theorem full_upperFixed
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    ∀ s : (fullCollar hp A0 A1 L).cells.VertexSlot,
      ((fullCollar hp A0 A1 L).cells.slotPoint s).time.1 = 1 →
        vectorValue hp (fullCollar hp A0 A1 L).cells (fullAssignment hp F0 F1 H A0 A1 L)
            (sampleVertex hp (fullCollar hp A0 A1 L).cells s) =
          A1.toRegularApproximation.map
            ((fullCollar hp A0 A1 L).cells.slotPoint s).spatial :=
  combinedAssignment_upperFixed (lowerMiddleCollar hp A0 A1 L).cells
    (upperCollar hp A0 A1 L).cells
    (lowerMiddleAssignment hp F0 F1 H A0 A1 L) (upperAssignment hp A0 A1 L)
    (upperSeam hp F0 F1 H A0 A1 L) A1.toRegularApproximation.map
    (upper_upperFixed hp A0 A1 L)

/-- Concrete full fine-collar data. -/
noncomputable def fineFullCollarData
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) :
    FineFullCollarData hp H A0 A1 where
  commonLevel :=
    max
      (max
        (positiveWitness hp A0.toRegularApproximation.level
          (lowerStackIndex A1 (middleRefinement hp F0 F1 H A0 A1))).commonLevel
        (baseLevel A0 A1 + middleRefinement hp F0 F1 H A0 A1))
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 (middleRefinement hp F0 F1 H A0 A1))).commonLevel
  timeLevel :=
    ((positiveWitness hp A0.toRegularApproximation.level
        (lowerStackIndex A1 (middleRefinement hp F0 F1 H A0 A1))).timeLevel +
        middleRefinement hp F0 F1 H A0 A1 + 1) +
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 (middleRefinement hp F0 F1 H A0 A1))).timeLevel + 1
  collar := fullCollar hp A0 A1 (middleRefinement hp F0 F1 H A0 A1)
  assignment := fullAssignment hp F0 F1 H A0 A1 (middleRefinement hp F0 F1 H A0 A1)
  horizontalVertexFixed :=
    ⟨full_lowerFixed hp F0 F1 H A0 A1 (middleRefinement hp F0 F1 H A0 A1),
      full_upperFixed hp F0 F1 H A0 A1 (middleRefinement hp F0 F1 H A0 A1)⟩
  baseAvoidsOrigin := full_avoidsOrigin hp F0 F1 H A0 A1

@[simp] theorem fineFullCollarData_collar
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) :
    (fineFullCollarData hp F0 F1 H A0 A1).collar =
      fullCollar hp A0 A1 (middleRefinement hp F0 F1 H A0 A1) := rfl

@[simp] theorem fineFullCollarData_assignment
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) :
    (fineFullCollarData hp F0 F1 H A0 A1).assignment =
      fullAssignment hp F0 F1 H A0 A1 (middleRefinement hp F0 F1 H A0 A1) := rfl

/-- Step 4: the full fine collar exists for every supplied stable endpoint pair and zero-free
homotopy. -/
theorem fineFullCollarConstruction_affinePullback :
    FineFullCollarConstructionTheorem := by
  intro p hp F0 F1 H A0 A1
  exact ⟨fineFullCollarData hp F0 F1 H A0 A1⟩

end StableFullCollarConstructionAffinePullback
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
