/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarStokes
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismGenericPerturbation
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismSubdivisionMargin
/-!
# Relative genericity for explicit affine collars

This module connects the boundary-restricted polynomial family of
`ExplicitAffineRelativeCollar` to the weaker positive-ray general-position interface used by the
finite Stokes theorem.

All facet determinant polynomials remain in the genericity family.  Codimension-two minors are
required only when the corresponding face is not purely horizontal.  Purely horizontal
codimension-two faces are handled by a separate endpoint-safety condition, which is the condition
to be derived from the two stable endpoint approximations.

The final section packages finite multivariate perturbation on movable parameter orbits and proves
that closeness there gives closeness of the reconstructed full assignment while retaining the
horizontal boundary literally.
-/

namespace NRR

open scoped BigOperators
open FoxNeuwirthOrderComplex
open MvPolynomial

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar
namespace RelativeGenericity

open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open Parameters
open Polynomials
open EquivariantPrismGenericPerturbation

variable {p : Nat}
variable {N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

/-- Simultaneous nonvanishing of the complete boundary-restricted polynomial family. -/
def IsRelativeGeneric
    (base : Assignment hp C) (move : MovableParameter hp C → Real) : Prop :=
  ∀ i : RelativeGenericityIndex hp C,
    MvPolynomial.eval move (restrictedGenericityPolynomial hp C base i) ≠ 0

/-- A single explicit movable assignment at which a restricted genericity value is nonzero proves
that the corresponding restricted polynomial is genuinely nonzero.  This is the useful geometric
form of the nontriviality obligation: collar constructions may provide a local witness rather than
an equality proof in a multivariate polynomial ring. -/
theorem restrictedGenericityPolynomial_ne_zero_of_evaluation
    (base : Assignment hp C) (i : RelativeGenericityIndex hp C)
    (move : MovableParameter hp C → Real)
    (hvalue : genericityValue hp C (replaceMovable hp C base move) i ≠ 0) :
    restrictedGenericityPolynomial hp C base i ≠ 0 := by
  intro hzero
  have heval := congrArg (MvPolynomial.eval move) hzero
  rw [eval_restrictedGenericityPolynomial] at heval
  exact hvalue (by simpa using heval)

/-- Pointwise geometric witnesses imply nontriviality of the complete finite restricted polynomial
family.  Different indices may use different movable assignments. -/
theorem restrictedGenericityPolynomial_ne_zero_of_witnesses
    (base : Assignment hp C)
    (hwitness : ∀ i : RelativeGenericityIndex hp C,
      ∃ move : MovableParameter hp C → Real,
        genericityValue hp C (replaceMovable hp C base move) i ≠ 0) :
    ∀ i : RelativeGenericityIndex hp C,
      restrictedGenericityPolynomial hp C base i ≠ 0 := by
  intro i
  obtain ⟨move, hmove⟩ := hwitness i
  exact restrictedGenericityPolynomial_ne_zero_of_evaluation hp C base i move hmove

/-- Only nonhorizontal local facets and the retained codimension-two minors need a genuinely
movable genericity witness.  Horizontal facet determinants are fixed endpoint determinants. -/
def RequiresMovableGenericityWitness
    (i : RelativeGenericityIndex hp C) : Prop :=
  match i with
  | Sum.inl qk => ¬ C.IsHorizontalFacet (C.facetClass qk)
  | Sum.inr _ => True

/-- Restrict a full assignment to its movable parameter subtype. -/
noncomputable def movableRestriction
    (base : Assignment hp C) : MovableParameter hp C → Real :=
  fun q => base q.1

/-- A horizontal local facet of an endpoint-fixed collar has nonzero determinant because it is
literally one of the two supplied stable endpoint facets. -/
theorem horizontalFacet_genericityValue_ne_zero
    {F₀ F₁ : RefinedAffineMap.ContinuousCoordinateMap p}
    (A₀ : RefinedAffineMap.StableRegularApproximation hp F₀)
    (A₁ : RefinedAffineMap.StableRegularApproximation hp F₁)
    {M L : Nat}
    (D : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L)
    (a : Assignment hp D.cells)
    (B : HorizontalVertexFixed hp A₀ A₁ D a)
    (q : D.cells.Cell) (k : Fin (p + 1))
    (hhorizontal : D.cells.IsHorizontalFacet (D.cells.facetClass (q, k))) :
    genericityValue hp D.cells a (Sum.inl (q, k)) ≠ 0 := by
  change facetDeterminant hp (localVertexMap hp D.cells a q) k ≠ 0
  let E : EndpointBoundaryFixed hp A₀ A₁ D a :=
    B.toEndpointBoundaryFixed hp A₀ A₁ D a
  rcases hhorizontal with hlower | hupper
  · obtain ⟨q₀, hq₀⟩ :=
      D.lowerFacet_exhaustive (D.cells.facetClass (q, k)) hlower
    rcases E.lowerData q₀ (q, k) hq₀.symm with ⟨g, hvertex, haffine⟩
    exact facetDeterminant_ne_zero_of_eq_refined_primeSmul hp
      (localVertexMap hp D.cells a q) k A₀.toRegularApproximation.level
      A₀.toRegularApproximation.map q₀ g hvertex
      (A₀.toRegularApproximation.regular q₀)
  · obtain ⟨q₁, hq₁⟩ :=
      D.upperFacet_exhaustive (D.cells.facetClass (q, k)) hupper
    rcases E.upperData q₁ (q, k) hq₁.symm with ⟨g, hvertex, haffine⟩
    exact facetDeterminant_ne_zero_of_eq_refined_primeSmul hp
      (localVertexMap hp D.cells a q) k A₁.toRegularApproximation.level
      A₁.toRegularApproximation.map q₁ g hvertex
      (A₁.toRegularApproximation.regular q₁)

/-- For the endpoint-adjusted collar assignment, horizontal facet genericity is automatic after
any movable perturbation. -/
theorem horizontalFacet_genericityValue_ne_zero_endpointAdjusted
    {F₀ F₁ : EquivariantCoordinateHomotopy.ZeroFreeMap hp}
    (H : EquivariantCoordinateHomotopy.ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : RefinedAffineMap.StableRegularApproximation hp F₀.map)
    (A₁ : RefinedAffineMap.StableRegularApproximation hp F₁.map)
    {M L : Nat}
    (D : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L)
    (move : MovableParameter hp D.cells → Real)
    (q : D.cells.Cell) (k : Fin (p + 1))
    (hhorizontal : D.cells.IsHorizontalFacet (D.cells.facetClass (q, k))) :
    genericityValue hp D.cells
      (replaceMovable hp D.cells
        (endpointAdjustedAssignment hp D.cells H
          A₀.toRegularApproximation A₁.toRegularApproximation) move)
      (Sum.inl (q, k)) ≠ 0 := by
  apply horizontalFacet_genericityValue_ne_zero hp A₀ A₁ D
  · exact horizontalVertexFixed_replaceMovable_endpointAdjustedAssignment hp H A₀ A₁ D move
  · exact hhorizontal

/-- Geometric witnesses are required only for the nonhorizontal part of the relative genericity
family; stable endpoint regularity supplies all horizontal facet witnesses automatically. -/
theorem all_relativeGenericityWitnesses_of_required
    {F₀ F₁ : EquivariantCoordinateHomotopy.ZeroFreeMap hp}
    (H : EquivariantCoordinateHomotopy.ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : RefinedAffineMap.StableRegularApproximation hp F₀.map)
    (A₁ : RefinedAffineMap.StableRegularApproximation hp F₁.map)
    {M L : Nat}
    (D : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L)
    (hwitness : ∀ i : RelativeGenericityIndex hp D.cells,
      RequiresMovableGenericityWitness hp D.cells i →
      ∃ move : MovableParameter hp D.cells → Real,
        genericityValue hp D.cells
          (replaceMovable hp D.cells
            (endpointAdjustedAssignment hp D.cells H
              A₀.toRegularApproximation A₁.toRegularApproximation) move) i ≠ 0) :
    ∀ i : RelativeGenericityIndex hp D.cells,
      ∃ move : MovableParameter hp D.cells → Real,
        genericityValue hp D.cells
          (replaceMovable hp D.cells
            (endpointAdjustedAssignment hp D.cells H
              A₀.toRegularApproximation A₁.toRegularApproximation) move) i ≠ 0 := by
  intro i
  by_cases hi : RequiresMovableGenericityWitness hp D.cells i
  · exact hwitness i hi
  · cases i with
    | inr qf =>
        exact (hi trivial).elim
    | inl qk =>
        have hhorizontal : D.cells.IsHorizontalFacet
            (D.cells.facetClass qk) := by
          simpa [RequiresMovableGenericityWitness] using
            (Classical.not_not.mp hi)
        let base : Assignment hp D.cells :=
          endpointAdjustedAssignment hp D.cells H
            A₀.toRegularApproximation A₁.toRegularApproximation
        let move : MovableParameter hp D.cells → Real :=
          movableRestriction hp D.cells base
        refine ⟨move, ?_⟩
        exact horizontalFacet_genericityValue_ne_zero_endpointAdjusted
          hp H A₀ A₁ D move qk.1 qk.2 hhorizontal

/-- Relative genericity gives facet regularity on every explicit top cell. -/
theorem facetRegular_of_relativeGeneric
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    (hgeneric : IsRelativeGeneric hp C base move)
    (q : C.Cell) :
    FacetRegular hp (localVertexMap hp C (replaceMovable hp C base move) q) := by
  intro k
  have h := hgeneric (Sum.inl (q, k))
  rw [eval_restrictedGenericityPolynomial] at h
  exact h

/-- Relative genericity makes every non-purely-horizontal codimension-two deviation matrix
nonsingular. -/
theorem codimTwoMinor_ne_zero_of_relativeGeneric
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    (hgeneric : IsRelativeGeneric hp C base move)
    (q : C.Cell) (f : CodimTwoFace p)
    (hf : ¬ IsPurelyHorizontalCodimTwo hp C q f) :
    Matrix.det (codimTwoDeviationMatrix hp C
      (replaceMovable hp C base move) q f) ≠ 0 := by
  let i : MovableCodimTwoIndex hp C := ⟨(q, f), hf⟩
  have h := hgeneric (Sum.inr i)
  rw [eval_restrictedGenericityPolynomial] at h
  exact h

/-- Safety condition left for the frozen endpoint geometry.  It is required only when the ordered
codimension-two face determined by the two vanishing barycentric coordinates is purely horizontal. -/
def HorizontalPositiveRayCodimTwoSafe
    (a : Assignment hp C) : Prop :=
  ∀ (q : C.Cell) (w : StandardSimplex p) (i j : Fin (p + 1)), (hij : i ≠ j) →
    (∀ r : Fin (p - 1),
      deviation hp (affineValue (localVertexMap hp C a q) w) r = 0) →
    0 < mean p (affineValue (localVertexMap hp C a q) w) →
    IsPurelyHorizontalCodimTwo hp C q (i, omittedIndex i j hij) →
    ¬ (w i = 0 ∧ w j = 0)

/-- A purely horizontal codimension-two point is represented on the proper skeleton of one of
the two actual endpoint triangulations, with exactly the same affine coordinate value.  This is the
geometric compatibility condition needed to transfer stable endpoint transversality to an arbitrary
relative collar triangulation. -/
def HorizontalEndpointSkeletonRepresentation
    {F₀ F₁ : RefinedAffineMap.ContinuousCoordinateMap p}
    (A₀ : RefinedAffineMap.StableRegularApproximation hp F₀)
    (A₁ : RefinedAffineMap.StableRegularApproximation hp F₁)
    {M L : Nat}
    (D : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L)
    (a : Assignment hp D.cells) : Prop :=
  ∀ (q : D.cells.Cell) (w : StandardSimplex p) (i j : Fin (p + 1)), (hij : i ≠ j) →
    IsPurelyHorizontalCodimTwo hp D.cells q (i, omittedIndex i j hij) →
    w i = 0 ∧ w j = 0 →
      (∃ (q₀ : RefinedAffineMap.TopCell hp A₀.toRegularApproximation.level)
          (u : StandardSimplex (p - 1)),
        ¬ StandardSimplex.IsInterior u ∧
        affineValue (localVertexMap hp D.cells a q) w =
          RefinedAffineMap.value hp A₀.toRegularApproximation.level
            A₀.toRegularApproximation.map q₀ u) ∨
      (∃ (q₁ : RefinedAffineMap.TopCell hp A₁.toRegularApproximation.level)
          (u : StandardSimplex (p - 1)),
        ¬ StandardSimplex.IsInterior u ∧
        affineValue (localVertexMap hp D.cells a q) w =
          RefinedAffineMap.value hp A₁.toRegularApproximation.level
            A₁.toRegularApproximation.map q₁ u)

/-- Stable endpoint skeleton transversality converts exact horizontal endpoint representation into
the positive-ray safety property required by the relative local Stokes theorem. -/
theorem horizontalPositiveRayCodimTwoSafe_of_endpointRepresentation
    {F₀ F₁ : RefinedAffineMap.ContinuousCoordinateMap p}
    (A₀ : RefinedAffineMap.StableRegularApproximation hp F₀)
    (A₁ : RefinedAffineMap.StableRegularApproximation hp F₁)
    {M L : Nat}
    (D : EndpointIdentifiedRelativeAffineCollar hp
      A₀.toRegularApproximation.level A₁.toRegularApproximation.level M L)
    (a : Assignment hp D.cells)
    (hrepresentation : HorizontalEndpointSkeletonRepresentation hp A₀ A₁ D a) :
    HorizontalPositiveRayCodimTwoSafe hp D.cells a := by
  intro q w i j hij hdev hmean hpure hzeros
  rcases hrepresentation q w i j hij hpure hzeros with
    ⟨q₀, u, huBoundary, hvalue⟩ | ⟨q₁, u, huBoundary, hvalue⟩
  · apply huBoundary
    apply A₀.positiveRaySkeletonFree q₀ u
    · intro r
      have hz := hdev r
      rw [hvalue] at hz
      simpa [deviation, sub_eq_zero] using hz
    · have hm := hmean
      rw [hvalue] at hm
      simpa [mean] using hm
  · apply huBoundary
    apply A₁.positiveRaySkeletonFree q₁ u
    · intro r
      have hz := hdev r
      rw [hvalue] at hz
      simpa [deviation, sub_eq_zero] using hz
    · have hm := hmean
      rw [hvalue] at hm
      simpa [mean] using hm

/-- On a purely horizontal codimension-two face, changing movable parameters does not alter the
represented affine value.  The two omitted barycentric coordinates vanish, while every retained
vertex belongs to a frozen endpoint boundary. -/
theorem affineValue_replaceMovable_eq_of_purelyHorizontalCodimTwo
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    (q : C.Cell) (w : StandardSimplex p) (i j : Fin (p + 1))
    (hij : i ≠ j) (hzeros : w i = 0 ∧ w j = 0)
    (hpure : IsPurelyHorizontalCodimTwo hp C q (i, omittedIndex i j hij)) :
    affineValue (localVertexMap hp C (replaceMovable hp C base move) q) w =
      affineValue (localVertexMap hp C base q) w := by
  funext r
  unfold affineValue
  rw [EquivariantPrismGenericPerturbation.sum_codimTwoVertex hp
      (fun k : Fin (p + 1) =>
        w k * (localVertexMap hp C (replaceMovable hp C base move) q).value k r)
      i j hij (by simp [hzeros.1]) (by simp [hzeros.2])]
  rw [EquivariantPrismGenericPerturbation.sum_codimTwoVertex hp
      (fun k : Fin (p + 1) => w k * (localVertexMap hp C base q).value k r)
      i j hij (by simp [hzeros.1]) (by simp [hzeros.2])]
  apply Finset.sum_congr rfl
  intro c hc
  let k : Fin (p + 1) :=
    EquivariantPrismGenericityPolynomials.codimTwoVertex hp
      (i, omittedIndex i j hij) c
  have hkHorizontal : IsHorizontalPoint (C.slotPoint (q, k)) := by
    rcases hpure with hlower | hupper
    · exact Or.inl (hlower c)
    · exact Or.inr (hupper c)
  have hv := replaceMovable_horizontal_localValue hp C base move (q, k) hkHorizontal
  simpa [k, localVertexMap] using
    congrArg (fun y : Fin p → Real => w k * y r) hv

/-- Horizontal positive-ray safety depends only on frozen endpoint values and is therefore
preserved by every replacement of the movable parameter orbits. -/
theorem horizontalPositiveRayCodimTwoSafe_replaceMovable
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    (hbase : HorizontalPositiveRayCodimTwoSafe hp C base) :
    HorizontalPositiveRayCodimTwoSafe hp C (replaceMovable hp C base move) := by
  intro q w i j hij hdev hmean hpure hzeros
  have hvalue := affineValue_replaceMovable_eq_of_purelyHorizontalCodimTwo
    hp C base move q w i j hij hzeros hpure
  apply hbase q w i j hij
  · intro r
    rw [← hvalue]
    exact hdev r
  · rw [← hvalue]
    exact hmean
  · exact hpure
  · exact hzeros

/-- Nonhorizontal minor regularity plus horizontal endpoint safety gives the exact
positive-ray-relative codimension-two avoidance condition. -/
theorem avoidsPositiveRayCodimTwo_of_relativeGeneric
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    (hgeneric : IsRelativeGeneric hp C base move)
    (hhorizontal : HorizontalPositiveRayCodimTwoSafe hp C
      (replaceMovable hp C base move))
    (q : C.Cell) :
    AvoidsPositiveRayCodimTwo hp
      (localVertexMap hp C (replaceMovable hp C base move) q) := by
  intro w i j hij hdev hmean hzeros
  let f : CodimTwoFace p := (i, omittedIndex i j hij)
  by_cases hpure : IsPurelyHorizontalCodimTwo hp C q f
  · exact hhorizontal q w i j hij hdev hmean hpure hzeros
  · let x : Fin (p - 1) → Real :=
      fun c => w (codimTwoVertex hp f c)
    have hmul :
        (codimTwoDeviationMatrix hp C (replaceMovable hp C base move) q f).mulVec x = 0 := by
      funext r
      have hsum :
          ∑ k : Fin (p + 1),
            w k * deviation hp
              ((localVertexMap hp C (replaceMovable hp C base move) q).value k) r = 0 := by
        rw [← deviation_affineValue_eq_weighted_sum]
        exact hdev r
      have hreindex := EquivariantPrismGenericPerturbation.sum_codimTwoVertex hp
        (fun k : Fin (p + 1) =>
          w k * deviation hp
            ((localVertexMap hp C (replaceMovable hp C base move) q).value k) r)
        i j hij (by simp [hzeros.1]) (by simp [hzeros.2])
      rw [hreindex] at hsum
      simpa [Matrix.mulVec, dotProduct, x, f, localVertexMap,
        codimTwoDeviationMatrix, codimTwoVertex, mul_comm] using hsum
    have hx : x = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero
        (codimTwoMinor_ne_zero_of_relativeGeneric hp C base move hgeneric q f hpure) hmul
    have hsumw := EquivariantPrismGenericPerturbation.sum_codimTwoVertex hp
      (fun k : Fin (p + 1) => w k) i j hij hzeros.1 hzeros.2
    have hright :
        (∑ c : Fin (p - 1), w (codimTwoVertex hp f c)) = 0 := by
      have h := congrArg (fun y : Fin (p - 1) → Real => ∑ c, y c) hx
      simpa [x] using h
    have hone : (1 : Real) = 0 := by
      calc
        (1 : Real) = ∑ k : Fin (p + 1), w k := w.sum_eq_one.symm
        _ = ∑ c : Fin (p - 1), w (codimTwoVertex hp f c) := by
          simpa [f, codimTwoVertex] using hsumw
        _ = 0 := hright
    norm_num at hone

/-- Relative genericity, horizontal endpoint safety, and origin avoidance give the local
positive-ray general-position interface. -/
theorem positiveRayGeneralPosition_of_relativeGeneric
    (base : Assignment hp C) (move : MovableParameter hp C → Real)
    (hgeneric : IsRelativeGeneric hp C base move)
    (hhorizontal : HorizontalPositiveRayCodimTwoSafe hp C
      (replaceMovable hp C base move))
    (havoid : ∀ q : C.Cell,
      AvoidsOrigin (localVertexMap hp C (replaceMovable hp C base move) q))
    (q : C.Cell) :
    PositiveRayGeneralPosition hp
      (localVertexMap hp C (replaceMovable hp C base move) q) where
  facetRegular := facetRegular_of_relativeGeneric hp C base move hgeneric q
  avoidsPositiveRayCodimTwo :=
    avoidsPositiveRayCodimTwo_of_relativeGeneric hp C base move hgeneric hhorizontal q
  avoidsOrigin := havoid q

/-- The relative genericity package implies the exact cellwise positive-ray Stokes identity. -/
theorem localPositiveRayStokes_of_relativeGeneric
    (D : FoxNeuwirthRelativeAffineCollar hp N₀ N₁ M L)
    (base : Assignment hp D.cells) (move : MovableParameter hp D.cells → Real)
    (hgeneric : IsRelativeGeneric hp D.cells base move)
    (hhorizontal : HorizontalPositiveRayCodimTwoSafe hp D.cells
      (replaceMovable hp D.cells base move))
    (havoid : ∀ q : D.cells.Cell,
      AvoidsOrigin
        (localVertexMap hp D.cells (replaceMovable hp D.cells base move) q)) :
    D.LocalPositiveRayStokes hp (replaceMovable hp D.cells base move) := by
  apply D.localPositiveRayStokes_of_positiveRayGeneralPosition hp
  intro q
  exact positiveRayGeneralPosition_of_relativeGeneric hp D.cells base move
    hgeneric hhorizontal havoid q

/-! ## Finite perturbation on movable parameter orbits -/

/-- A finite family of nonzero restricted polynomials admits a simultaneously generic movable
assignment arbitrarily close to any prescribed movable assignment. -/
theorem exists_relativeGeneric_move_close
    (base : Assignment hp C)
    (hpoly : ∀ i : RelativeGenericityIndex hp C,
      restrictedGenericityPolynomial hp C base i ≠ 0)
    (move₀ : MovableParameter hp C → Real)
    {eps : Real} (heps : 0 < eps) :
    ∃ move : MovableParameter hp C → Real,
      AssignmentClose move move₀ eps ∧ IsRelativeGeneric hp C base move := by
  obtain ⟨move, hclose, hgeneric⟩ :=
    exists_generic_assignment_close
      (restrictedGenericityPolynomial hp C base) hpoly move₀ heps
  exact ⟨move, hclose, hgeneric⟩

/-- Closeness on movable parameter orbits gives closeness of the reconstructed full assignments;
frozen horizontal parameters agree exactly. -/
theorem replaceMovable_assignmentClose
    (base : Assignment hp C)
    (move move₀ : MovableParameter hp C → Real)
    {eps : Real} (heps : 0 < eps)
    (hclose : AssignmentClose move move₀ eps) :
    AssignmentClose (replaceMovable hp C base move)
      (replaceMovable hp C base move₀) eps := by
  intro q
  by_cases hq : IsFrozenParameter hp C q
  · simp [replaceMovable, hq, heps]
  · simpa [replaceMovable, hq] using hclose ⟨q, hq⟩

/-! ## Quantitative origin-avoidance retention -/

/-- Replacing movable parameters by the restriction of the base assignment reconstructs the base
assignment exactly. -/
@[simp] theorem replaceMovable_movableRestriction
    (base : Assignment hp C) :
    replaceMovable hp C base (movableRestriction hp C base) = base := by
  funext q
  by_cases hq : IsFrozenParameter hp C q
  · simp [replaceMovable, hq]
  · simp [replaceMovable, movableRestriction, hq]

/-- The full parameter represented by one local vertex coordinate. -/
noncomputable def localParameter
    (q : C.Cell) (i : Fin (p + 1)) (j : Fin p) : Parameter hp C :=
  Quotient.mk _ (sampleVertex hp C (q, i), j)

@[simp] theorem localVertexMap_value_apply_eq_assignment_localParameter
    (a : Assignment hp C) (q : C.Cell)
    (i : Fin (p + 1)) (j : Fin p) :
    (localVertexMap hp C a q).value i j = a (localParameter hp C q i j) := rfl

/-- A coordinate witness for a uniform lower bound on every local affine value. -/
def LocalAffineCoordinateNormMargin
    (a : Assignment hp C) (m : Real) : Prop :=
  ∀ (q : C.Cell) (w : StandardSimplex p),
    ∃ j : Fin p,
      m ≤ |affineValue (localVertexMap hp C a q) w j|

/-- Coordinatewise closeness of full assignments bounds each coordinate of each local affine
interpolation. -/
theorem affineValue_coordinate_sub_abs_le_of_assignmentClose
    (a' a : Assignment hp C) {eps : Real}
    (hclose : AssignmentClose a' a eps)
    (q : C.Cell) (w : StandardSimplex p) (j : Fin p) :
    |affineValue (localVertexMap hp C a' q) w j -
      affineValue (localVertexMap hp C a q) w j| ≤ eps := by
  unfold affineValue
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i : Fin (p + 1),
        (w i * (localVertexMap hp C a' q).value i j -
          w i * (localVertexMap hp C a q).value i j)|
        ≤ ∑ i : Fin (p + 1),
          |w i * (localVertexMap hp C a' q).value i j -
            w i * (localVertexMap hp C a q).value i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin (p + 1),
        w i * |a' (localParameter hp C q i j) -
          a (localParameter hp C q i j)| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show
        w i * (localVertexMap hp C a' q).value i j -
            w i * (localVertexMap hp C a q).value i j =
          w i * ((localVertexMap hp C a' q).value i j -
            (localVertexMap hp C a q).value i j) by ring]
      simp [localVertexMap_value_apply_eq_assignment_localParameter,
        abs_mul, abs_of_nonneg (w.nonneg i)]
    _ ≤ ∑ i : Fin (p + 1), w i * eps := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (le_of_lt (hclose (localParameter hp C q i j))) (w.nonneg i)
    _ = eps := by
      rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

/-- A coordinate norm margin decreases by at most the assignment perturbation size. -/
theorem retain_localAffineCoordinateNormMargin
    (a' a : Assignment hp C) {m eps : Real}
    (hmargin : LocalAffineCoordinateNormMargin hp C a m)
    (hclose : AssignmentClose a' a eps) :
    LocalAffineCoordinateNormMargin hp C a' (m - eps) := by
  intro q w
  obtain ⟨j, hj⟩ := hmargin q w
  refine ⟨j, ?_⟩
  have hdiff := affineValue_coordinate_sub_abs_le_of_assignmentClose
    hp C a' a hclose q w j
  have htriangle :
      |affineValue (localVertexMap hp C a q) w j| ≤
        |affineValue (localVertexMap hp C a' q) w j -
          affineValue (localVertexMap hp C a q) w j| +
        |affineValue (localVertexMap hp C a' q) w j| := by
    calc
      |affineValue (localVertexMap hp C a q) w j| =
          |-(affineValue (localVertexMap hp C a' q) w j -
              affineValue (localVertexMap hp C a q) w j) +
            affineValue (localVertexMap hp C a' q) w j| := by
              congr 1
              ring
      _ ≤ |-(affineValue (localVertexMap hp C a' q) w j -
              affineValue (localVertexMap hp C a q) w j)| +
            |affineValue (localVertexMap hp C a' q) w j| :=
          abs_add_le _ _
      _ = |affineValue (localVertexMap hp C a' q) w j -
              affineValue (localVertexMap hp C a q) w j| +
            |affineValue (localVertexMap hp C a' q) w j| := by
          rw [abs_neg]
  linarith

/-- A positive coordinate norm margin implies local origin avoidance. -/
theorem avoidsOrigin_of_localAffineCoordinateNormMargin
    (a : Assignment hp C) {m : Real} (hm : 0 < m)
    (hmargin : LocalAffineCoordinateNormMargin hp C a m)
    (q : C.Cell) :
    AvoidsOrigin (localVertexMap hp C a q) := by
  intro w hzero
  obtain ⟨j, hj⟩ := hmargin q w
  have hjzero : affineValue (localVertexMap hp C a q) w j = 0 :=
    congrFun hzero j
  simp [hjzero] at hj
  linarith

/-- Cellwise origin avoidance on a finite relative collar automatically has a uniform positive
coordinate margin.  Compactness gives a positive norm minimum on each affine simplex; finiteness of
the cell family gives one common minimum, and the finite-product sup norm is attained in a
coordinate. -/
theorem exists_positive_localAffineCoordinateNormMargin
    (a : Assignment hp C)
    (havoid : ∀ q : C.Cell, AvoidsOrigin (localVertexMap hp C a q)) :
    ∃ m : Real, 0 < m ∧ LocalAffineCoordinateNormMargin hp C a m := by
  classical
  have hcell : ∀ q : C.Cell, ∃ m : Real, 0 < m ∧
      ∀ w : StandardSimplex p,
        m ≤ ‖affineValue (localVertexMap hp C a q) w‖ := by
    intro q
    have hcont : Continuous
        (fun w : StandardSimplex p =>
          ‖affineValue (localVertexMap hp C a q) w‖) := by
      apply Continuous.norm
      apply continuous_pi
      intro r
      exact continuous_finsetSum _ fun i _ => by
        have hw : Continuous (fun w : StandardSimplex p => (w : Fin (p + 1) → Real) i) :=
          (continuous_apply i).comp continuous_subtype_val
        have hc : Continuous (fun _ : StandardSimplex p =>
            (localVertexMap hp C a q).value i r) := continuous_const
        exact hw.mul hc
    have hcompact : IsCompact (Set.univ : Set (StandardSimplex p)) := by
      let f : SphereOddDegree.AffineBarycentricSubdivision.Delta p → StandardSimplex p :=
        StandardSimplex.ofDelta
      have hf : Continuous f := by
        rw [continuous_induced_rng]
        exact continuous_subtype_val
      have hrange : Set.range f = Set.univ := by
        ext w
        constructor
        · intro hw
          exact Set.mem_univ _
        · intro hw
          refine ⟨StandardSimplex.toDelta w, ?_⟩
          exact StandardSimplex.ofDelta_toDelta w
      let : CompactSpace (SphereOddDegree.AffineBarycentricSubdivision.Delta p) :=
        isCompact_iff_compactSpace.mp (SphereOddDegree.isCompact_finiteSimplex ℝ (Fin (p + 1)))
      have himage : IsCompact (Set.range f) := isCompact_range hf
      rw [hrange] at himage
      exact himage
    let wdefault : StandardSimplex p :=
      StandardSimplex.ofDelta
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) (0 : Fin (p + 1)))
    obtain ⟨w₀, hw₀⟩ :=
      IsCompact.exists_isMinOn hcompact
        ⟨wdefault, Set.mem_univ _⟩ hcont.continuousOn
    refine ⟨‖affineValue (localVertexMap hp C a q) w₀‖, ?_, ?_⟩
    · exact norm_pos_iff.mpr (havoid q w₀)
    · intro w
      exact hw₀.2 (Set.mem_univ w)
  let cellMargin : C.Cell → Real := fun q => Classical.choose (hcell q)
  have hcellMargin_pos : ∀ q : C.Cell, 0 < cellMargin q := by
    intro q
    exact (Classical.choose_spec (hcell q)).1
  have hcellMargin_le : ∀ (q : C.Cell) (w : StandardSimplex p),
      cellMargin q ≤ ‖affineValue (localVertexMap hp C a q) w‖ := by
    intro q w
    exact (Classical.choose_spec (hcell q)).2 w
  let margins : Finset Real := Finset.univ.image cellMargin
  have hmargins : margins.Nonempty := by
    obtain ⟨q₀⟩ := C.cell_nonempty
    exact ⟨cellMargin q₀, Finset.mem_image_of_mem cellMargin (Finset.mem_univ q₀)⟩
  let m : Real := margins.min' hmargins
  have hm_pos : 0 < m := by
    have hm_mem := Finset.min'_mem margins hmargins
    rcases Finset.mem_image.mp hm_mem with ⟨q, hq, hqeq⟩
    have hqpos := hcellMargin_pos q
    rw [hqeq] at hqpos
    exact hqpos
  refine ⟨m, hm_pos, ?_⟩
  intro q w
  have hm_le_cell : m ≤ cellMargin q := by
    exact Finset.min'_le margins (cellMargin q)
      (Finset.mem_image_of_mem cellMargin (Finset.mem_univ q))
  obtain ⟨j, hj⟩ :=
    EquivariantPrismSubdivisionMargin.exists_coordinate_abs_ge_norm hp
      (affineValue (localVertexMap hp C a q) w)
  exact ⟨j, le_trans hm_le_cell (le_trans (hcellMargin_le q w) hj)⟩

/-- Output of a small boundary-relative generic perturbation retaining half of a supplied origin
margin. -/
structure PerturbationResult
    (base : Assignment hp C) (m : Real) where
  /-- The selected values of the movable real coordinates. -/
  move : MovableParameter hp C → Real
  closeToBase : AssignmentClose
    (replaceMovable hp C base move) base (m / 2)
  relativeGeneric : IsRelativeGeneric hp C base move
  retainedMargin : LocalAffineCoordinateNormMargin hp C
    (replaceMovable hp C base move) (m / 2)
  avoidsOrigin : ∀ q : C.Cell,
    AvoidsOrigin (localVertexMap hp C (replaceMovable hp C base move) q)

/-- Simultaneously make all nontrivial boundary-relative genericity polynomials nonzero while
retaining half of a positive affine origin margin. -/
theorem exists_relativeGeneric_perturbation
    (base : Assignment hp C)
    (hpoly : ∀ i : RelativeGenericityIndex hp C,
      restrictedGenericityPolynomial hp C base i ≠ 0)
    {m : Real} (hm : 0 < m)
    (hmargin : LocalAffineCoordinateNormMargin hp C base m) :
    Nonempty (PerturbationResult hp C base m) := by
  have hm2 : 0 < m / 2 := by positivity
  obtain ⟨move, hmoveClose, hgeneric⟩ :=
    exists_relativeGeneric_move_close hp C base hpoly
      (movableRestriction hp C base) hm2
  have hfullClose : AssignmentClose
      (replaceMovable hp C base move) base (m / 2) := by
    have h := replaceMovable_assignmentClose hp C base move
      (movableRestriction hp C base) hm2 hmoveClose
    simpa using h
  have hretained : LocalAffineCoordinateNormMargin hp C
      (replaceMovable hp C base move) (m / 2) := by
    have h := retain_localAffineCoordinateNormMargin hp C
      (replaceMovable hp C base move) base hmargin hfullClose
    convert h using 1; ring
  refine ⟨{
    move := move
    closeToBase := hfullClose
    relativeGeneric := hgeneric
    retainedMargin := hretained
    avoidsOrigin := ?_ }⟩
  intro q
  exact avoidsOrigin_of_localAffineCoordinateNormMargin hp C
    (replaceMovable hp C base move) hm2 hretained q

end RelativeGenericity
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
