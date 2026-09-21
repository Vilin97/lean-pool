/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBEndpointFacetTargets
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismGenericityNonzero
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarAssignmentReverse
/-!
# Composition of boundary-relative facet targets

Lower-relative targets propagate through a stack composition: the left cells reuse their target,
while every right cell is strictly away from the external lower boundary and may use the universal
triangular facet witness.  Reversal gives upper-relative targets.  A final lower/upper composition
then produces targets respecting the exact frozen-parameter predicate.
-/

namespace NRR
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RouteBFacetTargetComposition

open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open ReferenceAffineOrbitCount
open ExplicitAffineRelativeCollar.RouteB
open ExplicitAffineRelativeCollarCompose
open ExplicitAffineRelativeCollarAssignmentCompose
open ExplicitAffineRelativeCollarReverse
open ExplicitAffineRelativeCollarAssignmentReverse
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open EquivariantPrismGenericityNonzero
open RouteBEndpointFacetTargets
open ExplicitAffineRelativeCollar.RouteB

variable {p N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)

/-- The facet matrix of the universal triangular target.  Both the row and the column index are
reindexed by `augmentedRowEquiv`, which is the dimension used inside `facetMatrix`. -/
theorem facetMatrix_witnessTarget
    (k : Fin (p + 1)) :
    facetMatrix hp (⟨facetWitnessTarget hp k⟩ : VertexMap p) k =
      fun r c => Fin.lastCases (1 : Real)
        (fun s => Fin.lastCases 0 (fun t => if s = t then 1 else 0)
          (augmentedRowEquiv hp c))
        (augmentedRowEquiv hp r) := by
  classical
  ext r c
  unfold facetMatrix
  generalize hr : augmentedRowEquiv hp r = r'
  refine Fin.lastCases ?_ (fun s => ?_) r'
  · simp
  · simp [deviation, facetValue, facetWitnessTarget_succAbove]
    generalize hc : augmentedRowEquiv hp c = c'
    refine Fin.lastCases ?_ (fun t => ?_) c'
    · simp
    · have hinj : coordinateLabel hp s = coordinateLabel hp t ↔ s = t :=
        (coordinateLabel_injective hp).eq_iff
      have hlast : lastLabel hp ≠ coordinateLabel hp t :=
        (coordinateLabel_ne_last hp t).symm
      simp [hinj, hlast]

/-- The universal triangular facet target has determinant one. -/
theorem facetWitnessTarget_determinant
    (k : Fin (p + 1)) :
    facetDeterminant hp (⟨facetWitnessTarget hp k⟩ : VertexMap p) k = 1 := by
  classical
  rw [facetDeterminant, facetMatrix_witnessTarget]
  let M : Matrix (Fin p) (Fin p) Real := fun r c => Fin.lastCases (1 : Real)
    (fun s => Fin.lastCases 0 (fun t => if s = t then 1 else 0)
      (augmentedRowEquiv hp c))
    (augmentedRowEquiv hp r)
  change Matrix.det M = 1
  rw [Matrix.det_of_isLowerTriangular]
  · have hd : ∀ i, M i i = 1 := by
      intro i
      dsimp [M]
      generalize hi : augmentedRowEquiv hp i = i'
      refine Fin.lastCases ?_ (fun s => ?_) i' <;> simp
    simp [hd]
  · intro i j hij
    dsimp [M]
    have hij' : i.val < j.val := hij
    generalize hi : augmentedRowEquiv hp i = i'
    generalize hj : augmentedRowEquiv hp j = j'
    have hiv : i.val = i'.val := congrArg Fin.val hi
    have hjv : j.val = j'.val := congrArg Fin.val hj
    have hord : i'.val < j'.val := by omega
    revert hord
    refine Fin.lastCases (motive := fun x => x.val < j'.val →
        Fin.lastCases (1 : Real)
          (fun s => Fin.lastCases (0 : Real)
            (fun t => if s = t then (1 : Real) else 0) j') x = (0 : Real))
      ?_ (fun s hord => ?_) i'
    · intro hord
      exfalso
      exact (not_lt_of_ge (Fin.le_last j')) hord
    · rw [Fin.lastCases_castSucc]
      revert hord
      refine Fin.lastCases (motive := fun x => s.castSucc.val < x.val →
          Fin.lastCases (0 : Real) (fun t => if s = t then (1 : Real) else 0) x =
            (0 : Real))
        ?_ (fun t hord => ?_) j'
      · intro hord
        rw [Fin.lastCases_last]
      · rw [Fin.lastCases_castSucc]
        rw [if_neg]
        intro hst
        exact (ne_of_lt hord) (congrArg Fin.val (congrArg Fin.castSucc hst))

/-- Universal target determinant is nonzero. -/
theorem facetWitnessTarget_determinant_ne_zero
    (k : Fin (p + 1)) :
    facetDeterminant hp (⟨facetWitnessTarget hp k⟩ : VertexMap p) k ≠ 0 := by
  rw [facetWitnessTarget_determinant]
  norm_num

/-- Lower-relative targets survive composition with an arbitrary right collar. -/
theorem lowerFacetTargets_combined_left
    {Nmid M₀ L₀ M₁ L₁ : Nat}
    (C : RelativeAffineCellSystem hp N₀ Nmid M₀ L₀)
    (D : RelativeAffineCellSystem hp Nmid N₁ M₁ L₁)
    (a : Assignment hp C) (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b))
    (hC : LowerFacetTargets hp C a) :
    LowerFacetTargets hp (combinedCells C D)
      (combinedAssignment C D a b hseam) := by
  intro q k
  cases q with
  | inl q =>
      obtain ⟨target, hfixed, hdet⟩ := hC q k
      refine ⟨target, ?_, hdet⟩
      intro i j hi
      have hi0 : (C.vertex q i).time.1 = 0 := by
        change (C.vertex q i).time.1 / 2 = 0 at hi
        linarith
      simpa [localVertexMap_combinedAssignment_left] using hfixed i j hi0
  | inr q =>
      refine ⟨facetWitnessTarget hp k, ?_,
        facetWitnessTarget_determinant_ne_zero hp k⟩
      intro i j hi
      have hnonneg := (D.vertex q i).time.2.1
      change (1 + (D.vertex q i).time.1) / 2 = 0 at hi
      exfalso
      linarith

/-- Upper-relative version of the facet-target property. -/
def UpperFacetTargets
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C) : Prop :=
  ∀ (q : C.Cell) (k : Fin (p + 1)),
    ∃ target : Fin (p + 1) → Fin p → Real,
      (∀ i j, (C.vertex q i).time.1 = 1 →
        target i j = (localVertexMap hp C a q).value i j) ∧
      facetDeterminant hp (⟨target⟩ : VertexMap p) k ≠ 0

/-- Reversal turns lower-relative targets into upper-relative targets. -/
theorem upperFacetTargets_reverse
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C)
    (hC : LowerFacetTargets hp C a) :
    UpperFacetTargets hp (reverseCells C) (reverseAssignment C a) := by
  intro q k
  obtain ⟨target, hfixed, hdet⟩ := hC q k
  refine ⟨target, ?_, hdet⟩
  intro i j hi
  have hi0 : (C.vertex q i).time.1 = 0 := by
    change 1 - (C.vertex q i).time.1 = 1 at hi
    linarith
  simpa [localVertexMap_reverseAssignment] using hfixed i j hi0

/-- Target-level form of exact frozen-boundary compatibility. -/
def FrozenFacetTargets
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C) : Prop :=
  ∀ (q : C.Cell) (k : Fin (p + 1)),
    ∃ target : Fin (p + 1) → Fin p → Real,
      LocalTargetRespectsFrozen hp C a q target ∧
      facetDeterminant hp (⟨target⟩ : VertexMap p) k ≠ 0

/-- Lower- and upper-relative targets combine into exact frozen-relative targets. -/
theorem frozenFacetTargets_combined
    {Nmid M₀ L₀ M₁ L₁ : Nat}
    (C : RelativeAffineCellSystem hp N₀ Nmid M₀ L₀)
    (D : RelativeAffineCellSystem hp Nmid N₁ M₁ L₁)
    (a : Assignment hp C) (b : Assignment hp D)
    (hseam : SeamCompatible C D (vectorValue hp C a) (vectorValue hp D b))
    (hC : LowerFacetTargets hp C a)
    (hD : UpperFacetTargets hp D b) :
    FrozenFacetTargets hp (combinedCells C D)
      (combinedAssignment C D a b hseam) := by
  intro q k
  cases q with
  | inl q =>
      obtain ⟨target, hfixed, hdet⟩ := hC q k
      refine ⟨target, ?_, hdet⟩
      intro i j hfrozen
      have hh := (isFrozenParameter_localParameter_iff hp
        (combinedCells C D) (Sum.inl q) i j).1 hfrozen
      rcases hh with hlower | hupper
      · have hi0 : (C.vertex q i).time.1 = 0 := by
          change (C.vertex q i).time.1 / 2 = 0 at hlower
          linarith
        change target i j =
          a (RelativeGenericity.localParameter hp C q i j)
        exact hfixed i j hi0
      · have hle := (C.vertex q i).time.2.2
        change (C.vertex q i).time.1 / 2 = 1 at hupper
        exfalso
        linarith
  | inr q =>
      obtain ⟨target, hfixed, hdet⟩ := hD q k
      refine ⟨target, ?_, hdet⟩
      intro i j hfrozen
      have hh := (isFrozenParameter_localParameter_iff hp
        (combinedCells C D) (Sum.inr q) i j).1 hfrozen
      rcases hh with hlower | hupper
      · have hge := (D.vertex q i).time.2.1
        change (1 + (D.vertex q i).time.1) / 2 = 0 at hlower
        exfalso
        linarith
      · have hi1 : (D.vertex q i).time.1 = 1 := by
          change (1 + (D.vertex q i).time.1) / 2 = 1 at hupper
          linarith
        change target i j =
          b (RelativeGenericity.localParameter hp D q i j)
        exact hfixed i j hi1

/-- Frozen-relative targets give the pointwise regularity witnesses consumed by Route B. -/
theorem allFacetRegularityWitnesses_of_frozenFacetTargets
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (base : Assignment hp C)
    (h : FrozenFacetTargets hp C base) :
    AllFacetRegularityWitnesses hp C base := by
  intro q k
  obtain ⟨target, hfrozen, hdet⟩ := h q k
  exact exists_facetRegularityWitness_of_localTarget hp C base q k target hfrozen hdet

end RouteBFacetTargetComposition
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
