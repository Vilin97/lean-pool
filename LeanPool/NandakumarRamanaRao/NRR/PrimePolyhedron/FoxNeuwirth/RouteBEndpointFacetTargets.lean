/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBFacetWitnessRealization
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EndpointStackIteratedAffinePullback
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
/-!
# Boundary-respecting facet targets for affine-pullback endpoint stacks

The first endpoint-stack layer has a distinguished coarse lower simplex.  Every time-zero local
vertex is one of its vertices, and those vertices are pairwise distinct.  A partial injection from
frozen facet columns to coarse-simplex vertices therefore extends to a permutation.  Filling the
remaining movable columns with the missing coarse-simplex values makes the selected facet a column
permutation of the regular endpoint matrix.
-/

namespace NRR
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RouteBEndpointFacetTargets

open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open ExplicitAffineRelativeCollar.RelativeGenericity
open ExplicitAffineRelativeCollar.RouteB
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open CompatibleRefinedChartHomotopy
open CompatibleChartMapOneStep
open EndpointStackIteratedAffinePullback


variable {p : Nat}

/-- Vertex-index shift between a one-step cell and its local subdivision cylinder. -/
theorem dimShift (hp : Nat.Prime p) : p + 1 = p - 1 + 2 := by
  have := hp.pos
  omega

/-- The local cylinder time of a one-step cell vertex. -/
theorem cylinderVertex_time (hp : Nat.Prime p) {N : Nat}
    (q : (RelativeSubdivisionOneStepCells.cellSystem hp N).Cell) (i : Fin (p + 1)) :
    (RelativeSubdivisionCylinderCombinatorics.vertex (p - 1) q.2
        (Fin.cast (dimShift hp) i)).2.1 =
      ((RelativeSubdivisionOneStepCells.cellSystem hp N).vertex q i).time.1 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  show (RelativeSubdivisionCylinderCombinatorics.vertex m q.2 i).2.1 = _
  simp [RelativeSubdivisionOneStepCells.cellSystem,
    RelativeSubdivisionOneStepCells.vertex, RelativeSubdivisionOneStepCells.chart,
    RelativeSubdivisionOneStepCells.liftPoint,
    RelativeSubdivisionOneStepCells.localPoint,
    CompatibleChartMapOneStep.localWeight_succ,
    EquivariantPrismVertexParameters.CylinderPoint.ofProd]

/-- The local cylinder point of a one-step cell vertex. -/
theorem cylinderVertex_point (hp : Nat.Prime p) {N : Nat}
    (q : (RelativeSubdivisionOneStepCells.cellSystem hp N).Cell) (i : Fin (p + 1)) :
    RelativeSubdivisionOneStepCells.localPoint hp q.2
        (stdSimplex.vertex (S := Real) i) =
      RelativeSubdivisionCylinderCombinatorics.vertex (p - 1) q.2
        (Fin.cast (dimShift hp) i) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  show RelativeSubdivisionOneStepCells.localPoint hp q.2
      (stdSimplex.vertex (S := Real) i) =
    RelativeSubdivisionCylinderCombinatorics.vertex m q.2 i
  simp [RelativeSubdivisionOneStepCells.localPoint,
    CompatibleChartMapOneStep.localWeight_succ]

/-- A finite partial injection into a finite type extends to a permutation. -/
theorem exists_perm_extending_finset
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (f : α → α)
    (hinj : Set.InjOn f (s : Set α)) :
    ∃ e : Equiv.Perm α, ∀ x ∈ s, e x = f x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨Equiv.refl α, by simp⟩
  | @insert a s ha ih =>
      have hinjS : Set.InjOn f (s : Set α) :=
        hinj.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
      obtain ⟨e, he⟩ := ih hinjS
      let e' : Equiv.Perm α := e.setValue a (f a)
      refine ⟨e', ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp [e', Equiv.setValue]
      · have hxa : x ≠ a := by
          intro h
          subst x
          exact ha hx
        have hxb : x ≠ e.symm (f a) := by
          intro h
          have hex : e x = f a := by simpa [h]
          have hfx : f x = f a := by rw [← he x hx, hex]
          exact hxa (hinj (Finset.mem_insert_of_mem hx)
            (Finset.mem_insert_self a s) hfx)
        have hswap : (Equiv.swap a (e.symm (f a))) x = x :=
          Equiv.swap_apply_of_ne_of_ne hxa hxb
        simp [e', Equiv.setValue, hswap, he x hx]

/-- Facet columns whose represented local vertices lie on the coarse lower boundary. -/
noncomputable def lowerFrozenColumns
    (hp : Nat.Prime p) {N : Nat}
    (q : (RelativeSubdivisionOneStepCells.cellSystem hp N).Cell) (k : Fin (p + 1)) : Finset (Fin p) :=
  Finset.univ.filter (fun c =>
    ((RelativeSubdivisionOneStepCells.cellSystem hp N).vertex q (k.succAbove c)).time.1 = 0)

/-- Coarse lower-simplex index represented by a frozen facet column. -/
noncomputable def lowerColumnIndex
    (hp : Nat.Prime p) {N : Nat}
    (q : (RelativeSubdivisionOneStepCells.cellSystem hp N).Cell) (k : Fin (p + 1))
    (c : {c // c ∈ lowerFrozenColumns hp q k}) : Fin p :=
  (augmentedRowEquiv hp).symm
    (Classical.choose
      (RelativeSubdivisionCylinderCombinatorics.vertex_eq_lowerBoundaryVertex_of_time_eq_zero
        (p - 1) q.2 (Fin.cast (dimShift hp) (k.succAbove c.1))
        ((cylinderVertex_time hp q (k.succAbove c.1)).trans
          (Finset.mem_filter.mp c.2).2)))

/-- The frozen-column map is injective. -/
theorem lowerColumnIndex_injective
    (hp : Nat.Prime p) {N : Nat}
    (q : (RelativeSubdivisionOneStepCells.cellSystem hp N).Cell) (k : Fin (p + 1)) :
    Function.Injective (lowerColumnIndex hp q k) := by
  intro a b hab
  apply Subtype.ext
  apply Fin.succAbove_right_injective (p := k)
  have hchoose :
      Classical.choose
        (RelativeSubdivisionCylinderCombinatorics.vertex_eq_lowerBoundaryVertex_of_time_eq_zero
          (p - 1) q.2 (Fin.cast (dimShift hp) (k.succAbove a.1))
          ((cylinderVertex_time hp q (k.succAbove a.1)).trans
            (Finset.mem_filter.mp a.2).2)) =
      Classical.choose
        (RelativeSubdivisionCylinderCombinatorics.vertex_eq_lowerBoundaryVertex_of_time_eq_zero
          (p - 1) q.2 (Fin.cast (dimShift hp) (k.succAbove b.1))
          ((cylinderVertex_time hp q (k.succAbove b.1)).trans
            (Finset.mem_filter.mp b.2).2)) := by
    have := hab
    simpa [lowerColumnIndex] using this
  have hvertex :
      Fin.cast (dimShift hp) (k.succAbove a.1) =
        Fin.cast (dimShift hp) (k.succAbove b.1) := by
    apply RelativeSubdivisionCylinderCombinatorics.vertex_injective_all (p - 1) q.2
    rw [Classical.choose_spec
        (RelativeSubdivisionCylinderCombinatorics.vertex_eq_lowerBoundaryVertex_of_time_eq_zero
          (p - 1) q.2 (Fin.cast (dimShift hp) (k.succAbove a.1))
          ((cylinderVertex_time hp q (k.succAbove a.1)).trans
            (Finset.mem_filter.mp a.2).2)),
      Classical.choose_spec
        (RelativeSubdivisionCylinderCombinatorics.vertex_eq_lowerBoundaryVertex_of_time_eq_zero
          (p - 1) q.2 (Fin.cast (dimShift hp) (k.succAbove b.1))
          ((cylinderVertex_time hp q (k.succAbove b.1)).trans
            (Finset.mem_filter.mp b.2).2)), hchoose]
  have hval : (k.succAbove a.1).val = (k.succAbove b.1).val := by
    simpa using congrArg Fin.val hvertex
  exact Fin.eq_of_val_eq hval

/-- A permutation extending the frozen-column identification. -/
noncomputable def lowerFacetPermutation
    (hp : Nat.Prime p) {N : Nat}
    (q : (RelativeSubdivisionOneStepCells.cellSystem hp N).Cell) (k : Fin (p + 1)) :
    Equiv.Perm (Fin p) :=
  Classical.choose (exists_perm_extending_finset
    (lowerFrozenColumns hp q k)
    (fun c => if hc : c ∈ lowerFrozenColumns hp q k then
      lowerColumnIndex hp q k ⟨c, hc⟩ else c)
    (by
      intro a ha b hb hab
      simp only [Finset.mem_coe] at ha hb
      simp [ha, hb] at hab
      exact congrArg Subtype.val
        (lowerColumnIndex_injective hp q k hab)))

/-- The chosen permutation agrees with the represented lower index on every frozen column. -/
theorem lowerFacetPermutation_frozen
    (hp : Nat.Prime p) {N : Nat}
    (q : (RelativeSubdivisionOneStepCells.cellSystem hp N).Cell) (k : Fin (p + 1))
    (c : Fin p) (hc : c ∈ lowerFrozenColumns hp q k) :
    lowerFacetPermutation hp q k c = lowerColumnIndex hp q k ⟨c, hc⟩ := by
  have h := Classical.choose_spec (exists_perm_extending_finset
    (lowerFrozenColumns hp q k)
    (fun c => if hc : c ∈ lowerFrozenColumns hp q k then
      lowerColumnIndex hp q k ⟨c, hc⟩ else c)
    (by
      intro a ha b hb hab
      simp only [Finset.mem_coe] at ha hb
      simp [ha, hb] at hab
      exact congrArg Subtype.val
        (lowerColumnIndex_injective hp q k hab))) c hc
  simpa [lowerFacetPermutation, hc] using h

/-- Boundary-respecting target whose selected facet is the regular endpoint matrix with permuted
columns. -/
noncomputable def oneStepLowerFacetTarget
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : StableRegularApproximation hp F)
    (q : (RelativeSubdivisionOneStepCells.cellSystem hp A.toRegularApproximation.level).Cell)
    (k : Fin (p + 1)) : Fin (p + 1) → Fin p → Real :=
  fun i j =>
    if h : ∃ c : Fin p, i = k.succAbove c then
      vertexValue hp A.toRegularApproximation.level A.toRegularApproximation.map q.1
        (augmentedRowEquiv hp (lowerFacetPermutation hp q k (Classical.choose h))) j
    else
      (localVertexMap hp (RelativeSubdivisionOneStepCells.cellSystem hp A.toRegularApproximation.level)
        (CompatibleChartMapOneStep.assignment hp
          (baseOriginalPLMap hp A.toRegularApproximation)) q).value i j

/-- Values on the selected facet have the advertised permuted endpoint form. -/
theorem oneStepLowerFacetTarget_succAbove
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : StableRegularApproximation hp F)
    (q : (RelativeSubdivisionOneStepCells.cellSystem hp A.toRegularApproximation.level).Cell)
    (k : Fin (p + 1)) (c : Fin p) (j : Fin p) :
    oneStepLowerFacetTarget hp A q k (k.succAbove c) j =
      vertexValue hp A.toRegularApproximation.level A.toRegularApproximation.map q.1
        (augmentedRowEquiv hp (lowerFacetPermutation hp q k c)) j := by
  classical
  let h : ∃ d : Fin p, k.succAbove c = k.succAbove d := ⟨c, rfl⟩
  rw [oneStepLowerFacetTarget, dif_pos h]
  have hc : Classical.choose h = c :=
    Fin.succAbove_right_injective (p := k) (Classical.choose_spec h).symm
  simp

/-- The selected target facet matrix is a column permutation of the endpoint regularity matrix. -/
theorem facetMatrix_oneStepLowerFacetTarget
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : StableRegularApproximation hp F)
    (q : (RelativeSubdivisionOneStepCells.cellSystem hp A.toRegularApproximation.level).Cell)
    (k : Fin (p + 1)) :
    facetMatrix hp (⟨oneStepLowerFacetTarget hp A q k⟩ : VertexMap p) k =
      (augmentedMatrix hp A.toRegularApproximation.level
        A.toRegularApproximation.map q.1).submatrix (augmentedRowEquiv hp)
          (fun i => augmentedRowEquiv hp (lowerFacetPermutation hp q k i)) := by
  ext r c
  obtain ⟨t, rfl⟩ : ∃ t, r = (augmentedRowEquiv hp).symm t :=
    ⟨augmentedRowEquiv hp r, by simp⟩
  refine Fin.lastCases ?_ (fun s => ?_) t
  · simp [facetMatrix, augmentedMatrix]
  · simp [facetMatrix, facetValue, oneStepLowerFacetTarget_succAbove,
      augmentedMatrix, deviationVertexValue, deviation]

/-- The selected target facet is regular. -/
theorem oneStepLowerFacetTarget_determinant_ne_zero
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : StableRegularApproximation hp F)
    (q : (RelativeSubdivisionOneStepCells.cellSystem hp A.toRegularApproximation.level).Cell)
    (k : Fin (p + 1)) :
    facetDeterminant hp (⟨oneStepLowerFacetTarget hp A q k⟩ : VertexMap p) k ≠ 0 := by
  rw [facetDeterminant, facetMatrix_oneStepLowerFacetTarget]
  have hsub :
      (augmentedMatrix hp A.toRegularApproximation.level
          A.toRegularApproximation.map q.1).submatrix (augmentedRowEquiv hp)
          (fun i => augmentedRowEquiv hp (lowerFacetPermutation hp q k i)) =
        (((augmentedMatrix hp A.toRegularApproximation.level
            A.toRegularApproximation.map q.1).submatrix
            (augmentedRowEquiv hp) (augmentedRowEquiv hp)).submatrix id
          (lowerFacetPermutation hp q k)) := rfl
  rw [hsub, Matrix.det_permute', Matrix.det_submatrix_equiv_self]
  refine mul_ne_zero ?_ (A.toRegularApproximation.regular q.1)
  rcases Int.units_eq_one_or (Equiv.Perm.sign (lowerFacetPermutation hp q k)) with h | h <;>
    simp [h]
/-- The target leaves every lower-horizontal local scalar coordinate fixed. -/
theorem oneStepLowerFacetTarget_respects_lower
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : StableRegularApproximation hp F)
    (q : (RelativeSubdivisionOneStepCells.cellSystem hp A.toRegularApproximation.level).Cell)
    (k : Fin (p + 1)) :
    ∀ (i : Fin (p + 1)) (j : Fin p),
      ((RelativeSubdivisionOneStepCells.cellSystem hp A.toRegularApproximation.level).vertex q i).time.1 = 0 →
      oneStepLowerFacetTarget hp A q k i j =
        (localVertexMap hp (RelativeSubdivisionOneStepCells.cellSystem hp A.toRegularApproximation.level)
          (CompatibleChartMapOneStep.assignment hp
            (baseOriginalPLMap hp A.toRegularApproximation)) q).value i j := by
  intro i j hi
  classical
  by_cases hik : i = k
  · subst i
    simp [oneStepLowerFacetTarget]
  · obtain ⟨c, hsucc⟩ : ∃ c : Fin p, k.succAbove c = i := Fin.exists_succAbove_eq hik
    have hcFrozen : c ∈ lowerFrozenColumns hp q k := by
      simp only [lowerFrozenColumns, Finset.mem_filter, Finset.mem_univ, true_and, hsucc]
      exact hi
    rw [← hsucc, oneStepLowerFacetTarget_succAbove,
      lowerFacetPermutation_frozen hp q k c hcFrozen]
    have hi' :
        ((RelativeSubdivisionOneStepCells.cellSystem hp
          A.toRegularApproximation.level).vertex q (k.succAbove c)).time.1 = 0 := by
      rw [hsucc]
      exact hi
    have hspec := Classical.choose_spec
      (RelativeSubdivisionCylinderCombinatorics.vertex_eq_lowerBoundaryVertex_of_time_eq_zero
        (p - 1) q.2 (Fin.cast (dimShift hp) (k.succAbove c))
        ((cylinderVertex_time hp q (k.succAbove c)).trans hi'))
    rw [lowerColumnIndex, Equiv.apply_symm_apply]
    simp only [localVertexMap,
      CompatibleChartMapOneStep.vectorValue_assignment_sample,
      CompatibleChartMapOneStep.localVector,
      CompatibleChartMapOneStep.localSpatialWeight]
    rw [(cylinderVertex_point hp q (k.succAbove c)).trans hspec]
    simp [baseOriginalPLMap, RefinedAffineMap.value,
      RelativeSubdivisionCylinderCombinatorics.lowerBoundaryVertex,
      StandardSimplex.ofDelta, stdSimplex.vertex, Pi.single_apply, ite_mul,
      Finset.sum_ite_eq']

/-- Lower-relative facet target property used by stack composition. -/
def LowerFacetTargets
    (hp : Nat.Prime p)
    {N₀ N₁ M L : Nat}
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C) : Prop :=
  ∀ (q : C.Cell) (k : Fin (p + 1)),
    ∃ target : Fin (p + 1) → Fin p → Real,
      (∀ i j, (C.vertex q i).time.1 = 0 →
        target i j = (localVertexMap hp C a q).value i j) ∧
      facetDeterminant hp (⟨target⟩ : VertexMap p) k ≠ 0

/-- One endpoint layer has lower-relative facet targets. -/
theorem oneStep_lowerFacetTargets
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : StableRegularApproximation hp F) :
    LowerFacetTargets hp (RelativeSubdivisionOneStepCells.cellSystem hp A.toRegularApproximation.level)
      (CompatibleChartMapOneStep.assignment hp
        (baseOriginalPLMap hp A.toRegularApproximation)) := by
  intro q k
  exact ⟨oneStepLowerFacetTarget hp A q k,
    oneStepLowerFacetTarget_respects_lower hp A q k,
    oneStepLowerFacetTarget_determinant_ne_zero hp A q k⟩

end RouteBEndpointFacetTargets
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
