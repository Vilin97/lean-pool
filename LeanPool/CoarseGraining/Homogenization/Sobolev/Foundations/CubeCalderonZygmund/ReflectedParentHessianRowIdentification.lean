/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectionHessianRowCellH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectedParentInteriorHessian

/-!
# Identifying the reflected-parent weak Hessian

The canonical interior `H²` construction on the half-scaled reflected parent
produces an abstract weak Hessian. This file identifies each of its rows almost
everywhere with the mixed-parity reflection of the corresponding source row.
The proof uses weak-derivative uniqueness on each open reflection cell and the
fact that the finitely many cells cover the centered parent modulo reflecting
faces of measure zero.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace HasWeakHessianOn

/-- On the half-scaled reflected parent, the weak Hessian row of the canonical
interior representative is the mixed-parity reflection of the source row.

The two exact gradient identities are precisely those returned by
`exists_cubeDirichletOddReflectionParent_innerHalf_hasWeakHessianOn`. -/
theorem cubeDirichletOddReflectionParent_innerHalf_hessianRow_ae_eq
    {d : ℕ} {m : ℤ}
    {u : H1Function (openCubeSet (originCube d m))}
    (Hsrc : HasWeakHessianOn (openCubeSet (originCube d m)) u)
    {uP : H1Function (openCubeSet (originCube d (m + 1)))}
    (huP_grad :
      uP.grad =
        cubeDirichletOddReflectionVectorField (originCube d m)
          (fun y ↦ u.grad y))
    {uU : H1Function
      (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ))}
    (huU_grad : uU.grad = uP.grad)
    (HU : HasWeakHessianOn
      (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)) uU)
    (i : Fin d) :
    (fun x ↦ HilbertVec.ofVec (fun j ↦ HU.hess i j x)) =ᵐ[
        MeasureTheory.volume.restrict
          (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ))]
      fun x ↦ HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField
          (originCube d m) i (fun y j ↦ Hsrc.hess i j y) x) := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let U : Set (Vec d) := scaledOpenCubeSet Qp (1 / 2 : ℝ)
  let reflectedRow : Vec d → Vec d :=
    cubeDirichletOddReflectionHessianRowVectorField Q i
      (fun y j ↦ Hsrc.hess i j y)
  have hUopen : IsOpen U :=
    (isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Qp
      (by norm_num : 0 < (1 / 2 : ℝ))).isOpen
  have hUparent : U ⊆ openCubeSet Qp := by
    intro x hx
    apply scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Qp
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
    intro j
    exact le_of_lt (hx j)
  have hscalar :
      (fun x ↦ uU.grad x i) =
        cubeDirichletOddReflectionGradientCoordScalar Q i
          (fun y ↦ u.grad y i) := by
    funext x
    have hx := congrArg (fun G : Vec d → Vec d ↦ G x i)
      (huU_grad.trans huP_grad)
    change
      uU.grad x i =
        cubeDirichletOddReflectionVectorField Q (fun y ↦ u.grad y) x i
      at hx
    rw [hx]
    simp only [cubeDirichletOddReflectionVectorField,
      cubeCoordinateFoldReflectedVectorField, Pi.smul_apply, smul_eq_mul,
      cubeDirichletOddReflectionGradientCoordScalar]
    ring
  have hcoordCell : ∀ (choice : Fin d → Fin 3) (j : Fin d),
      (fun x ↦ HU.hess i j x) =ᵐ[
          MeasureTheory.volume.restrict
            (U ∩ openCubeSet (cubeFaceReflectionCellCube Q choice))]
        fun x ↦ reflectedRow x j := by
    intro choice j
    let cell : Set (Vec d) :=
      openCubeSet (cubeFaceReflectionCellCube Q choice)
    let V : Set (Vec d) := U ∩ cell
    have hcellOpen : IsOpen cell :=
      isOpen_openCubeSet (cubeFaceReflectionCellCube Q choice)
    have hVopen : IsOpen V := hUopen.inter hcellOpen
    have hactual :
        HasWeakPartialDerivOn V j
          (cubeDirichletOddReflectionGradientCoordScalar Q i
            (fun y ↦ u.grad y i))
          (fun x ↦ HU.hess i j x) := by
      have hweak := (HU.weak_second i j).restrict hVopen Set.inter_subset_left
      rw [hscalar] at hweak
      exact hweak
    have hreflected :
        HasWeakPartialDerivOn V j
          (cubeDirichletOddReflectionGradientCoordScalar Q i
            (fun y ↦ u.grad y i))
          (fun x ↦ reflectedRow x j) := by
      have hweak :=
        (Hsrc.cubeDirichletOddReflectionGradientCoord_hasWeakGradientOn_cell
          choice i j).restrict hVopen Set.inter_subset_right
      simpa only [reflectedRow] using hweak
    have hactualLoc : MeasureTheory.LocallyIntegrableOn
        (fun x ↦ HU.hess i j x) V MeasureTheory.volume :=
      (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
        ((HU.hess_memL2 i j).locallyIntegrable (by norm_num))).mono_set
          Set.inter_subset_left
    rcases
      Hsrc.cubeDirichletOddReflectionHessianRowVectorField_isPotentialOn_cell
        choice i with ⟨w, hw⟩
    have hreflectedLocCell : MeasureTheory.LocallyIntegrableOn
        (fun x ↦ reflectedRow x j) cell MeasureTheory.volume := by
      have hwLoc :=
        MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
          ((w.gradMemL2 j).locallyIntegrable (by norm_num))
      simpa only [hw, reflectedRow] using hwLoc
    have hreflectedLoc : MeasureTheory.LocallyIntegrableOn
        (fun x ↦ reflectedRow x j) V MeasureTheory.volume :=
      hreflectedLocCell.mono_set Set.inter_subset_right
    simpa only [V, cell] using
      HasWeakPartialDerivOn.ae_eq hVopen hactualLoc hreflectedLoc
        hactual hreflected
  have hcoord : ∀ j : Fin d,
      (fun x ↦ HU.hess i j x) =ᵐ[MeasureTheory.volume.restrict U]
        fun x ↦ reflectedRow x j := by
    intro j
    have hcells : ∀ᵐ x ∂MeasureTheory.volume,
        ∀ choice : Fin d → Fin 3,
          x ∈ U ∩ openCubeSet (cubeFaceReflectionCellCube Q choice) →
            HU.hess i j x = reflectedRow x j := by
      rw [Filter.eventually_all]
      intro choice
      have h := hcoordCell choice j
      rw [Filter.EventuallyEq,
        MeasureTheory.ae_restrict_iff'
          (hUopen.measurableSet.inter
            (measurableSet_openCubeSet
              (cubeFaceReflectionCellCube Q choice)))] at h
      exact h
    have hcover : ∀ᵐ x ∂MeasureTheory.volume,
        x ∈ U →
          ∃ choice : Fin d → Fin 3,
            x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice) := by
      filter_upwards
        [cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m]
        with x hx xU
      have xParent : x ∈ openCubeSet Qp := hUparent xU
      have xBlock : x ∈ cubeFaceReflectionBlockSet Q := by
        exact hx.mpr xParent
      rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q] at xBlock
      exact Set.mem_iUnion.mp xBlock
    rw [Filter.EventuallyEq,
      MeasureTheory.ae_restrict_iff' hUopen.measurableSet]
    filter_upwards [hcells, hcover] with x hxcells hxcover xU
    rcases hxcover xU with ⟨choice, hxcell⟩
    exact hxcells choice ⟨xU, hxcell⟩
  change
    (fun x ↦ HilbertVec.ofVec (fun j ↦ HU.hess i j x)) =ᵐ[
        MeasureTheory.volume.restrict U]
      fun x ↦ HilbertVec.ofVec (reflectedRow x)
  have hcoords : ∀ᵐ x ∂MeasureTheory.volume.restrict U,
      ∀ j : Fin d, HU.hess i j x = reflectedRow x j := by
    rw [Filter.eventually_all]
    exact hcoord
  filter_upwards [hcoords] with x hx
  apply HilbertVec.ext
  intro j
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hx j

end HasWeakHessianOn

end

end Homogenization
