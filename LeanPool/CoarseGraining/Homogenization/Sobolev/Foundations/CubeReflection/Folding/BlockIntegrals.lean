/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Reflections
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Folding.BlockDecomposition

/-! # Block Integrals -/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

/-- On a reflection-block cell, the smooth cell-folded potential has gradient
given by the all-coordinate reflected vector field. -/
theorem euclideanGradient_comp_cubeFaceReflectionCellFoldMap_eq_reflectedVectorField
    {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (choice : Fin d → Fin 3) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    euclideanGradient
        (fun y => u (cubeFaceReflectionCellFoldMap Q choice y)) x =
      cubeCoordinateFoldReflectedVectorField Q (euclideanGradient u) x := by
  rw [euclideanGradient_comp_cubeFaceReflectionCellFoldMap hu Q choice x]
  rw [cubeCoordinateFoldReflectedVectorField_eq_cellFoldLinear_of_mem_cellCube
    Q choice (euclideanGradient u) hx]

/-- The Hessian-square energy of a smooth function precomposed with a
reflection-cell fold is one copy of the original cube Hessian-square energy. -/
theorem setIntegral_cubeFaceReflectionCellCube_sum_sq_secondDeriv_comp_cellFoldMap
    {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        (∑ k : Fin d, ∑ l : Fin d,
          (euclideanCoordSecondDeriv k l
            (fun y => u (cubeFaceReflectionCellFoldMap Q choice y)) x) ^ 2)
        ∂volume =
      ∫ y in openCubeSet Q,
        (∑ k : Fin d, ∑ l : Fin d,
          (euclideanCoordSecondDeriv k l u y) ^ 2) ∂volume := by
  calc
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        (∑ k : Fin d, ∑ l : Fin d,
          (euclideanCoordSecondDeriv k l
            (fun y => u (cubeFaceReflectionCellFoldMap Q choice y)) x) ^ 2)
        ∂volume =
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        (∑ k : Fin d, ∑ l : Fin d,
          (euclideanCoordSecondDeriv k l u
            (cubeFaceReflectionCellFoldMap Q choice x)) ^ 2)
        ∂volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
          intro x _hx
          exact sum_sq_euclideanCoordSecondDeriv_comp_cubeFaceReflectionCellFoldMap
            hu Q choice x
    _ = ∫ y in openCubeSet Q,
        (∑ k : Fin d, ∑ l : Fin d,
          (euclideanCoordSecondDeriv k l u y) ^ 2) ∂volume := by
          simpa using
            setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap
              Q choice
              (fun y =>
                ∑ k : Fin d, ∑ l : Fin d,
                  (euclideanCoordSecondDeriv k l u y) ^ 2)

/-- The Laplacian-square energy of a smooth function precomposed with a
reflection-cell fold is one copy of the original cube Laplacian-square energy. -/
theorem setIntegral_cubeFaceReflectionCellCube_laplacian_sq_comp_cellFoldMap
    {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        (euclideanCoordLaplacian
          (fun y => u (cubeFaceReflectionCellFoldMap Q choice y)) x) ^ 2
        ∂volume =
      ∫ y in openCubeSet Q, (euclideanCoordLaplacian u y) ^ 2
        ∂volume := by
  calc
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        (euclideanCoordLaplacian
          (fun y => u (cubeFaceReflectionCellFoldMap Q choice y)) x) ^ 2
        ∂volume =
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        (euclideanCoordLaplacian u
          (cubeFaceReflectionCellFoldMap Q choice x)) ^ 2
        ∂volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
          intro x _hx
          exact congrArg (fun z : ℝ => z ^ 2)
            (euclideanCoordLaplacian_comp_cubeFaceReflectionCellFoldMap
              hu Q choice x)
    _ = ∫ y in openCubeSet Q, (euclideanCoordLaplacian u y) ^ 2
        ∂volume := by
          simpa using
            setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap
              Q choice
              (fun y => (euclideanCoordLaplacian u y) ^ 2)

/-- The scalar square energy on any reflection-block cell is one copy of the
original cube energy. -/
theorem setIntegral_cubeFaceReflectionCellCube_cubeCoordinateFoldReflectedScalar_sq
    {d : ℕ} {F : Vec d → ℝ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        cubeCoordinateFoldReflectedScalar Q F x *
          cubeCoordinateFoldReflectedScalar Q F x ∂volume =
      ∫ y in openCubeSet Q, F y * F y ∂volume := by
  calc
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        cubeCoordinateFoldReflectedScalar Q F x *
          cubeCoordinateFoldReflectedScalar Q F x ∂volume
        =
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        F (cubeFaceReflectionCellFoldMap Q choice x) *
          F (cubeFaceReflectionCellFoldMap Q choice x) ∂volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
          intro x hx
          change
            cubeCoordinateFoldReflectedScalar Q F x *
                cubeCoordinateFoldReflectedScalar Q F x =
              F (cubeFaceReflectionCellFoldMap Q choice x) *
                F (cubeFaceReflectionCellFoldMap Q choice x)
          simp [cubeCoordinateFoldReflectedScalar,
            cubeCoordinateFold_eq_cubeFaceReflectionCellFoldMap_of_mem_cellCube
              Q choice hx]
    _ = ∫ y in openCubeSet Q, F y * F y ∂volume := by
          simpa using
            setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap
              Q choice (fun y => F y * F y)

/-- The vector self-pairing energy on any reflection-block cell is one copy
of the original cube energy. -/
theorem setIntegral_cubeFaceReflectionCellCube_cubeCoordinateFoldReflectedVectorField_self_pairing
    {d : ℕ} {G : Vec d → Vec d}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
          (cubeCoordinateFoldReflectedVectorField Q G x) ∂volume =
      ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂volume := by
  calc
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
          (cubeCoordinateFoldReflectedVectorField Q G x) ∂volume
        =
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        vecDot (G (cubeFaceReflectionCellFoldMap Q choice x))
          (G (cubeFaceReflectionCellFoldMap Q choice x)) ∂volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
          intro x hx
          change
            vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
                (cubeCoordinateFoldReflectedVectorField Q G x) =
              vecDot (G (cubeFaceReflectionCellFoldMap Q choice x))
                (G (cubeFaceReflectionCellFoldMap Q choice x))
          rw [vecDot_cubeCoordinateFoldReflectedVectorField_self,
            cubeCoordinateFold_eq_cubeFaceReflectionCellFoldMap_of_mem_cellCube
              Q choice hx]
    _ = ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂volume := by
          simpa using
            setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap
              Q choice (fun y => vecDot (G y) (G y))

/-- The scalar square energy on the full all-coordinate reflection block is
the sum of one identical copy over each reflection cell. -/
theorem setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_sq
    {d : ℕ} {F : Vec d → ℝ} (Q : TriadicCube d)
    (hF :
      MeasureTheory.Integrable
        (fun y => F y * F y) (volume.restrict (openCubeSet Q))) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x *
          cubeCoordinateFoldReflectedScalar Q F x ∂volume =
      (Fintype.card (Fin d → Fin 3) : ℝ) *
        ∫ y in openCubeSet Q, F y * F y ∂volume := by
  classical
  let f : Vec d → ℝ := fun x =>
    cubeCoordinateFoldReflectedScalar Q F x *
      cubeCoordinateFoldReflectedScalar Q F x
  have hfcell :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.Integrable f
          (volume.restrict (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    intro choice
    have hcomp :
        MeasureTheory.Integrable
          (fun x =>
            F (cubeFaceReflectionCellFoldMap Q choice x) *
              F (cubeFaceReflectionCellFoldMap Q choice x))
          (volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) :=
      integrable_cubeFaceReflectionCellCube_comp_cellFoldMap
        (Q := Q) (choice := choice) (g := fun y => F y * F y) hF
    refine hcomp.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))]
      with x hx
    simp [f, cubeCoordinateFoldReflectedScalar,
      cubeCoordinateFold_eq_cubeFaceReflectionCellFoldMap_of_mem_cellCube
        Q choice hx]
  calc
    ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x *
          cubeCoordinateFoldReflectedScalar Q F x ∂volume
        = ∫ x in cubeFaceReflectionBlockSet Q, f x ∂volume := rfl
    _ = ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            f x ∂volume := by
          exact setIntegral_cubeFaceReflectionBlockSet_cellCube Q f hfcell
    _ = ∑ _choice : Fin d → Fin 3,
          ∫ y in openCubeSet Q, F y * F y ∂volume := by
          apply Finset.sum_congr rfl
          intro choice _hchoice
          simpa [f] using
            setIntegral_cubeFaceReflectionCellCube_cubeCoordinateFoldReflectedScalar_sq
              Q choice
    _ = (Fintype.card (Fin d → Fin 3) : ℝ) *
        ∫ y in openCubeSet Q, F y * F y ∂volume := by
          simp

/-- The vector self-pairing energy on the full all-coordinate reflection block
is the sum of one identical copy over each reflection cell. -/
theorem setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField_self_pairing
    {d : ℕ} {G : Vec d → Vec d} (Q : TriadicCube d)
    (hG :
      MeasureTheory.Integrable
        (fun y => vecDot (G y) (G y))
        (volume.restrict (openCubeSet Q))) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
          (cubeCoordinateFoldReflectedVectorField Q G x) ∂volume =
      (Fintype.card (Fin d → Fin 3) : ℝ) *
        ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂volume := by
  classical
  let f : Vec d → ℝ := fun x =>
    vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
      (cubeCoordinateFoldReflectedVectorField Q G x)
  have hfcell :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.Integrable f
          (volume.restrict (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    intro choice
    have hcomp :
        MeasureTheory.Integrable
          (fun x =>
            vecDot (G (cubeFaceReflectionCellFoldMap Q choice x))
              (G (cubeFaceReflectionCellFoldMap Q choice x)))
          (volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) :=
      integrable_cubeFaceReflectionCellCube_comp_cellFoldMap
        (Q := Q) (choice := choice) (g := fun y => vecDot (G y) (G y)) hG
    refine hcomp.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))]
      with x hx
    change
      vecDot (G (cubeFaceReflectionCellFoldMap Q choice x))
          (G (cubeFaceReflectionCellFoldMap Q choice x)) =
        vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
          (cubeCoordinateFoldReflectedVectorField Q G x)
    rw [vecDot_cubeCoordinateFoldReflectedVectorField_self,
      cubeCoordinateFold_eq_cubeFaceReflectionCellFoldMap_of_mem_cellCube
        Q choice hx]
  calc
    ∫ x in cubeFaceReflectionBlockSet Q,
        vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
          (cubeCoordinateFoldReflectedVectorField Q G x) ∂volume
        = ∫ x in cubeFaceReflectionBlockSet Q, f x ∂volume := rfl
    _ = ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            f x ∂volume := by
          exact setIntegral_cubeFaceReflectionBlockSet_cellCube Q f hfcell
    _ = ∑ _choice : Fin d → Fin 3,
          ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂volume := by
          apply Finset.sum_congr rfl
          intro choice _hchoice
          simpa [f] using
            setIntegral_cubeFaceReflectionCellCube_cubeCoordinateFoldReflectedVectorField_self_pairing
              Q choice
    _ = (Fintype.card (Fin d → Fin 3) : ℝ) *
        ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂volume := by
          simp

/-- Set-integral split over the union of an open cube and its upper face
neighbor. -/
theorem setIntegral_openCubeSet_union_upperFaceNeighbor {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (i : Fin d) (f : Vec d → E)
    (hQ :
      MeasureTheory.Integrable f
        (volume.restrict (openCubeSet Q)))
    (hN :
      MeasureTheory.Integrable f
        (volume.restrict (openCubeSet (cubeUpperFaceNeighbor Q i)))) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        f x ∂volume =
      ∫ x in openCubeSet Q, f x ∂volume +
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i), f x ∂volume := by
  exact MeasureTheory.setIntegral_union
    (disjoint_openCubeSet_cubeUpperFaceNeighbor Q i)
    (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i)) hQ hN

/-- Set-integral split over the union of an open cube and its lower face
neighbor. -/
theorem setIntegral_openCubeSet_union_lowerFaceNeighbor {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (i : Fin d) (f : Vec d → E)
    (hQ :
      MeasureTheory.Integrable f
        (volume.restrict (openCubeSet Q)))
    (hN :
      MeasureTheory.Integrable f
        (volume.restrict (openCubeSet (cubeLowerFaceNeighbor Q i)))) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        f x ∂volume =
      ∫ x in openCubeSet Q, f x ∂volume +
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i), f x ∂volume := by
  exact MeasureTheory.setIntegral_union
    (disjoint_openCubeSet_cubeLowerFaceNeighbor Q i)
    (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i)) hQ hN

/-- Set-integral split over the lower/original/upper one-coordinate
face-neighbor slab. -/
theorem setIntegral_cubeFaceNeighborSlabSet {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (i : Fin d) (f : Vec d → E)
    (hL :
      MeasureTheory.Integrable f
        (volume.restrict (openCubeSet (cubeLowerFaceNeighbor Q i))))
    (hQ :
      MeasureTheory.Integrable f
        (volume.restrict (openCubeSet Q)))
    (hU :
      MeasureTheory.Integrable f
        (volume.restrict (openCubeSet (cubeUpperFaceNeighbor Q i)))) :
    ∫ x in cubeFaceNeighborSlabSet Q i, f x ∂volume =
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i), f x ∂volume +
      ∫ x in openCubeSet Q, f x ∂volume +
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i), f x ∂volume := by
  let L := openCubeSet (cubeLowerFaceNeighbor Q i)
  let M := openCubeSet Q
  let U := openCubeSet (cubeUpperFaceNeighbor Q i)
  have hLM_U : Disjoint (L ∪ M) U := by
    rw [Set.disjoint_left]
    intro x hxLM hxU
    rcases hxLM with hxL | hxM
    · exact
        (Set.disjoint_left.mp
          (disjoint_cubeLowerFaceNeighbor_cubeUpperFaceNeighbor Q i)
          hxL) hxU
    · exact
        (Set.disjoint_left.mp
          (disjoint_openCubeSet_cubeUpperFaceNeighbor Q i)
          hxM) hxU
  have hLM :
      MeasureTheory.Integrable f (volume.restrict (L ∪ M)) := by
    simpa [MeasureTheory.IntegrableOn, L, M] using
      (MeasureTheory.integrableOn_union.mpr ⟨hL, hQ⟩ :
        MeasureTheory.IntegrableOn f (L ∪ M) volume)
  have hsplitLM :
      ∫ x in L ∪ M, f x ∂volume =
        ∫ x in L, f x ∂volume + ∫ x in M, f x ∂volume := by
    exact MeasureTheory.setIntegral_union
      (disjoint_openCubeSet_cubeLowerFaceNeighbor Q i).symm
      (measurableSet_openCubeSet Q) hL hQ
  have hsplitAll :
      ∫ x in (L ∪ M) ∪ U, f x ∂volume =
        ∫ x in L ∪ M, f x ∂volume + ∫ x in U, f x ∂volume := by
    exact MeasureTheory.setIntegral_union hLM_U
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i)) hLM hU
  calc
    ∫ x in cubeFaceNeighborSlabSet Q i, f x ∂volume
        = ∫ x in (L ∪ M) ∪ U, f x ∂volume := by
          simp [cubeFaceNeighborSlabSet, L, M, U]
    _ = ∫ x in L ∪ M, f x ∂volume + ∫ x in U, f x ∂volume := hsplitAll
    _ = (∫ x in L, f x ∂volume + ∫ x in M, f x ∂volume) +
          ∫ x in U, f x ∂volume := by
          rw [hsplitLM]
    _ = ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i), f x ∂volume +
          ∫ x in openCubeSet Q, f x ∂volume +
          ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i), f x ∂volume := by
          simp [L, M, U]
end

end Homogenization
