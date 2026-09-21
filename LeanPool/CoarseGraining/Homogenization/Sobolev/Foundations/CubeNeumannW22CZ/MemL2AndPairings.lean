/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.Definitions

/-! # Mem L2And Pairings -/

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- The squared `L²` energy of the slab-reflected scalar on the
lower/original/upper face-neighbor slab is three copies of the original cube
energy. -/
theorem setIntegral_cubeFaceNeighborSlabSet_faceNeighborSlabReflectedScalar_sq
    {d : ℕ} {F : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    ∫ x in cubeFaceNeighborSlabSet Q i,
        faceNeighborSlabReflectedScalar Q i F x *
          faceNeighborSlabReflectedScalar Q i F x
        ∂MeasureTheory.volume =
      3 * ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume := by
  classical
  let L := openCubeSet (cubeLowerFaceNeighbor Q i)
  let M := openCubeSet Q
  let U := openCubeSet (cubeUpperFaceNeighbor Q i)
  let S := cubeFaceNeighborSlabSet Q i
  let f : Vec d → ℝ := fun x =>
    faceNeighborSlabReflectedScalar Q i F x *
      faceNeighborSlabReflectedScalar Q i F x
  have hSlab : MemScalarL2 S (faceNeighborSlabReflectedScalar Q i F) := by
    simpa [S, M] using
      memScalarL2_cubeFaceNeighborSlabSet_faceNeighborSlabReflectedScalar
        Q i hF
  have hfS :
      MeasureTheory.Integrable f (MeasureTheory.volume.restrict S) := by
    simpa [f] using! hSlab.integrable_mul hSlab
  have hLsub : L ⊆ S := by
    intro x hx
    exact Or.inl (Or.inl hx)
  have hMsub : M ⊆ S := by
    intro x hx
    exact Or.inl (Or.inr hx)
  have hUsub : U ⊆ S := by
    intro x hx
    exact Or.inr hx
  have hfL :
      MeasureTheory.Integrable f (MeasureTheory.volume.restrict L) :=
    hfS.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hLsub)
  have hfM :
      MeasureTheory.Integrable f (MeasureTheory.volume.restrict M) :=
    hfS.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hMsub)
  have hfU :
      MeasureTheory.Integrable f (MeasureTheory.volume.restrict U) :=
    hfS.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hUsub)
  have hsplit :=
    setIntegral_cubeFaceNeighborSlabSet Q i f hfL hfM hfU
  have hL_eq :
      ∫ x in L, f x ∂MeasureTheory.volume =
        ∫ x in L,
          F (cubeLowerFaceReflection Q i x) *
            F (cubeLowerFaceReflection Q i x) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i)) ?_
    intro x hx
    simpa [f, L] using
      congrArg (fun y => y * y)
        (faceNeighborSlabReflectedScalar_of_mem_lower Q i F
          (x := x) hx)
  have hM_eq :
      ∫ x in M, f x ∂MeasureTheory.volume =
        ∫ x in M, F x * F x ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet Q) ?_
    intro x hx
    simpa [f, M] using
      congrArg (fun y => y * y)
        (faceNeighborSlabReflectedScalar_of_mem_cube Q i F (x := x) hx)
  have hU_eq :
      ∫ x in U, f x ∂MeasureTheory.volume =
        ∫ x in U,
          F (cubeUpperFaceReflection Q i x) *
            F (cubeUpperFaceReflection Q i x) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i)) ?_
    intro x hx
    simpa [f, U] using
      congrArg (fun y => y * y)
        (faceNeighborSlabReflectedScalar_of_mem_upper Q i F
          (x := x) hx)
  calc
    ∫ x in cubeFaceNeighborSlabSet Q i,
        faceNeighborSlabReflectedScalar Q i F x *
          faceNeighborSlabReflectedScalar Q i F x
        ∂MeasureTheory.volume
        = ∫ x in L, f x ∂MeasureTheory.volume +
          ∫ x in M, f x ∂MeasureTheory.volume +
          ∫ x in U, f x ∂MeasureTheory.volume := by
            simpa [f, S, L, M, U] using hsplit
    _ = ∫ x in L,
          F (cubeLowerFaceReflection Q i x) *
            F (cubeLowerFaceReflection Q i x) ∂MeasureTheory.volume +
        ∫ x in M, F x * F x ∂MeasureTheory.volume +
        ∫ x in U,
          F (cubeUpperFaceReflection Q i x) *
            F (cubeUpperFaceReflection Q i x) ∂MeasureTheory.volume := by
          rw [hL_eq, hM_eq, hU_eq]
    _ = ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume +
        ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume +
        ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume := by
          rw [show
            (∫ x in L,
              F (cubeLowerFaceReflection Q i x) *
                F (cubeLowerFaceReflection Q i x) ∂MeasureTheory.volume) =
              ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume by
                simpa [L] using
                  setIntegral_cubeLowerFaceNeighbor_reflectedScalar_sq Q i]
          rw [show
            (∫ x in U,
              F (cubeUpperFaceReflection Q i x) *
                F (cubeUpperFaceReflection Q i x) ∂MeasureTheory.volume) =
              ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume by
                simpa [U] using
                  setIntegral_cubeUpperFaceNeighbor_reflectedScalar_sq Q i]
    _ = 3 * ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume := by
          ring

/-- The vector self-pairing energy of the slab-reflected field on the
lower/original/upper face-neighbor slab is three copies of the original cube
energy. -/
theorem setIntegral_cubeFaceNeighborSlabSet_faceNeighborSlabReflectedVectorField_self_pairing
    {d : ℕ} {G : Vec d → Vec d} (Q : TriadicCube d) (i : Fin d)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    ∫ x in cubeFaceNeighborSlabSet Q i,
        vecDot (faceNeighborSlabReflectedVectorField Q i G x)
          (faceNeighborSlabReflectedVectorField Q i G x)
        ∂MeasureTheory.volume =
      3 * ∫ y in openCubeSet Q, vecDot (G y) (G y)
          ∂MeasureTheory.volume := by
  classical
  let L := openCubeSet (cubeLowerFaceNeighbor Q i)
  let M := openCubeSet Q
  let U := openCubeSet (cubeUpperFaceNeighbor Q i)
  let S := cubeFaceNeighborSlabSet Q i
  let f : Vec d → ℝ := fun x =>
    vecDot (faceNeighborSlabReflectedVectorField Q i G x)
      (faceNeighborSlabReflectedVectorField Q i G x)
  have hSlab : MemVectorL2 S (faceNeighborSlabReflectedVectorField Q i G) := by
    simpa [S, M] using
      memVectorL2_cubeFaceNeighborSlabSet_faceNeighborSlabReflectedVectorField
        Q i hG
  have hfS :
      MeasureTheory.Integrable f (MeasureTheory.volume.restrict S) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, f] using
      integrableOn_vecDot_of_memVectorL2 (U := S) hSlab hSlab
  have hLsub : L ⊆ S := by
    intro x hx
    exact Or.inl (Or.inl hx)
  have hMsub : M ⊆ S := by
    intro x hx
    exact Or.inl (Or.inr hx)
  have hUsub : U ⊆ S := by
    intro x hx
    exact Or.inr hx
  have hfL :
      MeasureTheory.Integrable f (MeasureTheory.volume.restrict L) :=
    hfS.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hLsub)
  have hfM :
      MeasureTheory.Integrable f (MeasureTheory.volume.restrict M) :=
    hfS.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hMsub)
  have hfU :
      MeasureTheory.Integrable f (MeasureTheory.volume.restrict U) :=
    hfS.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hUsub)
  have hsplit :=
    setIntegral_cubeFaceNeighborSlabSet Q i f hfL hfM hfU
  have hL_eq :
      ∫ x in L, f x ∂MeasureTheory.volume =
        ∫ x in L,
          vecDot
            (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
            (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i)) ?_
    intro x hx
    simpa [f, L] using
      congrArg (fun v => vecDot v v)
        (faceNeighborSlabReflectedVectorField_of_mem_lower Q i G
          (x := x) hx)
  have hM_eq :
      ∫ x in M, f x ∂MeasureTheory.volume =
        ∫ x in M, vecDot (G x) (G x) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet Q) ?_
    intro x hx
    simpa [f, M] using
      congrArg (fun v => vecDot v v)
        (faceNeighborSlabReflectedVectorField_of_mem_cube Q i G
          (x := x) hx)
  have hU_eq :
      ∫ x in U, f x ∂MeasureTheory.volume =
        ∫ x in U,
          vecDot
            (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
            (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i)) ?_
    intro x hx
    simpa [f, U] using
      congrArg (fun v => vecDot v v)
        (faceNeighborSlabReflectedVectorField_of_mem_upper Q i G
          (x := x) hx)
  calc
    ∫ x in cubeFaceNeighborSlabSet Q i,
        vecDot (faceNeighborSlabReflectedVectorField Q i G x)
          (faceNeighborSlabReflectedVectorField Q i G x)
        ∂MeasureTheory.volume
        = ∫ x in L, f x ∂MeasureTheory.volume +
          ∫ x in M, f x ∂MeasureTheory.volume +
          ∫ x in U, f x ∂MeasureTheory.volume := by
            simpa [f, S, L, M, U] using hsplit
    _ = ∫ x in L,
          vecDot
            (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
            (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
          ∂MeasureTheory.volume +
        ∫ x in M, vecDot (G x) (G x) ∂MeasureTheory.volume +
        ∫ x in U,
          vecDot
            (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
            (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
          ∂MeasureTheory.volume := by
          rw [hL_eq, hM_eq, hU_eq]
    _ = ∫ x in openCubeSet Q, vecDot (G x) (G x) ∂MeasureTheory.volume +
        ∫ x in openCubeSet Q, vecDot (G x) (G x) ∂MeasureTheory.volume +
        ∫ x in openCubeSet Q, vecDot (G x) (G x) ∂MeasureTheory.volume := by
          rw [show
            (∫ x in L,
              vecDot
                (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
                (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
              ∂MeasureTheory.volume) =
              ∫ x in openCubeSet Q, vecDot (G x) (G x)
                ∂MeasureTheory.volume by
                simpa [L] using
                  setIntegral_cubeLowerFaceNeighbor_reflectedField_self_pairing
                    Q i]
          rw [show
            (∫ x in U,
              vecDot
                (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
                (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
              ∂MeasureTheory.volume) =
              ∫ x in openCubeSet Q, vecDot (G x) (G x)
                ∂MeasureTheory.volume by
                simpa [U] using
                  setIntegral_cubeUpperFaceNeighbor_reflectedField_self_pairing
                    Q i]
    _ = 3 * ∫ x in openCubeSet Q, vecDot (G x) (G x)
          ∂MeasureTheory.volume := by
          ring

/-- The squared `L²` energy of the all-coordinate reflected scalar on the full
reflection block is one copy of the original cube energy for each reflected
cell. This is the `MemScalarL2` wrapper around the geometric cell
change-of-variables theorem. -/
theorem setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_sq_of_memScalarL2
    {d : ℕ} {F : Vec d → ℝ} (Q : TriadicCube d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x *
          cubeCoordinateFoldReflectedScalar Q F x
        ∂MeasureTheory.volume =
      (Fintype.card (Fin d → Fin 3) : ℝ) *
        ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume := by
  exact
    setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_sq
      Q (by simpa [volumeMeasureOn] using! hF.integrable_mul hF)

/-- The squared `L²` energy of the all-coordinate reflected scalar on the full
reflection block, with the cell count normalized to `(3 : ℝ)^d`. -/
theorem setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_sq_of_memScalarL2_three_pow
    {d : ℕ} {F : Vec d → ℝ} (Q : TriadicCube d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x *
          cubeCoordinateFoldReflectedScalar Q F x
        ∂MeasureTheory.volume =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume := by
  rw [setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_sq_of_memScalarL2
      Q hF,
    real_card_cubeFaceReflectionChoices]

/-- The cross pairing of two all-coordinate reflected scalar fields on the
full reflection block is one copy of the original cube pairing for each
reflection cell. -/
theorem setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_mul_of_memScalarL2
    {d : ℕ} {F U : Vec d → ℝ} (Q : TriadicCube d)
    (hF : MemScalarL2 (openCubeSet Q) F)
    (hU : MemScalarL2 (openCubeSet Q) U) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x *
          cubeCoordinateFoldReflectedScalar Q U x
        ∂MeasureTheory.volume =
      (Fintype.card (Fin d → Fin 3) : ℝ) *
        ∫ y in openCubeSet Q, F y * U y ∂MeasureTheory.volume := by
  classical
  let f : Vec d → ℝ := fun x =>
    cubeCoordinateFoldReflectedScalar Q F x *
      cubeCoordinateFoldReflectedScalar Q U x
  have hbase :
      MeasureTheory.Integrable (fun y => F y * U y)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using! hF.integrable_mul hU
  have hfcell :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.Integrable f
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    intro choice
    have hcomp :
        MeasureTheory.Integrable
          (fun x =>
            F (cubeFaceReflectionCellFoldMap Q choice x) *
              U (cubeFaceReflectionCellFoldMap Q choice x))
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) :=
      integrable_cubeFaceReflectionCellCube_comp_cellFoldMap
        (Q := Q) (choice := choice) (g := fun y => F y * U y) hbase
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
          cubeCoordinateFoldReflectedScalar Q U x
        ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet Q, f x ∂MeasureTheory.volume := rfl
    _ = ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            f x ∂MeasureTheory.volume := by
          exact setIntegral_cubeFaceReflectionBlockSet_cellCube Q f hfcell
    _ = ∑ _choice : Fin d → Fin 3,
          ∫ y in openCubeSet Q, F y * U y ∂MeasureTheory.volume := by
          apply Finset.sum_congr rfl
          intro choice _hchoice
          calc
            ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
                f x ∂MeasureTheory.volume =
              ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
                F (cubeFaceReflectionCellFoldMap Q choice x) *
                  U (cubeFaceReflectionCellFoldMap Q choice x)
                ∂MeasureTheory.volume := by
                refine MeasureTheory.setIntegral_congr_fun
                  (measurableSet_openCubeSet
                    (cubeFaceReflectionCellCube Q choice)) ?_
                intro x hx
                simp [f, cubeCoordinateFoldReflectedScalar,
                  cubeCoordinateFold_eq_cubeFaceReflectionCellFoldMap_of_mem_cellCube
                    Q choice hx]
            _ = ∫ y in openCubeSet Q, F y * U y ∂MeasureTheory.volume := by
                simpa using
                  setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap
                    Q choice (fun y => F y * U y)
    _ = (Fintype.card (Fin d → Fin 3) : ℝ) *
        ∫ y in openCubeSet Q, F y * U y ∂MeasureTheory.volume := by
          simp

/-- The reflected scalar cross pairing on the full reflection block, with the
cell count normalized to `(3 : ℝ)^d`. -/
theorem setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_mul_of_memScalarL2_three_pow
    {d : ℕ} {F U : Vec d → ℝ} (Q : TriadicCube d)
    (hF : MemScalarL2 (openCubeSet Q) F)
    (hU : MemScalarL2 (openCubeSet Q) U) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x *
          cubeCoordinateFoldReflectedScalar Q U x
        ∂MeasureTheory.volume =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet Q, F y * U y ∂MeasureTheory.volume := by
  rw [setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_mul_of_memScalarL2
      Q hF hU,
    real_card_cubeFaceReflectionChoices]

/-- The all-coordinate reflected scalar forcing is `L²` on the full
reflection block whenever the original forcing is `L²` on `Q`. -/
theorem memScalarL2_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar
    {d : ℕ} {F : Vec d → ℝ} (Q : TriadicCube d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    MemScalarL2 (cubeFaceReflectionBlockSet Q)
      (cubeCoordinateFoldReflectedScalar Q F) := by
  classical
  let cell : (Fin d → Fin 3) → Set (Vec d) := fun choice =>
    openCubeSet (cubeFaceReflectionCellCube Q choice)
  have hcell :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.MemLp (cubeCoordinateFoldReflectedScalar Q F)
          (2 : ℝ≥0∞) (MeasureTheory.volume.restrict (cell choice)) := by
    intro choice
    have hmp :=
      (measurePreserving_cubeFaceReflectionCellFoldMap Q choice).restrict_preimage_emb
        (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
        (openCubeSet Q)
    have hcomp :
        MeasureTheory.MemLp
          (fun x => F (cubeFaceReflectionCellFoldMap Q choice x))
          (2 : ℝ≥0∞)
          (MeasureTheory.volume.restrict (cell choice)) := by
      have hcomp' := hF.comp_measurePreserving hmp
      simpa [MemScalarL2, volumeMeasureOn,
        preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice,
        Function.comp_def, cell] using hcomp'
    exact MeasureTheory.MemLp.ae_eq (by
      filter_upwards
        [MeasureTheory.ae_restrict_mem
          (measurableSet_openCubeSet
            (cubeFaceReflectionCellCube Q choice))]
        with x hx
      exact (cubeCoordinateFoldReflectedScalar_eq_cellFoldMap_of_mem_cellCube
        Q choice F hx).symm) hcomp
  have hae :
      MeasureTheory.AEStronglyMeasurable
        (cubeCoordinateFoldReflectedScalar Q F)
        (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
    rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
    exact MeasureTheory.AEStronglyMeasurable.iUnion fun choice => by
      simpa [cell] using (hcell choice).aestronglyMeasurable
  have hint :
      MeasureTheory.Integrable
        (fun x => ‖cubeCoordinateFoldReflectedScalar Q F x‖ ^ (2 : ℕ))
        (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
    rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
    exact MeasureTheory.integrableOn_finite_iUnion.2 fun choice => by
      have hsq :=
        (MeasureTheory.memLp_two_iff_integrable_sq_norm
          (hcell choice).aestronglyMeasurable).1 (hcell choice)
      simpa [MeasureTheory.IntegrableOn, cell] using hsq
  simpa [MemScalarL2, volumeMeasureOn] using
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hae).2 hint

/-- The block-indicator localization of the all-coordinate reflected scalar is
a global `L²` function. -/
theorem memLp_indicator_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar
    {d : ℕ} {F : Vec d → ℝ} (Q : TriadicCube d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    MeasureTheory.MemLp
      (Set.indicator (cubeFaceReflectionBlockSet Q)
        (cubeCoordinateFoldReflectedScalar Q F))
      (2 : ℝ≥0∞) MeasureTheory.volume := by
  rw [MeasureTheory.memLp_indicator_iff_restrict
    (measurableSet_cubeFaceReflectionBlockSet Q)]
  simpa [MemScalarL2, volumeMeasureOn] using
    memScalarL2_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar
      Q hF

/-- The global squared norm of the block-indicator reflected scalar is exactly
the `3^d` reflected copy count times the original cube scalar energy. -/
theorem integral_indicator_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_norm_sq
    {d : ℕ} {F : Vec d → ℝ} (Q : TriadicCube d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    ∫ x,
        ‖Set.indicator (cubeFaceReflectionBlockSet Q)
          (cubeCoordinateFoldReflectedScalar Q F) x‖ ^ (2 : ℝ)
        ∂MeasureTheory.volume =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume := by
  let S : Set (Vec d) := cubeFaceReflectionBlockSet Q
  let FR : Vec d → ℝ := cubeCoordinateFoldReflectedScalar Q F
  have hpoint :
      (fun x =>
        ‖Set.indicator S FR x‖ ^ (2 : ℝ)) =
        Set.indicator S (fun x => FR x * FR x) := by
    funext x
    by_cases hx : x ∈ S <;> simp [S, FR, hx, pow_two, Real.norm_eq_abs]
  calc
    ∫ x, ‖Set.indicator (cubeFaceReflectionBlockSet Q)
          (cubeCoordinateFoldReflectedScalar Q F) x‖ ^ (2 : ℝ)
        ∂MeasureTheory.volume
        = ∫ x, Set.indicator S (fun x => FR x * FR x) x
            ∂MeasureTheory.volume := by
            rw [hpoint]
    _ = ∫ x in S, FR x * FR x ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_indicator
            (measurableSet_cubeFaceReflectionBlockSet Q)]
    _ = (3 : ℝ) ^ d *
        ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume := by
          simpa [S, FR] using
            setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_sq_of_memScalarL2_three_pow
              Q hF

/-- The all-coordinate reflected vector field is `L²` on the full reflection
block whenever the original vector field is `L²` on `Q`. -/
theorem memVectorL2_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField
    {d : ℕ} {G : Vec d → Vec d} (Q : TriadicCube d)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    MemVectorL2 (cubeFaceReflectionBlockSet Q)
      (cubeCoordinateFoldReflectedVectorField Q G) := by
  classical
  let cell : (Fin d → Fin 3) → Set (Vec d) := fun choice =>
    openCubeSet (cubeFaceReflectionCellCube Q choice)
  have hcell :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.MemLp (cubeCoordinateFoldReflectedVectorField Q G)
          (2 : ℝ≥0∞) (MeasureTheory.volume.restrict (cell choice)) := by
    intro choice
    have hmp :=
      (measurePreserving_cubeFaceReflectionCellFoldMap Q choice).restrict_preimage_emb
        (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
        (openCubeSet Q)
    have hcomp :
        MeasureTheory.MemLp
          (fun x => G (cubeFaceReflectionCellFoldMap Q choice x))
          (2 : ℝ≥0∞)
          (MeasureTheory.volume.restrict (cell choice)) := by
      have hcomp' := hG.comp_measurePreserving hmp
      simpa [MemVectorL2, volumeMeasureOn,
        preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice,
        Function.comp_def, cell] using hcomp'
    have hfold :
        MeasureTheory.MemLp
          (fun x =>
            cubeFaceReflectionCellFoldLinear choice
              (G (cubeFaceReflectionCellFoldMap Q choice x)))
          (2 : ℝ≥0∞)
          (MeasureTheory.volume.restrict (cell choice)) := by
      simpa [Function.comp_def] using
        (cubeFaceReflectionCellFoldLinear choice).comp_memLp' hcomp
    exact MeasureTheory.MemLp.ae_eq (by
      filter_upwards
        [MeasureTheory.ae_restrict_mem
          (measurableSet_openCubeSet
            (cubeFaceReflectionCellCube Q choice))]
        with x hx
      exact (cubeCoordinateFoldReflectedVectorField_eq_cellFoldLinear_of_mem_cellCube
        Q choice G hx).symm) hfold
  have hae :
      MeasureTheory.AEStronglyMeasurable
        (cubeCoordinateFoldReflectedVectorField Q G)
        (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
    rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
    exact MeasureTheory.AEStronglyMeasurable.iUnion fun choice => by
      simpa [cell] using (hcell choice).aestronglyMeasurable
  have hint :
      MeasureTheory.Integrable
        (fun x => ‖cubeCoordinateFoldReflectedVectorField Q G x‖ ^ (2 : ℕ))
        (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
    rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
    exact MeasureTheory.integrableOn_finite_iUnion.2 fun choice => by
      have hsq :=
        (MeasureTheory.memLp_two_iff_integrable_sq_norm
          (hcell choice).aestronglyMeasurable).1 (hcell choice)
      simpa [MeasureTheory.IntegrableOn, cell] using hsq
  simpa [MemVectorL2, volumeMeasureOn] using
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hae).2 hint

/-- The block-indicator localization of the all-coordinate reflected vector
field is a global `L²` vector field. -/
theorem memLp_indicator_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField
    {d : ℕ} {G : Vec d → Vec d} (Q : TriadicCube d)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    MeasureTheory.MemLp
      (Set.indicator (cubeFaceReflectionBlockSet Q)
        (cubeCoordinateFoldReflectedVectorField Q G))
      (2 : ℝ≥0∞) MeasureTheory.volume := by
  rw [MeasureTheory.memLp_indicator_iff_restrict
    (measurableSet_cubeFaceReflectionBlockSet Q)]
  simpa [MemVectorL2, volumeMeasureOn] using
    memVectorL2_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField
      Q hG

/-- The vector self-pairing energy of the all-coordinate reflected vector
field on the full reflection block is one copy of the original cube energy for
each reflected cell. This is the `MemVectorL2` wrapper around the geometric
cell change-of-variables theorem. -/
theorem setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField_self_pairing_of_memVectorL2
    {d : ℕ} {G : Vec d → Vec d} (Q : TriadicCube d)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
          (cubeCoordinateFoldReflectedVectorField Q G x)
        ∂MeasureTheory.volume =
      (Fintype.card (Fin d → Fin 3) : ℝ) *
        ∫ y in openCubeSet Q, vecDot (G y) (G y)
          ∂MeasureTheory.volume := by
  have hInt :
      MeasureTheory.Integrable
        (fun y => vecDot (G y) (G y))
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      integrableOn_vecDot_of_memVectorL2
        (U := openCubeSet Q) hG hG
  exact
    setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField_self_pairing
      Q hInt

/-- The vector self-pairing energy of the all-coordinate reflected field on
the full reflection block, with the cell count normalized to `(3 : ℝ)^d`. -/
theorem setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField_self_pairing_of_memVectorL2_three_pow
    {d : ℕ} {G : Vec d → Vec d} (Q : TriadicCube d)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
          (cubeCoordinateFoldReflectedVectorField Q G x)
        ∂MeasureTheory.volume =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet Q, vecDot (G y) (G y)
          ∂MeasureTheory.volume := by
  rw [setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField_self_pairing_of_memVectorL2
      Q hG,
    real_card_cubeFaceReflectionChoices]

/-- The squared `L²` energy of the upper-face reflected scalar on the doubled
domain is two copies of the original cube energy. -/
theorem setIntegral_openCubeSet_union_upperFaceReflectedScalar_sq {d : ℕ}
    {F : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        upperFaceReflectedScalar Q i F x *
          upperFaceReflectedScalar Q i F x ∂MeasureTheory.volume =
      2 * ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume := by
  let R : Vec d → ℝ := fun x => F (cubeUpperFaceReflection Q i x)
  have hR : MemScalarL2 (openCubeSet (cubeUpperFaceNeighbor Q i)) R :=
    memScalarL2_cubeUpperFaceNeighbor_comp_reflection Q i hF
  have hQ :
      MeasureTheory.Integrable
        (fun x =>
          upperFaceReflectedScalar Q i F x *
            upperFaceReflectedScalar Q i F x)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    have hmain :
        MeasureTheory.Integrable
          (fun x => F x * F x)
          (MeasureTheory.volume.restrict (openCubeSet Q)) := by
      simpa using! hF.integrable_mul hF
    refine hmain.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    simp [upperFaceReflectedScalar, hx]
  have hN :
      MeasureTheory.Integrable
        (fun x =>
          upperFaceReflectedScalar Q i F x *
            upperFaceReflectedScalar Q i F x)
        (MeasureTheory.volume.restrict
          (openCubeSet (cubeUpperFaceNeighbor Q i))) := by
    have hreflected :
        MeasureTheory.Integrable
          (fun x => R x * R x)
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeUpperFaceNeighbor Q i))) := by
      simpa using! hR.integrable_mul hR
    refine hreflected.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i))] with x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact
        (Set.disjoint_left.mp
          (disjoint_openCubeSet_cubeUpperFaceNeighbor Q i) hxQ) hx
    simp [upperFaceReflectedScalar, hxQ, R]
  have hsplit :=
    setIntegral_openCubeSet_union_upperFaceNeighbor Q i
      (fun x =>
        upperFaceReflectedScalar Q i F x *
          upperFaceReflectedScalar Q i F x) hQ hN
  have hQeq :
      ∫ x in openCubeSet Q,
          upperFaceReflectedScalar Q i F x *
            upperFaceReflectedScalar Q i F x ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet Q) ?_
    intro x hx
    simp [upperFaceReflectedScalar, hx]
  have hNeq :
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
          upperFaceReflectedScalar Q i F x *
            upperFaceReflectedScalar Q i F x ∂MeasureTheory.volume =
        ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
          F (cubeUpperFaceReflection Q i x) *
            F (cubeUpperFaceReflection Q i x) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i)) ?_
    intro x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact
        (Set.disjoint_left.mp
          (disjoint_openCubeSet_cubeUpperFaceNeighbor Q i) hxQ) hx
    simp [upperFaceReflectedScalar, hxQ]
  calc
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        upperFaceReflectedScalar Q i F x *
          upperFaceReflectedScalar Q i F x ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            upperFaceReflectedScalar Q i F x *
              upperFaceReflectedScalar Q i F x ∂MeasureTheory.volume +
          ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
            upperFaceReflectedScalar Q i F x *
              upperFaceReflectedScalar Q i F x ∂MeasureTheory.volume := hsplit
    _ = ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume +
          ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
            F (cubeUpperFaceReflection Q i x) *
              F (cubeUpperFaceReflection Q i x) ∂MeasureTheory.volume := by
          rw [hQeq, hNeq]
    _ = ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume +
          ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume := by
          rw [setIntegral_cubeUpperFaceNeighbor_reflectedScalar_sq Q i]
    _ = 2 * ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume := by
          ring

/-- The squared `L²` energy of the lower-face reflected scalar on the doubled
domain is two copies of the original cube energy. -/
theorem setIntegral_openCubeSet_union_lowerFaceReflectedScalar_sq {d : ℕ}
    {F : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        lowerFaceReflectedScalar Q i F x *
          lowerFaceReflectedScalar Q i F x ∂MeasureTheory.volume =
      2 * ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume := by
  let R : Vec d → ℝ := fun x => F (cubeLowerFaceReflection Q i x)
  have hR : MemScalarL2 (openCubeSet (cubeLowerFaceNeighbor Q i)) R :=
    memScalarL2_cubeLowerFaceNeighbor_comp_reflection Q i hF
  have hQ :
      MeasureTheory.Integrable
        (fun x =>
          lowerFaceReflectedScalar Q i F x *
            lowerFaceReflectedScalar Q i F x)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    have hmain :
        MeasureTheory.Integrable
          (fun x => F x * F x)
          (MeasureTheory.volume.restrict (openCubeSet Q)) := by
      simpa using! hF.integrable_mul hF
    refine hmain.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    simp [lowerFaceReflectedScalar, hx]
  have hN :
      MeasureTheory.Integrable
        (fun x =>
          lowerFaceReflectedScalar Q i F x *
            lowerFaceReflectedScalar Q i F x)
        (MeasureTheory.volume.restrict
          (openCubeSet (cubeLowerFaceNeighbor Q i))) := by
    have hreflected :
        MeasureTheory.Integrable
          (fun x => R x * R x)
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeLowerFaceNeighbor Q i))) := by
      simpa using! hR.integrable_mul hR
    refine hreflected.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i))] with x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact
        (Set.disjoint_left.mp
          (disjoint_openCubeSet_cubeLowerFaceNeighbor Q i) hxQ) hx
    simp [lowerFaceReflectedScalar, hxQ, R]
  have hsplit :=
    setIntegral_openCubeSet_union_lowerFaceNeighbor Q i
      (fun x =>
        lowerFaceReflectedScalar Q i F x *
          lowerFaceReflectedScalar Q i F x) hQ hN
  have hQeq :
      ∫ x in openCubeSet Q,
          lowerFaceReflectedScalar Q i F x *
            lowerFaceReflectedScalar Q i F x ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet Q) ?_
    intro x hx
    simp [lowerFaceReflectedScalar, hx]
  have hNeq :
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
          lowerFaceReflectedScalar Q i F x *
            lowerFaceReflectedScalar Q i F x ∂MeasureTheory.volume =
        ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
          F (cubeLowerFaceReflection Q i x) *
            F (cubeLowerFaceReflection Q i x) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i)) ?_
    intro x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact
        (Set.disjoint_left.mp
          (disjoint_openCubeSet_cubeLowerFaceNeighbor Q i) hxQ) hx
    simp [lowerFaceReflectedScalar, hxQ]
  calc
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        lowerFaceReflectedScalar Q i F x *
          lowerFaceReflectedScalar Q i F x ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            lowerFaceReflectedScalar Q i F x *
              lowerFaceReflectedScalar Q i F x ∂MeasureTheory.volume +
          ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
            lowerFaceReflectedScalar Q i F x *
              lowerFaceReflectedScalar Q i F x ∂MeasureTheory.volume := hsplit
    _ = ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume +
          ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
            F (cubeLowerFaceReflection Q i x) *
              F (cubeLowerFaceReflection Q i x) ∂MeasureTheory.volume := by
          rw [hQeq, hNeq]
    _ = ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume +
          ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume := by
          rw [setIntegral_cubeLowerFaceNeighbor_reflectedScalar_sq Q i]
    _ = 2 * ∫ x in openCubeSet Q, F x * F x ∂MeasureTheory.volume := by
          ring

/-- The vector self-pairing energy of the upper-face reflected field on the
doubled domain is two copies of the original cube energy. -/
theorem setIntegral_openCubeSet_union_upperFaceReflectedVectorField_self_pairing
    {d : ℕ} {G : Vec d → Vec d} (Q : TriadicCube d) (i : Fin d)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot (upperFaceReflectedVectorField Q i G x)
          (upperFaceReflectedVectorField Q i G x) ∂MeasureTheory.volume =
      2 * ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂MeasureTheory.volume := by
  let R : Vec d → Vec d :=
    fun x => coordReflectionLinear i (G (cubeUpperFaceReflection Q i x))
  have hR : MemVectorL2 (openCubeSet (cubeUpperFaceNeighbor Q i)) R :=
    memVectorL2_cubeUpperFaceNeighbor_reflected Q i hG
  have hQ :
      MeasureTheory.Integrable
        (fun x =>
          vecDot (upperFaceReflectedVectorField Q i G x)
            (upperFaceReflectedVectorField Q i G x))
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    have hmain :
        MeasureTheory.IntegrableOn
          (fun x => vecDot (G x) (G x)) (openCubeSet Q) :=
      integrableOn_vecDot_of_memVectorL2 hG hG
    simpa [MeasureTheory.IntegrableOn] using
      hmain.congr_fun_ae (by
        filter_upwards
          [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
        simp [upperFaceReflectedVectorField, hx])
  have hN :
      MeasureTheory.Integrable
        (fun x =>
          vecDot (upperFaceReflectedVectorField Q i G x)
            (upperFaceReflectedVectorField Q i G x))
        (MeasureTheory.volume.restrict
          (openCubeSet (cubeUpperFaceNeighbor Q i))) := by
    have hreflected :
        MeasureTheory.IntegrableOn
          (fun x => vecDot (R x) (R x))
          (openCubeSet (cubeUpperFaceNeighbor Q i)) :=
      integrableOn_vecDot_of_memVectorL2 hR hR
    simpa [MeasureTheory.IntegrableOn] using
      hreflected.congr_fun_ae (by
        filter_upwards
          [MeasureTheory.ae_restrict_mem
            (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i))] with x hx
        have hxQ : x ∉ openCubeSet Q := by
          intro hxQ
          exact
            (Set.disjoint_left.mp
              (disjoint_openCubeSet_cubeUpperFaceNeighbor Q i) hxQ) hx
        simp [upperFaceReflectedVectorField, hxQ, R])
  have hsplit :=
    setIntegral_openCubeSet_union_upperFaceNeighbor Q i
      (fun x =>
        vecDot (upperFaceReflectedVectorField Q i G x)
          (upperFaceReflectedVectorField Q i G x)) hQ hN
  have hQeq :
      ∫ x in openCubeSet Q,
          vecDot (upperFaceReflectedVectorField Q i G x)
            (upperFaceReflectedVectorField Q i G x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q, vecDot (G x) (G x) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet Q) ?_
    intro x hx
    simp [upperFaceReflectedVectorField, hx]
  have hNeq :
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
          vecDot (upperFaceReflectedVectorField Q i G x)
            (upperFaceReflectedVectorField Q i G x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
          vecDot
            (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
            (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
            ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i)) ?_
    intro x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact
        (Set.disjoint_left.mp
          (disjoint_openCubeSet_cubeUpperFaceNeighbor Q i) hxQ) hx
    simp [upperFaceReflectedVectorField, hxQ]
  calc
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot (upperFaceReflectedVectorField Q i G x)
          (upperFaceReflectedVectorField Q i G x) ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            vecDot (upperFaceReflectedVectorField Q i G x)
              (upperFaceReflectedVectorField Q i G x) ∂MeasureTheory.volume +
          ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
            vecDot (upperFaceReflectedVectorField Q i G x)
              (upperFaceReflectedVectorField Q i G x) ∂MeasureTheory.volume := hsplit
    _ = ∫ x in openCubeSet Q, vecDot (G x) (G x) ∂MeasureTheory.volume +
          ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
            vecDot
              (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
              (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
              ∂MeasureTheory.volume := by
          rw [hQeq, hNeq]
    _ = ∫ x in openCubeSet Q, vecDot (G x) (G x) ∂MeasureTheory.volume +
          ∫ x in openCubeSet Q, vecDot (G x) (G x) ∂MeasureTheory.volume := by
          rw [setIntegral_cubeUpperFaceNeighbor_reflectedField_self_pairing Q i]
    _ = 2 * ∫ x in openCubeSet Q, vecDot (G x) (G x) ∂MeasureTheory.volume := by
          ring

/-- The vector self-pairing energy of the lower-face reflected field on the
doubled domain is two copies of the original cube energy. -/
theorem setIntegral_openCubeSet_union_lowerFaceReflectedVectorField_self_pairing
    {d : ℕ} {G : Vec d → Vec d} (Q : TriadicCube d) (i : Fin d)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot (lowerFaceReflectedVectorField Q i G x)
          (lowerFaceReflectedVectorField Q i G x) ∂MeasureTheory.volume =
      2 * ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂MeasureTheory.volume := by
  let R : Vec d → Vec d :=
    fun x => coordReflectionLinear i (G (cubeLowerFaceReflection Q i x))
  have hR : MemVectorL2 (openCubeSet (cubeLowerFaceNeighbor Q i)) R :=
    memVectorL2_cubeLowerFaceNeighbor_reflected Q i hG
  have hQ :
      MeasureTheory.Integrable
        (fun x =>
          vecDot (lowerFaceReflectedVectorField Q i G x)
            (lowerFaceReflectedVectorField Q i G x))
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    have hmain :
        MeasureTheory.IntegrableOn
          (fun x => vecDot (G x) (G x)) (openCubeSet Q) :=
      integrableOn_vecDot_of_memVectorL2 hG hG
    simpa [MeasureTheory.IntegrableOn] using
      hmain.congr_fun_ae (by
        filter_upwards
          [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
        simp [lowerFaceReflectedVectorField, hx])
  have hN :
      MeasureTheory.Integrable
        (fun x =>
          vecDot (lowerFaceReflectedVectorField Q i G x)
            (lowerFaceReflectedVectorField Q i G x))
        (MeasureTheory.volume.restrict
          (openCubeSet (cubeLowerFaceNeighbor Q i))) := by
    have hreflected :
        MeasureTheory.IntegrableOn
          (fun x => vecDot (R x) (R x))
          (openCubeSet (cubeLowerFaceNeighbor Q i)) :=
      integrableOn_vecDot_of_memVectorL2 hR hR
    simpa [MeasureTheory.IntegrableOn] using
      hreflected.congr_fun_ae (by
        filter_upwards
          [MeasureTheory.ae_restrict_mem
            (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i))] with x hx
        have hxQ : x ∉ openCubeSet Q := by
          intro hxQ
          exact
            (Set.disjoint_left.mp
              (disjoint_openCubeSet_cubeLowerFaceNeighbor Q i) hxQ) hx
        simp [lowerFaceReflectedVectorField, hxQ, R])
  have hsplit :=
    setIntegral_openCubeSet_union_lowerFaceNeighbor Q i
      (fun x =>
        vecDot (lowerFaceReflectedVectorField Q i G x)
          (lowerFaceReflectedVectorField Q i G x)) hQ hN
  have hQeq :
      ∫ x in openCubeSet Q,
          vecDot (lowerFaceReflectedVectorField Q i G x)
            (lowerFaceReflectedVectorField Q i G x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q, vecDot (G x) (G x) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet Q) ?_
    intro x hx
    simp [lowerFaceReflectedVectorField, hx]
  have hNeq :
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
          vecDot (lowerFaceReflectedVectorField Q i G x)
            (lowerFaceReflectedVectorField Q i G x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
          vecDot
            (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
            (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
            ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i)) ?_
    intro x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact
        (Set.disjoint_left.mp
          (disjoint_openCubeSet_cubeLowerFaceNeighbor Q i) hxQ) hx
    simp [lowerFaceReflectedVectorField, hxQ]
  calc
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot (lowerFaceReflectedVectorField Q i G x)
          (lowerFaceReflectedVectorField Q i G x) ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            vecDot (lowerFaceReflectedVectorField Q i G x)
              (lowerFaceReflectedVectorField Q i G x) ∂MeasureTheory.volume +
          ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
            vecDot (lowerFaceReflectedVectorField Q i G x)
              (lowerFaceReflectedVectorField Q i G x) ∂MeasureTheory.volume := hsplit
    _ = ∫ x in openCubeSet Q, vecDot (G x) (G x) ∂MeasureTheory.volume +
          ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
            vecDot
              (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
              (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
              ∂MeasureTheory.volume := by
          rw [hQeq, hNeq]
    _ = ∫ x in openCubeSet Q, vecDot (G x) (G x) ∂MeasureTheory.volume +
          ∫ x in openCubeSet Q, vecDot (G x) (G x) ∂MeasureTheory.volume := by
          rw [setIntegral_cubeLowerFaceNeighbor_reflectedField_self_pairing Q i]
    _ = 2 * ∫ x in openCubeSet Q, vecDot (G x) (G x) ∂MeasureTheory.volume := by
          ring

end

end Homogenization
