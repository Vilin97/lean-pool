/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.OddReflection
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.MemL2AndPairings
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionGeometry

/-! # Reflection L2 -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

/-!
# `L²` control for odd reflected Dirichlet forcing

Odd reflection has the same squared magnitude as the unsigned coordinate-fold
reflection already used in the Neumann/CZ layer.  This file records the
scalar forcing consequences of that observation.
-/

/-- The all-coordinate odd reflected scalar is `L²` on the reflection block
whenever the original scalar is `L²` on the cube. -/
theorem memScalarL2_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar
    {d : ℕ} {F : Vec d → ℝ} (Q : TriadicCube d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    MemScalarL2 (cubeFaceReflectionBlockSet Q)
      (cubeDirichletOddReflectionScalar Q F) := by
  classical
  let cell : (Fin d → Fin 3) → Set (Vec d) := fun choice =>
    openCubeSet (cubeFaceReflectionCellCube Q choice)
  have hcell :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.MemLp (cubeDirichletOddReflectionScalar Q F)
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
    have hsign :
        MeasureTheory.MemLp
          (fun x =>
            cubeDirichletOddReflectionCellSign choice *
              F (cubeFaceReflectionCellFoldMap Q choice x))
          (2 : ℝ≥0∞)
          (MeasureTheory.volume.restrict (cell choice)) :=
      hcomp.const_mul (cubeDirichletOddReflectionCellSign choice)
    exact MeasureTheory.MemLp.ae_eq (by
      filter_upwards
        [MeasureTheory.ae_restrict_mem
          (measurableSet_openCubeSet
            (cubeFaceReflectionCellCube Q choice))]
        with x hx
      simpa [cubeDirichletOddReflectionCellScalar] using
        (cubeDirichletOddReflectionScalar_eq_cellScalar_of_mem_cellCube
          Q choice F hx).symm) hsign
  have hae :
      MeasureTheory.AEStronglyMeasurable
        (cubeDirichletOddReflectionScalar Q F)
        (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
    rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
    exact MeasureTheory.AEStronglyMeasurable.iUnion fun choice => by
      simpa [cell] using (hcell choice).aestronglyMeasurable
  have hint :
      MeasureTheory.Integrable
        (fun x => ‖cubeDirichletOddReflectionScalar Q F x‖ ^ (2 : ℕ))
        (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
    rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
    exact MeasureTheory.integrableOn_finite_iUnion.2 fun choice => by
      have hsq :=
        (MeasureTheory.memLp_two_iff_integrable_sq_norm
          (hcell choice).aestronglyMeasurable).1 (hcell choice)
      simpa [MeasureTheory.IntegrableOn, cell] using hsq
  simpa [MemScalarL2, volumeMeasureOn] using
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hae).2 hint

/-- The squared `L²` energy of the odd reflected scalar on the full reflection
block is one copy of the original cube energy for each reflection cell. -/
theorem setIntegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar_sq_of_memScalarL2
    {d : ℕ} {F : Vec d → ℝ} (Q : TriadicCube d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        cubeDirichletOddReflectionScalar Q F x *
          cubeDirichletOddReflectionScalar Q F x
        ∂MeasureTheory.volume =
      (Fintype.card (Fin d → Fin 3) : ℝ) *
        ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume := by
  calc
    ∫ x in cubeFaceReflectionBlockSet Q,
        cubeDirichletOddReflectionScalar Q F x *
          cubeDirichletOddReflectionScalar Q F x
        ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x *
          cubeCoordinateFoldReflectedScalar Q F x
        ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_cubeFaceReflectionBlockSet Q) ?_
          intro x _hx
          exact cubeDirichletOddReflectionScalar_mul_self Q F x
    _ = (Fintype.card (Fin d → Fin 3) : ℝ) *
        ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume := by
          exact
            setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_sq_of_memScalarL2
              Q hF

/-- The squared `L²` energy of the odd reflected scalar on the full reflection
block, with the cell count normalized to `(3 : ℝ)^d`. -/
theorem setIntegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar_sq_of_memScalarL2_three_pow
    {d : ℕ} {F : Vec d → ℝ} (Q : TriadicCube d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        cubeDirichletOddReflectionScalar Q F x *
          cubeDirichletOddReflectionScalar Q F x
        ∂MeasureTheory.volume =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume := by
  rw [setIntegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar_sq_of_memScalarL2
      Q hF,
    real_card_cubeFaceReflectionChoices]

/-- The odd reflected scalar forcing is `L²` on the centered parent cube. -/
theorem memScalarL2_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar
    {d : ℕ} {m : ℤ} {F : Vec d → ℝ}
    (hF : MemScalarL2 (openCubeSet (originCube d m)) F) :
    MemScalarL2 (openCubeSet (originCube d (m + 1)))
      (cubeDirichletOddReflectionScalar (originCube d m) F) := by
  have hblock :=
    memScalarL2_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar
      (originCube d m) hF
  have hmeasure :
      volumeMeasureOn (openCubeSet (originCube d (m + 1))) =
        volumeMeasureOn (cubeFaceReflectionBlockSet (originCube d m)) := by
    simpa [volumeMeasureOn] using
      MeasureTheory.Measure.restrict_congr_set
        (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm
  simpa [MemScalarL2, hmeasure] using hblock

/-- The all-coordinate odd reflected vector field is `L²` on the full
reflection block whenever the original vector field is `L²` on the cube. -/
theorem memVectorL2_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField
    {d : ℕ} {G : Vec d → Vec d} (Q : TriadicCube d)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    MemVectorL2 (cubeFaceReflectionBlockSet Q)
      (cubeDirichletOddReflectionVectorField Q G) := by
  classical
  let cell : (Fin d → Fin 3) → Set (Vec d) := fun choice =>
    openCubeSet (cubeFaceReflectionCellCube Q choice)
  have hcell :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.MemLp (cubeDirichletOddReflectionVectorField Q G)
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
            cubeDirichletOddReflectionCellSign choice •
              cubeFaceReflectionCellFoldLinear choice
                (G (cubeFaceReflectionCellFoldMap Q choice x)))
          (2 : ℝ≥0∞)
          (MeasureTheory.volume.restrict (cell choice)) := by
      have hlinear :
          MeasureTheory.MemLp
            (fun x =>
              cubeFaceReflectionCellFoldLinear choice
                (G (cubeFaceReflectionCellFoldMap Q choice x)))
            (2 : ℝ≥0∞)
            (MeasureTheory.volume.restrict (cell choice)) := by
        simpa [Function.comp_def] using
          (cubeFaceReflectionCellFoldLinear choice).comp_memLp' hcomp
      simpa [smul_eq_mul] using!
        hlinear.const_smul (cubeDirichletOddReflectionCellSign choice)
    exact MeasureTheory.MemLp.ae_eq (by
      filter_upwards
        [MeasureTheory.ae_restrict_mem
          (measurableSet_openCubeSet
            (cubeFaceReflectionCellCube Q choice))]
        with x hx
      simpa [cubeDirichletOddReflectionCellVectorField] using
        (cubeDirichletOddReflectionVectorField_eq_cellVectorField_of_mem_cellCube
          Q choice G hx).symm) hfold
  have hae :
      MeasureTheory.AEStronglyMeasurable
        (cubeDirichletOddReflectionVectorField Q G)
        (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
    rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
    exact MeasureTheory.AEStronglyMeasurable.iUnion fun choice => by
      simpa [cell] using (hcell choice).aestronglyMeasurable
  have hint :
      MeasureTheory.Integrable
        (fun x => ‖cubeDirichletOddReflectionVectorField Q G x‖ ^ (2 : ℕ))
        (MeasureTheory.volume.restrict (cubeFaceReflectionBlockSet Q)) := by
    rw [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q]
    exact MeasureTheory.integrableOn_finite_iUnion.2 fun choice => by
      have hsq :=
        (MeasureTheory.memLp_two_iff_integrable_sq_norm
          (hcell choice).aestronglyMeasurable).1 (hcell choice)
      simpa [MeasureTheory.IntegrableOn, cell] using hsq
  simpa [MemVectorL2, volumeMeasureOn] using
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hae).2 hint

/-- The odd reflected vector field is `L²` on the centered parent cube. -/
theorem memVectorL2_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField
    {d : ℕ} {m : ℤ} {G : Vec d → Vec d}
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G) :
    MemVectorL2 (openCubeSet (originCube d (m + 1)))
      (cubeDirichletOddReflectionVectorField (originCube d m) G) := by
  have hblock :=
    memVectorL2_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionVectorField
      (originCube d m) hG
  have hmeasure :
      volumeMeasureOn (openCubeSet (originCube d (m + 1))) =
        volumeMeasureOn (cubeFaceReflectionBlockSet (originCube d m)) := by
    simpa [volumeMeasureOn] using
      MeasureTheory.Measure.restrict_congr_set
        (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm
  simpa [MemVectorL2, hmeasure] using hblock

/-- Scalar odd-reflected energy on the centered parent cube is `3^d` copies
of the original cube energy. -/
theorem setIntegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar_sq_of_memScalarL2_three_pow
    {d : ℕ} {m : ℤ} {F : Vec d → ℝ}
    (hF : MemScalarL2 (openCubeSet (originCube d m)) F) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        cubeDirichletOddReflectionScalar (originCube d m) F x *
          cubeDirichletOddReflectionScalar (originCube d m) F x
        ∂MeasureTheory.volume =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet (originCube d m), F y * F y
          ∂MeasureTheory.volume := by
  rw [setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
    (m := m)
    (f := fun x =>
      cubeDirichletOddReflectionScalar (originCube d m) F x *
        cubeDirichletOddReflectionScalar (originCube d m) F x)]
  exact
    setIntegral_cubeFaceReflectionBlockSet_cubeDirichletOddReflectionScalar_sq_of_memScalarL2_three_pow
      (originCube d m) hF

/-- Vector odd-reflected energy on the centered parent cube is `3^d` copies
of the original cube energy. -/
theorem setIntegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_self_pairing_of_memVectorL2_three_pow
    {d : ℕ} {m : ℤ} {G : Vec d → Vec d}
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        vecDot
          (cubeDirichletOddReflectionVectorField (originCube d m) G x)
          (cubeDirichletOddReflectionVectorField (originCube d m) G x)
        ∂MeasureTheory.volume =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet (originCube d m), vecDot (G y) (G y)
          ∂MeasureTheory.volume := by
  rw [setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
    (m := m)
    (f := fun x =>
      vecDot
        (cubeDirichletOddReflectionVectorField (originCube d m) G x)
        (cubeDirichletOddReflectionVectorField (originCube d m) G x))]
  calc
    ∫ x in cubeFaceReflectionBlockSet (originCube d m),
        vecDot
          (cubeDirichletOddReflectionVectorField (originCube d m) G x)
          (cubeDirichletOddReflectionVectorField (originCube d m) G x)
        ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet (originCube d m),
        vecDot
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x)
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x)
        ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_cubeFaceReflectionBlockSet (originCube d m)) ?_
          intro x _hx
          exact cubeDirichletOddReflectionVectorField_self_pairing (originCube d m) G x
    _ =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet (originCube d m), vecDot (G y) (G y)
          ∂MeasureTheory.volume := by
          exact
            setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField_self_pairing_of_memVectorL2_three_pow
              (originCube d m) hG

end

end Homogenization
