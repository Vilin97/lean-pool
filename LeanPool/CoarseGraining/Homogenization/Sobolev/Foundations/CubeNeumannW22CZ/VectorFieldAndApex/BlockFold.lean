/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.Definitions
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.MemL2AndPairings
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.VectorFieldAndApex.WeakEquationHelpers

/-! # Block Fold -/

namespace Homogenization

open scoped ENNReal

noncomputable section


namespace H1Function

/-- Precompose an `H¹` function on the original cube with one affine
reflection-cell fold. On that cell, the weak gradient is the corresponding
linear sign fold of the original weak gradient. -/
noncomputable def cubeFaceReflectionCellFold {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) (choice : Fin d → Fin 3) :
    H1Function (openCubeSet (cubeFaceReflectionCellCube Q choice)) := by
  let cell : Set (Vec d) := openCubeSet (cubeFaceReflectionCellCube Q choice)
  let T : Vec d → Vec d := cubeFaceReflectionCellFoldMap Q choice
  let L : Vec d →L[ℝ] Vec d := cubeFaceReflectionCellFoldLinear choice
  have hmp :=
    (measurePreserving_cubeFaceReflectionCellFoldMap Q choice).restrict_preimage_emb
      (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
      (openCubeSet Q)
  refine
    { toFun := fun x => u (T x)
      grad := fun x => L (u.grad (T x))
      memL2 := ?_
      gradMemL2 := ?_
      hasWeakGradient := ?_ }
  · have hcomp' := u.memL2.comp_measurePreserving hmp
    simpa [MemL2On, volumeMeasureOn,
      preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice,
      Function.comp_def, cell, T] using hcomp'
  · intro i
    have hcomp :
        MeasureTheory.MemLp (fun x => u.grad (T x))
          (2 : ℝ≥0∞) (MeasureTheory.volume.restrict cell) := by
      have hcomp' := u.grad_memVectorL2.comp_measurePreserving hmp
      simpa [MemVectorL2, volumeMeasureOn,
        preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice,
        Function.comp_def, cell, T] using hcomp'
    have hfold :
        MeasureTheory.MemLp (fun x => L (u.grad (T x)))
          (2 : ℝ≥0∞) (MeasureTheory.volume.restrict cell) := by
      simpa [Function.comp_def] using L.comp_memLp' hcomp
    have hfoldVector : MemVectorL2 cell (fun x => L (u.grad (T x))) := by
      simpa [MemVectorL2, volumeMeasureOn] using hfold
    simpa [MemL2On, MemScalarL2, volumeMeasureOn, cell, T, L] using
      memScalarL2_coord_of_memVectorL2 hfoldVector i
  · intro i φ hφ hφ_supp hφ_sub
    let ψ : Vec d → ℝ := fun y => φ (T y)
    have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
      simpa [ψ, T] using
        contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ
    have hψ_supp : HasCompactSupport ψ := by
      simpa [ψ, T] using
        hasCompactSupport_comp_cubeFaceReflectionCellFoldMap Q choice hφ_supp
    have hψ_sub : tsupport ψ ⊆ openCubeSet Q := by
      intro y hy
      have hTy : T y ∈ tsupport φ := by
        rw [show ψ = φ ∘ cubeFaceReflectionCellFoldHomeomorph Q choice by
          rfl, tsupport_comp_eq_preimage φ
            (cubeFaceReflectionCellFoldHomeomorph Q choice)] at hy
        exact hy
      have hTy_cell : T y ∈ cell := hφ_sub hTy
      have hpre :
          T y ∈ T ⁻¹' openCubeSet Q := by
        simpa [T, cell,
          preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice] using hTy_cell
      simpa [T, cubeFaceReflectionCellFoldMap_involutive Q choice y] using hpre
    have hweak := u.hasWeakGradient i ψ hψ_smooth hψ_supp hψ_sub
    have hweak_coord :
        ∫ x in openCubeSet Q, u x * euclideanCoordDeriv i ψ x
            ∂MeasureTheory.volume =
          -∫ x in openCubeSet Q, u.grad x i * ψ x
            ∂MeasureTheory.volume := by
      simpa [euclideanCoordDeriv] using hweak
    have hleft_change :
        ∫ x in cell, u (T x) * euclideanCoordDeriv i φ x
            ∂MeasureTheory.volume =
          ∫ y in openCubeSet Q,
            u y * euclideanCoordDeriv i φ (T y) ∂MeasureTheory.volume := by
      let g : Vec d → ℝ := fun y => u y * euclideanCoordDeriv i φ (T y)
      calc
        ∫ x in cell, u (T x) * euclideanCoordDeriv i φ x
            ∂MeasureTheory.volume =
          ∫ x in cell, g (T x) ∂MeasureTheory.volume := by
            refine MeasureTheory.setIntegral_congr_fun
              (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
            intro x _hx
            simp [g, T, cubeFaceReflectionCellFoldMap_involutive Q choice x]
        _ = ∫ y in openCubeSet Q, g y ∂MeasureTheory.volume := by
            simpa [cell, T, g] using
              setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap
                Q choice g
    have hright_change :
        ∫ x in cell, (L (u.grad (T x))) i * φ x
            ∂MeasureTheory.volume =
          ∫ y in openCubeSet Q, (L (u.grad y)) i * ψ y
            ∂MeasureTheory.volume := by
      let g : Vec d → ℝ := fun y => (L (u.grad y)) i * ψ y
      calc
        ∫ x in cell, (L (u.grad (T x))) i * φ x
            ∂MeasureTheory.volume =
          ∫ x in cell, g (T x) ∂MeasureTheory.volume := by
            refine MeasureTheory.setIntegral_congr_fun
              (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
            intro x _hx
            simp [g, ψ, T, cubeFaceReflectionCellFoldMap_involutive Q choice x]
        _ = ∫ y in openCubeSet Q, g y ∂MeasureTheory.volume := by
            simpa [cell, T, g] using
              setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap
                Q choice g
    have hderiv :
        ∀ y,
          euclideanCoordDeriv i ψ y =
            (if choice i = 1 then (1 : ℝ) else -1) *
              euclideanCoordDeriv i φ (T y) := by
      intro y
      have hgrad :=
        congrFun
          (euclideanGradient_comp_cubeFaceReflectionCellFoldMap
            hφ Q choice y) i
      simpa [ψ, T, L, euclideanGradient, euclideanCoordDeriv] using hgrad
    change
      ∫ x in cell, u (T x) * euclideanCoordDeriv i φ x
          ∂MeasureTheory.volume =
        -∫ x in cell, (L (u.grad (T x))) i * φ x
          ∂MeasureTheory.volume
    rw [hleft_change, hright_change]
    by_cases h1 : choice i = 1
    · have hleft :
          ∫ y in openCubeSet Q,
              u y * euclideanCoordDeriv i φ (T y) ∂MeasureTheory.volume =
            ∫ y in openCubeSet Q,
              u y * euclideanCoordDeriv i ψ y ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet Q) ?_
          intro y _hy
          have hy := hderiv y
          simp [h1] at hy
          have hy' :
              euclideanCoordDeriv i φ (T y) =
                euclideanCoordDeriv i ψ y := hy.symm
          simp [hy']
      have hright :
          ∫ y in openCubeSet Q, (L (u.grad y)) i * ψ y
              ∂MeasureTheory.volume =
            ∫ y in openCubeSet Q, u.grad y i * ψ y
              ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet Q) ?_
          intro y _hy
          simp [L, h1]
      rw [hleft, hright]
      simpa using hweak_coord
    · have hleft :
          ∫ y in openCubeSet Q,
              u y * euclideanCoordDeriv i φ (T y) ∂MeasureTheory.volume =
            -∫ y in openCubeSet Q,
              u y * euclideanCoordDeriv i ψ y ∂MeasureTheory.volume := by
          rw [← MeasureTheory.integral_neg]
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet Q) ?_
          intro y _hy
          have hy := hderiv y
          simp [h1] at hy
          have hy' :
              euclideanCoordDeriv i φ (T y) =
                -euclideanCoordDeriv i ψ y := by
            linarith
          change u y * euclideanCoordDeriv i φ (T y) =
            -(u y * euclideanCoordDeriv i ψ y)
          rw [hy']
          ring
      have hright :
          ∫ y in openCubeSet Q, (L (u.grad y)) i * ψ y
              ∂MeasureTheory.volume =
            -∫ y in openCubeSet Q, u.grad y i * ψ y
              ∂MeasureTheory.volume := by
          rw [← MeasureTheory.integral_neg]
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet Q) ?_
          intro y _hy
          simp [L, h1]
      rw [hleft, hright]
      linarith [hweak_coord]

@[simp] theorem cubeFaceReflectionCellFold_toFun {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) (choice : Fin d → Fin 3) (x : Vec d) :
    (u.cubeFaceReflectionCellFold choice).toFun x =
      u.toFun (cubeFaceReflectionCellFoldMap Q choice x) :=
  rfl

@[simp] theorem cubeFaceReflectionCellFold_grad {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) (choice : Fin d → Fin 3) (x : Vec d) :
    (u.cubeFaceReflectionCellFold choice).grad x =
      cubeFaceReflectionCellFoldLinear choice
        (u.grad (cubeFaceReflectionCellFoldMap Q choice x)) :=
  rfl

theorem cubeFaceReflectionCellFold_isPotentialOn {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) (choice : Fin d → Fin 3) :
    IsPotentialOn (openCubeSet (cubeFaceReflectionCellCube Q choice))
      (fun x =>
        cubeFaceReflectionCellFoldLinear choice
          (u.grad (cubeFaceReflectionCellFoldMap Q choice x))) :=
  (u.cubeFaceReflectionCellFold choice).isPotentialOn

/-- On a reflection cell, the reflected vector field is the weak gradient of
the cell-folded potential, using the global reflected-vector representative. -/
theorem cubeFaceReflectionCellFold_isPotentialOn_reflectedVectorField
    {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) (choice : Fin d → Fin 3) :
    IsPotentialOn (openCubeSet (cubeFaceReflectionCellCube Q choice))
      (cubeCoordinateFoldReflectedVectorField Q (fun y => u.grad y)) := by
  refine IsPotentialOn.congr_ae ?_
    (u.cubeFaceReflectionCellFold_isPotentialOn choice)
  filter_upwards
    [MeasureTheory.ae_restrict_mem
      (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))]
    with x hx
  exact
    (cubeCoordinateFoldReflectedVectorField_eq_cellFoldLinear_of_mem_cellCube
      Q choice (fun y => u.grad y) hx).symm

/-- Single-cell weak-gradient identity for a test supported in the full
reflection block, localized to this cell by zero extension. The statement uses
the global reflected scalar/vector representatives, so it can be summed over
cells without further representative conversions. -/
theorem cubeFaceReflectionCellFold_weakGradient_of_tsupport_subset_block
    {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) (choice : Fin d → Fin 3)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ cubeFaceReflectionBlockSet Q)
    (i : Fin d) :
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        cubeCoordinateFoldReflectedScalar Q u.toFun x *
          euclideanCoordDeriv i φ x ∂MeasureTheory.volume =
      -∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        (cubeCoordinateFoldReflectedVectorField Q (fun y => u.grad y) x) i *
          φ x ∂MeasureTheory.volume := by
  let cell : Set (Vec d) := openCubeSet (cubeFaceReflectionCellCube Q choice)
  let φc : Vec d → ℝ := Set.indicator cell φ
  have hφc : ContDiff ℝ (⊤ : ℕ∞) φc := by
    simpa [φc, cell] using
      contDiff_indicator_cubeFaceReflectionCell_of_tsupport_subset_block
        Q choice hφ hφ_sub
  have hφcs : HasCompactSupport φc := by
    simpa [φc, cell] using
      hasCompactSupport_indicator_cubeFaceReflectionCell Q choice hφs
  have hφc_sub : tsupport φc ⊆ cell := by
    simpa [φc, cell] using
      tsupport_indicator_cubeFaceReflectionCell_subset Q choice hφ_sub
  have hweak :=
    (u.cubeFaceReflectionCellFold choice).hasWeakGradient
      i φc hφc hφcs hφc_sub
  have hleft :
      ∫ x in cell,
          cubeCoordinateFoldReflectedScalar Q u.toFun x *
            euclideanCoordDeriv i φ x ∂MeasureTheory.volume =
        ∫ x in cell,
          (u.cubeFaceReflectionCellFold choice) x *
            euclideanCoordDeriv i φc x ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
    intro x hx
    have hscalar :=
      cubeCoordinateFoldReflectedScalar_eq_cellFoldMap_of_mem_cellCube
        Q choice u.toFun hx
    have hderiv :
        euclideanCoordDeriv i φc x = euclideanCoordDeriv i φ x := by
      have heq :=
        eventuallyEq_indicator_cubeFaceReflectionCell_of_mem
          Q choice φ (by simpa [cell] using hx)
      unfold euclideanCoordDeriv
      rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq]
    change
      cubeCoordinateFoldReflectedScalar Q u.toFun x *
          euclideanCoordDeriv i φ x =
        u.toFun (cubeFaceReflectionCellFoldMap Q choice x) *
          euclideanCoordDeriv i φc x
    rw [hscalar, hderiv]
  have hright :
      ∫ x in cell,
          (cubeCoordinateFoldReflectedVectorField Q (fun y => u.grad y) x) i *
            φ x ∂MeasureTheory.volume =
        ∫ x in cell,
          (u.cubeFaceReflectionCellFold choice).grad x i *
            φc x ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
    intro x hx
    have hvec :=
      cubeCoordinateFoldReflectedVectorField_eq_cellFoldLinear_of_mem_cellCube
        Q choice (fun y => u.grad y) hx
    change
      (cubeCoordinateFoldReflectedVectorField Q (fun y => u.grad y) x) i *
          φ x =
        (cubeFaceReflectionCellFoldLinear choice
          (u.grad (cubeFaceReflectionCellFoldMap Q choice x))) i *
          φc x
    rw [hvec]
    simp [φc, cell, Set.indicator_of_mem hx]
  change
    ∫ x in cell,
        cubeCoordinateFoldReflectedScalar Q u.toFun x *
          euclideanCoordDeriv i φ x ∂MeasureTheory.volume =
      -∫ x in cell,
        (cubeCoordinateFoldReflectedVectorField Q (fun y => u.grad y) x) i *
          φ x ∂MeasureTheory.volume
  rw [hleft, hright]
  simpa [φc, euclideanCoordDeriv] using hweak

/-- Fold an `H¹` function on the original cube to the whole all-coordinate
reflection block. The scalar part is even-reflected by coordinate folding, and
the weak gradient is the corresponding reflected vector field. -/
noncomputable def cubeFaceReflectionBlockFold {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) :
    H1Function (cubeFaceReflectionBlockSet Q) := by
  let S : Set (Vec d) := cubeFaceReflectionBlockSet Q
  let uR : Vec d → ℝ := cubeCoordinateFoldReflectedScalar Q u.toFun
  let GR : Vec d → Vec d :=
    cubeCoordinateFoldReflectedVectorField Q (fun y => u.grad y)
  have huOpen : MemScalarL2 (openCubeSet Q) u.toFun := by
    simpa [MemScalarL2, volumeMeasureOn] using u.memL2
  have hGOpen : MemVectorL2 (openCubeSet Q) (fun y => u.grad y) := by
    simpa [MemVectorL2, volumeMeasureOn] using u.grad_memVectorL2
  have huR : MemScalarL2 S uR := by
    simpa [S, uR] using
      memScalarL2_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar
        Q huOpen
  have hGR : MemVectorL2 S GR := by
    simpa [S, GR] using
      memVectorL2_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField
        Q hGOpen
  refine
    { toFun := uR
      grad := GR
      memL2 := by
        simpa [MemScalarL2, MemL2On, volumeMeasureOn, S, uR] using huR
      gradMemL2 := by
        intro i
        simpa [MemScalarL2, MemL2On, volumeMeasureOn, S, GR] using
          memScalarL2_coord_of_memVectorL2 hGR i
      hasWeakGradient := ?_ }
  intro i φ hφ hφs hφ_sub
  let left : Vec d → ℝ := fun x => uR x * euclideanCoordDeriv i φ x
  let right : Vec d → ℝ := fun x => GR x i * φ x
  have hφL2 : MemScalarL2 S φ := by
    have hφ_cont : Continuous φ :=
      (hφ.differentiable (by simp)).continuous
    simpa [MemScalarL2, volumeMeasureOn, S] using
      (hφ_cont.memLp_of_hasCompactSupport hφs).restrict S
  have hDφL2 : MemScalarL2 S (euclideanCoordDeriv i φ) := by
    have hD_cont : Continuous (euclideanCoordDeriv i φ) :=
      (contDiff_euclideanCoordDeriv hφ i).continuous
    have hD_supp : HasCompactSupport (euclideanCoordDeriv i φ) :=
      hasCompactSupport_euclideanCoordDeriv hφs i
    simpa [MemScalarL2, volumeMeasureOn, S] using
      (hD_cont.memLp_of_hasCompactSupport hD_supp).restrict S
  have hGRi : MemScalarL2 S (fun x => GR x i) :=
    memScalarL2_coord_of_memVectorL2 hGR i
  have hleftS :
      MeasureTheory.Integrable left (MeasureTheory.volume.restrict S) := by
    simpa [left] using! huR.integrable_mul hDφL2
  have hrightS :
      MeasureTheory.Integrable right (MeasureTheory.volume.restrict S) := by
    simpa [right] using! hGRi.integrable_mul hφL2
  have hcell_subset :
      ∀ choice : Fin d → Fin 3,
        openCubeSet (cubeFaceReflectionCellCube Q choice) ⊆ S := by
    intro choice
    simpa [S, openCubeSet_cubeFaceReflectionCellCube] using
      cubeFaceReflectionCellSet_subset_cubeFaceReflectionBlockSet Q choice
  have hleftCellInt :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.Integrable left
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    intro choice
    exact hleftS.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
        (hcell_subset choice))
  have hrightCellInt :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.Integrable right
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    intro choice
    exact hrightS.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
        (hcell_subset choice))
  have hleftSplit :
      ∫ x in S, left x ∂MeasureTheory.volume =
        ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            left x ∂MeasureTheory.volume := by
    simpa [S] using
      setIntegral_cubeFaceReflectionBlockSet_cellCube Q left hleftCellInt
  have hrightSplit :
      ∫ x in S, right x ∂MeasureTheory.volume =
        ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            right x ∂MeasureTheory.volume := by
    simpa [S] using
      setIntegral_cubeFaceReflectionBlockSet_cellCube Q right hrightCellInt
  have hcell :
      ∀ choice : Fin d → Fin 3,
        ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            left x ∂MeasureTheory.volume =
          -∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            right x ∂MeasureTheory.volume := by
    intro choice
    simpa [left, right, uR, GR] using
      u.cubeFaceReflectionCellFold_weakGradient_of_tsupport_subset_block
        choice hφ hφs hφ_sub i
  change
    ∫ x in S, left x ∂MeasureTheory.volume =
      -∫ x in S, right x ∂MeasureTheory.volume
  calc
    ∫ x in S, left x ∂MeasureTheory.volume =
      ∑ choice : Fin d → Fin 3,
        ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
          left x ∂MeasureTheory.volume := hleftSplit
    _ = ∑ choice : Fin d → Fin 3,
        -∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
          right x ∂MeasureTheory.volume := by
          apply Finset.sum_congr rfl
          intro choice _hchoice
          exact hcell choice
    _ = -∑ choice : Fin d → Fin 3,
        ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
          right x ∂MeasureTheory.volume := by
          simp
    _ = -∫ x in S, right x ∂MeasureTheory.volume := by
          rw [hrightSplit]

@[simp] theorem cubeFaceReflectionBlockFold_toFun {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) (x : Vec d) :
    u.cubeFaceReflectionBlockFold.toFun x =
      cubeCoordinateFoldReflectedScalar Q u.toFun x :=
  rfl

@[simp] theorem cubeFaceReflectionBlockFold_grad {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) (x : Vec d) :
    u.cubeFaceReflectionBlockFold.grad x =
      cubeCoordinateFoldReflectedVectorField Q (fun y => u.grad y) x :=
  rfl

/-- The reflected vector field on the whole reflection block is a Sobolev
potential, witnessed by the block-folded scalar potential. -/
theorem cubeFaceReflectionBlockFold_isPotentialOn {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) :
    IsPotentialOn (cubeFaceReflectionBlockSet Q)
      (cubeCoordinateFoldReflectedVectorField Q (fun y => u.grad y)) :=
  u.cubeFaceReflectionBlockFold.isPotentialOn

end H1Function

end

end Homogenization
