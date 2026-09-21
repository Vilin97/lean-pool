/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.Definitions
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.FoldedAndWeakScalar
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.MemL2AndPairings
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.VectorFieldAndApex.ReflectedEqCellSlab

/-! # Block Global And Apex -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace MeanZeroNeumannPoissonSolution

variable {d : ℕ} {Q : TriadicCube d} {F : Vec d → ℝ}

/-- Compact-test weak equation on the full all-coordinate reflection block,
obtained by summing the single-cell weak equations over the finite `3^d`
cell decomposition. -/
theorem cubeFaceReflectionBlock_reflectedVectorField_weakEquationOnBlock_of_compactSupport
    (W : MeanZeroNeumannPoissonSolution Q F)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        vecDot
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x * φ x
          ∂MeasureTheory.volume := by
  classical
  let G : Vec d → Vec d := fun y => W.w.toH1Function.grad y
  let gradBlock : Vec d → ℝ := fun x =>
    vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
      (euclideanGradient φ x)
  let forceBlock : Vec d → ℝ := fun x =>
    cubeCoordinateFoldReflectedScalar Q F x * φ x
  have hGopen : MemVectorL2 (openCubeSet Q) G := by
    simpa [MemVectorL2, volumeMeasureOn, G] using
      W.w.toH1Function.grad_memVectorL2
  have hFopen : MemScalarL2 (openCubeSet Q) F := by
    simpa [MemScalarL2, volumeMeasureOn] using hF
  have hgradCellInt :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.Integrable gradBlock
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    intro choice
    let ψ : Vec d → ℝ :=
      fun y => φ (cubeFaceReflectionCellFoldMap Q choice y)
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
      simpa [ψ] using
        contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ
    have hψs : HasCompactSupport ψ := by
      simpa [ψ] using
        hasCompactSupport_comp_cubeFaceReflectionCellFoldMap Q choice hφs
    have hgradψ : MemVectorL2 (openCubeSet Q) (euclideanGradient ψ) :=
      memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hψ hψs
    have hbase :
        MeasureTheory.Integrable
          (fun y => vecDot (G y) (euclideanGradient ψ y))
          (MeasureTheory.volume.restrict (openCubeSet Q)) := by
      simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
        integrableOn_vecDot_of_memVectorL2
          (U := openCubeSet Q) hGopen hgradψ
    have hcomp :
        MeasureTheory.Integrable
          (fun x =>
            vecDot (G (cubeFaceReflectionCellFoldMap Q choice x))
              (euclideanGradient ψ
                (cubeFaceReflectionCellFoldMap Q choice x)))
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) :=
      integrable_cubeFaceReflectionCellCube_comp_cellFoldMap
        (Q := Q) (choice := choice)
        (g := fun y => vecDot (G y) (euclideanGradient ψ y)) hbase
    refine hcomp.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))]
      with x hx
    have hvec :=
      cubeCoordinateFoldReflectedVectorField_eq_cellFoldLinear_of_mem_cellCube
        Q choice G hx
    have hgradAtFold :
        euclideanGradient ψ (cubeFaceReflectionCellFoldMap Q choice x) =
          cubeFaceReflectionCellFoldLinear choice (euclideanGradient φ x) := by
      have hg :=
        euclideanGradient_comp_cubeFaceReflectionCellFoldMap
          hφ Q choice (cubeFaceReflectionCellFoldMap Q choice x)
      simpa [ψ, cubeFaceReflectionCellFoldMap_involutive Q choice x] using hg
    calc
      vecDot (G (cubeFaceReflectionCellFoldMap Q choice x))
          (euclideanGradient ψ
            (cubeFaceReflectionCellFoldMap Q choice x)) =
        vecDot (G (cubeFaceReflectionCellFoldMap Q choice x))
            (cubeFaceReflectionCellFoldLinear choice
              (euclideanGradient φ x)) := by
              rw [hgradAtFold]
      _ = vecDot
            (cubeFaceReflectionCellFoldLinear choice
              (G (cubeFaceReflectionCellFoldMap Q choice x)))
            (euclideanGradient φ x) := by
              exact
                (vecDot_cubeFaceReflectionCellFoldLinear_left
                  choice (G (cubeFaceReflectionCellFoldMap Q choice x))
                  (euclideanGradient φ x)).symm
      _ = gradBlock x := by
              simp [gradBlock, hvec]
  have hforceCellInt :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.Integrable forceBlock
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    intro choice
    let ψ : Vec d → ℝ :=
      fun y => φ (cubeFaceReflectionCellFoldMap Q choice y)
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
      simpa [ψ] using
        contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ
    have hψs : HasCompactSupport ψ := by
      simpa [ψ] using
        hasCompactSupport_comp_cubeFaceReflectionCellFoldMap Q choice hφs
    have hψL2 : MemScalarL2 (openCubeSet Q) ψ := by
      have hψ_cont : Continuous ψ :=
        (hψ.differentiable (by simp)).continuous
      simpa [MemScalarL2, volumeMeasureOn] using
        (hψ_cont.memLp_of_hasCompactSupport hψs).restrict (openCubeSet Q)
    have hbase :
        MeasureTheory.Integrable (fun y => F y * ψ y)
          (MeasureTheory.volume.restrict (openCubeSet Q)) :=
      hFopen.integrable_mul hψL2
    have hcomp :
        MeasureTheory.Integrable
          (fun x =>
            F (cubeFaceReflectionCellFoldMap Q choice x) *
              ψ (cubeFaceReflectionCellFoldMap Q choice x))
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) :=
      integrable_cubeFaceReflectionCellCube_comp_cellFoldMap
        (Q := Q) (choice := choice) (g := fun y => F y * ψ y) hbase
    refine hcomp.congr ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice))]
      with x hx
    have hscalar :=
      cubeCoordinateFoldReflectedScalar_eq_cellFoldMap_of_mem_cellCube
        Q choice F hx
    have hψfold :
        ψ (cubeFaceReflectionCellFoldMap Q choice x) = φ x := by
      simp [ψ, cubeFaceReflectionCellFoldMap_involutive Q choice x]
    change
      F (cubeFaceReflectionCellFoldMap Q choice x) *
          ψ (cubeFaceReflectionCellFoldMap Q choice x) =
        forceBlock x
    simp [forceBlock, hscalar, hψfold]
  have hgradSplit :
      ∫ x in cubeFaceReflectionBlockSet Q, gradBlock x
          ∂MeasureTheory.volume =
        ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            gradBlock x ∂MeasureTheory.volume :=
    setIntegral_cubeFaceReflectionBlockSet_cellCube Q gradBlock hgradCellInt
  have hforceSplit :
      ∫ x in cubeFaceReflectionBlockSet Q, forceBlock x
          ∂MeasureTheory.volume =
        ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            forceBlock x ∂MeasureTheory.volume :=
    setIntegral_cubeFaceReflectionBlockSet_cellCube Q forceBlock hforceCellInt
  have hcellEq :
      ∀ choice : Fin d → Fin 3,
        ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            gradBlock x ∂MeasureTheory.volume =
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            forceBlock x ∂MeasureTheory.volume := by
    intro choice
    simpa [gradBlock, forceBlock, G] using
      W.cubeFaceReflectionCell_reflectedVectorField_weakEquationOnCell_of_compactSupport
        choice hφ hφs hmean hF
  change
    ∫ x in cubeFaceReflectionBlockSet Q, gradBlock x
        ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet Q, forceBlock x
        ∂MeasureTheory.volume
  calc
    ∫ x in cubeFaceReflectionBlockSet Q, gradBlock x
        ∂MeasureTheory.volume =
      ∑ choice : Fin d → Fin 3,
        ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
          gradBlock x ∂MeasureTheory.volume := hgradSplit
    _ = ∑ choice : Fin d → Fin 3,
        ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
          forceBlock x ∂MeasureTheory.volume := by
          apply Finset.sum_congr rfl
          intro choice _hchoice
          exact hcellEq choice
    _ = ∫ x in cubeFaceReflectionBlockSet Q, forceBlock x
        ∂MeasureTheory.volume := hforceSplit.symm

/-- Compact-test weak equation on the full all-coordinate reflection block,
with the right-hand side given in the normalized cube `L²` measure used by the
endpoint interfaces. -/
theorem cubeFaceReflectionBlock_reflectedVectorField_weakEquationOnBlock_of_compactSupport_of_memLp_normalizedCubeMeasure
    (W : MeanZeroNeumannPoissonSolution Q F)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        vecDot
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x * φ x
          ∂MeasureTheory.volume := by
  have hFopen :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [MemL2On, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  exact
    W.cubeFaceReflectionBlock_reflectedVectorField_weakEquationOnBlock_of_compactSupport
      hφ hφs hmean hFopen

/-- Promote the reflected-block compact-test weak equation to a whole-space
weak equation when the chosen test has zero contribution off the reflected
block.

This is the interface used by the smooth Euclidean `-Δu` test: a mollified or
cutoff test supported inside the reflection block can be read as a global
compactly supported test on `ℝ^d`. -/
theorem cubeFaceReflectionBlock_reflectedVectorField_weakEquationOn_univ_of_compl_zero
    (W : MeanZeroNeumannPoissonSolution Q F)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgrad_zero :
      ∀ x, x ∉ cubeFaceReflectionBlockSet Q →
        vecDot
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) = 0)
    (hforce_zero :
      ∀ x, x ∉ cubeFaceReflectionBlockSet Q →
        cubeCoordinateFoldReflectedScalar Q F x * φ x = 0) :
    ∫ x,
        vecDot
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x,
        cubeCoordinateFoldReflectedScalar Q F x * φ x
          ∂MeasureTheory.volume := by
  let gradBlock : Vec d → ℝ := fun x =>
    vecDot
      (cubeCoordinateFoldReflectedVectorField Q
        (fun y => W.w.toH1Function.grad y) x)
      (euclideanGradient φ x)
  let forceBlock : Vec d → ℝ := fun x =>
    cubeCoordinateFoldReflectedScalar Q F x * φ x
  have hgrad_univ :
      ∫ x in cubeFaceReflectionBlockSet Q, gradBlock x ∂MeasureTheory.volume =
        ∫ x, gradBlock x ∂MeasureTheory.volume := by
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := cubeFaceReflectionBlockSet Q) (μ := MeasureTheory.volume)
      (f := gradBlock) (by simpa [gradBlock] using hgrad_zero)
  have hforce_univ :
      ∫ x in cubeFaceReflectionBlockSet Q, forceBlock x ∂MeasureTheory.volume =
        ∫ x, forceBlock x ∂MeasureTheory.volume := by
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := cubeFaceReflectionBlockSet Q) (μ := MeasureTheory.volume)
      (f := forceBlock) (by simpa [forceBlock] using hforce_zero)
  have hblock :
      ∫ x in cubeFaceReflectionBlockSet Q, gradBlock x
          ∂MeasureTheory.volume =
        ∫ x in cubeFaceReflectionBlockSet Q, forceBlock x
          ∂MeasureTheory.volume := by
    simpa [gradBlock, forceBlock] using
      W.cubeFaceReflectionBlock_reflectedVectorField_weakEquationOnBlock_of_compactSupport_of_memLp_normalizedCubeMeasure
        hφ hφs hmean hF
  calc
    ∫ x, gradBlock x ∂MeasureTheory.volume
        = ∫ x in cubeFaceReflectionBlockSet Q, gradBlock x
            ∂MeasureTheory.volume := hgrad_univ.symm
    _ = ∫ x in cubeFaceReflectionBlockSet Q, forceBlock x
            ∂MeasureTheory.volume := hblock
    _ = ∫ x, forceBlock x ∂MeasureTheory.volume := hforce_univ

/-- Whole-space reflected weak equation from pointwise zero of the test and
its Euclidean gradient off the reflection block. -/
theorem cubeFaceReflectionBlock_reflectedVectorField_weakEquationOn_univ_of_test_zero
    (W : MeanZeroNeumannPoissonSolution Q F)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hφ_zero :
      ∀ x, x ∉ cubeFaceReflectionBlockSet Q → φ x = 0)
    (hgradφ_zero :
      ∀ x, x ∉ cubeFaceReflectionBlockSet Q →
        euclideanGradient φ x = 0) :
    ∫ x,
        vecDot
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x,
        cubeCoordinateFoldReflectedScalar Q F x * φ x
          ∂MeasureTheory.volume := by
  exact
    W.cubeFaceReflectionBlock_reflectedVectorField_weakEquationOn_univ_of_compl_zero
      hφ hφs hmean hF
      (by
        intro x hx
        rw [hgradφ_zero x hx]
        simp [vecDot])
      (by
        intro x hx
        rw [hφ_zero x hx]
        simp)

/-- Whole-space reflected weak equation for compact smooth tests whose
topological support is contained in the reflection block. -/
theorem cubeFaceReflectionBlock_reflectedVectorField_weakEquationOn_univ_of_tsupport_subset
    (W : MeanZeroNeumannPoissonSolution Q F)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ cubeFaceReflectionBlockSet Q)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∫ x,
        vecDot
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x,
        cubeCoordinateFoldReflectedScalar Q F x * φ x
          ∂MeasureTheory.volume := by
  exact
    W.cubeFaceReflectionBlock_reflectedVectorField_weakEquationOn_univ_of_test_zero
      hφ hφs hmean hF
      (by
        intro x hx
        exact image_eq_zero_of_notMem_tsupport fun hxt => hx (hφ_sub hxt))
      (by
        intro x hx
        exact euclideanGradient_eq_zero_of_notMem_tsupport fun hxt => hx (hφ_sub hxt))

/-- Whole-space reflected weak equation with the reflected forcing localized by
the reflection-block indicator. This is the global forcing form used by
Euclidean `L²` estimates. -/
theorem cubeFaceReflectionBlock_reflectedVectorField_weakEquationOn_univ_indicator_of_tsupport_subset
    (W : MeanZeroNeumannPoissonSolution Q F)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ cubeFaceReflectionBlockSet Q)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∫ x,
        vecDot
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x,
        Set.indicator (cubeFaceReflectionBlockSet Q)
          (cubeCoordinateFoldReflectedScalar Q F) x * φ x
          ∂MeasureTheory.volume := by
  have hbase :=
    W.cubeFaceReflectionBlock_reflectedVectorField_weakEquationOn_univ_of_tsupport_subset
      hφ hφs hφ_sub hmean hF
  refine hbase.trans ?_
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ cubeFaceReflectionBlockSet Q
    · simp [hx]
    · have hxt : x ∉ tsupport φ := fun h => hx (hφ_sub h)
      simp [hx, image_eq_zero_of_notMem_tsupport hxt]

/-- The reflected Neumann gradient is `L²` on the full reflection block. -/
theorem cubeFaceReflectionBlock_reflectedGradient_memVectorL2
    (W : MeanZeroNeumannPoissonSolution Q F) :
    MemVectorL2 (cubeFaceReflectionBlockSet Q)
      (cubeCoordinateFoldReflectedVectorField Q
        (fun y => W.w.toH1Function.grad y)) := by
  have hGopen : MemVectorL2 (openCubeSet Q)
      (fun y => W.w.toH1Function.grad y) := by
    simpa [MemVectorL2, volumeMeasureOn] using
      W.w.toH1Function.grad_memVectorL2
  exact
    memVectorL2_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField
      Q hGopen

/-- The block-indicator localization of the reflected Neumann gradient is a
global `L²` vector field. -/
theorem cubeFaceReflectionBlock_reflectedGradient_indicator_memLp
    (W : MeanZeroNeumannPoissonSolution Q F) :
    MeasureTheory.MemLp
      (Set.indicator (cubeFaceReflectionBlockSet Q)
        (cubeCoordinateFoldReflectedVectorField Q
          (fun y => W.w.toH1Function.grad y)))
      (2 : ℝ≥0∞) MeasureTheory.volume := by
  have hGopen : MemVectorL2 (openCubeSet Q)
      (fun y => W.w.toH1Function.grad y) := by
    simpa [MemVectorL2, volumeMeasureOn] using
      W.w.toH1Function.grad_memVectorL2
  exact
    memLp_indicator_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField
      Q hGopen

/-- Global reflected weak equation packaged with the global `L²` forcing
witness needed by Euclidean estimates. -/
theorem cubeFaceReflectionBlock_reflectedVectorField_globalWeakEquationWithL2Forcing
    (W : MeanZeroNeumannPoissonSolution Q F)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp
        (Set.indicator (cubeFaceReflectionBlockSet Q)
          (cubeCoordinateFoldReflectedScalar Q F))
        (2 : ℝ≥0∞) MeasureTheory.volume ∧
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ cubeFaceReflectionBlockSet Q →
        ∫ x,
            vecDot
              (cubeCoordinateFoldReflectedVectorField Q
                (fun y => W.w.toH1Function.grad y) x)
              (euclideanGradient φ x) ∂MeasureTheory.volume =
          ∫ x,
            Set.indicator (cubeFaceReflectionBlockSet Q)
              (cubeCoordinateFoldReflectedScalar Q F) x * φ x
              ∂MeasureTheory.volume := by
  constructor
  · have hFopen : MemScalarL2 (openCubeSet Q) F := by
      simpa [MemScalarL2, volumeMeasureOn] using
        memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
    exact
      memLp_indicator_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar
        Q hFopen
  · intro φ hφ hφs hφ_sub
    exact
      W.cubeFaceReflectionBlock_reflectedVectorField_weakEquationOn_univ_indicator_of_tsupport_subset
        hφ hφs hφ_sub hmean hF

/-- Global reflected weak equation packaged with both global `L²` data: the
block-indicator reflected gradient and the block-indicator reflected forcing. -/
theorem cubeFaceReflectionBlock_reflectedVectorField_globalWeakEquationWithL2Data
    (W : MeanZeroNeumannPoissonSolution Q F)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp
        (Set.indicator (cubeFaceReflectionBlockSet Q)
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y)))
        (2 : ℝ≥0∞) MeasureTheory.volume ∧
      MeasureTheory.MemLp
        (Set.indicator (cubeFaceReflectionBlockSet Q)
          (cubeCoordinateFoldReflectedScalar Q F))
        (2 : ℝ≥0∞) MeasureTheory.volume ∧
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ cubeFaceReflectionBlockSet Q →
        ∫ x,
            vecDot
              (cubeCoordinateFoldReflectedVectorField Q
                (fun y => W.w.toH1Function.grad y) x)
              (euclideanGradient φ x) ∂MeasureTheory.volume =
          ∫ x,
            Set.indicator (cubeFaceReflectionBlockSet Q)
              (cubeCoordinateFoldReflectedScalar Q F) x * φ x
              ∂MeasureTheory.volume := by
  refine ⟨W.cubeFaceReflectionBlock_reflectedGradient_indicator_memLp, ?_⟩
  exact
    W.cubeFaceReflectionBlock_reflectedVectorField_globalWeakEquationWithL2Forcing
      hmean hF

/-- H10-test version of the reflected weak equation on the all-coordinate
reflection block. This is the density bridge from the compact-test reflection
identity to the Sobolev test space needed for the eventual reflected
potential/limit argument. -/
theorem cubeFaceReflectionBlock_reflectedVectorField_weakEquationOnBlock_h10
    (W : MeanZeroNeumannPoissonSolution Q F)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∀ φ : H10Function (cubeFaceReflectionBlockSet Q),
      ∫ x in cubeFaceReflectionBlockSet Q,
          vecDot
            (cubeCoordinateFoldReflectedVectorField Q
              (fun y => W.w.toH1Function.grad y) x)
            (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in cubeFaceReflectionBlockSet Q,
          cubeCoordinateFoldReflectedScalar Q F x *
            φ.toH1Function x ∂MeasureTheory.volume := by
  let U : Set (Vec d) := cubeFaceReflectionBlockSet Q
  let G : Vec d → Vec d :=
    cubeCoordinateFoldReflectedVectorField Q
      (fun y => W.w.toH1Function.grad y)
  let fR : Vec d → ℝ := cubeCoordinateFoldReflectedScalar Q F
  have hG : MemVectorL2 U G := by
    simpa [U, G] using
      W.cubeFaceReflectionBlock_reflectedGradient_memVectorL2
  have hFopen : MemScalarL2 (openCubeSet Q) F := by
    simpa [MemScalarL2, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hfR : MemScalarL2 U fR := by
    simpa [U, fR] using
      memScalarL2_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar
        Q hFopen
  have htest :
      ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ U →
          ∫ x in U, vecDot (G x) (euclideanGradient ψ x)
              ∂MeasureTheory.volume =
            ∫ x in U, fR x * ψ x ∂MeasureTheory.volume := by
    intro ψ hψ hψs _hψ_sub
    simpa [U, G, fR] using
      W.cubeFaceReflectionBlock_reflectedVectorField_weakEquationOnBlock_of_compactSupport_of_memLp_normalizedCubeMeasure
        (by simpa using hψ) hψs hmean hF
  simpa [U, G, fR] using
    h10WeakEquationOn_of_contDiff_tests
      (U := U) (G := G) (f := fR)
      (isOpen_cubeFaceReflectionBlockSet Q) hG hfR htest

/-- Energy identity obtained by testing the reflected H10 weak equation against
a supplied H10 potential for the reflected gradient. This isolates the next
hard step: constructing such a potential for the reflected Neumann gradient. -/
theorem cubeFaceReflectionBlock_reflectedVectorField_energyIdentity_of_h10Potential
    (W : MeanZeroNeumannPoissonSolution Q F)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (uR : H10Function (cubeFaceReflectionBlockSet Q))
    (huR_grad :
      uR.toH1Function.grad =
        cubeCoordinateFoldReflectedVectorField Q
          (fun y => W.w.toH1Function.grad y)) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        vecDot
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x *
          uR.toH1Function x ∂MeasureTheory.volume := by
  have hweak :=
    W.cubeFaceReflectionBlock_reflectedVectorField_weakEquationOnBlock_h10
      hmean hF uR
  simpa [huR_grad] using hweak

/-- Energy identity for the reflected block-folded H¹ potential. This avoids
any zero-trace claim: both sides are reduced by cell reflection to `3^d`
copies of the original Neumann self-test identity on `Q`. -/
theorem cubeFaceReflectionBlock_reflectedVectorField_energyIdentity_blockFold
    (W : MeanZeroNeumannPoissonSolution Q F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        vecDot
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x *
          (H1Function.cubeFaceReflectionBlockFold W.w.toH1Function).toFun x
          ∂MeasureTheory.volume := by
  let G : Vec d → Vec d := fun y => W.w.toH1Function.grad y
  have hGopen : MemVectorL2 (openCubeSet Q) G := by
    simpa [G, MemVectorL2, volumeMeasureOn] using
      W.w.toH1Function.grad_memVectorL2
  have hFopen : MemScalarL2 (openCubeSet Q) F := by
    simpa [MemScalarL2, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  have huopen : MemScalarL2 (openCubeSet Q) W.w.toH1Function.toFun := by
    simpa [MemScalarL2, volumeMeasureOn] using
      W.w.toH1Function.memL2
  have hleft :
      ∫ x in cubeFaceReflectionBlockSet Q,
          vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
            (cubeCoordinateFoldReflectedVectorField Q G x)
          ∂MeasureTheory.volume =
        (3 : ℝ) ^ d *
          ∫ y in openCubeSet Q, vecDot (G y) (G y)
            ∂MeasureTheory.volume :=
    setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField_self_pairing_of_memVectorL2_three_pow
      Q hGopen
  have hright :
      ∫ x in cubeFaceReflectionBlockSet Q,
          cubeCoordinateFoldReflectedScalar Q F x *
            cubeCoordinateFoldReflectedScalar Q W.w.toH1Function.toFun x
          ∂MeasureTheory.volume =
        (3 : ℝ) ^ d *
          ∫ y in openCubeSet Q,
            F y * W.w.toH1Function.toFun y ∂MeasureTheory.volume :=
    setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_mul_of_memScalarL2_three_pow
      Q hFopen huopen
  calc
    ∫ x in cubeFaceReflectionBlockSet Q,
        vecDot
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          ∂MeasureTheory.volume =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet Q, vecDot (G y) (G y)
          ∂MeasureTheory.volume := by
          simpa [G] using hleft
    _ = (3 : ℝ) ^ d *
        ∫ y in openCubeSet Q,
          F y * W.w.toH1Function.toFun y ∂MeasureTheory.volume := by
          rw [W.equation_self]
    _ = ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x *
          cubeCoordinateFoldReflectedScalar Q W.w.toH1Function.toFun x
          ∂MeasureTheory.volume := hright.symm
    _ = ∫ x in cubeFaceReflectionBlockSet Q,
        cubeCoordinateFoldReflectedScalar Q F x *
          (H1Function.cubeFaceReflectionBlockFold W.w.toH1Function).toFun x
          ∂MeasureTheory.volume := by
          simp [H1Function.cubeFaceReflectionBlockFold_toFun]

/-- Smooth localized Euclidean CZ estimate obtained from the reflected weak
equation, assuming the smooth potential has the reflected vector field as its
gradient. This isolates the remaining density/mollification bridge. -/
theorem cubeFaceReflectionBlock_smoothLocalizedEuclideanCZ_of_reflectedGradient
    (W : MeanZeroNeumannPoissonSolution Q F)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u)
    (hu_sub : tsupport u ⊆ cubeFaceReflectionBlockSet Q)
    (hgrad :
      (fun x => euclideanGradient u x) =ᵐ[MeasureTheory.volume]
        fun x =>
          cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x) :
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2
        ∂MeasureTheory.volume) ≤
      (∫ x,
        ‖Set.indicator (cubeFaceReflectionBlockSet Q)
          (cubeCoordinateFoldReflectedScalar Q F) x‖ ^ (2 : ℝ)
          ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖euclideanCoordLaplacian u x‖ ^ (2 : ℝ)
          ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
  let fR : Vec d → ℝ :=
    Set.indicator (cubeFaceReflectionBlockSet Q)
      (cubeCoordinateFoldReflectedScalar Q F)
  have hcontract :=
    W.cubeFaceReflectionBlock_reflectedVectorField_globalWeakEquationWithL2Forcing
      hmean hF
  have hweak :
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ cubeFaceReflectionBlockSet Q →
        ∫ x, vecDot (euclideanGradient u x) (euclideanGradient φ x)
            ∂MeasureTheory.volume =
          ∫ x, fR x * φ x ∂MeasureTheory.volume := by
    intro φ hφ hφs hφ_sub
    calc
      ∫ x, vecDot (euclideanGradient u x) (euclideanGradient φ x)
          ∂MeasureTheory.volume =
        ∫ x,
          vecDot
            (cubeCoordinateFoldReflectedVectorField Q
              (fun y => W.w.toH1Function.grad y) x)
            (euclideanGradient φ x) ∂MeasureTheory.volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hgrad] with x hx
            rw [hx]
      _ = ∫ x, fR x * φ x ∂MeasureTheory.volume := by
            simpa [fR] using hcontract.2 φ hφ hφs hφ_sub
  simpa [fR] using
    integral_sum_euclideanCoordSecondDeriv_sq_le_forcing_l2_mul_laplacian_l2_of_tsupport_subset
      (U := cubeFaceReflectionBlockSet Q) hu hu_supp hu_sub hcontract.1 hweak

/-- Smooth localized Euclidean CZ estimate from the reflected weak equation,
with the all-space reflected forcing norm converted back to the original cube
forcing energy. -/
theorem cubeFaceReflectionBlock_smoothLocalizedEuclideanCZ_of_reflectedGradient_cubeEnergy
    (W : MeanZeroNeumannPoissonSolution Q F)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u)
    (hu_sub : tsupport u ⊆ cubeFaceReflectionBlockSet Q)
    (hgrad :
      (fun x => euclideanGradient u x) =ᵐ[MeasureTheory.volume]
        fun x =>
          cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x) :
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2
        ∂MeasureTheory.volume) ≤
      ((3 : ℝ) ^ d *
        ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume) ^
          (1 / (2 : ℝ)) *
        (∫ x, ‖euclideanCoordLaplacian u x‖ ^ (2 : ℝ)
          ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
  have hbase :=
    W.cubeFaceReflectionBlock_smoothLocalizedEuclideanCZ_of_reflectedGradient
      hmean hF hu hu_supp hu_sub hgrad
  have hFopen : MemScalarL2 (openCubeSet Q) F := by
    simpa [MemScalarL2, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hforce :
      ∫ x,
          ‖Set.indicator (cubeFaceReflectionBlockSet Q)
            (cubeCoordinateFoldReflectedScalar Q F) x‖ ^ (2 : ℝ)
          ∂MeasureTheory.volume =
        (3 : ℝ) ^ d *
          ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume :=
    integral_indicator_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_norm_sq
      Q hFopen
  have hforce_sq :
      ∫ x,
          (Set.indicator (cubeFaceReflectionBlockSet Q)
            (cubeCoordinateFoldReflectedScalar Q F) x) ^ 2
          ∂MeasureTheory.volume =
        (3 : ℝ) ^ d *
          ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume := by
    simpa [pow_two, Real.norm_eq_abs] using hforce
  simpa [hforce_sq] using hbase

/-- Smooth localized reflected Euclidean CZ estimate with the Laplacian factor
cancelled on the Euclidean side. -/
theorem cubeFaceReflectionBlock_smoothLocalizedEuclideanCZ_of_reflectedGradient_forcingL2
    (W : MeanZeroNeumannPoissonSolution Q F)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u)
    (hu_sub : tsupport u ⊆ cubeFaceReflectionBlockSet Q)
    (hgrad :
      (fun x => euclideanGradient u x) =ᵐ[MeasureTheory.volume]
        fun x =>
          cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x) :
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2
        ∂MeasureTheory.volume) ≤
      ∫ x,
        ‖Set.indicator (cubeFaceReflectionBlockSet Q)
          (cubeCoordinateFoldReflectedScalar Q F) x‖ ^ (2 : ℝ)
          ∂MeasureTheory.volume := by
  let fR : Vec d → ℝ :=
    Set.indicator (cubeFaceReflectionBlockSet Q)
      (cubeCoordinateFoldReflectedScalar Q F)
  have hcontract :=
    W.cubeFaceReflectionBlock_reflectedVectorField_globalWeakEquationWithL2Forcing
      hmean hF
  have hweak :
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ cubeFaceReflectionBlockSet Q →
        ∫ x, vecDot (euclideanGradient u x) (euclideanGradient φ x)
            ∂MeasureTheory.volume =
          ∫ x, fR x * φ x ∂MeasureTheory.volume := by
    intro φ hφ hφs hφ_sub
    calc
      ∫ x, vecDot (euclideanGradient u x) (euclideanGradient φ x)
          ∂MeasureTheory.volume =
        ∫ x,
          vecDot
            (cubeCoordinateFoldReflectedVectorField Q
              (fun y => W.w.toH1Function.grad y) x)
            (euclideanGradient φ x) ∂MeasureTheory.volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hgrad] with x hx
            rw [hx]
      _ = ∫ x, fR x * φ x ∂MeasureTheory.volume := by
            simpa [fR] using hcontract.2 φ hφ hφs hφ_sub
  simpa [fR] using
    integral_sum_euclideanCoordSecondDeriv_sq_le_forcing_l2_of_tsupport_subset
      (U := cubeFaceReflectionBlockSet Q) hu hu_supp hu_sub hcontract.1 hweak

/-- Smooth localized reflected Euclidean CZ estimate with forcing energy
converted back to the original cube. -/
theorem cubeFaceReflectionBlock_smoothLocalizedEuclideanCZ_of_reflectedGradient_cubeForcingL2
    (W : MeanZeroNeumannPoissonSolution Q F)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u)
    (hu_sub : tsupport u ⊆ cubeFaceReflectionBlockSet Q)
    (hgrad :
      (fun x => euclideanGradient u x) =ᵐ[MeasureTheory.volume]
        fun x =>
          cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x) :
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2
        ∂MeasureTheory.volume) ≤
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume := by
  have hbase :=
    W.cubeFaceReflectionBlock_smoothLocalizedEuclideanCZ_of_reflectedGradient_forcingL2
      hmean hF hu hu_supp hu_sub hgrad
  have hFopen : MemScalarL2 (openCubeSet Q) F := by
    simpa [MemScalarL2, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hforce :
      ∫ x,
          ‖Set.indicator (cubeFaceReflectionBlockSet Q)
            (cubeCoordinateFoldReflectedScalar Q F) x‖ ^ (2 : ℝ)
          ∂MeasureTheory.volume =
        (3 : ℝ) ^ d *
          ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume :=
    integral_indicator_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_norm_sq
      Q hFopen
  have hforce_sq :
      ∫ x,
          (Set.indicator (cubeFaceReflectionBlockSet Q)
            (cubeCoordinateFoldReflectedScalar Q F) x) ^ 2
          ∂MeasureTheory.volume =
        (3 : ℝ) ^ d *
          ∫ y in openCubeSet Q, F y * F y ∂MeasureTheory.volume := by
    simpa [pow_two, Real.norm_eq_abs] using hforce
  simpa [hforce_sq] using hbase

end MeanZeroNeumannPoissonSolution

end

end Homogenization
