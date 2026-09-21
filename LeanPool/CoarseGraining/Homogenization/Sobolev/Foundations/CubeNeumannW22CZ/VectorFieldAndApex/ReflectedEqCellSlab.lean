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
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.VectorFieldAndApex.BlockFold

/-! # Reflected Eq Cell Slab -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace MeanZeroNeumannPoissonSolution

variable {d : ℕ} {Q : TriadicCube d} {F : Vec d → ℝ}

/-- The reflected Neumann gradient is a Sobolev potential on each individual
reflection cell. This is the cellwise gluing datum for the global block
construction. -/
theorem cubeFaceReflectionCell_reflectedGradient_isPotentialOn
    (W : MeanZeroNeumannPoissonSolution Q F)
    (choice : Fin d → Fin 3) :
    IsPotentialOn (openCubeSet (cubeFaceReflectionCellCube Q choice))
      (cubeCoordinateFoldReflectedVectorField Q
        (fun y => W.w.toH1Function.grad y)) := by
  exact
    W.w.toH1Function.cubeFaceReflectionCellFold_isPotentialOn_reflectedVectorField
      choice

/-- The reflected Neumann gradient is a Sobolev potential on the whole
all-coordinate reflection block. -/
theorem cubeFaceReflectionBlock_reflectedGradient_isPotentialOn
    (W : MeanZeroNeumannPoissonSolution Q F) :
    IsPotentialOn (cubeFaceReflectionBlockSet Q)
      (cubeCoordinateFoldReflectedVectorField Q
        (fun y => W.w.toH1Function.grad y)) := by
  exact W.w.toH1Function.cubeFaceReflectionBlockFold_isPotentialOn

/-- Upper-face reflected weak equation in reflected-field notation. -/
theorem upperFace_reflectedVectorField_weakEquationOnUnion
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hmean : cubeAverage Q F = 0)
    (hgradMain :
      MeasureTheory.Integrable
        (fun x => vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x))
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hgradReflected :
      MeasureTheory.Integrable
        (fun x =>
          vecDot (W.w.toH1Function.grad x)
            (euclideanGradient (fun z => φ (cubeUpperFaceReflection Q i z)) x))
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hF :
      MeasureTheory.Integrable F
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hFmain :
      MeasureTheory.Integrable
        (fun x => F x * φ x)
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hFreflected :
      MeasureTheory.Integrable
        (fun x => F x * φ (cubeUpperFaceReflection Q i x))
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (upperFaceReflectedVectorField Q i
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        upperFaceReflectedScalar Q i F x * φ x
          ∂MeasureTheory.volume := by
  have hUnion :
      MeasurableSet (openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i)) :=
    (measurableSet_openCubeSet Q).union
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i))
  have hgrad_eq :
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
          vecDot
            (upperFaceReflectedVectorField Q i
              (fun y => W.w.toH1Function.grad y) x)
            (euclideanGradient φ x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
          upperFaceReflectedGradientPairingIntegrand Q i
            (fun y => W.w.toH1Function.grad y) φ x ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hUnion ?_
    intro x _hx
    by_cases hxQ : x ∈ openCubeSet Q
    · simp [upperFaceReflectedVectorField,
        upperFaceReflectedGradientPairingIntegrand, hxQ]
    · simp [upperFaceReflectedVectorField,
        upperFaceReflectedGradientPairingIntegrand, hxQ]
  have hforce_eq :
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
          upperFaceReflectedScalar Q i F x * φ x ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
          upperFaceReflectedForcingIntegrand Q i F φ x
            ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hUnion ?_
    intro x _hx
    by_cases hxQ : x ∈ openCubeSet Q
    · simp [upperFaceReflectedScalar, upperFaceReflectedForcingIntegrand, hxQ]
    · simp [upperFaceReflectedScalar, upperFaceReflectedForcingIntegrand, hxQ]
  rw [hgrad_eq, hforce_eq]
  exact
    W.upperFace_reflectedWeakEquationOnUnion
      i hφ hmean hgradMain hgradReflected hF hFmain hFreflected

/-- Lower-face reflected weak equation in reflected-field notation. -/
theorem lowerFace_reflectedVectorField_weakEquationOnUnion
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hmean : cubeAverage Q F = 0)
    (hgradMain :
      MeasureTheory.Integrable
        (fun x => vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x))
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hgradReflected :
      MeasureTheory.Integrable
        (fun x =>
          vecDot (W.w.toH1Function.grad x)
            (euclideanGradient (fun z => φ (cubeLowerFaceReflection Q i z)) x))
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hF :
      MeasureTheory.Integrable F
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hFmain :
      MeasureTheory.Integrable
        (fun x => F x * φ x)
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hFreflected :
      MeasureTheory.Integrable
        (fun x => F x * φ (cubeLowerFaceReflection Q i x))
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (lowerFaceReflectedVectorField Q i
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        lowerFaceReflectedScalar Q i F x * φ x
          ∂MeasureTheory.volume := by
  have hUnion :
      MeasurableSet (openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i)) :=
    (measurableSet_openCubeSet Q).union
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i))
  have hgrad_eq :
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
          vecDot
            (lowerFaceReflectedVectorField Q i
              (fun y => W.w.toH1Function.grad y) x)
            (euclideanGradient φ x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
          lowerFaceReflectedGradientPairingIntegrand Q i
            (fun y => W.w.toH1Function.grad y) φ x ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hUnion ?_
    intro x _hx
    by_cases hxQ : x ∈ openCubeSet Q
    · simp [lowerFaceReflectedVectorField,
        lowerFaceReflectedGradientPairingIntegrand, hxQ]
    · simp [lowerFaceReflectedVectorField,
        lowerFaceReflectedGradientPairingIntegrand, hxQ]
  have hforce_eq :
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
          lowerFaceReflectedScalar Q i F x * φ x ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
          lowerFaceReflectedForcingIntegrand Q i F φ x
            ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hUnion ?_
    intro x _hx
    by_cases hxQ : x ∈ openCubeSet Q
    · simp [lowerFaceReflectedScalar, lowerFaceReflectedForcingIntegrand, hxQ]
    · simp [lowerFaceReflectedScalar, lowerFaceReflectedForcingIntegrand, hxQ]
  rw [hgrad_eq, hforce_eq]
  exact
    W.lowerFace_reflectedWeakEquationOnUnion
      i hφ hmean hgradMain hgradReflected hF hFmain hFreflected

/-- Compact-test upper-face reflected weak equation in reflected-field
notation, using the normalized cube `L²` hypothesis from the endpoint
interfaces. -/
theorem upperFace_reflectedVectorField_weakEquationOnUnion_of_compactSupport_of_memLp_normalizedCubeMeasure
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (upperFaceReflectedVectorField Q i
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        upperFaceReflectedScalar Q i F x * φ x
          ∂MeasureTheory.volume := by
  have hUnion :
      MeasurableSet (openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i)) :=
    (measurableSet_openCubeSet Q).union
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i))
  have hgrad_eq :
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
          vecDot
            (upperFaceReflectedVectorField Q i
              (fun y => W.w.toH1Function.grad y) x)
            (euclideanGradient φ x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
          upperFaceReflectedGradientPairingIntegrand Q i
            (fun y => W.w.toH1Function.grad y) φ x ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hUnion ?_
    intro x _hx
    by_cases hxQ : x ∈ openCubeSet Q
    · simp [upperFaceReflectedVectorField,
        upperFaceReflectedGradientPairingIntegrand, hxQ]
    · simp [upperFaceReflectedVectorField,
        upperFaceReflectedGradientPairingIntegrand, hxQ]
  have hforce_eq :
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
          upperFaceReflectedScalar Q i F x * φ x ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
          upperFaceReflectedForcingIntegrand Q i F φ x
            ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hUnion ?_
    intro x _hx
    by_cases hxQ : x ∈ openCubeSet Q
    · simp [upperFaceReflectedScalar, upperFaceReflectedForcingIntegrand, hxQ]
    · simp [upperFaceReflectedScalar, upperFaceReflectedForcingIntegrand, hxQ]
  rw [hgrad_eq, hforce_eq]
  exact
    W.upperFace_reflectedWeakEquationOnUnion_of_compactSupport_of_memLp_normalizedCubeMeasure
      i hφ hφs hmean hF

/-- Compact-test lower-face reflected weak equation in reflected-field
notation, using the normalized cube `L²` hypothesis from the endpoint
interfaces. -/
theorem lowerFace_reflectedVectorField_weakEquationOnUnion_of_compactSupport_of_memLp_normalizedCubeMeasure
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (lowerFaceReflectedVectorField Q i
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        lowerFaceReflectedScalar Q i F x * φ x
          ∂MeasureTheory.volume := by
  have hUnion :
      MeasurableSet (openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i)) :=
    (measurableSet_openCubeSet Q).union
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i))
  have hgrad_eq :
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
          vecDot
            (lowerFaceReflectedVectorField Q i
              (fun y => W.w.toH1Function.grad y) x)
            (euclideanGradient φ x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
          lowerFaceReflectedGradientPairingIntegrand Q i
            (fun y => W.w.toH1Function.grad y) φ x ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hUnion ?_
    intro x _hx
    by_cases hxQ : x ∈ openCubeSet Q
    · simp [lowerFaceReflectedVectorField,
        lowerFaceReflectedGradientPairingIntegrand, hxQ]
    · simp [lowerFaceReflectedVectorField,
        lowerFaceReflectedGradientPairingIntegrand, hxQ]
  have hforce_eq :
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
          lowerFaceReflectedScalar Q i F x * φ x ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
          lowerFaceReflectedForcingIntegrand Q i F φ x
            ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hUnion ?_
    intro x _hx
    by_cases hxQ : x ∈ openCubeSet Q
    · simp [lowerFaceReflectedScalar, lowerFaceReflectedForcingIntegrand, hxQ]
    · simp [lowerFaceReflectedScalar, lowerFaceReflectedForcingIntegrand, hxQ]
  rw [hgrad_eq, hforce_eq]
  exact
    W.lowerFace_reflectedWeakEquationOnUnion_of_compactSupport_of_memLp_normalizedCubeMeasure
      i hφ hφs hmean hF

/-- Compact-test weak equation on the lower/original/upper one-coordinate
reflected slab, in reflected-field notation. Algebraically this is the lower
one-face reflected equation plus the upper one-face reflected equation, minus
the original cube equation. -/
theorem faceNeighborSlab_reflectedVectorField_weakEquationOnSlab_of_compactSupport
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in cubeFaceNeighborSlabSet Q i,
        vecDot
          (faceNeighborSlabReflectedVectorField Q i
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in cubeFaceNeighborSlabSet Q i,
        faceNeighborSlabReflectedScalar Q i F x * φ x
          ∂MeasureTheory.volume := by
  classical
  let G : Vec d → Vec d := fun y => W.w.toH1Function.grad y
  let L := openCubeSet (cubeLowerFaceNeighbor Q i)
  let M := openCubeSet Q
  let U := openCubeSet (cubeUpperFaceNeighbor Q i)
  let S := cubeFaceNeighborSlabSet Q i
  let gradSlab : Vec d → ℝ := fun x =>
    vecDot (faceNeighborSlabReflectedVectorField Q i G x)
      (euclideanGradient φ x)
  let forceSlab : Vec d → ℝ := fun x =>
    faceNeighborSlabReflectedScalar Q i F x * φ x
  let gradL : ℝ :=
    ∫ x in L,
      vecDot
        (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
        (euclideanGradient φ x) ∂MeasureTheory.volume
  let gradM : ℝ :=
    ∫ x in M, vecDot (G x) (euclideanGradient φ x)
      ∂MeasureTheory.volume
  let gradU : ℝ :=
    ∫ x in U,
      vecDot
        (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
        (euclideanGradient φ x) ∂MeasureTheory.volume
  let forceL : ℝ :=
    ∫ x in L, F (cubeLowerFaceReflection Q i x) * φ x
      ∂MeasureTheory.volume
  let forceM : ℝ :=
    ∫ x in M, F x * φ x ∂MeasureTheory.volume
  let forceU : ℝ :=
    ∫ x in U, F (cubeUpperFaceReflection Q i x) * φ x
      ∂MeasureTheory.volume
  have hFopen : MemScalarL2 M F := by
    simpa [MemScalarL2, volumeMeasureOn, M] using hF
  have hGopen : MemVectorL2 M G := by
    simpa [MemVectorL2, volumeMeasureOn, G, M] using
      W.w.toH1Function.grad_memVectorL2
  let : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict M) := by
    simpa [M] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let ψU : Vec d → ℝ := fun z => φ (cubeUpperFaceReflection Q i z)
  let ψL : Vec d → ℝ := fun z => φ (cubeLowerFaceReflection Q i z)
  have hψU : ContDiff ℝ (⊤ : ℕ∞) ψU := by
    simpa [ψU, cubeUpperFaceReflection] using!
      hφ.comp (contDiff_coordFaceReflection (cubeUpperFaceCoord Q i) i)
  have hψL : ContDiff ℝ (⊤ : ℕ∞) ψL := by
    simpa [ψL, cubeLowerFaceReflection] using!
      hφ.comp (contDiff_coordFaceReflection (cubeLowerFaceCoord Q i) i)
  have hψUs : HasCompactSupport ψU := by
    simpa [ψU] using hasCompactSupport_comp_cubeUpperFaceReflection hφs Q i
  have hψLs : HasCompactSupport ψL := by
    simpa [ψL] using hasCompactSupport_comp_cubeLowerFaceReflection hφs Q i
  have hgradMain :
      MeasureTheory.Integrable
        (fun x => vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x))
        (MeasureTheory.volume.restrict M) := by
    have hgradφ : MemVectorL2 M (euclideanGradient φ) :=
      memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hφ hφs
    simpa [MeasureTheory.IntegrableOn, G, M] using
      integrableOn_vecDot_of_memVectorL2 (U := M) hGopen hgradφ
  have hgradUpperReflected :
      MeasureTheory.Integrable
        (fun x =>
          vecDot (W.w.toH1Function.grad x)
            (euclideanGradient (fun z => φ (cubeUpperFaceReflection Q i z)) x))
        (MeasureTheory.volume.restrict M) := by
    have hgradψU : MemVectorL2 M (euclideanGradient ψU) :=
      memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hψU hψUs
    simpa [MeasureTheory.IntegrableOn, G, M, ψU] using
      integrableOn_vecDot_of_memVectorL2 (U := M) hGopen hgradψU
  have hgradLowerReflected :
      MeasureTheory.Integrable
        (fun x =>
          vecDot (W.w.toH1Function.grad x)
            (euclideanGradient (fun z => φ (cubeLowerFaceReflection Q i z)) x))
        (MeasureTheory.volume.restrict M) := by
    have hgradψL : MemVectorL2 M (euclideanGradient ψL) :=
      memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hψL hψLs
    simpa [MeasureTheory.IntegrableOn, G, M, ψL] using
      integrableOn_vecDot_of_memVectorL2 (U := M) hGopen hgradψL
  have hFint :
      MeasureTheory.Integrable F (MeasureTheory.volume.restrict M) :=
    hFopen.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hφL2 : MemScalarL2 M φ := by
    have hφ_cont : Continuous φ := (hφ.differentiable (by simp)).continuous
    simpa [MemScalarL2, volumeMeasureOn, M] using
      (hφ_cont.memLp_of_hasCompactSupport hφs).restrict M
  have hψUL2 : MemScalarL2 M ψU := by
    have hψU_cont : Continuous ψU :=
      (hψU.differentiable (by simp)).continuous
    simpa [MemScalarL2, volumeMeasureOn, M] using
      (hψU_cont.memLp_of_hasCompactSupport hψUs).restrict M
  have hψLL2 : MemScalarL2 M ψL := by
    have hψL_cont : Continuous ψL :=
      (hψL.differentiable (by simp)).continuous
    simpa [MemScalarL2, volumeMeasureOn, M] using
      (hψL_cont.memLp_of_hasCompactSupport hψLs).restrict M
  have hFmain :
      MeasureTheory.Integrable
        (fun x => F x * φ x) (MeasureTheory.volume.restrict M) :=
    hFopen.integrable_mul hφL2
  have hFupperReflected :
      MeasureTheory.Integrable
        (fun x => F x * φ (cubeUpperFaceReflection Q i x))
        (MeasureTheory.volume.restrict M) := by
    simpa [ψU] using! hFopen.integrable_mul hψUL2
  have hFlowerReflected :
      MeasureTheory.Integrable
        (fun x => F x * φ (cubeLowerFaceReflection Q i x))
        (MeasureTheory.volume.restrict M) := by
    simpa [ψL] using! hFopen.integrable_mul hψLL2
  have hUpperEq : gradM + gradU = forceM + forceU := by
    simpa [gradM, gradU, forceM, forceU, G, M, U] using
      W.upperFace_reflectedGradient_pairing_eq_reflectedRhs
        i hφ hmean hgradMain hgradUpperReflected hFint hFmain
        hFupperReflected
  have hLowerEq : gradM + gradL = forceM + forceL := by
    simpa [gradM, gradL, forceM, forceL, G, M, L] using
      W.lowerFace_reflectedGradient_pairing_eq_reflectedRhs
        i hφ hmean hgradMain hgradLowerReflected hFint hFmain
        hFlowerReflected
  have hCubeEq : gradM = forceM := by
    simpa [gradM, forceM, G, M] using
      W.weakEquationOnCube_of_compactSupport
        hφ hφs hmean hF
  have hGslab : MemVectorL2 S (faceNeighborSlabReflectedVectorField Q i G) := by
    simpa [S, M] using
      memVectorL2_cubeFaceNeighborSlabSet_faceNeighborSlabReflectedVectorField
        Q i hGopen
  have hgradφSlab : MemVectorL2 S (euclideanGradient φ) :=
    memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hφ hφs
  have hgradSlabInt :
      MeasureTheory.Integrable gradSlab (MeasureTheory.volume.restrict S) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, gradSlab] using
      integrableOn_vecDot_of_memVectorL2 (U := S) hGslab hgradφSlab
  have hFslab : MemScalarL2 S (faceNeighborSlabReflectedScalar Q i F) := by
    simpa [S, M] using
      memScalarL2_cubeFaceNeighborSlabSet_faceNeighborSlabReflectedScalar
        Q i hFopen
  have hφSlab : MemScalarL2 S φ := by
    have hφ_cont : Continuous φ := (hφ.differentiable (by simp)).continuous
    simpa [MemScalarL2, volumeMeasureOn, S] using
      (hφ_cont.memLp_of_hasCompactSupport hφs).restrict S
  have hforceSlabInt :
      MeasureTheory.Integrable forceSlab (MeasureTheory.volume.restrict S) := by
    simpa [forceSlab] using! hFslab.integrable_mul hφSlab
  have hLsub : L ⊆ S := by
    intro x hx
    exact Or.inl (Or.inl hx)
  have hMsub : M ⊆ S := by
    intro x hx
    exact Or.inl (Or.inr hx)
  have hUsub : U ⊆ S := by
    intro x hx
    exact Or.inr hx
  have hgradL_int :
      MeasureTheory.Integrable gradSlab (MeasureTheory.volume.restrict L) :=
    hgradSlabInt.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hLsub)
  have hgradM_int :
      MeasureTheory.Integrable gradSlab (MeasureTheory.volume.restrict M) :=
    hgradSlabInt.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hMsub)
  have hgradU_int :
      MeasureTheory.Integrable gradSlab (MeasureTheory.volume.restrict U) :=
    hgradSlabInt.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hUsub)
  have hforceL_int :
      MeasureTheory.Integrable forceSlab (MeasureTheory.volume.restrict L) :=
    hforceSlabInt.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hLsub)
  have hforceM_int :
      MeasureTheory.Integrable forceSlab (MeasureTheory.volume.restrict M) :=
    hforceSlabInt.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hMsub)
  have hforceU_int :
      MeasureTheory.Integrable forceSlab (MeasureTheory.volume.restrict U) :=
    hforceSlabInt.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hUsub)
  have hgradL_eq :
      ∫ x in L, gradSlab x ∂MeasureTheory.volume = gradL := by
    change
      ∫ x in L, gradSlab x ∂MeasureTheory.volume =
        ∫ x in L,
          vecDot
            (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
            (euclideanGradient φ x) ∂MeasureTheory.volume
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i)) ?_
    intro x hx
    simpa [gradSlab, L] using
      congrArg (fun v => vecDot v (euclideanGradient φ x))
        (faceNeighborSlabReflectedVectorField_of_mem_lower Q i G
          (x := x) hx)
  have hgradM_eq :
      ∫ x in M, gradSlab x ∂MeasureTheory.volume = gradM := by
    change
      ∫ x in M, gradSlab x ∂MeasureTheory.volume =
        ∫ x in M, vecDot (G x) (euclideanGradient φ x)
          ∂MeasureTheory.volume
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet Q) ?_
    intro x hx
    simpa [gradSlab, M] using
      congrArg (fun v => vecDot v (euclideanGradient φ x))
        (faceNeighborSlabReflectedVectorField_of_mem_cube Q i G
          (x := x) hx)
  have hgradU_eq :
      ∫ x in U, gradSlab x ∂MeasureTheory.volume = gradU := by
    change
      ∫ x in U, gradSlab x ∂MeasureTheory.volume =
        ∫ x in U,
          vecDot
            (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
            (euclideanGradient φ x) ∂MeasureTheory.volume
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i)) ?_
    intro x hx
    simpa [gradSlab, U] using
      congrArg (fun v => vecDot v (euclideanGradient φ x))
        (faceNeighborSlabReflectedVectorField_of_mem_upper Q i G
          (x := x) hx)
  have hforceL_eq :
      ∫ x in L, forceSlab x ∂MeasureTheory.volume = forceL := by
    change
      ∫ x in L, forceSlab x ∂MeasureTheory.volume =
        ∫ x in L, F (cubeLowerFaceReflection Q i x) * φ x
          ∂MeasureTheory.volume
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i)) ?_
    intro x hx
    simpa [forceSlab, L] using
      congrArg (fun y => y * φ x)
        (faceNeighborSlabReflectedScalar_of_mem_lower Q i F
          (x := x) hx)
  have hforceM_eq :
      ∫ x in M, forceSlab x ∂MeasureTheory.volume = forceM := by
    change
      ∫ x in M, forceSlab x ∂MeasureTheory.volume =
        ∫ x in M, F x * φ x ∂MeasureTheory.volume
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet Q) ?_
    intro x hx
    simpa [forceSlab, M] using
      congrArg (fun y => y * φ x)
        (faceNeighborSlabReflectedScalar_of_mem_cube Q i F (x := x) hx)
  have hforceU_eq :
      ∫ x in U, forceSlab x ∂MeasureTheory.volume = forceU := by
    change
      ∫ x in U, forceSlab x ∂MeasureTheory.volume =
        ∫ x in U, F (cubeUpperFaceReflection Q i x) * φ x
          ∂MeasureTheory.volume
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i)) ?_
    intro x hx
    simpa [forceSlab, U] using
      congrArg (fun y => y * φ x)
        (faceNeighborSlabReflectedScalar_of_mem_upper Q i F
          (x := x) hx)
  have hgradSplit :
      ∫ x in S, gradSlab x ∂MeasureTheory.volume =
        gradL + gradM + gradU := by
    calc
      ∫ x in S, gradSlab x ∂MeasureTheory.volume =
          ∫ x in L, gradSlab x ∂MeasureTheory.volume +
          ∫ x in M, gradSlab x ∂MeasureTheory.volume +
          ∫ x in U, gradSlab x ∂MeasureTheory.volume := by
            simpa [S, L, M, U] using
              setIntegral_cubeFaceNeighborSlabSet Q i gradSlab
                hgradL_int hgradM_int hgradU_int
      _ = gradL + gradM + gradU := by
            rw [hgradL_eq, hgradM_eq, hgradU_eq]
  have hforceSplit :
      ∫ x in S, forceSlab x ∂MeasureTheory.volume =
        forceL + forceM + forceU := by
    calc
      ∫ x in S, forceSlab x ∂MeasureTheory.volume =
          ∫ x in L, forceSlab x ∂MeasureTheory.volume +
          ∫ x in M, forceSlab x ∂MeasureTheory.volume +
          ∫ x in U, forceSlab x ∂MeasureTheory.volume := by
            simpa [S, L, M, U] using
              setIntegral_cubeFaceNeighborSlabSet Q i forceSlab
                hforceL_int hforceM_int hforceU_int
      _ = forceL + forceM + forceU := by
            rw [hforceL_eq, hforceM_eq, hforceU_eq]
  have hAlgebra : gradL + gradM + gradU = forceL + forceM + forceU := by
    calc
      gradL + gradM + gradU =
          (gradM + gradL) + (gradM + gradU) - gradM := by ring
      _ = (forceM + forceL) + (forceM + forceU) - forceM := by
            rw [hLowerEq, hUpperEq, hCubeEq]
      _ = forceL + forceM + forceU := by ring
  change
    ∫ x in S, gradSlab x ∂MeasureTheory.volume =
      ∫ x in S, forceSlab x ∂MeasureTheory.volume
  rw [hgradSplit, hforceSplit]
  exact hAlgebra

/-- Compact-test weak equation on the lower/original/upper one-coordinate
reflected slab, with the right-hand side given in the normalized cube `L²`
measure used by the endpoint interfaces. -/
theorem faceNeighborSlab_reflectedVectorField_weakEquationOnSlab_of_compactSupport_of_memLp_normalizedCubeMeasure
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∫ x in cubeFaceNeighborSlabSet Q i,
        vecDot
          (faceNeighborSlabReflectedVectorField Q i
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in cubeFaceNeighborSlabSet Q i,
        faceNeighborSlabReflectedScalar Q i F x * φ x
          ∂MeasureTheory.volume := by
  have hFopen :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [MemL2On, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  exact
    W.faceNeighborSlab_reflectedVectorField_weakEquationOnSlab_of_compactSupport
      i hφ hφs hmean hFopen

/-- Compact-test weak equation on a single all-coordinate reflection-block
cell. The proof tests the original cube equation with `φ` precomposed by the
cell fold, then changes variables through the fold map. -/
theorem cubeFaceReflectionCell_reflectedVectorField_weakEquationOnCell_of_compactSupport
    (W : MeanZeroNeumannPoissonSolution Q F)
    (choice : Fin d → Fin 3) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        vecDot
          (cubeCoordinateFoldReflectedVectorField Q
            (fun y => W.w.toH1Function.grad y) x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        cubeCoordinateFoldReflectedScalar Q F x * φ x
          ∂MeasureTheory.volume := by
  classical
  let G : Vec d → Vec d := fun y => W.w.toH1Function.grad y
  let ψ : Vec d → ℝ :=
    fun y => φ (cubeFaceReflectionCellFoldMap Q choice y)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ] using
      contDiff_comp_cubeFaceReflectionCellFoldMap Q choice hφ
  have hψs : HasCompactSupport ψ := by
    simpa [ψ] using
      hasCompactSupport_comp_cubeFaceReflectionCellFoldMap Q choice hφs
  have hCube := W.weakEquationOnCube_of_compactSupport hψ hψs hmean hF
  have hgradCell :
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
          vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
            (euclideanGradient φ x) ∂MeasureTheory.volume =
        ∫ y in openCubeSet Q,
          vecDot (G y) (euclideanGradient ψ y) ∂MeasureTheory.volume := by
    calc
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
          vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
            (euclideanGradient φ x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
          vecDot (G (cubeFaceReflectionCellFoldMap Q choice x))
            (euclideanGradient ψ (cubeFaceReflectionCellFoldMap Q choice x))
          ∂MeasureTheory.volume := by
            refine MeasureTheory.setIntegral_congr_fun
              (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
            intro x hx
            have hvec :=
              cubeCoordinateFoldReflectedVectorField_eq_cellFoldLinear_of_mem_cellCube
                Q choice G hx
            have hgradAtFold :
                euclideanGradient ψ (cubeFaceReflectionCellFoldMap Q choice x) =
                  cubeFaceReflectionCellFoldLinear choice
                    (euclideanGradient φ x) := by
              have hg :=
                euclideanGradient_comp_cubeFaceReflectionCellFoldMap
                  hφ Q choice (cubeFaceReflectionCellFoldMap Q choice x)
              simpa [ψ, cubeFaceReflectionCellFoldMap_involutive Q choice x]
                using hg
            calc
              vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
                  (euclideanGradient φ x)
                  = vecDot
                      (cubeFaceReflectionCellFoldLinear choice
                        (G (cubeFaceReflectionCellFoldMap Q choice x)))
                      (euclideanGradient φ x) := by
                        rw [hvec]
              _ = vecDot (G (cubeFaceReflectionCellFoldMap Q choice x))
                    (cubeFaceReflectionCellFoldLinear choice
                      (euclideanGradient φ x)) := by
                        exact
                          vecDot_cubeFaceReflectionCellFoldLinear_left
                            choice
                            (G (cubeFaceReflectionCellFoldMap Q choice x))
                            (euclideanGradient φ x)
              _ = vecDot (G (cubeFaceReflectionCellFoldMap Q choice x))
                    (euclideanGradient ψ
                      (cubeFaceReflectionCellFoldMap Q choice x)) := by
                        rw [hgradAtFold]
      _ = ∫ y in openCubeSet Q,
          vecDot (G y) (euclideanGradient ψ y) ∂MeasureTheory.volume := by
            simpa using
              setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap
                Q choice (fun y => vecDot (G y) (euclideanGradient ψ y))
  have hforceCell :
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
          cubeCoordinateFoldReflectedScalar Q F x * φ x
          ∂MeasureTheory.volume =
        ∫ y in openCubeSet Q, F y * ψ y ∂MeasureTheory.volume := by
    calc
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
          cubeCoordinateFoldReflectedScalar Q F x * φ x
          ∂MeasureTheory.volume =
        ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
          F (cubeFaceReflectionCellFoldMap Q choice x) *
            ψ (cubeFaceReflectionCellFoldMap Q choice x)
          ∂MeasureTheory.volume := by
            refine MeasureTheory.setIntegral_congr_fun
              (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
            intro x hx
            have hscalar :=
              cubeCoordinateFoldReflectedScalar_eq_cellFoldMap_of_mem_cellCube
                Q choice F hx
            have hψfold :
                ψ (cubeFaceReflectionCellFoldMap Q choice x) = φ x := by
              simp [ψ, cubeFaceReflectionCellFoldMap_involutive Q choice x]
            change
              cubeCoordinateFoldReflectedScalar Q F x * φ x =
                F (cubeFaceReflectionCellFoldMap Q choice x) *
                  ψ (cubeFaceReflectionCellFoldMap Q choice x)
            rw [hscalar, hψfold]
      _ = ∫ y in openCubeSet Q, F y * ψ y ∂MeasureTheory.volume := by
            simpa using
              setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap
                Q choice (fun y => F y * ψ y)
  change
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        vecDot (cubeCoordinateFoldReflectedVectorField Q G x)
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        cubeCoordinateFoldReflectedScalar Q F x * φ x ∂MeasureTheory.volume
  rw [hgradCell, hforceCell]
  exact hCube

end MeanZeroNeumannPoissonSolution

end

end Homogenization
