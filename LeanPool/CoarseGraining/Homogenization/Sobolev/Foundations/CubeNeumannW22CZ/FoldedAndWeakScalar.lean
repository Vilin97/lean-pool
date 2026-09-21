/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Reflections
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Homeomorphism
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Derivatives
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.CubePairings
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.Definitions

/-! # Folded And Weak Scalar -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace MeanZeroNeumannPoissonSolution

variable {d : ℕ} {Q : TriadicCube d} {F : Vec d → ℝ}

/-- The weak Neumann equation tested against the folded upper-face reflection
test. This is the formal replacement for saying that the one-face even
reflection solves the reflected equation. -/
theorem equation_foldedCubeUpperFaceTest
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∫ x in openCubeSet Q,
        vecDot (W.w.toH1Function.grad x)
          (euclideanGradient (foldedCubeUpperFaceTest Q i φ) x)
          ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q,
        F x * (foldedCubeUpperFaceMeanZeroH1Test Q i hφ).toH1Function x
          ∂MeasureTheory.volume := by
  simpa using W.equation (foldedCubeUpperFaceMeanZeroH1Test Q i hφ)

/-- The weak Neumann equation tested against the folded lower-face reflection
test. -/
theorem equation_foldedCubeLowerFaceTest
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∫ x in openCubeSet Q,
        vecDot (W.w.toH1Function.grad x)
          (euclideanGradient (foldedCubeLowerFaceTest Q i φ) x)
          ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q,
        F x * (foldedCubeLowerFaceMeanZeroH1Test Q i hφ).toH1Function x
          ∂MeasureTheory.volume := by
  simpa using W.equation (foldedCubeLowerFaceMeanZeroH1Test Q i hφ)

/-- One upper-face weak reflection identity for an arbitrary smooth test. The
second integral is over the neighboring reflected cube with the reflected weak
gradient field. -/
theorem upperFace_reflectedGradient_pairing_eq_rhs
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hmain :
      MeasureTheory.Integrable
        (fun x => vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x))
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hreflected :
      MeasureTheory.Integrable
        (fun x =>
          vecDot (W.w.toH1Function.grad x)
            (euclideanGradient (fun z => φ (cubeUpperFaceReflection Q i z)) x))
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in openCubeSet Q,
        vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i
            (W.w.toH1Function.grad (cubeUpperFaceReflection Q i x)))
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q,
        F x * (foldedCubeUpperFaceMeanZeroH1Test Q i hφ).toH1Function x
          ∂MeasureTheory.volume := by
  let G : Vec d → Vec d := fun x => W.w.toH1Function.grad x
  have hsplit :=
    setIntegral_foldedCubeUpperFaceTest_reflectedField_pairing
      (G := G) hφ Q i hmain hreflected
  have heq := W.equation_foldedCubeUpperFaceTest i hφ
  calc
    ∫ x in openCubeSet Q,
        vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i
            (W.w.toH1Function.grad (cubeUpperFaceReflection Q i x)))
          (euclideanGradient φ x) ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            vecDot (W.w.toH1Function.grad x)
              (euclideanGradient (foldedCubeUpperFaceTest Q i φ) x)
              ∂MeasureTheory.volume := by
            simpa [G] using hsplit.symm
    _ = ∫ x in openCubeSet Q,
        F x * (foldedCubeUpperFaceMeanZeroH1Test Q i hφ).toH1Function x
          ∂MeasureTheory.volume := heq

/-- One lower-face weak reflection identity for an arbitrary smooth test. The
second integral is over the neighboring reflected cube with the reflected weak
gradient field. -/
theorem lowerFace_reflectedGradient_pairing_eq_rhs
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hmain :
      MeasureTheory.Integrable
        (fun x => vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x))
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hreflected :
      MeasureTheory.Integrable
        (fun x =>
          vecDot (W.w.toH1Function.grad x)
            (euclideanGradient (fun z => φ (cubeLowerFaceReflection Q i z)) x))
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in openCubeSet Q,
        vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i
            (W.w.toH1Function.grad (cubeLowerFaceReflection Q i x)))
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q,
        F x * (foldedCubeLowerFaceMeanZeroH1Test Q i hφ).toH1Function x
          ∂MeasureTheory.volume := by
  let G : Vec d → Vec d := fun x => W.w.toH1Function.grad x
  have hsplit :=
    setIntegral_foldedCubeLowerFaceTest_reflectedField_pairing
      (G := G) hφ Q i hmain hreflected
  have heq := W.equation_foldedCubeLowerFaceTest i hφ
  calc
    ∫ x in openCubeSet Q,
        vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i
            (W.w.toH1Function.grad (cubeLowerFaceReflection Q i x)))
          (euclideanGradient φ x) ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            vecDot (W.w.toH1Function.grad x)
              (euclideanGradient (foldedCubeLowerFaceTest Q i φ) x)
              ∂MeasureTheory.volume := by
            simpa [G] using hsplit.symm
    _ = ∫ x in openCubeSet Q,
        F x * (foldedCubeLowerFaceMeanZeroH1Test Q i hφ).toH1Function x
          ∂MeasureTheory.volume := heq

/-- One upper-face reflected weak equation with the forcing also split across
the reflected neighboring cube. This is the weak-form version of the reflected
solution statement for a zero-average forcing. -/
theorem upperFace_reflectedGradient_pairing_eq_reflectedRhs
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
    ∫ x in openCubeSet Q,
        vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i
            (W.w.toH1Function.grad (cubeUpperFaceReflection Q i x)))
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        F (cubeUpperFaceReflection Q i x) * φ x ∂MeasureTheory.volume := by
  calc
    ∫ x in openCubeSet Q,
        vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i
            (W.w.toH1Function.grad (cubeUpperFaceReflection Q i x)))
          (euclideanGradient φ x) ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            F x * (foldedCubeUpperFaceMeanZeroH1Test Q i hφ).toH1Function x
            ∂MeasureTheory.volume :=
            W.upperFace_reflectedGradient_pairing_eq_rhs
              i hφ hgradMain hgradReflected
    _ = ∫ x in openCubeSet Q,
          F x * foldedCubeUpperFaceTest Q i φ x ∂MeasureTheory.volume :=
          setIntegral_mul_foldedCubeUpperFaceMeanZeroH1Test_eq_of_cubeAverage_eq_zero
            i hφ hmean hF
            (integrable_mul_foldedCubeUpperFaceTest_of_integrable_split
              i hFmain hFreflected)
    _ = ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        F (cubeUpperFaceReflection Q i x) * φ x ∂MeasureTheory.volume :=
          setIntegral_mul_foldedCubeUpperFaceTest_reflection_split
            i hFmain hFreflected

/-- One lower-face reflected weak equation with the forcing also split across
the reflected neighboring cube. -/
theorem lowerFace_reflectedGradient_pairing_eq_reflectedRhs
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
    ∫ x in openCubeSet Q,
        vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i
            (W.w.toH1Function.grad (cubeLowerFaceReflection Q i x)))
          (euclideanGradient φ x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        F (cubeLowerFaceReflection Q i x) * φ x ∂MeasureTheory.volume := by
  calc
    ∫ x in openCubeSet Q,
        vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i
            (W.w.toH1Function.grad (cubeLowerFaceReflection Q i x)))
          (euclideanGradient φ x) ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            F x * (foldedCubeLowerFaceMeanZeroH1Test Q i hφ).toH1Function x
            ∂MeasureTheory.volume :=
            W.lowerFace_reflectedGradient_pairing_eq_rhs
              i hφ hgradMain hgradReflected
    _ = ∫ x in openCubeSet Q,
          F x * foldedCubeLowerFaceTest Q i φ x ∂MeasureTheory.volume :=
          setIntegral_mul_foldedCubeLowerFaceMeanZeroH1Test_eq_of_cubeAverage_eq_zero
            i hφ hmean hF
            (integrable_mul_foldedCubeLowerFaceTest_of_integrable_split
              i hFmain hFreflected)
    _ = ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        F (cubeLowerFaceReflection Q i x) * φ x ∂MeasureTheory.volume :=
          setIntegral_mul_foldedCubeLowerFaceTest_reflection_split
            i hFmain hFreflected

/-- Upper-face reflected weak equation written as a single integral over the
doubled open domain `Q ∪ Q⁺`. -/
theorem upperFace_reflectedWeakEquationOnUnion
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
        upperFaceReflectedGradientPairingIntegrand Q i
          (fun y => W.w.toH1Function.grad y) φ x ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        upperFaceReflectedForcingIntegrand Q i F φ x
          ∂MeasureTheory.volume := by
  let G : Vec d → Vec d := fun y => W.w.toH1Function.grad y
  have hgradNeighbor :
      MeasureTheory.Integrable
        (fun x =>
          vecDot
            (coordReflectionLinear i
              (W.w.toH1Function.grad (cubeUpperFaceReflection Q i x)))
            (euclideanGradient φ x))
        (MeasureTheory.volume.restrict (openCubeSet (cubeUpperFaceNeighbor Q i))) := by
    simpa [G] using
      integrable_cubeUpperFaceNeighbor_reflectedField_pairing
        (G := G) hφ Q i hgradReflected
  have hgradQ_piece :
      MeasureTheory.Integrable
        (upperFaceReflectedGradientPairingIntegrand Q i G φ)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    refine hgradMain.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_openCubeSet Q)] with x hx
    simp [upperFaceReflectedGradientPairingIntegrand, G, hx]
  have hgradN_piece :
      MeasureTheory.Integrable
        (upperFaceReflectedGradientPairingIntegrand Q i G φ)
        (MeasureTheory.volume.restrict
          (openCubeSet (cubeUpperFaceNeighbor Q i))) := by
    refine hgradNeighbor.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i))] with x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact (Set.disjoint_left.mp
        (disjoint_openCubeSet_cubeUpperFaceNeighbor Q i)) hxQ hx
    simp [upperFaceReflectedGradientPairingIntegrand, G, hxQ]
  have hforceNeighbor :
      MeasureTheory.Integrable
        (fun x => F (cubeUpperFaceReflection Q i x) * φ x)
        (MeasureTheory.volume.restrict
          (openCubeSet (cubeUpperFaceNeighbor Q i))) :=
    integrable_cubeUpperFaceNeighbor_reflectedScalar_mul Q i hFreflected
  have hforceQ_piece :
      MeasureTheory.Integrable
        (upperFaceReflectedForcingIntegrand Q i F φ)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    refine hFmain.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_openCubeSet Q)] with x hx
    simp [upperFaceReflectedForcingIntegrand, hx]
  have hforceN_piece :
      MeasureTheory.Integrable
        (upperFaceReflectedForcingIntegrand Q i F φ)
        (MeasureTheory.volume.restrict
          (openCubeSet (cubeUpperFaceNeighbor Q i))) := by
    refine hforceNeighbor.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i))] with x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact (Set.disjoint_left.mp
        (disjoint_openCubeSet_cubeUpperFaceNeighbor Q i)) hxQ hx
    simp [upperFaceReflectedForcingIntegrand, hxQ]
  have hgradUnion :=
    setIntegral_openCubeSet_union_upperFaceNeighbor Q i
      (upperFaceReflectedGradientPairingIntegrand Q i G φ)
      hgradQ_piece hgradN_piece
  have hforceUnion :=
    setIntegral_openCubeSet_union_upperFaceNeighbor Q i
      (upperFaceReflectedForcingIntegrand Q i F φ)
      hforceQ_piece hforceN_piece
  have hgradQ_integral :
      ∫ x in openCubeSet Q,
          upperFaceReflectedGradientPairingIntegrand Q i G φ x
          ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet Q) ?_
    intro x hx
    simp [upperFaceReflectedGradientPairingIntegrand, G, hx]
  have hgradN_integral :
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
          upperFaceReflectedGradientPairingIntegrand Q i G φ x
          ∂MeasureTheory.volume =
        ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
          vecDot
            (coordReflectionLinear i
              (W.w.toH1Function.grad (cubeUpperFaceReflection Q i x)))
            (euclideanGradient φ x) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i)) ?_
    intro x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact (Set.disjoint_left.mp
        (disjoint_openCubeSet_cubeUpperFaceNeighbor Q i)) hxQ hx
    simp [upperFaceReflectedGradientPairingIntegrand, G, hxQ]
  have hforceQ_integral :
      ∫ x in openCubeSet Q,
          upperFaceReflectedForcingIntegrand Q i F φ x
          ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet Q) ?_
    intro x hx
    simp [upperFaceReflectedForcingIntegrand, hx]
  have hforceN_integral :
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
          upperFaceReflectedForcingIntegrand Q i F φ x
          ∂MeasureTheory.volume =
        ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
          F (cubeUpperFaceReflection Q i x) * φ x
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeUpperFaceNeighbor Q i)) ?_
    intro x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact (Set.disjoint_left.mp
        (disjoint_openCubeSet_cubeUpperFaceNeighbor Q i)) hxQ hx
    simp [upperFaceReflectedForcingIntegrand, hxQ]
  have hpair :=
    W.upperFace_reflectedGradient_pairing_eq_reflectedRhs
      i hφ hmean hgradMain hgradReflected hF hFmain hFreflected
  calc
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        upperFaceReflectedGradientPairingIntegrand Q i
          (fun y => W.w.toH1Function.grad y) φ x ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
            ∂MeasureTheory.volume +
          ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
            vecDot
              (coordReflectionLinear i
                (W.w.toH1Function.grad (cubeUpperFaceReflection Q i x)))
              (euclideanGradient φ x) ∂MeasureTheory.volume := by
            rw [show
              (∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
                  upperFaceReflectedGradientPairingIntegrand Q i
                    (fun y => W.w.toH1Function.grad y) φ x
                    ∂MeasureTheory.volume) =
                (∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
                  upperFaceReflectedGradientPairingIntegrand Q i G φ x
                    ∂MeasureTheory.volume) by rfl]
            rw [hgradUnion, hgradQ_integral, hgradN_integral]
    _ = ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume +
          ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
            F (cubeUpperFaceReflection Q i x) * φ x
            ∂MeasureTheory.volume := hpair
    _ = ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        upperFaceReflectedForcingIntegrand Q i F φ x
          ∂MeasureTheory.volume := by
            rw [hforceUnion, hforceQ_integral, hforceN_integral]

/-- Lower-face reflected weak equation written as a single integral over the
doubled open domain `Q ∪ Q⁻`. -/
theorem lowerFace_reflectedWeakEquationOnUnion
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
        lowerFaceReflectedGradientPairingIntegrand Q i
          (fun y => W.w.toH1Function.grad y) φ x ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        lowerFaceReflectedForcingIntegrand Q i F φ x
          ∂MeasureTheory.volume := by
  let G : Vec d → Vec d := fun y => W.w.toH1Function.grad y
  have hgradNeighbor :
      MeasureTheory.Integrable
        (fun x =>
          vecDot
            (coordReflectionLinear i
              (W.w.toH1Function.grad (cubeLowerFaceReflection Q i x)))
            (euclideanGradient φ x))
        (MeasureTheory.volume.restrict (openCubeSet (cubeLowerFaceNeighbor Q i))) := by
    simpa [G] using
      integrable_cubeLowerFaceNeighbor_reflectedField_pairing
        (G := G) hφ Q i hgradReflected
  have hgradQ_piece :
      MeasureTheory.Integrable
        (lowerFaceReflectedGradientPairingIntegrand Q i G φ)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    refine hgradMain.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_openCubeSet Q)] with x hx
    simp [lowerFaceReflectedGradientPairingIntegrand, G, hx]
  have hgradN_piece :
      MeasureTheory.Integrable
        (lowerFaceReflectedGradientPairingIntegrand Q i G φ)
        (MeasureTheory.volume.restrict
          (openCubeSet (cubeLowerFaceNeighbor Q i))) := by
    refine hgradNeighbor.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i))] with x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact (Set.disjoint_left.mp
        (disjoint_openCubeSet_cubeLowerFaceNeighbor Q i)) hxQ hx
    simp [lowerFaceReflectedGradientPairingIntegrand, G, hxQ]
  have hforceNeighbor :
      MeasureTheory.Integrable
        (fun x => F (cubeLowerFaceReflection Q i x) * φ x)
        (MeasureTheory.volume.restrict
          (openCubeSet (cubeLowerFaceNeighbor Q i))) :=
    integrable_cubeLowerFaceNeighbor_reflectedScalar_mul Q i hFreflected
  have hforceQ_piece :
      MeasureTheory.Integrable
        (lowerFaceReflectedForcingIntegrand Q i F φ)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    refine hFmain.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_openCubeSet Q)] with x hx
    simp [lowerFaceReflectedForcingIntegrand, hx]
  have hforceN_piece :
      MeasureTheory.Integrable
        (lowerFaceReflectedForcingIntegrand Q i F φ)
        (MeasureTheory.volume.restrict
          (openCubeSet (cubeLowerFaceNeighbor Q i))) := by
    refine hforceNeighbor.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i))] with x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact (Set.disjoint_left.mp
        (disjoint_openCubeSet_cubeLowerFaceNeighbor Q i)) hxQ hx
    simp [lowerFaceReflectedForcingIntegrand, hxQ]
  have hgradUnion :=
    setIntegral_openCubeSet_union_lowerFaceNeighbor Q i
      (lowerFaceReflectedGradientPairingIntegrand Q i G φ)
      hgradQ_piece hgradN_piece
  have hforceUnion :=
    setIntegral_openCubeSet_union_lowerFaceNeighbor Q i
      (lowerFaceReflectedForcingIntegrand Q i F φ)
      hforceQ_piece hforceN_piece
  have hgradQ_integral :
      ∫ x in openCubeSet Q,
          lowerFaceReflectedGradientPairingIntegrand Q i G φ x
          ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet Q) ?_
    intro x hx
    simp [lowerFaceReflectedGradientPairingIntegrand, G, hx]
  have hgradN_integral :
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
          lowerFaceReflectedGradientPairingIntegrand Q i G φ x
          ∂MeasureTheory.volume =
        ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
          vecDot
            (coordReflectionLinear i
              (W.w.toH1Function.grad (cubeLowerFaceReflection Q i x)))
            (euclideanGradient φ x) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i)) ?_
    intro x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact (Set.disjoint_left.mp
        (disjoint_openCubeSet_cubeLowerFaceNeighbor Q i)) hxQ hx
    simp [lowerFaceReflectedGradientPairingIntegrand, G, hxQ]
  have hforceQ_integral :
      ∫ x in openCubeSet Q,
          lowerFaceReflectedForcingIntegrand Q i F φ x
          ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet Q) ?_
    intro x hx
    simp [lowerFaceReflectedForcingIntegrand, hx]
  have hforceN_integral :
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
          lowerFaceReflectedForcingIntegrand Q i F φ x
          ∂MeasureTheory.volume =
        ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
          F (cubeLowerFaceReflection Q i x) * φ x
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i)) ?_
    intro x hx
    have hxQ : x ∉ openCubeSet Q := by
      intro hxQ
      exact (Set.disjoint_left.mp
        (disjoint_openCubeSet_cubeLowerFaceNeighbor Q i)) hxQ hx
    simp [lowerFaceReflectedForcingIntegrand, hxQ]
  have hpair :=
    W.lowerFace_reflectedGradient_pairing_eq_reflectedRhs
      i hφ hmean hgradMain hgradReflected hF hFmain hFreflected
  calc
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        lowerFaceReflectedGradientPairingIntegrand Q i
          (fun y => W.w.toH1Function.grad y) φ x ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
            ∂MeasureTheory.volume +
          ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
            vecDot
              (coordReflectionLinear i
                (W.w.toH1Function.grad (cubeLowerFaceReflection Q i x)))
              (euclideanGradient φ x) ∂MeasureTheory.volume := by
            rw [show
              (∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
                  lowerFaceReflectedGradientPairingIntegrand Q i
                    (fun y => W.w.toH1Function.grad y) φ x
                    ∂MeasureTheory.volume) =
                (∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
                  lowerFaceReflectedGradientPairingIntegrand Q i G φ x
                    ∂MeasureTheory.volume) by rfl]
            rw [hgradUnion, hgradQ_integral, hgradN_integral]
    _ = ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume +
          ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
            F (cubeLowerFaceReflection Q i x) * φ x
            ∂MeasureTheory.volume := hpair
    _ = ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        lowerFaceReflectedForcingIntegrand Q i F φ x
          ∂MeasureTheory.volume := by
            rw [hforceUnion, hforceQ_integral, hforceN_integral]

/-- Compact-test version of the upper-face reflected weak equation. This
derives the side integrability assumptions in
`upperFace_reflectedWeakEquationOnUnion` from the natural `L²` data. -/
theorem upperFace_reflectedWeakEquationOnUnion_of_compactSupport
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        upperFaceReflectedGradientPairingIntegrand Q i
          (fun y => W.w.toH1Function.grad y) φ x ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        upperFaceReflectedForcingIntegrand Q i F φ x
          ∂MeasureTheory.volume := by
  let ψ : Vec d → ℝ := fun z => φ (cubeUpperFaceReflection Q i z)
  let : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ, cubeUpperFaceReflection] using!
      hφ.comp (contDiff_coordFaceReflection (cubeUpperFaceCoord Q i) i)
  have hψs : HasCompactSupport ψ := by
    simpa [ψ] using hasCompactSupport_comp_cubeUpperFaceReflection hφs Q i
  have hgradMain :
      MeasureTheory.Integrable
        (fun x => vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x))
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    have hgradφ :
        MemVectorL2 (openCubeSet Q) (euclideanGradient φ) :=
      memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hφ hφs
    simpa [MeasureTheory.IntegrableOn] using
      integrableOn_vecDot_of_memVectorL2
        (U := openCubeSet Q)
        W.w.toH1Function.grad_memVectorL2 hgradφ
  have hgradReflected :
      MeasureTheory.Integrable
        (fun x =>
          vecDot (W.w.toH1Function.grad x)
            (euclideanGradient (fun z => φ (cubeUpperFaceReflection Q i z)) x))
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    have hgradψ :
        MemVectorL2 (openCubeSet Q) (euclideanGradient ψ) :=
      memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hψ hψs
    simpa [MeasureTheory.IntegrableOn, ψ] using
      integrableOn_vecDot_of_memVectorL2
        (U := openCubeSet Q)
        W.w.toH1Function.grad_memVectorL2 hgradψ
  have hFint :
      MeasureTheory.Integrable F
        (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    hF.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hφL2 :
      MeasureTheory.MemLp φ (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    have hφ_cont : Continuous φ := (hφ.differentiable (by simp)).continuous
    exact (hφ_cont.memLp_of_hasCompactSupport hφs).restrict (openCubeSet Q)
  have hψL2 :
      MeasureTheory.MemLp ψ (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    have hψ_cont : Continuous ψ := (hψ.differentiable (by simp)).continuous
    exact (hψ_cont.memLp_of_hasCompactSupport hψs).restrict (openCubeSet Q)
  have hFmain :
      MeasureTheory.Integrable
        (fun x => F x * φ x)
        (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    hF.integrable_mul hφL2
  have hFreflected :
      MeasureTheory.Integrable
        (fun x => F x * φ (cubeUpperFaceReflection Q i x))
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [ψ] using! hF.integrable_mul hψL2
  exact
    W.upperFace_reflectedWeakEquationOnUnion
      i hφ hmean hgradMain hgradReflected hFint hFmain hFreflected

/-- Compact-test version of the lower-face reflected weak equation. This
derives the side integrability assumptions in
`lowerFace_reflectedWeakEquationOnUnion` from the natural `L²` data. -/
theorem lowerFace_reflectedWeakEquationOnUnion_of_compactSupport
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        lowerFaceReflectedGradientPairingIntegrand Q i
          (fun y => W.w.toH1Function.grad y) φ x ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        lowerFaceReflectedForcingIntegrand Q i F φ x
          ∂MeasureTheory.volume := by
  let ψ : Vec d → ℝ := fun z => φ (cubeLowerFaceReflection Q i z)
  let : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ, cubeLowerFaceReflection] using!
      hφ.comp (contDiff_coordFaceReflection (cubeLowerFaceCoord Q i) i)
  have hψs : HasCompactSupport ψ := by
    simpa [ψ] using hasCompactSupport_comp_cubeLowerFaceReflection hφs Q i
  have hgradMain :
      MeasureTheory.Integrable
        (fun x => vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x))
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    have hgradφ :
        MemVectorL2 (openCubeSet Q) (euclideanGradient φ) :=
      memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hφ hφs
    simpa [MeasureTheory.IntegrableOn] using
      integrableOn_vecDot_of_memVectorL2
        (U := openCubeSet Q)
        W.w.toH1Function.grad_memVectorL2 hgradφ
  have hgradReflected :
      MeasureTheory.Integrable
        (fun x =>
          vecDot (W.w.toH1Function.grad x)
            (euclideanGradient (fun z => φ (cubeLowerFaceReflection Q i z)) x))
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    have hgradψ :
        MemVectorL2 (openCubeSet Q) (euclideanGradient ψ) :=
      memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hψ hψs
    simpa [MeasureTheory.IntegrableOn, ψ] using
      integrableOn_vecDot_of_memVectorL2
        (U := openCubeSet Q)
        W.w.toH1Function.grad_memVectorL2 hgradψ
  have hFint :
      MeasureTheory.Integrable F
        (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    hF.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hφL2 :
      MeasureTheory.MemLp φ (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    have hφ_cont : Continuous φ := (hφ.differentiable (by simp)).continuous
    exact (hφ_cont.memLp_of_hasCompactSupport hφs).restrict (openCubeSet Q)
  have hψL2 :
      MeasureTheory.MemLp ψ (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    have hψ_cont : Continuous ψ := (hψ.differentiable (by simp)).continuous
    exact (hψ_cont.memLp_of_hasCompactSupport hψs).restrict (openCubeSet Q)
  have hFmain :
      MeasureTheory.Integrable
        (fun x => F x * φ x)
        (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    hF.integrable_mul hφL2
  have hFreflected :
      MeasureTheory.Integrable
        (fun x => F x * φ (cubeLowerFaceReflection Q i x))
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [ψ] using! hF.integrable_mul hψL2
  exact
    W.lowerFace_reflectedWeakEquationOnUnion
      i hφ hmean hgradMain hgradReflected hFint hFmain hFreflected

/-- Compact-test weak equation on the original cube. The test need not be
mean-zero: the zero-average forcing hypothesis removes the subtracted constant
from the mean-zero test normalization. -/
theorem weakEquationOnCube_of_compactSupport
    (W : MeanZeroNeumannPoissonSolution Q F)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in openCubeSet Q,
        vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
        ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume := by
  let : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let v : H1Function (openCubeSet Q) :=
    H1Function.ofContDiff (isOpen_openCubeSet Q)
      (hφ.of_le (by simp)) hφs
  let ψ : H1MeanZeroFunction (openCubeSet Q) := v.toMeanZero
  have hgrad_eq :
      ∫ x in openCubeSet Q,
          vecDot (W.w.toH1Function.grad x) (ψ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun
      (measurableSet_openCubeSet Q) ?_
    intro x _hx
    simp [ψ, v, H1Function.ofContDiff]
    change vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x) =
      vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
    rfl
  have hFint :
      MeasureTheory.Integrable F
        (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    hF.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hφL2 :
      MeasureTheory.MemLp φ (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    have hφ_cont : Continuous φ := (hφ.differentiable (by simp)).continuous
    exact (hφ_cont.memLp_of_hasCompactSupport hφs).restrict (openCubeSet Q)
  have hFφ :
      MeasureTheory.Integrable
        (fun x => F x * φ x)
        (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    hF.integrable_mul hφL2
  have hFint_zero :
      ∫ x in openCubeSet Q, F x ∂MeasureTheory.volume = 0 := by
    rw [setIntegral_openCubeSet_eq_cubeVolume_mul_cubeAverage, hmean, mul_zero]
  let c : ℝ := integralAverage (openCubeSet Q) v
  have hforce_eq :
      ∫ x in openCubeSet Q, F x * ψ.toH1Function x
          ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume := by
    calc
      ∫ x in openCubeSet Q, F x * ψ.toH1Function x
          ∂MeasureTheory.volume
          = ∫ x in openCubeSet Q, F x * φ x - F x * c
              ∂MeasureTheory.volume := by
              refine MeasureTheory.setIntegral_congr_fun
                (measurableSet_openCubeSet Q) ?_
              intro x _hx
              simp [ψ, v, H1Function.ofContDiff, c, mul_sub]
      _ = ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume -
            ∫ x in openCubeSet Q, F x * c ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_sub hFφ (hFint.mul_const c)]
      _ = ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_mul_const, hFint_zero]
            ring
  calc
    ∫ x in openCubeSet Q,
        vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
        ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            vecDot (W.w.toH1Function.grad x) (ψ.toH1Function.grad x)
            ∂MeasureTheory.volume := hgrad_eq.symm
    _ = ∫ x in openCubeSet Q, F x * ψ.toH1Function x
          ∂MeasureTheory.volume := W.equation ψ
    _ = ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume := hforce_eq

/-- Compact-test upper-face reflected weak equation, with the right-hand side
given in the normalized cube `L²` measure used by the Poisson endpoint
interfaces. -/
theorem upperFace_reflectedWeakEquationOnUnion_of_compactSupport_of_memLp_normalizedCubeMeasure
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        upperFaceReflectedGradientPairingIntegrand Q i
          (fun y => W.w.toH1Function.grad y) φ x ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i),
        upperFaceReflectedForcingIntegrand Q i F φ x
          ∂MeasureTheory.volume := by
  have hFopen :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [MemL2On, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  exact
    W.upperFace_reflectedWeakEquationOnUnion_of_compactSupport
      i hφ hφs hmean hFopen

/-- Compact-test lower-face reflected weak equation, with the right-hand side
given in the normalized cube `L²` measure used by the Poisson endpoint
interfaces. -/
theorem lowerFace_reflectedWeakEquationOnUnion_of_compactSupport_of_memLp_normalizedCubeMeasure
    (W : MeanZeroNeumannPoissonSolution Q F)
    (i : Fin d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        lowerFaceReflectedGradientPairingIntegrand Q i
          (fun y => W.w.toH1Function.grad y) φ x ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i),
        lowerFaceReflectedForcingIntegrand Q i F φ x
          ∂MeasureTheory.volume := by
  have hFopen :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [MemL2On, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  exact
    W.lowerFace_reflectedWeakEquationOnUnion_of_compactSupport
      i hφ hφs hmean hFopen

/-- Compact-test weak equation on the original cube, with the right-hand side
given in the normalized cube `L²` measure used by the Poisson endpoint
interfaces. -/
theorem weakEquationOnCube_of_compactSupport_of_memLp_normalizedCubeMeasure
    (W : MeanZeroNeumannPoissonSolution Q F)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∫ x in openCubeSet Q,
        vecDot (W.w.toH1Function.grad x) (euclideanGradient φ x)
        ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume := by
  have hFopen :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa [MemL2On, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  exact
    W.weakEquationOnCube_of_compactSupport hφ hφs hmean hFopen

end MeanZeroNeumannPoissonSolution

end

end Homogenization
