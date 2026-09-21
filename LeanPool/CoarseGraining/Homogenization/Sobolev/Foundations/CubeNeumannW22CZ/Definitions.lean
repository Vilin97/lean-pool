/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Reflections
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Folding
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Homeomorphism
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Derivatives

/-! # Definitions -/

namespace Homogenization

open scoped ENNReal

noncomputable section


/-- The folded upper-face test, normalized to the mean-zero Neumann test space.

The normalization subtracts a constant only, so its weak gradient is still the
folded classical gradient. -/
def foldedCubeUpperFaceMeanZeroH1Test {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : H1MeanZeroFunction (openCubeSet Q) := by
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  exact (foldedCubeUpperFaceH1Test Q i hφ).toMeanZero

/-- The folded lower-face test, normalized to the mean-zero Neumann test space.

The normalization subtracts a constant only, so its weak gradient is still the
folded classical gradient. -/
def foldedCubeLowerFaceMeanZeroH1Test {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : H1MeanZeroFunction (openCubeSet Q) := by
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  exact (foldedCubeLowerFaceH1Test Q i hφ).toMeanZero

@[simp] theorem foldedCubeUpperFaceMeanZeroH1Test_grad {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d) :
    (foldedCubeUpperFaceMeanZeroH1Test Q i hφ).toH1Function.grad x =
      euclideanGradient (foldedCubeUpperFaceTest Q i φ) x := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  simp [foldedCubeUpperFaceMeanZeroH1Test]

@[simp] theorem foldedCubeLowerFaceMeanZeroH1Test_grad {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d) :
    (foldedCubeLowerFaceMeanZeroH1Test Q i hφ).toH1Function.grad x =
      euclideanGradient (foldedCubeLowerFaceTest Q i φ) x := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  simp [foldedCubeLowerFaceMeanZeroH1Test]

/-- If the forcing has zero cube average, subtracting the average from a folded
upper-face test does not change the forcing pairing. -/
theorem setIntegral_mul_foldedCubeUpperFaceMeanZeroH1Test_eq_of_cubeAverage_eq_zero
    {d : ℕ} {Q : TriadicCube d} {F φ : Vec d → ℝ}
    (i : Fin d) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.Integrable F
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hfold :
      MeasureTheory.Integrable
        (fun x => F x * foldedCubeUpperFaceTest Q i φ x)
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in openCubeSet Q,
        F x * (foldedCubeUpperFaceMeanZeroH1Test Q i hφ).toH1Function x
        ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q,
        F x * foldedCubeUpperFaceTest Q i φ x ∂MeasureTheory.volume := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let c : ℝ := integralAverage (openCubeSet Q) (foldedCubeUpperFaceH1Test Q i hφ)
  have hFint_zero :
      ∫ x in openCubeSet Q, F x ∂MeasureTheory.volume = 0 := by
    rw [setIntegral_openCubeSet_eq_cubeVolume_mul_cubeAverage, hmean, mul_zero]
  calc
    ∫ x in openCubeSet Q,
        F x * (foldedCubeUpperFaceMeanZeroH1Test Q i hφ).toH1Function x
        ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            F x * foldedCubeUpperFaceTest Q i φ x - F x * c
            ∂MeasureTheory.volume := by
            apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
            intro x _hx
            simp [foldedCubeUpperFaceMeanZeroH1Test, c, mul_sub]
    _ = ∫ x in openCubeSet Q,
          F x * foldedCubeUpperFaceTest Q i φ x ∂MeasureTheory.volume -
        ∫ x in openCubeSet Q, F x * c ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_sub hfold (hF.mul_const c)]
    _ = ∫ x in openCubeSet Q,
          F x * foldedCubeUpperFaceTest Q i φ x ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_mul_const, hFint_zero]
          ring

/-- If the forcing has zero cube average, subtracting the average from a folded
lower-face test does not change the forcing pairing. -/
theorem setIntegral_mul_foldedCubeLowerFaceMeanZeroH1Test_eq_of_cubeAverage_eq_zero
    {d : ℕ} {Q : TriadicCube d} {F φ : Vec d → ℝ}
    (i : Fin d) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.Integrable F
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hfold :
      MeasureTheory.Integrable
        (fun x => F x * foldedCubeLowerFaceTest Q i φ x)
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in openCubeSet Q,
        F x * (foldedCubeLowerFaceMeanZeroH1Test Q i hφ).toH1Function x
        ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q,
        F x * foldedCubeLowerFaceTest Q i φ x ∂MeasureTheory.volume := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let c : ℝ := integralAverage (openCubeSet Q) (foldedCubeLowerFaceH1Test Q i hφ)
  have hFint_zero :
      ∫ x in openCubeSet Q, F x ∂MeasureTheory.volume = 0 := by
    rw [setIntegral_openCubeSet_eq_cubeVolume_mul_cubeAverage, hmean, mul_zero]
  calc
    ∫ x in openCubeSet Q,
        F x * (foldedCubeLowerFaceMeanZeroH1Test Q i hφ).toH1Function x
        ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q,
            F x * foldedCubeLowerFaceTest Q i φ x - F x * c
            ∂MeasureTheory.volume := by
            apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
            intro x _hx
            simp [foldedCubeLowerFaceMeanZeroH1Test, c, mul_sub]
    _ = ∫ x in openCubeSet Q,
          F x * foldedCubeLowerFaceTest Q i φ x ∂MeasureTheory.volume -
        ∫ x in openCubeSet Q, F x * c ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_sub hfold (hF.mul_const c)]
    _ = ∫ x in openCubeSet Q,
          F x * foldedCubeLowerFaceTest Q i φ x ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_mul_const, hFint_zero]
          ring

/-- Split the forcing pairing against a folded upper-face test into the
original cube and its reflected upper-face neighbor. -/
theorem setIntegral_mul_foldedCubeUpperFaceTest_reflection_split
    {d : ℕ} {Q : TriadicCube d} {F φ : Vec d → ℝ}
    (i : Fin d)
    (hmain :
      MeasureTheory.Integrable
        (fun x => F x * φ x)
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hreflected :
      MeasureTheory.Integrable
        (fun x => F x * φ (cubeUpperFaceReflection Q i x))
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in openCubeSet Q,
        F x * foldedCubeUpperFaceTest Q i φ x ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        F (cubeUpperFaceReflection Q i x) * φ x ∂MeasureTheory.volume := by
  let A : Vec d → ℝ := fun x => F x * φ x
  let B : Vec d → ℝ := fun x => F x * φ (cubeUpperFaceReflection Q i x)
  have hreflect :=
    setIntegral_cubeUpperFaceNeighbor_comp_reflection Q i B
  calc
    ∫ x in openCubeSet Q,
        F x * foldedCubeUpperFaceTest Q i φ x ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q, A x + B x ∂MeasureTheory.volume := by
            apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
            intro x _hx
            simp [A, B, foldedCubeUpperFaceTest, foldedCoordFaceTest,
              cubeUpperFaceReflection, mul_add]
    _ = ∫ x in openCubeSet Q, A x ∂MeasureTheory.volume +
        ∫ x in openCubeSet Q, B x ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_add hmain hreflected]
    _ = ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        F (cubeUpperFaceReflection Q i x) * φ x ∂MeasureTheory.volume := by
          rw [show (∫ x in openCubeSet Q, A x ∂MeasureTheory.volume) =
              ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume by rfl]
          rw [show (∫ x in openCubeSet Q, B x ∂MeasureTheory.volume) =
              ∫ x in openCubeSet Q,
                F x * φ (cubeUpperFaceReflection Q i x) ∂MeasureTheory.volume by rfl]
          rw [← hreflect]
          apply congrArg
            (fun t =>
              ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume + t)
          apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet _)
          intro x _hx
          simp [B]

/-- Split the forcing pairing against a folded lower-face test into the
original cube and its reflected lower-face neighbor. -/
theorem setIntegral_mul_foldedCubeLowerFaceTest_reflection_split
    {d : ℕ} {Q : TriadicCube d} {F φ : Vec d → ℝ}
    (i : Fin d)
    (hmain :
      MeasureTheory.Integrable
        (fun x => F x * φ x)
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hreflected :
      MeasureTheory.Integrable
        (fun x => F x * φ (cubeLowerFaceReflection Q i x))
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    ∫ x in openCubeSet Q,
        F x * foldedCubeLowerFaceTest Q i φ x ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        F (cubeLowerFaceReflection Q i x) * φ x ∂MeasureTheory.volume := by
  let A : Vec d → ℝ := fun x => F x * φ x
  let B : Vec d → ℝ := fun x => F x * φ (cubeLowerFaceReflection Q i x)
  have hreflect :=
    setIntegral_cubeLowerFaceNeighbor_comp_reflection Q i B
  calc
    ∫ x in openCubeSet Q,
        F x * foldedCubeLowerFaceTest Q i φ x ∂MeasureTheory.volume
        = ∫ x in openCubeSet Q, A x + B x ∂MeasureTheory.volume := by
            apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
            intro x _hx
            simp [A, B, foldedCubeLowerFaceTest, foldedCoordFaceTest,
              cubeLowerFaceReflection, mul_add]
    _ = ∫ x in openCubeSet Q, A x ∂MeasureTheory.volume +
        ∫ x in openCubeSet Q, B x ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_add hmain hreflected]
    _ = ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume +
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        F (cubeLowerFaceReflection Q i x) * φ x ∂MeasureTheory.volume := by
          rw [show (∫ x in openCubeSet Q, A x ∂MeasureTheory.volume) =
              ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume by rfl]
          rw [show (∫ x in openCubeSet Q, B x ∂MeasureTheory.volume) =
              ∫ x in openCubeSet Q,
                F x * φ (cubeLowerFaceReflection Q i x) ∂MeasureTheory.volume by rfl]
          rw [← hreflect]
          apply congrArg
            (fun t =>
              ∫ x in openCubeSet Q, F x * φ x ∂MeasureTheory.volume + t)
          apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet _)
          intro x _hx
          simp [B]

/-- Integrability of the upper-face folded forcing pairing follows from
integrability of the original and reflected pieces. -/
theorem integrable_mul_foldedCubeUpperFaceTest_of_integrable_split
    {d : ℕ} {Q : TriadicCube d} {F φ : Vec d → ℝ}
    (i : Fin d)
    (hmain :
      MeasureTheory.Integrable
        (fun x => F x * φ x)
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hreflected :
      MeasureTheory.Integrable
        (fun x => F x * φ (cubeUpperFaceReflection Q i x))
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    MeasureTheory.Integrable
      (fun x => F x * foldedCubeUpperFaceTest Q i φ x)
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  let A : Vec d → ℝ := fun x => F x * φ x
  let B : Vec d → ℝ := fun x => F x * φ (cubeUpperFaceReflection Q i x)
  have hsum :
      MeasureTheory.Integrable (fun x => A x + B x)
        (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    hmain.add hreflected
  refine hsum.congr ?_
  filter_upwards with x
  simp [A, B, foldedCubeUpperFaceTest, foldedCoordFaceTest,
    cubeUpperFaceReflection, mul_add]

/-- Integrability of the lower-face folded forcing pairing follows from
integrability of the original and reflected pieces. -/
theorem integrable_mul_foldedCubeLowerFaceTest_of_integrable_split
    {d : ℕ} {Q : TriadicCube d} {F φ : Vec d → ℝ}
    (i : Fin d)
    (hmain :
      MeasureTheory.Integrable
        (fun x => F x * φ x)
        (MeasureTheory.volume.restrict (openCubeSet Q)))
    (hreflected :
      MeasureTheory.Integrable
        (fun x => F x * φ (cubeLowerFaceReflection Q i x))
        (MeasureTheory.volume.restrict (openCubeSet Q))) :
    MeasureTheory.Integrable
      (fun x => F x * foldedCubeLowerFaceTest Q i φ x)
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  let A : Vec d → ℝ := fun x => F x * φ x
  let B : Vec d → ℝ := fun x => F x * φ (cubeLowerFaceReflection Q i x)
  have hsum :
      MeasureTheory.Integrable (fun x => A x + B x)
        (MeasureTheory.volume.restrict (openCubeSet Q)) :=
    hmain.add hreflected
  refine hsum.congr ?_
  filter_upwards with x
  simp [A, B, foldedCubeLowerFaceTest, foldedCoordFaceTest,
    cubeLowerFaceReflection, mul_add]

/-- Piecewise gradient-pairing integrand for the upper-face doubled domain:
the original field on `Q`, and the reflected field on the upper neighbor. -/
def upperFaceReflectedGradientPairingIntegrand {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (G : Vec d → Vec d)
    (φ : Vec d → ℝ) : Vec d → ℝ := by
  classical
  exact fun x =>
    if x ∈ openCubeSet Q then
      vecDot (G x) (euclideanGradient φ x)
    else
      vecDot
        (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
        (euclideanGradient φ x)

/-- Piecewise gradient-pairing integrand for the lower-face doubled domain:
the original field on `Q`, and the reflected field on the lower neighbor. -/
def lowerFaceReflectedGradientPairingIntegrand {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (G : Vec d → Vec d)
    (φ : Vec d → ℝ) : Vec d → ℝ := by
  classical
  exact fun x =>
    if x ∈ openCubeSet Q then
      vecDot (G x) (euclideanGradient φ x)
    else
      vecDot
        (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
        (euclideanGradient φ x)

/-- Piecewise forcing integrand for the upper-face doubled domain: the
original forcing on `Q`, and the reflected forcing on the upper neighbor. -/
def upperFaceReflectedForcingIntegrand {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (F φ : Vec d → ℝ) :
    Vec d → ℝ := by
  classical
  exact fun x =>
    if x ∈ openCubeSet Q then
      F x * φ x
    else
      F (cubeUpperFaceReflection Q i x) * φ x

/-- Piecewise forcing integrand for the lower-face doubled domain: the
original forcing on `Q`, and the reflected forcing on the lower neighbor. -/
def lowerFaceReflectedForcingIntegrand {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (F φ : Vec d → ℝ) :
    Vec d → ℝ := by
  classical
  exact fun x =>
    if x ∈ openCubeSet Q then
      F x * φ x
    else
      F (cubeLowerFaceReflection Q i x) * φ x

/-- Even-reflected vector field across the upper face of `Q`, written on the
doubled domain by using the original field on `Q` and the reflected field on
the neighboring cube. -/
def upperFaceReflectedVectorField {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (G : Vec d → Vec d) :
    Vec d → Vec d := by
  classical
  exact fun x =>
    if x ∈ openCubeSet Q then
      G x
    else
      coordReflectionLinear i (G (cubeUpperFaceReflection Q i x))

/-- Even-reflected vector field across the lower face of `Q`. -/
def lowerFaceReflectedVectorField {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (G : Vec d → Vec d) :
    Vec d → Vec d := by
  classical
  exact fun x =>
    if x ∈ openCubeSet Q then
      G x
    else
      coordReflectionLinear i (G (cubeLowerFaceReflection Q i x))

/-- Even-reflected scalar forcing across the upper face of `Q`. -/
def upperFaceReflectedScalar {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (F : Vec d → ℝ) :
    Vec d → ℝ := by
  classical
  exact fun x =>
    if x ∈ openCubeSet Q then
      F x
    else
      F (cubeUpperFaceReflection Q i x)

/-- Even-reflected scalar forcing across the lower face of `Q`. -/
def lowerFaceReflectedScalar {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (F : Vec d → ℝ) :
    Vec d → ℝ := by
  classical
  exact fun x =>
    if x ∈ openCubeSet Q then
      F x
    else
      F (cubeLowerFaceReflection Q i x)

/-- Even-reflected vector field on the one-coordinate lower/original/upper
face-neighbor slab. -/
def faceNeighborSlabReflectedVectorField {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (G : Vec d → Vec d) :
    Vec d → Vec d := by
  classical
  exact fun x =>
    if x ∈ openCubeSet (cubeLowerFaceNeighbor Q i) then
      coordReflectionLinear i (G (cubeLowerFaceReflection Q i x))
    else if x ∈ openCubeSet Q then
      G x
    else
      coordReflectionLinear i (G (cubeUpperFaceReflection Q i x))

/-- Even-reflected scalar forcing on the one-coordinate lower/original/upper
face-neighbor slab. -/
def faceNeighborSlabReflectedScalar {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (F : Vec d → ℝ) :
    Vec d → ℝ := by
  classical
  exact fun x =>
    if x ∈ openCubeSet (cubeLowerFaceNeighbor Q i) then
      F (cubeLowerFaceReflection Q i x)
    else if x ∈ openCubeSet Q then
      F x
    else
      F (cubeUpperFaceReflection Q i x)

@[simp] theorem faceNeighborSlabReflectedVectorField_of_mem_lower {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (G : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet (cubeLowerFaceNeighbor Q i)) :
    faceNeighborSlabReflectedVectorField Q i G x =
      coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)) := by
  simp [faceNeighborSlabReflectedVectorField, hx]

@[simp] theorem faceNeighborSlabReflectedScalar_of_mem_lower {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (F : Vec d → ℝ)
    {x : Vec d} (hx : x ∈ openCubeSet (cubeLowerFaceNeighbor Q i)) :
    faceNeighborSlabReflectedScalar Q i F x =
      F (cubeLowerFaceReflection Q i x) := by
  simp [faceNeighborSlabReflectedScalar, hx]

@[simp] theorem faceNeighborSlabReflectedVectorField_of_mem_cube {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (G : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    faceNeighborSlabReflectedVectorField Q i G x = G x := by
  have hxL : x ∉ openCubeSet (cubeLowerFaceNeighbor Q i) := by
    exact (Set.disjoint_left.mp
      (disjoint_openCubeSet_cubeLowerFaceNeighbor Q i) hx)
  simp [faceNeighborSlabReflectedVectorField, hx, hxL]

@[simp] theorem faceNeighborSlabReflectedScalar_of_mem_cube {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (F : Vec d → ℝ)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    faceNeighborSlabReflectedScalar Q i F x = F x := by
  have hxL : x ∉ openCubeSet (cubeLowerFaceNeighbor Q i) := by
    exact (Set.disjoint_left.mp
      (disjoint_openCubeSet_cubeLowerFaceNeighbor Q i) hx)
  simp [faceNeighborSlabReflectedScalar, hx, hxL]

@[simp] theorem faceNeighborSlabReflectedVectorField_of_mem_upper {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (G : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet (cubeUpperFaceNeighbor Q i)) :
    faceNeighborSlabReflectedVectorField Q i G x =
      coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)) := by
  have hxL : x ∉ openCubeSet (cubeLowerFaceNeighbor Q i) := by
    intro hxL
    exact
      (Set.disjoint_left.mp
        (disjoint_cubeLowerFaceNeighbor_cubeUpperFaceNeighbor Q i)
        hxL) hx
  have hxQ : x ∉ openCubeSet Q := by
    intro hxQ
    exact
      (Set.disjoint_left.mp
        (disjoint_openCubeSet_cubeUpperFaceNeighbor Q i)
        hxQ) hx
  simp [faceNeighborSlabReflectedVectorField, hxL, hxQ]

@[simp] theorem faceNeighborSlabReflectedScalar_of_mem_upper {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (F : Vec d → ℝ)
    {x : Vec d} (hx : x ∈ openCubeSet (cubeUpperFaceNeighbor Q i)) :
    faceNeighborSlabReflectedScalar Q i F x =
      F (cubeUpperFaceReflection Q i x) := by
  have hxL : x ∉ openCubeSet (cubeLowerFaceNeighbor Q i) := by
    intro hxL
    exact
      (Set.disjoint_left.mp
        (disjoint_cubeLowerFaceNeighbor_cubeUpperFaceNeighbor Q i)
        hxL) hx
  have hxQ : x ∉ openCubeSet Q := by
    intro hxQ
    exact
      (Set.disjoint_left.mp
        (disjoint_openCubeSet_cubeUpperFaceNeighbor Q i)
        hxQ) hx
  simp [faceNeighborSlabReflectedScalar, hxL, hxQ]

/-- On the lower slab cube, the all-coordinate reflected scalar agrees with
the one-coordinate slab reflected scalar. -/
theorem cubeCoordinateFoldReflectedScalar_eq_faceNeighborSlabReflectedScalar_of_mem_lower
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (F : Vec d → ℝ)
    {x : Vec d} (hx : x ∈ openCubeSet (cubeLowerFaceNeighbor Q i)) :
    cubeCoordinateFoldReflectedScalar Q F x =
      faceNeighborSlabReflectedScalar Q i F x := by
  rw [faceNeighborSlabReflectedScalar_of_mem_lower Q i F hx]
  simp [cubeCoordinateFoldReflectedScalar,
    cubeCoordinateFold_eq_cubeLowerFaceReflection_of_mem_neighbor Q i hx]

/-- On the original cube, the all-coordinate reflected scalar agrees with the
one-coordinate slab reflected scalar. -/
theorem cubeCoordinateFoldReflectedScalar_eq_faceNeighborSlabReflectedScalar_of_mem_cube
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (F : Vec d → ℝ)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    cubeCoordinateFoldReflectedScalar Q F x =
      faceNeighborSlabReflectedScalar Q i F x := by
  rw [faceNeighborSlabReflectedScalar_of_mem_cube Q i F hx]
  exact cubeCoordinateFoldReflectedScalar_eq_self_of_mem_openCubeSet Q F hx

/-- On the upper slab cube, the all-coordinate reflected scalar agrees with
the one-coordinate slab reflected scalar. -/
theorem cubeCoordinateFoldReflectedScalar_eq_faceNeighborSlabReflectedScalar_of_mem_upper
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (F : Vec d → ℝ)
    {x : Vec d} (hx : x ∈ openCubeSet (cubeUpperFaceNeighbor Q i)) :
    cubeCoordinateFoldReflectedScalar Q F x =
      faceNeighborSlabReflectedScalar Q i F x := by
  rw [faceNeighborSlabReflectedScalar_of_mem_upper Q i F hx]
  simp [cubeCoordinateFoldReflectedScalar,
    cubeCoordinateFold_eq_cubeUpperFaceReflection_of_mem_neighbor Q i hx]

/-- On the lower slab cube, the all-coordinate reflected vector field agrees
with the one-coordinate slab reflected vector field. -/
theorem cubeCoordinateFoldReflectedVectorField_eq_faceNeighborSlabReflectedVectorField_of_mem_lower
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (G : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet (cubeLowerFaceNeighbor Q i)) :
    cubeCoordinateFoldReflectedVectorField Q G x =
      faceNeighborSlabReflectedVectorField Q i G x := by
  rw [faceNeighborSlabReflectedVectorField_of_mem_lower Q i G hx]
  ext j
  by_cases hji : j = i
  · subst j
    simp [cubeCoordinateFoldReflectedVectorField,
      cubeCoordinateFold_eq_cubeLowerFaceReflection_of_mem_neighbor Q i hx,
      cubeCoordinateFoldSign_of_mem_cubeLowerFaceNeighbor Q i hx]
  · simp [cubeCoordinateFoldReflectedVectorField,
      cubeCoordinateFold_eq_cubeLowerFaceReflection_of_mem_neighbor Q i hx,
      cubeCoordinateFoldSign_of_mem_cubeLowerFaceNeighbor Q i hx, hji]

/-- On the original cube, the all-coordinate reflected vector field agrees
with the one-coordinate slab reflected vector field. -/
theorem cubeCoordinateFoldReflectedVectorField_eq_faceNeighborSlabReflectedVectorField_of_mem_cube
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (G : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    cubeCoordinateFoldReflectedVectorField Q G x =
      faceNeighborSlabReflectedVectorField Q i G x := by
  rw [faceNeighborSlabReflectedVectorField_of_mem_cube Q i G hx]
  exact cubeCoordinateFoldReflectedVectorField_eq_self_of_mem_openCubeSet Q G hx

/-- On the upper slab cube, the all-coordinate reflected vector field agrees
with the one-coordinate slab reflected vector field. -/
theorem cubeCoordinateFoldReflectedVectorField_eq_faceNeighborSlabReflectedVectorField_of_mem_upper
    {d : ℕ} (Q : TriadicCube d) (i : Fin d) (G : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet (cubeUpperFaceNeighbor Q i)) :
    cubeCoordinateFoldReflectedVectorField Q G x =
      faceNeighborSlabReflectedVectorField Q i G x := by
  rw [faceNeighborSlabReflectedVectorField_of_mem_upper Q i G hx]
  ext j
  by_cases hji : j = i
  · subst j
    simp [cubeCoordinateFoldReflectedVectorField,
      cubeCoordinateFold_eq_cubeUpperFaceReflection_of_mem_neighbor Q i hx,
      cubeCoordinateFoldSign_of_mem_cubeUpperFaceNeighbor Q i hx]
  · simp [cubeCoordinateFoldReflectedVectorField,
      cubeCoordinateFold_eq_cubeUpperFaceReflection_of_mem_neighbor Q i hx,
      cubeCoordinateFoldSign_of_mem_cubeUpperFaceNeighbor Q i hx, hji]

/-- The upper-face reflected scalar forcing is `L²` on the doubled
cube-neighbor domain whenever the original forcing is `L²` on `Q`. -/
theorem memScalarL2_openCubeSet_union_upperFaceReflectedScalar {d : ℕ}
    {F : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    MemScalarL2
      (openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i))
      (upperFaceReflectedScalar Q i F) := by
  classical
  let U := openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i)
  let S := openCubeSet Q
  let R : Vec d → ℝ := fun x => F (cubeUpperFaceReflection Q i x)
  have hR : MemScalarL2 (openCubeSet (cubeUpperFaceNeighbor Q i)) R :=
    memScalarL2_cubeUpperFaceNeighbor_comp_reflection Q i hF
  have hmain :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        ((MeasureTheory.volume.restrict U).restrict S) := by
    exact hF.mono_measure
      (MeasureTheory.Measure.restrict_mono_measure
        MeasureTheory.Measure.restrict_le_self S)
  have hreflected :
      MeasureTheory.MemLp R (2 : ℝ≥0∞)
        ((MeasureTheory.volume.restrict U).restrict Sᶜ) := by
    have hmeasure :
        (MeasureTheory.volume.restrict U).restrict Sᶜ ≤
          MeasureTheory.volume.restrict
            (openCubeSet (cubeUpperFaceNeighbor Q i)) := by
      rw [MeasureTheory.Measure.restrict_restrict
        (measurableSet_openCubeSet Q).compl]
      refine MeasureTheory.Measure.restrict_mono_set
        MeasureTheory.volume ?_
      intro x hx
      rcases hx.2 with hxQ | hxN
      · exact False.elim (hx.1 hxQ)
      · exact hxN
    exact hR.mono_measure hmeasure
  have hpiece :
      MeasureTheory.MemLp (S.piecewise F R) (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict U) :=
    MeasureTheory.MemLp.piecewise
      (μ := MeasureTheory.volume.restrict U) (s := S)
      (p := (2 : ℝ≥0∞)) (measurableSet_openCubeSet Q)
      hmain hreflected
  simpa [MemScalarL2, volumeMeasureOn, upperFaceReflectedScalar, U, S, R,
    Set.piecewise] using! hpiece

/-- The lower-face reflected scalar forcing is `L²` on the doubled
cube-neighbor domain whenever the original forcing is `L²` on `Q`. -/
theorem memScalarL2_openCubeSet_union_lowerFaceReflectedScalar {d : ℕ}
    {F : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    MemScalarL2
      (openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i))
      (lowerFaceReflectedScalar Q i F) := by
  classical
  let U := openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i)
  let S := openCubeSet Q
  let R : Vec d → ℝ := fun x => F (cubeLowerFaceReflection Q i x)
  have hR : MemScalarL2 (openCubeSet (cubeLowerFaceNeighbor Q i)) R :=
    memScalarL2_cubeLowerFaceNeighbor_comp_reflection Q i hF
  have hmain :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        ((MeasureTheory.volume.restrict U).restrict S) := by
    exact hF.mono_measure
      (MeasureTheory.Measure.restrict_mono_measure
        MeasureTheory.Measure.restrict_le_self S)
  have hreflected :
      MeasureTheory.MemLp R (2 : ℝ≥0∞)
        ((MeasureTheory.volume.restrict U).restrict Sᶜ) := by
    have hmeasure :
        (MeasureTheory.volume.restrict U).restrict Sᶜ ≤
          MeasureTheory.volume.restrict
            (openCubeSet (cubeLowerFaceNeighbor Q i)) := by
      rw [MeasureTheory.Measure.restrict_restrict
        (measurableSet_openCubeSet Q).compl]
      refine MeasureTheory.Measure.restrict_mono_set
        MeasureTheory.volume ?_
      intro x hx
      rcases hx.2 with hxQ | hxN
      · exact False.elim (hx.1 hxQ)
      · exact hxN
    exact hR.mono_measure hmeasure
  have hpiece :
      MeasureTheory.MemLp (S.piecewise F R) (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict U) :=
    MeasureTheory.MemLp.piecewise
      (μ := MeasureTheory.volume.restrict U) (s := S)
      (p := (2 : ℝ≥0∞)) (measurableSet_openCubeSet Q)
      hmain hreflected
  simpa [MemScalarL2, volumeMeasureOn, lowerFaceReflectedScalar, U, S, R,
    Set.piecewise] using! hpiece

/-- The upper-face reflected vector field is `L²` on the doubled
cube-neighbor domain whenever the original vector field is `L²` on `Q`. -/
theorem memVectorL2_openCubeSet_union_upperFaceReflectedVectorField {d : ℕ}
    {G : Vec d → Vec d} (Q : TriadicCube d) (i : Fin d)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    MemVectorL2
      (openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i))
      (upperFaceReflectedVectorField Q i G) := by
  classical
  let U := openCubeSet Q ∪ openCubeSet (cubeUpperFaceNeighbor Q i)
  let S := openCubeSet Q
  let R : Vec d → Vec d :=
    fun x => coordReflectionLinear i (G (cubeUpperFaceReflection Q i x))
  have hR : MemVectorL2 (openCubeSet (cubeUpperFaceNeighbor Q i)) R :=
    memVectorL2_cubeUpperFaceNeighbor_reflected Q i hG
  have hmain :
      MeasureTheory.MemLp G (2 : ℝ≥0∞)
        ((MeasureTheory.volume.restrict U).restrict S) := by
    exact hG.mono_measure
      (MeasureTheory.Measure.restrict_mono_measure
        MeasureTheory.Measure.restrict_le_self S)
  have hreflected :
      MeasureTheory.MemLp R (2 : ℝ≥0∞)
        ((MeasureTheory.volume.restrict U).restrict Sᶜ) := by
    have hmeasure :
        (MeasureTheory.volume.restrict U).restrict Sᶜ ≤
          MeasureTheory.volume.restrict
            (openCubeSet (cubeUpperFaceNeighbor Q i)) := by
      rw [MeasureTheory.Measure.restrict_restrict
        (measurableSet_openCubeSet Q).compl]
      refine MeasureTheory.Measure.restrict_mono_set
        MeasureTheory.volume ?_
      intro x hx
      rcases hx.2 with hxQ | hxN
      · exact False.elim (hx.1 hxQ)
      · exact hxN
    exact hR.mono_measure hmeasure
  have hpiece :
      MeasureTheory.MemLp (S.piecewise G R) (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict U) :=
    MeasureTheory.MemLp.piecewise
      (μ := MeasureTheory.volume.restrict U) (s := S)
      (p := (2 : ℝ≥0∞)) (measurableSet_openCubeSet Q)
      hmain hreflected
  simpa [MemVectorL2, volumeMeasureOn, upperFaceReflectedVectorField, U, S, R,
    Set.piecewise] using! hpiece

/-- The lower-face reflected vector field is `L²` on the doubled
cube-neighbor domain whenever the original vector field is `L²` on `Q`. -/
theorem memVectorL2_openCubeSet_union_lowerFaceReflectedVectorField {d : ℕ}
    {G : Vec d → Vec d} (Q : TriadicCube d) (i : Fin d)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    MemVectorL2
      (openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i))
      (lowerFaceReflectedVectorField Q i G) := by
  classical
  let U := openCubeSet Q ∪ openCubeSet (cubeLowerFaceNeighbor Q i)
  let S := openCubeSet Q
  let R : Vec d → Vec d :=
    fun x => coordReflectionLinear i (G (cubeLowerFaceReflection Q i x))
  have hR : MemVectorL2 (openCubeSet (cubeLowerFaceNeighbor Q i)) R :=
    memVectorL2_cubeLowerFaceNeighbor_reflected Q i hG
  have hmain :
      MeasureTheory.MemLp G (2 : ℝ≥0∞)
        ((MeasureTheory.volume.restrict U).restrict S) := by
    exact hG.mono_measure
      (MeasureTheory.Measure.restrict_mono_measure
        MeasureTheory.Measure.restrict_le_self S)
  have hreflected :
      MeasureTheory.MemLp R (2 : ℝ≥0∞)
        ((MeasureTheory.volume.restrict U).restrict Sᶜ) := by
    have hmeasure :
        (MeasureTheory.volume.restrict U).restrict Sᶜ ≤
          MeasureTheory.volume.restrict
            (openCubeSet (cubeLowerFaceNeighbor Q i)) := by
      rw [MeasureTheory.Measure.restrict_restrict
        (measurableSet_openCubeSet Q).compl]
      refine MeasureTheory.Measure.restrict_mono_set
        MeasureTheory.volume ?_
      intro x hx
      rcases hx.2 with hxQ | hxN
      · exact False.elim (hx.1 hxQ)
      · exact hxN
    exact hR.mono_measure hmeasure
  have hpiece :
      MeasureTheory.MemLp (S.piecewise G R) (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict U) :=
    MeasureTheory.MemLp.piecewise
      (μ := MeasureTheory.volume.restrict U) (s := S)
      (p := (2 : ℝ≥0∞)) (measurableSet_openCubeSet Q)
      hmain hreflected
  simpa [MemVectorL2, volumeMeasureOn, lowerFaceReflectedVectorField, U, S, R,
    Set.piecewise] using! hpiece

/-- The one-coordinate slab-reflected scalar forcing is `L²` on the
lower/original/upper face-neighbor slab whenever the original forcing is `L²`
on `Q`. -/
theorem memScalarL2_cubeFaceNeighborSlabSet_faceNeighborSlabReflectedScalar
    {d : ℕ} {F : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    MemScalarL2 (cubeFaceNeighborSlabSet Q i)
      (faceNeighborSlabReflectedScalar Q i F) := by
  classical
  let L := openCubeSet (cubeLowerFaceNeighbor Q i)
  let M := openCubeSet Q
  let U := openCubeSet (cubeUpperFaceNeighbor Q i)
  let S := cubeFaceNeighborSlabSet Q i
  let lower : Vec d → ℝ := fun x => F (cubeLowerFaceReflection Q i x)
  let upper : Vec d → ℝ := fun x => F (cubeUpperFaceReflection Q i x)
  have hLower : MemScalarL2 L lower :=
    memScalarL2_cubeLowerFaceNeighbor_comp_reflection Q i hF
  have hUpper : MemScalarL2 U upper :=
    memScalarL2_cubeUpperFaceNeighbor_comp_reflection Q i hF
  have hleft :
      MeasureTheory.MemLp lower (2 : ℝ≥0∞)
        ((MeasureTheory.volume.restrict S).restrict L) := by
    exact hLower.mono_measure
      (MeasureTheory.Measure.restrict_mono_measure
        MeasureTheory.Measure.restrict_le_self L)
  have hmid :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (((MeasureTheory.volume.restrict S).restrict Lᶜ).restrict M) := by
    exact hF.mono_measure <| by
      calc
        ((MeasureTheory.volume.restrict S).restrict Lᶜ).restrict M
            ≤ (MeasureTheory.volume.restrict S).restrict M :=
              MeasureTheory.Measure.restrict_mono_measure
                MeasureTheory.Measure.restrict_le_self M
        _ ≤ MeasureTheory.volume.restrict M :=
              MeasureTheory.Measure.restrict_mono_measure
                MeasureTheory.Measure.restrict_le_self M
  have hrightMeasure :
      (((MeasureTheory.volume.restrict S).restrict Lᶜ).restrict Mᶜ) ≤
        MeasureTheory.volume.restrict U := by
    have hMeasM : MeasurableSet M := measurableSet_openCubeSet Q
    have hMeasL : MeasurableSet L :=
      measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i)
    have hMeasML : MeasurableSet (Mᶜ ∩ Lᶜ) :=
      hMeasM.compl.inter hMeasL.compl
    rw [MeasureTheory.Measure.restrict_restrict hMeasM.compl]
    rw [MeasureTheory.Measure.restrict_restrict hMeasML]
    refine MeasureTheory.Measure.restrict_mono_set
      MeasureTheory.volume ?_
    intro x hx
    rcases hx.2 with hLM | hxU
    · rcases hLM with hxL | hxM
      · exact False.elim (hx.1.2 hxL)
      · exact False.elim (hx.1.1 hxM)
    · exact hxU
  have hright :
      MeasureTheory.MemLp upper (2 : ℝ≥0∞)
        (((MeasureTheory.volume.restrict S).restrict Lᶜ).restrict Mᶜ) :=
    hUpper.mono_measure hrightMeasure
  have htail :
      MeasureTheory.MemLp (M.piecewise F upper) (2 : ℝ≥0∞)
        ((MeasureTheory.volume.restrict S).restrict Lᶜ) :=
    MeasureTheory.MemLp.piecewise
      (μ := (MeasureTheory.volume.restrict S).restrict Lᶜ)
      (s := M) (p := (2 : ℝ≥0∞)) (measurableSet_openCubeSet Q)
      hmid hright
  have hpiece :
      MeasureTheory.MemLp (L.piecewise lower (M.piecewise F upper))
        (2 : ℝ≥0∞) (MeasureTheory.volume.restrict S) :=
    MeasureTheory.MemLp.piecewise
      (μ := MeasureTheory.volume.restrict S) (s := L)
      (p := (2 : ℝ≥0∞))
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i))
      hleft htail
  simpa [MemScalarL2, volumeMeasureOn, faceNeighborSlabReflectedScalar,
    Set.piecewise, S, L, M, U, lower, upper] using! hpiece

/-- The one-coordinate slab-reflected vector field is `L²` on the
lower/original/upper face-neighbor slab whenever the original vector field is
`L²` on `Q`. -/
theorem memVectorL2_cubeFaceNeighborSlabSet_faceNeighborSlabReflectedVectorField
    {d : ℕ} {G : Vec d → Vec d} (Q : TriadicCube d) (i : Fin d)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    MemVectorL2 (cubeFaceNeighborSlabSet Q i)
      (faceNeighborSlabReflectedVectorField Q i G) := by
  classical
  let L := openCubeSet (cubeLowerFaceNeighbor Q i)
  let M := openCubeSet Q
  let U := openCubeSet (cubeUpperFaceNeighbor Q i)
  let S := cubeFaceNeighborSlabSet Q i
  let lower : Vec d → Vec d :=
    fun x => coordReflectionLinear i (G (cubeLowerFaceReflection Q i x))
  let upper : Vec d → Vec d :=
    fun x => coordReflectionLinear i (G (cubeUpperFaceReflection Q i x))
  have hLower : MemVectorL2 L lower :=
    memVectorL2_cubeLowerFaceNeighbor_reflected Q i hG
  have hUpper : MemVectorL2 U upper :=
    memVectorL2_cubeUpperFaceNeighbor_reflected Q i hG
  have hleft :
      MeasureTheory.MemLp lower (2 : ℝ≥0∞)
        ((MeasureTheory.volume.restrict S).restrict L) := by
    exact hLower.mono_measure
      (MeasureTheory.Measure.restrict_mono_measure
        MeasureTheory.Measure.restrict_le_self L)
  have hmid :
      MeasureTheory.MemLp G (2 : ℝ≥0∞)
        (((MeasureTheory.volume.restrict S).restrict Lᶜ).restrict M) := by
    exact hG.mono_measure <| by
      calc
        ((MeasureTheory.volume.restrict S).restrict Lᶜ).restrict M
            ≤ (MeasureTheory.volume.restrict S).restrict M :=
              MeasureTheory.Measure.restrict_mono_measure
                MeasureTheory.Measure.restrict_le_self M
        _ ≤ MeasureTheory.volume.restrict M :=
              MeasureTheory.Measure.restrict_mono_measure
                MeasureTheory.Measure.restrict_le_self M
  have hrightMeasure :
      (((MeasureTheory.volume.restrict S).restrict Lᶜ).restrict Mᶜ) ≤
        MeasureTheory.volume.restrict U := by
    have hMeasM : MeasurableSet M := measurableSet_openCubeSet Q
    have hMeasL : MeasurableSet L :=
      measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i)
    have hMeasML : MeasurableSet (Mᶜ ∩ Lᶜ) :=
      hMeasM.compl.inter hMeasL.compl
    rw [MeasureTheory.Measure.restrict_restrict hMeasM.compl]
    rw [MeasureTheory.Measure.restrict_restrict hMeasML]
    refine MeasureTheory.Measure.restrict_mono_set
      MeasureTheory.volume ?_
    intro x hx
    rcases hx.2 with hLM | hxU
    · rcases hLM with hxL | hxM
      · exact False.elim (hx.1.2 hxL)
      · exact False.elim (hx.1.1 hxM)
    · exact hxU
  have hright :
      MeasureTheory.MemLp upper (2 : ℝ≥0∞)
        (((MeasureTheory.volume.restrict S).restrict Lᶜ).restrict Mᶜ) :=
    hUpper.mono_measure hrightMeasure
  have htail :
      MeasureTheory.MemLp (M.piecewise G upper) (2 : ℝ≥0∞)
        ((MeasureTheory.volume.restrict S).restrict Lᶜ) :=
    MeasureTheory.MemLp.piecewise
      (μ := (MeasureTheory.volume.restrict S).restrict Lᶜ)
      (s := M) (p := (2 : ℝ≥0∞)) (measurableSet_openCubeSet Q)
      hmid hright
  have hpiece :
      MeasureTheory.MemLp (L.piecewise lower (M.piecewise G upper))
        (2 : ℝ≥0∞) (MeasureTheory.volume.restrict S) :=
    MeasureTheory.MemLp.piecewise
      (μ := MeasureTheory.volume.restrict S) (s := L)
      (p := (2 : ℝ≥0∞))
      (measurableSet_openCubeSet (cubeLowerFaceNeighbor Q i))
      hleft htail
  simpa [MemVectorL2, volumeMeasureOn, faceNeighborSlabReflectedVectorField,
    Set.piecewise, S, L, M, U, lower, upper] using! hpiece

end

end Homogenization
