/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentTestFold
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.WeakDerivativeTestClosure

/-! # Reflection Parent Test Weak Identity -/

namespace Homogenization

open scoped ENNReal Manifold

noncomputable section

/-!
# Weak derivative identity for folded parent tests

The signed folded parent test is generally not compactly supported inside the
original open cube, but it vanishes on the two relevant coordinate faces.  This
file packages the face-zero cutoff closure needed to use it in the original
cube weak-gradient identity.
-/

private theorem memScalarL2_of_contDiff_hasCompactSupport {d : ℕ}
    (U : Set (Vec d)) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_compact : HasCompactSupport ψ) :
    MemScalarL2 U ψ := by
  simpa [MemScalarL2, volumeMeasureOn] using
    (hψ.continuous.memLp_of_hasCompactSupport hψ_compact).restrict U

private theorem memScalarL2_euclideanCoordDeriv_of_contDiff_hasCompactSupport
    {d : ℕ} (U : Set (Vec d)) (i : Fin d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_compact : HasCompactSupport ψ) :
    MemScalarL2 U (euclideanCoordDeriv i ψ) := by
  simpa [MemScalarL2, volumeMeasureOn] using
    ((contDiff_euclideanCoordDeriv hψ i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordDeriv hψ_compact i)).restrict U

/-- The original-cube weak derivative identity may be tested against the
signed folded parent test. -/
theorem H1Function.integral_mul_deriv_foldedParentScalarTest_eq_neg_integral_mul_originCube
    {d : ℕ} (m : ℤ) (u : H1Function (openCubeSet (originCube d m)))
    (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet (originCube d (m + 1))) :
    ∫ y in openCubeSet (originCube d m),
        u y *
          euclideanCoordDeriv i
            (cubeFaceReflectionFoldedParentScalarTest (originCube d m) i φ) y
          ∂MeasureTheory.volume =
      -∫ y in openCubeSet (originCube d m),
          u.grad y i *
            cubeFaceReflectionFoldedParentScalarTest (originCube d m) i φ y
          ∂MeasureTheory.volume := by
  classical
  let Q : TriadicCube d := originCube d m
  let ψ : Vec d → ℝ := cubeFaceReflectionFoldedParentScalarTest Q i φ
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ, Q] using
      contDiff_cubeFaceReflectionFoldedParentScalarTest (originCube d m) i hφ
  have hψ_compact : HasCompactSupport ψ := by
    simpa [ψ, Q] using
      hasCompactSupport_cubeFaceReflectionFoldedParentScalarTest (originCube d m) i hφ_compact
  have hψ_mem : MemScalarL2 (openCubeSet Q) ψ :=
    memScalarL2_of_contDiff_hasCompactSupport (openCubeSet Q) hψ_smooth hψ_compact
  have hDψ_mem :
      MemScalarL2 (openCubeSet Q) (euclideanCoordDeriv i ψ) :=
    memScalarL2_euclideanCoordDeriv_of_contDiff_hasCompactSupport
      (openCubeSet Q) i hψ_smooth hψ_compact
  have hlower_zero : ∀ x : Vec d, ψ (cubeLowerFaceProjection Q i x) = 0 := by
    simpa [ψ, Q] using
      cubeFaceReflectionFoldedParentScalarTest_lowerFaceProjection_eq_zero_originCube
        (m := m) i hφ_sub
  have hupper_zero : ∀ x : Vec d, ψ (cubeUpperFaceProjection Q i x) = 0 := by
    simpa [ψ, Q] using
      cubeFaceReflectionFoldedParentScalarTest_upperFaceProjection_eq_zero_originCube
        (m := m) i hφ_sub
  let L : ℝ := Classical.choose
    (exists_bound_fderiv_of_contDiff_hasCompactSupport hψ_smooth hψ_compact)
  have hL : 0 ≤ L :=
    (Classical.choose_spec
      (exists_bound_fderiv_of_contDiff_hasCompactSupport hψ_smooth hψ_compact)).1
  have hbound : ∀ x : Vec d, ‖fderiv ℝ ψ x‖ ≤ L :=
    (Classical.choose_spec
      (exists_bound_fderiv_of_contDiff_hasCompactSupport hψ_smooth hψ_compact)).2
  let ψn : ℕ → Vec d → ℝ := fun n x => faceCutoff Q n x * ψ x
  have hψn_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψn n) := by
    intro n
    simpa [ψn] using (faceCutoff Q n).smooth.mul hψ_smooth
  have hψn_compact : ∀ n, HasCompactSupport (ψn n) := by
    intro n
    simpa [ψn] using! ((faceCutoff Q n).hasCompactSupport.mul_right :
      HasCompactSupport (fun x : Vec d => faceCutoff Q n x * ψ x))
  have hψn_sub : ∀ n, tsupport (ψn n) ⊆ openCubeSet Q := by
    intro n
    exact (tsupport_mul_subset_left
      (f := (faceCutoff Q n : Vec d → ℝ)) (g := ψ)).trans
        ((faceCutoff Q n).tsupport_subset_openCubeSet_of_nonneg_of_lt_one
          (faceCutoffOuterRadius_nonneg n) (faceCutoffOuterRadius_lt_one n))
  have hψn_mem : ∀ n, MemScalarL2 (openCubeSet Q) (ψn n) := by
    intro n
    exact memScalarL2_of_contDiff_hasCompactSupport
      (openCubeSet Q) (hψn_smooth n) (hψn_compact n)
  have hDψn_mem :
      ∀ n, MemScalarL2 (openCubeSet Q)
        (fun x => euclideanCoordDeriv i (ψn n) x) := by
    intro n
    exact memScalarL2_euclideanCoordDeriv_of_contDiff_hasCompactSupport
      (openCubeSet Q) i (hψn_smooth n) (hψn_compact n)
  have hψn_to_ψ :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm (fun x => ψn n x - ψ x) 2
            (volumeMeasureOn (openCubeSet Q)))
        Filter.atTop (nhds 0) := by
    have htail :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm (fun x => ψ x - faceCutoff Q n x * ψ x) 2
              (volumeMeasureOn (openCubeSet Q)))
          Filter.atTop (nhds 0) :=
      QuantitativeCubeCutoff.tendsto_eLpNorm_sub_mul_of_tendsto_inner
        (Q := Q) (g := ψ)
        (ρ₁ := faceCutoffInnerRadius) (ρ₂ := faceCutoffOuterRadius)
        (η := fun n => faceCutoff Q n)
        tendsto_faceCutoffInnerRadius_one hψ_mem
    refine htail.congr' ?_
    filter_upwards with n
    have hfun :
        (fun x : Vec d => ψn n x - ψ x) =
          -(fun x : Vec d => ψ x - faceCutoff Q n x * ψ x) := by
      funext x
      simp [ψn]
    rw [hfun, MeasureTheory.eLpNorm_neg]
  have hDψn_to_Dψ :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x => euclideanCoordDeriv i (ψn n) x - euclideanCoordDeriv i ψ x)
            2 (volumeMeasureOn (openCubeSet Q)))
        Filter.atTop (nhds 0) := by
    simpa [ψn] using
      tendsto_eLpNorm_euclideanCoordDeriv_faceCutoff_mul_sub_of_face_zero
        Q i ψ hL hψ_smooth hψ_compact hbound hlower_zero hupper_zero
  have hweak :
      ∫ y in openCubeSet Q, u y * euclideanCoordDeriv i ψ y
          ∂MeasureTheory.volume =
        -∫ y in openCubeSet Q, u.grad y i * ψ y ∂MeasureTheory.volume :=
    HasWeakPartialDerivOn.integral_mul_deriv_eq_neg_integral_mul_of_eLpNorm_approx
      (U := openCubeSet Q) (i := i) (u := u) (gi := fun y => u.grad y i)
      (ψ := ψ) (Dψ := euclideanCoordDeriv i ψ)
      (u.hasWeakGradient i) u.memL2 (u.gradMemL2 i)
      hψ_mem hDψ_mem ψn hψn_smooth hψn_compact hψn_sub
      hψn_mem hDψn_mem hψn_to_ψ hDψn_to_Dψ
  simpa [Q, ψ] using hweak

/-- The same weak identity with the folded-test derivative expanded into the
cellwise parent derivative sum. -/
theorem H1Function.integral_mul_foldedParentScalarTest_derivSum_eq_neg_integral_mul_originCube
    {d : ℕ} (m : ℤ) (u : H1Function (openCubeSet (originCube d m)))
    (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet (originCube d (m + 1))) :
    ∫ y in openCubeSet (originCube d m),
        u y *
          (∑ choice : Fin d → Fin 3,
            euclideanCoordDeriv i φ
              (cubeFaceReflectionCellFoldMap (originCube d m) choice y))
          ∂MeasureTheory.volume =
      -∫ y in openCubeSet (originCube d m),
          u.grad y i *
            cubeFaceReflectionFoldedParentScalarTest (originCube d m) i φ y
          ∂MeasureTheory.volume := by
  have hbase :=
    u.integral_mul_deriv_foldedParentScalarTest_eq_neg_integral_mul_originCube
      m i hφ hφ_compact hφ_sub
  convert hbase using 1
  refine MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet (originCube d m)) ?_
  intro y _hy
  change u y *
      (∑ choice : Fin d → Fin 3,
        euclideanCoordDeriv i φ
          (cubeFaceReflectionCellFoldMap (originCube d m) choice y)) =
    u y *
      euclideanCoordDeriv i
        (cubeFaceReflectionFoldedParentScalarTest (originCube d m) i φ) y
  rw [← euclideanCoordDeriv_cubeFaceReflectionFoldedParentScalarTest
    (Q := originCube d m) (i := i) (φ := φ) hφ y]

end

end Homogenization
