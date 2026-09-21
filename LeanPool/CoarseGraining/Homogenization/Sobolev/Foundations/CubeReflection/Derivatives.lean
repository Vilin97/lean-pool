/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.EuclideanL2CZ
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Homeomorphism

/-! # Derivatives -/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

theorem coordReflectionLinear_basisVec {d : ℕ} (i k : Fin d) :
    coordReflectionLinear i (basisVec k) =
      (if k = i then (-1 : ℝ) else 1) • basisVec k := by
  ext j
  by_cases hki : k = i
  · subst k
    by_cases hji : j = i <;> simp [hji]
  · have hik : i ≠ k := fun h => hki h.symm
    by_cases hji : j = i <;> by_cases hjk : j = k <;>
      simp [hki, hik, hji, hjk]

theorem fderiv_coordFaceReflection {d : ℕ}
    (a : ℝ) (i : Fin d) (x : Vec d) :
    fderiv ℝ (coordFaceReflection a i) x = coordReflectionLinear i := by
  unfold coordFaceReflection
  rw [fderiv_add_const]
  exact (coordReflectionLinear i).fderiv

theorem differentiableAt_coordFaceReflection {d : ℕ}
    (a : ℝ) (i : Fin d) (x : Vec d) :
    DifferentiableAt ℝ (coordFaceReflection a i) x := by
  have hlin : DifferentiableAt ℝ (fun y : Vec d => coordReflectionLinear i y) x :=
    (coordReflectionLinear i).differentiableAt
  exact hlin.add_const _

/-- First coordinate-derivative chain rule for scalar functions composed with a
coordinate face reflection. The normal derivative changes sign; tangential
derivatives do not. -/
theorem euclideanCoordDeriv_comp_coordFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (a : ℝ) (i k : Fin d) (x : Vec d) :
    euclideanCoordDeriv k (fun y => u (coordFaceReflection a i y)) x =
      (if k = i then (-1 : ℝ) else 1) *
        euclideanCoordDeriv k u (coordFaceReflection a i x) := by
  unfold euclideanCoordDeriv
  have hcomp :
      fderiv ℝ (fun y => u (coordFaceReflection a i y)) x =
        (fderiv ℝ u (coordFaceReflection a i x)).comp (coordReflectionLinear i) := by
    change fderiv ℝ (u ∘ coordFaceReflection a i) x =
      (fderiv ℝ u (coordFaceReflection a i x)).comp (coordReflectionLinear i)
    rw [fderiv_comp]
    · rw [fderiv_coordFaceReflection]
    · exact (hu.differentiable (by simp)) (coordFaceReflection a i x)
    · exact differentiableAt_coordFaceReflection a i x
  rw [hcomp]
  rw [ContinuousLinearMap.comp_apply, coordReflectionLinear_basisVec]
  by_cases hki : k = i <;> simp [hki]

theorem euclideanGradient_comp_coordFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (a : ℝ) (i : Fin d) (x : Vec d) :
    euclideanGradient (fun y => u (coordFaceReflection a i y)) x =
      coordReflectionLinear i (euclideanGradient u (coordFaceReflection a i x)) := by
  ext k
  simp [euclideanGradient, euclideanCoordDeriv_comp_coordFaceReflection hu a i k x]

/-- Fold a scalar test through a coordinate face: on the original side this is
`φ + φ ∘ r`, where `r` is the face reflection. -/
def foldedCoordFaceTest {d : ℕ}
    (a : ℝ) (i : Fin d) (φ : Vec d → ℝ) : Vec d → ℝ :=
  fun x => φ x + φ (coordFaceReflection a i x)

def foldedCubeUpperFaceTest {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (φ : Vec d → ℝ) : Vec d → ℝ :=
  foldedCoordFaceTest (cubeUpperFaceCoord Q i) i φ

def foldedCubeLowerFaceTest {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) (φ : Vec d → ℝ) : Vec d → ℝ :=
  foldedCoordFaceTest (cubeLowerFaceCoord Q i) i φ

theorem contDiff_foldedCoordFaceTest {d : ℕ}
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (a : ℝ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (foldedCoordFaceTest a i φ) := by
  simpa [foldedCoordFaceTest, Function.comp] using!
    hφ.add (hφ.comp (contDiff_coordFaceReflection a i))

theorem contDiff_foldedCubeUpperFaceTest {d : ℕ}
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (foldedCubeUpperFaceTest Q i φ) := by
  simpa [foldedCubeUpperFaceTest] using
    contDiff_foldedCoordFaceTest hφ (cubeUpperFaceCoord Q i) i

theorem contDiff_foldedCubeLowerFaceTest {d : ℕ}
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (foldedCubeLowerFaceTest Q i φ) := by
  simpa [foldedCubeLowerFaceTest] using
    contDiff_foldedCoordFaceTest hφ (cubeLowerFaceCoord Q i) i

theorem hasCompactSupport_comp_coordFaceReflection {d : ℕ}
    {φ : Vec d → ℝ} (hφ : HasCompactSupport φ)
    (a : ℝ) (i : Fin d) :
    HasCompactSupport (fun x => φ (coordFaceReflection a i x)) := by
  show HasCompactSupport (φ ∘ coordFaceReflectionHomeomorph a i)
  simpa [Function.comp, coordFaceReflectionHomeomorph] using
    hφ.comp_homeomorph (coordFaceReflectionHomeomorph a i)

theorem hasCompactSupport_comp_cubeUpperFaceReflection {d : ℕ}
    {φ : Vec d → ℝ} (hφ : HasCompactSupport φ)
    (Q : TriadicCube d) (i : Fin d) :
    HasCompactSupport (fun x => φ (cubeUpperFaceReflection Q i x)) := by
  simpa [cubeUpperFaceReflection] using
    hasCompactSupport_comp_coordFaceReflection hφ (cubeUpperFaceCoord Q i) i

theorem hasCompactSupport_comp_cubeLowerFaceReflection {d : ℕ}
    {φ : Vec d → ℝ} (hφ : HasCompactSupport φ)
    (Q : TriadicCube d) (i : Fin d) :
    HasCompactSupport (fun x => φ (cubeLowerFaceReflection Q i x)) := by
  simpa [cubeLowerFaceReflection] using
    hasCompactSupport_comp_coordFaceReflection hφ (cubeLowerFaceCoord Q i) i

theorem hasCompactSupport_foldedCoordFaceTest {d : ℕ}
    {φ : Vec d → ℝ} (hφ : HasCompactSupport φ)
    (a : ℝ) (i : Fin d) :
    HasCompactSupport (foldedCoordFaceTest a i φ) := by
  simpa [foldedCoordFaceTest] using!
    hφ.add (hasCompactSupport_comp_coordFaceReflection hφ a i)

theorem hasCompactSupport_foldedCubeUpperFaceTest {d : ℕ}
    {φ : Vec d → ℝ} (hφ : HasCompactSupport φ)
    (Q : TriadicCube d) (i : Fin d) :
    HasCompactSupport (foldedCubeUpperFaceTest Q i φ) := by
  simpa [foldedCubeUpperFaceTest] using
    hasCompactSupport_foldedCoordFaceTest hφ (cubeUpperFaceCoord Q i) i

theorem hasCompactSupport_foldedCubeLowerFaceTest {d : ℕ}
    {φ : Vec d → ℝ} (hφ : HasCompactSupport φ)
    (Q : TriadicCube d) (i : Fin d) :
    HasCompactSupport (foldedCubeLowerFaceTest Q i φ) := by
  simpa [foldedCubeLowerFaceTest] using
    hasCompactSupport_foldedCoordFaceTest hφ (cubeLowerFaceCoord Q i) i

theorem euclideanGradient_foldedCoordFaceTest {d : ℕ}
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (a : ℝ) (i : Fin d) (x : Vec d) :
    euclideanGradient (foldedCoordFaceTest a i φ) x =
      euclideanGradient φ x +
        coordReflectionLinear i (euclideanGradient φ (coordFaceReflection a i x)) := by
  have hφdiff : DifferentiableAt ℝ φ x :=
    (hφ.differentiable (by simp)) x
  have hcompdiff :
      DifferentiableAt ℝ (fun y => φ (coordFaceReflection a i y)) x := by
    exact ((hφ.differentiable (by simp)) (coordFaceReflection a i x)).comp x
      (differentiableAt_coordFaceReflection a i x)
  have hderiv :
      fderiv ℝ (foldedCoordFaceTest a i φ) x =
        fderiv ℝ φ x +
          fderiv ℝ (fun y => φ (coordFaceReflection a i y)) x := by
    change fderiv ℝ (φ + fun y => φ (coordFaceReflection a i y)) x =
      fderiv ℝ φ x +
        fderiv ℝ (fun y => φ (coordFaceReflection a i y)) x
    exact fderiv_add hφdiff hcompdiff
  ext k
  unfold euclideanGradient euclideanCoordDeriv
  rw [hderiv]
  rw [add_apply]
  rw [show fderiv ℝ (fun y => φ (coordFaceReflection a i y)) x (basisVec k) =
      euclideanCoordDeriv k (fun y => φ (coordFaceReflection a i y)) x by rfl]
  rw [euclideanCoordDeriv_comp_coordFaceReflection hφ a i k x]
  by_cases hki : k = i <;> simp [hki, euclideanCoordDeriv]

theorem euclideanGradient_foldedCubeUpperFaceTest {d : ℕ}
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    euclideanGradient (foldedCubeUpperFaceTest Q i φ) x =
      euclideanGradient φ x +
        coordReflectionLinear i (euclideanGradient φ (cubeUpperFaceReflection Q i x)) := by
  simpa [foldedCubeUpperFaceTest, cubeUpperFaceReflection] using
    euclideanGradient_foldedCoordFaceTest hφ (cubeUpperFaceCoord Q i) i x

theorem euclideanGradient_foldedCubeLowerFaceTest {d : ℕ}
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    euclideanGradient (foldedCubeLowerFaceTest Q i φ) x =
      euclideanGradient φ x +
        coordReflectionLinear i (euclideanGradient φ (cubeLowerFaceReflection Q i x)) := by
  simpa [foldedCubeLowerFaceTest, cubeLowerFaceReflection] using
    euclideanGradient_foldedCoordFaceTest hφ (cubeLowerFaceCoord Q i) i x

theorem vecDot_euclideanGradient_foldedCoordFaceTest {d : ℕ}
    {u φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (a : ℝ) (i : Fin d) (x : Vec d) :
    vecDot (euclideanGradient u x)
        (euclideanGradient (foldedCoordFaceTest a i φ) x) =
      vecDot (euclideanGradient u x) (euclideanGradient φ x) +
        vecDot (euclideanGradient u x)
          (coordReflectionLinear i (euclideanGradient φ (coordFaceReflection a i x))) := by
  rw [euclideanGradient_foldedCoordFaceTest hφ a i x]
  simp [vecDot_add_right]

theorem vecDot_euclideanGradient_foldedCubeUpperFaceTest {d : ℕ}
    {u φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    vecDot (euclideanGradient u x)
        (euclideanGradient (foldedCubeUpperFaceTest Q i φ) x) =
      vecDot (euclideanGradient u x) (euclideanGradient φ x) +
        vecDot (euclideanGradient u x)
          (coordReflectionLinear i (euclideanGradient φ (cubeUpperFaceReflection Q i x))) := by
  simpa [foldedCubeUpperFaceTest, cubeUpperFaceReflection] using
    vecDot_euclideanGradient_foldedCoordFaceTest
      (u := u) (φ := φ) hφ (cubeUpperFaceCoord Q i) i x

theorem vecDot_euclideanGradient_foldedCubeLowerFaceTest {d : ℕ}
    {u φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    vecDot (euclideanGradient u x)
        (euclideanGradient (foldedCubeLowerFaceTest Q i φ) x) =
      vecDot (euclideanGradient u x) (euclideanGradient φ x) +
        vecDot (euclideanGradient u x)
          (coordReflectionLinear i (euclideanGradient φ (cubeLowerFaceReflection Q i x))) := by
  simpa [foldedCubeLowerFaceTest, cubeLowerFaceReflection] using
    vecDot_euclideanGradient_foldedCoordFaceTest
      (u := u) (φ := φ) hφ (cubeLowerFaceCoord Q i) i x

/-- The folded upper-face smooth test, packaged as an `H¹(openCubeSet Q)`
witness for variational Neumann equations. -/
noncomputable def foldedCubeUpperFaceH1Test {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)
    ((contDiff_foldedCubeUpperFaceTest hφ Q i).of_le (by simp))

/-- The folded lower-face smooth test, packaged as an `H¹(openCubeSet Q)`
witness for variational Neumann equations. -/
noncomputable def foldedCubeLowerFaceH1Test {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)
    ((contDiff_foldedCubeLowerFaceTest hφ Q i).of_le (by simp))

@[simp] theorem foldedCubeUpperFaceH1Test_toFun {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (foldedCubeUpperFaceH1Test Q i hφ).toFun =
      foldedCubeUpperFaceTest Q i φ := by
  simp [foldedCubeUpperFaceH1Test,
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain]

@[simp] theorem foldedCubeLowerFaceH1Test_toFun {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (foldedCubeLowerFaceH1Test Q i hφ).toFun =
      foldedCubeLowerFaceTest Q i φ := by
  simp [foldedCubeLowerFaceH1Test,
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain]

@[simp] theorem foldedCubeUpperFaceH1Test_grad {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d) :
    (foldedCubeUpperFaceH1Test Q i hφ).grad x =
      euclideanGradient (foldedCubeUpperFaceTest Q i φ) x := by
  ext k
  simp [foldedCubeUpperFaceH1Test,
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain, euclideanGradient,
    euclideanCoordDeriv]

@[simp] theorem foldedCubeLowerFaceH1Test_grad {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d) :
    (foldedCubeLowerFaceH1Test Q i hφ).grad x =
      euclideanGradient (foldedCubeLowerFaceTest Q i φ) x := by
  ext k
  simp [foldedCubeLowerFaceH1Test,
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain, euclideanGradient,
    euclideanCoordDeriv]

theorem vecDot_euclideanGradient_comp_coordFaceReflection_pairing {d : ℕ}
    {u φ : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (a : ℝ) (i : Fin d) (x : Vec d) :
    vecDot
        (euclideanGradient (fun y => u (coordFaceReflection a i y))
          (coordFaceReflection a i x))
        (euclideanGradient φ (coordFaceReflection a i x)) =
      vecDot (euclideanGradient u x)
        (euclideanGradient (fun y => φ (coordFaceReflection a i y)) x) := by
  rw [euclideanGradient_comp_coordFaceReflection hu a i (coordFaceReflection a i x)]
  rw [coordFaceReflection_involutive]
  rw [euclideanGradient_comp_coordFaceReflection hφ a i x]
  exact vecDot_coordReflectionLinear_left i (euclideanGradient u x)
    (euclideanGradient φ (coordFaceReflection a i x))

/-- Second coordinate-derivative chain rule for scalar functions composed with
a coordinate face reflection. Each differentiation in the reflected normal
direction contributes one sign. -/
theorem euclideanCoordSecondDeriv_comp_coordFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (a : ℝ) (i k l : Fin d) (x : Vec d) :
    euclideanCoordSecondDeriv k l (fun y => u (coordFaceReflection a i y)) x =
      ((if k = i then (-1 : ℝ) else 1) *
        (if l = i then (-1 : ℝ) else 1)) *
        euclideanCoordSecondDeriv k l u (coordFaceReflection a i x) := by
  let sk : ℝ := if k = i then (-1 : ℝ) else 1
  let sl : ℝ := if l = i then (-1 : ℝ) else 1
  have hderiv_fun :
      euclideanCoordDeriv k (fun y => u (coordFaceReflection a i y)) =
        fun y => sk * euclideanCoordDeriv k u (coordFaceReflection a i y) := by
    funext y
    simpa [sk] using euclideanCoordDeriv_comp_coordFaceReflection hu a i k y
  unfold euclideanCoordSecondDeriv
  rw [hderiv_fun]
  have hdiff :
      DifferentiableAt ℝ
        (fun y => euclideanCoordDeriv k u (coordFaceReflection a i y)) x := by
    exact (((contDiff_euclideanCoordDeriv hu k).differentiable (by simp))
      (coordFaceReflection a i x)).comp x (differentiableAt_coordFaceReflection a i x)
  rw [fderiv_const_mul hdiff sk]
  change sk *
      euclideanCoordDeriv l
        (fun y => euclideanCoordDeriv k u (coordFaceReflection a i y)) x =
    (sk * sl) * euclideanCoordSecondDeriv k l u (coordFaceReflection a i x)
  rw [euclideanCoordDeriv_comp_coordFaceReflection
    (u := euclideanCoordDeriv k u) (contDiff_euclideanCoordDeriv hu k) a i l x]
  simp [euclideanCoordSecondDeriv, euclideanCoordDeriv, sk, sl]

theorem euclideanCoordSecondDeriv_diag_comp_coordFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (a : ℝ) (i k : Fin d) (x : Vec d) :
    euclideanCoordSecondDeriv k k (fun y => u (coordFaceReflection a i y)) x =
      euclideanCoordSecondDeriv k k u (coordFaceReflection a i x) := by
  rw [euclideanCoordSecondDeriv_comp_coordFaceReflection hu a i k k x]
  by_cases hki : k = i <;> simp [hki]

theorem euclideanCoordLaplacian_comp_coordFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (a : ℝ) (i : Fin d) (x : Vec d) :
    euclideanCoordLaplacian (fun y => u (coordFaceReflection a i y)) x =
      euclideanCoordLaplacian u (coordFaceReflection a i x) := by
  unfold euclideanCoordLaplacian
  apply Finset.sum_congr rfl
  intro k _hk
  exact euclideanCoordSecondDeriv_diag_comp_coordFaceReflection hu a i k x

theorem sum_sq_euclideanCoordSecondDeriv_comp_coordFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (a : ℝ) (i : Fin d) (x : Vec d) :
    (∑ k : Fin d, ∑ l : Fin d,
        (euclideanCoordSecondDeriv k l
          (fun y => u (coordFaceReflection a i y)) x) ^ 2) =
      ∑ k : Fin d, ∑ l : Fin d,
        (euclideanCoordSecondDeriv k l u (coordFaceReflection a i x)) ^ 2 := by
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro l _hl
  rw [euclideanCoordSecondDeriv_comp_coordFaceReflection hu a i k l x]
  by_cases hki : k = i <;> by_cases hli : l = i <;> simp [hki, hli, pow_two]

theorem euclideanCoordDeriv_comp_cubeUpperFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (i k : Fin d) (x : Vec d) :
    euclideanCoordDeriv k (fun y => u (cubeUpperFaceReflection Q i y)) x =
      (if k = i then (-1 : ℝ) else 1) *
        euclideanCoordDeriv k u (cubeUpperFaceReflection Q i x) := by
  simpa [cubeUpperFaceReflection] using
    euclideanCoordDeriv_comp_coordFaceReflection
      (u := u) hu (cubeUpperFaceCoord Q i) i k x

theorem euclideanCoordDeriv_comp_cubeLowerFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (i k : Fin d) (x : Vec d) :
    euclideanCoordDeriv k (fun y => u (cubeLowerFaceReflection Q i y)) x =
      (if k = i then (-1 : ℝ) else 1) *
        euclideanCoordDeriv k u (cubeLowerFaceReflection Q i x) := by
  simpa [cubeLowerFaceReflection] using
    euclideanCoordDeriv_comp_coordFaceReflection
      (u := u) hu (cubeLowerFaceCoord Q i) i k x

theorem euclideanGradient_comp_cubeUpperFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    euclideanGradient (fun y => u (cubeUpperFaceReflection Q i y)) x =
      coordReflectionLinear i (euclideanGradient u (cubeUpperFaceReflection Q i x)) := by
  simpa [cubeUpperFaceReflection] using
    euclideanGradient_comp_coordFaceReflection
      (u := u) hu (cubeUpperFaceCoord Q i) i x

theorem euclideanGradient_comp_cubeLowerFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    euclideanGradient (fun y => u (cubeLowerFaceReflection Q i y)) x =
      coordReflectionLinear i (euclideanGradient u (cubeLowerFaceReflection Q i x)) := by
  simpa [cubeLowerFaceReflection] using
    euclideanGradient_comp_coordFaceReflection
      (u := u) hu (cubeLowerFaceCoord Q i) i x

theorem vecDot_euclideanGradient_comp_cubeUpperFaceReflection_pairing {d : ℕ}
    {u φ : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    vecDot
        (euclideanGradient (fun y => u (cubeUpperFaceReflection Q i y))
          (cubeUpperFaceReflection Q i x))
        (euclideanGradient φ (cubeUpperFaceReflection Q i x)) =
      vecDot (euclideanGradient u x)
        (euclideanGradient (fun y => φ (cubeUpperFaceReflection Q i y)) x) := by
  simpa [cubeUpperFaceReflection] using
    vecDot_euclideanGradient_comp_coordFaceReflection_pairing
      (u := u) (φ := φ) hu hφ (cubeUpperFaceCoord Q i) i x

theorem vecDot_euclideanGradient_comp_cubeLowerFaceReflection_pairing {d : ℕ}
    {u φ : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    vecDot
        (euclideanGradient (fun y => u (cubeLowerFaceReflection Q i y))
          (cubeLowerFaceReflection Q i x))
        (euclideanGradient φ (cubeLowerFaceReflection Q i x)) =
      vecDot (euclideanGradient u x)
        (euclideanGradient (fun y => φ (cubeLowerFaceReflection Q i y)) x) := by
  simpa [cubeLowerFaceReflection] using
    vecDot_euclideanGradient_comp_coordFaceReflection_pairing
      (u := u) (φ := φ) hu hφ (cubeLowerFaceCoord Q i) i x

end

end Homogenization
