/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.EuclideanL2CZ
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Derivatives
import Mathlib.MeasureTheory.Group.Measure

/-! # Cube Pairings -/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

theorem setIntegral_cubeUpperFaceNeighbor_reflectedField_pairing {d : ℕ}
    {G : Vec d → Vec d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d) :
    ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
          (euclideanGradient φ x) ∂volume =
      ∫ y in openCubeSet Q,
        vecDot (G y)
          (euclideanGradient (fun z => φ (cubeUpperFaceReflection Q i z)) y) ∂volume := by
  let g : Vec d → ℝ := fun y =>
    vecDot (coordReflectionLinear i (G y))
      (euclideanGradient φ (cubeUpperFaceReflection Q i y))
  calc
    ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
          (euclideanGradient φ x) ∂volume
        = ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
            g (cubeUpperFaceReflection Q i x) ∂volume := by
            apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet _)
            intro x _hx
            change
              vecDot
                  (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
                  (euclideanGradient φ x) =
                vecDot
                  (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
                  (euclideanGradient φ
                    (cubeUpperFaceReflection Q i (cubeUpperFaceReflection Q i x)))
            rw [cubeUpperFaceReflection_involutive]
    _ = ∫ y in openCubeSet Q, g y ∂volume :=
          setIntegral_cubeUpperFaceNeighbor_comp_reflection Q i g
    _ = ∫ y in openCubeSet Q,
        vecDot (G y)
          (euclideanGradient (fun z => φ (cubeUpperFaceReflection Q i z)) y) ∂volume := by
          apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
          intro y _hy
          change
            vecDot (coordReflectionLinear i (G y))
                (euclideanGradient φ (cubeUpperFaceReflection Q i y)) =
              vecDot (G y)
                (euclideanGradient (fun z => φ (cubeUpperFaceReflection Q i z)) y)
          rw [euclideanGradient_comp_cubeUpperFaceReflection hφ Q i y]
          exact vecDot_coordReflectionLinear_left i (G y)
            (euclideanGradient φ (cubeUpperFaceReflection Q i y))

/-- Integrability of the reflected weak-gradient pairing on the upper face
neighbor, transported from the corresponding reflected test pairing on `Q`. -/
theorem integrable_cubeUpperFaceNeighbor_reflectedField_pairing {d : ℕ}
    {G : Vec d → Vec d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d)
    (hreflected :
      MeasureTheory.Integrable
        (fun y =>
          vecDot (G y)
            (euclideanGradient (fun z => φ (cubeUpperFaceReflection Q i z)) y))
        (volume.restrict (openCubeSet Q))) :
    MeasureTheory.Integrable
      (fun x =>
        vecDot
          (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
          (euclideanGradient φ x))
      (volume.restrict (openCubeSet (cubeUpperFaceNeighbor Q i))) := by
  let B : Vec d → ℝ := fun x =>
    vecDot
      (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
      (euclideanGradient φ x)
  have hcomp :
      MeasureTheory.Integrable
        (fun y => B (cubeUpperFaceReflection Q i y))
        (volume.restrict (openCubeSet Q)) := by
    refine hreflected.congr ?_
    filter_upwards with y
    simp [B]
    rw [euclideanGradient_comp_cubeUpperFaceReflection hφ Q i y]
    exact (vecDot_coordReflectionLinear_left i (G y)
      (euclideanGradient φ (cubeUpperFaceReflection Q i y))).symm
  have hpre :
      MeasureTheory.IntegrableOn
        (fun y => B (cubeUpperFaceReflection Q i y))
        (cubeUpperFaceReflection Q i ⁻¹'
          openCubeSet (cubeUpperFaceNeighbor Q i)) volume := by
    simpa [MeasureTheory.IntegrableOn,
      preimage_cubeUpperFaceReflection_neighbor Q i] using hcomp
  have hiff := MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
    (measurePreserving_cubeUpperFaceReflection Q i)
    (measurableEmbedding_cubeUpperFaceReflection Q i)
    (f := B) (s := openCubeSet (cubeUpperFaceNeighbor Q i))
  have hB :
      MeasureTheory.IntegrableOn B
        (openCubeSet (cubeUpperFaceNeighbor Q i)) volume :=
    hiff.mp hpre
  simpa [MeasureTheory.IntegrableOn, B] using hB

theorem setIntegral_cubeLowerFaceNeighbor_reflectedField_pairing {d : ℕ}
    {G : Vec d → Vec d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d) :
    ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
          (euclideanGradient φ x) ∂volume =
      ∫ y in openCubeSet Q,
        vecDot (G y)
          (euclideanGradient (fun z => φ (cubeLowerFaceReflection Q i z)) y) ∂volume := by
  let g : Vec d → ℝ := fun y =>
    vecDot (coordReflectionLinear i (G y))
      (euclideanGradient φ (cubeLowerFaceReflection Q i y))
  calc
    ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
          (euclideanGradient φ x) ∂volume
        = ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
            g (cubeLowerFaceReflection Q i x) ∂volume := by
            apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet _)
            intro x _hx
            change
              vecDot
                  (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
                  (euclideanGradient φ x) =
                vecDot
                  (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
                  (euclideanGradient φ
                    (cubeLowerFaceReflection Q i (cubeLowerFaceReflection Q i x)))
            rw [cubeLowerFaceReflection_involutive]
    _ = ∫ y in openCubeSet Q, g y ∂volume :=
          setIntegral_cubeLowerFaceNeighbor_comp_reflection Q i g
    _ = ∫ y in openCubeSet Q,
        vecDot (G y)
          (euclideanGradient (fun z => φ (cubeLowerFaceReflection Q i z)) y) ∂volume := by
          apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
          intro y _hy
          change
            vecDot (coordReflectionLinear i (G y))
                (euclideanGradient φ (cubeLowerFaceReflection Q i y)) =
              vecDot (G y)
                (euclideanGradient (fun z => φ (cubeLowerFaceReflection Q i z)) y)
          rw [euclideanGradient_comp_cubeLowerFaceReflection hφ Q i y]
          exact vecDot_coordReflectionLinear_left i (G y)
            (euclideanGradient φ (cubeLowerFaceReflection Q i y))

/-- Integrability of the reflected weak-gradient pairing on the lower face
neighbor, transported from the corresponding reflected test pairing on `Q`. -/
theorem integrable_cubeLowerFaceNeighbor_reflectedField_pairing {d : ℕ}
    {G : Vec d → Vec d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d)
    (hreflected :
      MeasureTheory.Integrable
        (fun y =>
          vecDot (G y)
            (euclideanGradient (fun z => φ (cubeLowerFaceReflection Q i z)) y))
        (volume.restrict (openCubeSet Q))) :
    MeasureTheory.Integrable
      (fun x =>
        vecDot
          (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
          (euclideanGradient φ x))
      (volume.restrict (openCubeSet (cubeLowerFaceNeighbor Q i))) := by
  let B : Vec d → ℝ := fun x =>
    vecDot
      (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
      (euclideanGradient φ x)
  have hcomp :
      MeasureTheory.Integrable
        (fun y => B (cubeLowerFaceReflection Q i y))
        (volume.restrict (openCubeSet Q)) := by
    refine hreflected.congr ?_
    filter_upwards with y
    simp [B]
    rw [euclideanGradient_comp_cubeLowerFaceReflection hφ Q i y]
    exact (vecDot_coordReflectionLinear_left i (G y)
      (euclideanGradient φ (cubeLowerFaceReflection Q i y))).symm
  have hpre :
      MeasureTheory.IntegrableOn
        (fun y => B (cubeLowerFaceReflection Q i y))
        (cubeLowerFaceReflection Q i ⁻¹'
          openCubeSet (cubeLowerFaceNeighbor Q i)) volume := by
    simpa [MeasureTheory.IntegrableOn,
      preimage_cubeLowerFaceReflection_neighbor Q i] using hcomp
  have hiff := MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
    (measurePreserving_cubeLowerFaceReflection Q i)
    (measurableEmbedding_cubeLowerFaceReflection Q i)
    (f := B) (s := openCubeSet (cubeLowerFaceNeighbor Q i))
  have hB :
      MeasureTheory.IntegrableOn B
        (openCubeSet (cubeLowerFaceNeighbor Q i)) volume :=
    hiff.mp hpre
  simpa [MeasureTheory.IntegrableOn, B] using hB

theorem setIntegral_foldedCubeUpperFaceTest_reflectedField_pairing {d : ℕ}
    {G : Vec d → Vec d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d)
    (hmain :
      MeasureTheory.Integrable
        (fun y => vecDot (G y) (euclideanGradient φ y))
        (volume.restrict (openCubeSet Q)))
    (hreflected :
      MeasureTheory.Integrable
        (fun y =>
          vecDot (G y)
            (euclideanGradient (fun z => φ (cubeUpperFaceReflection Q i z)) y))
        (volume.restrict (openCubeSet Q))) :
    ∫ y in openCubeSet Q,
        vecDot (G y)
          (euclideanGradient (foldedCubeUpperFaceTest Q i φ) y) ∂volume =
      ∫ y in openCubeSet Q,
        vecDot (G y) (euclideanGradient φ y) ∂volume +
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
          (euclideanGradient φ x) ∂volume := by
  let A : Vec d → ℝ := fun y => vecDot (G y) (euclideanGradient φ y)
  let B : Vec d → ℝ := fun y =>
    vecDot (G y)
      (euclideanGradient (fun z => φ (cubeUpperFaceReflection Q i z)) y)
  calc
    ∫ y in openCubeSet Q,
        vecDot (G y)
          (euclideanGradient (foldedCubeUpperFaceTest Q i φ) y) ∂volume
        = ∫ y in openCubeSet Q, A y + B y ∂volume := by
            apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
            intro y _hy
            change
              vecDot (G y)
                  (euclideanGradient (foldedCubeUpperFaceTest Q i φ) y) =
                A y + B y
            rw [euclideanGradient_foldedCubeUpperFaceTest hφ Q i y]
            simp [A, B, vecDot_add_right, euclideanGradient_comp_cubeUpperFaceReflection hφ Q i y]
    _ = ∫ y in openCubeSet Q, A y ∂volume +
        ∫ y in openCubeSet Q, B y ∂volume := by
          rw [MeasureTheory.integral_add]
          · exact hmain
          · exact hreflected
    _ = ∫ y in openCubeSet Q,
        vecDot (G y) (euclideanGradient φ y) ∂volume +
      ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
          (euclideanGradient φ x) ∂volume := by
          rw [show (∫ y in openCubeSet Q, A y ∂volume) =
              ∫ y in openCubeSet Q,
                vecDot (G y) (euclideanGradient φ y) ∂volume by rfl]
          rw [show (∫ y in openCubeSet Q, B y ∂volume) =
              ∫ y in openCubeSet Q,
                vecDot (G y)
                  (euclideanGradient (fun z => φ (cubeUpperFaceReflection Q i z)) y)
                  ∂volume by rfl]
          rw [← setIntegral_cubeUpperFaceNeighbor_reflectedField_pairing hφ Q i]

theorem setIntegral_foldedCubeLowerFaceTest_reflectedField_pairing {d : ℕ}
    {G : Vec d → Vec d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d)
    (hmain :
      MeasureTheory.Integrable
        (fun y => vecDot (G y) (euclideanGradient φ y))
        (volume.restrict (openCubeSet Q)))
    (hreflected :
      MeasureTheory.Integrable
        (fun y =>
          vecDot (G y)
            (euclideanGradient (fun z => φ (cubeLowerFaceReflection Q i z)) y))
        (volume.restrict (openCubeSet Q))) :
    ∫ y in openCubeSet Q,
        vecDot (G y)
          (euclideanGradient (foldedCubeLowerFaceTest Q i φ) y) ∂volume =
      ∫ y in openCubeSet Q,
        vecDot (G y) (euclideanGradient φ y) ∂volume +
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
          (euclideanGradient φ x) ∂volume := by
  let A : Vec d → ℝ := fun y => vecDot (G y) (euclideanGradient φ y)
  let B : Vec d → ℝ := fun y =>
    vecDot (G y)
      (euclideanGradient (fun z => φ (cubeLowerFaceReflection Q i z)) y)
  calc
    ∫ y in openCubeSet Q,
        vecDot (G y)
          (euclideanGradient (foldedCubeLowerFaceTest Q i φ) y) ∂volume
        = ∫ y in openCubeSet Q, A y + B y ∂volume := by
            apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
            intro y _hy
            change
              vecDot (G y)
                  (euclideanGradient (foldedCubeLowerFaceTest Q i φ) y) =
                A y + B y
            rw [euclideanGradient_foldedCubeLowerFaceTest hφ Q i y]
            simp [A, B, vecDot_add_right, euclideanGradient_comp_cubeLowerFaceReflection hφ Q i y]
    _ = ∫ y in openCubeSet Q, A y ∂volume +
        ∫ y in openCubeSet Q, B y ∂volume := by
          rw [MeasureTheory.integral_add]
          · exact hmain
          · exact hreflected
    _ = ∫ y in openCubeSet Q,
        vecDot (G y) (euclideanGradient φ y) ∂volume +
      ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
          (euclideanGradient φ x) ∂volume := by
          rw [show (∫ y in openCubeSet Q, A y ∂volume) =
              ∫ y in openCubeSet Q,
                vecDot (G y) (euclideanGradient φ y) ∂volume by rfl]
          rw [show (∫ y in openCubeSet Q, B y ∂volume) =
              ∫ y in openCubeSet Q,
                vecDot (G y)
                  (euclideanGradient (fun z => φ (cubeLowerFaceReflection Q i z)) y)
                  ∂volume by rfl]
          rw [← setIntegral_cubeLowerFaceNeighbor_reflectedField_pairing hφ Q i]

theorem setIntegral_cubeUpperFaceNeighbor_reflectedGradient_pairing {d : ℕ}
    {u φ : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d) :
    ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (euclideanGradient (fun y => u (cubeUpperFaceReflection Q i y)) x)
          (euclideanGradient φ x) ∂volume =
      ∫ y in openCubeSet Q,
        vecDot (euclideanGradient u y)
          (euclideanGradient (fun z => φ (cubeUpperFaceReflection Q i z)) y) ∂volume := by
  let g : Vec d → ℝ := fun y =>
    vecDot
      (euclideanGradient (fun z => u (cubeUpperFaceReflection Q i z))
        (cubeUpperFaceReflection Q i y))
      (euclideanGradient φ (cubeUpperFaceReflection Q i y))
  calc
    ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (euclideanGradient (fun y => u (cubeUpperFaceReflection Q i y)) x)
          (euclideanGradient φ x) ∂volume
        = ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
            g (cubeUpperFaceReflection Q i x) ∂volume := by
            apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet _)
            intro x _hx
            simp [g, cubeUpperFaceReflection]
    _ = ∫ y in openCubeSet Q, g y ∂volume :=
          setIntegral_cubeUpperFaceNeighbor_comp_reflection Q i g
    _ = ∫ y in openCubeSet Q,
        vecDot (euclideanGradient u y)
          (euclideanGradient (fun z => φ (cubeUpperFaceReflection Q i z)) y) ∂volume := by
          apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
          intro y _hy
          exact vecDot_euclideanGradient_comp_cubeUpperFaceReflection_pairing hu hφ Q i y

theorem setIntegral_cubeLowerFaceNeighbor_reflectedGradient_pairing {d : ℕ}
    {u φ : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : TriadicCube d) (i : Fin d) :
    ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (euclideanGradient (fun y => u (cubeLowerFaceReflection Q i y)) x)
          (euclideanGradient φ x) ∂volume =
      ∫ y in openCubeSet Q,
        vecDot (euclideanGradient u y)
          (euclideanGradient (fun z => φ (cubeLowerFaceReflection Q i z)) y) ∂volume := by
  let g : Vec d → ℝ := fun y =>
    vecDot
      (euclideanGradient (fun z => u (cubeLowerFaceReflection Q i z))
        (cubeLowerFaceReflection Q i y))
      (euclideanGradient φ (cubeLowerFaceReflection Q i y))
  calc
    ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (euclideanGradient (fun y => u (cubeLowerFaceReflection Q i y)) x)
          (euclideanGradient φ x) ∂volume
        = ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
            g (cubeLowerFaceReflection Q i x) ∂volume := by
            apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet _)
            intro x _hx
            simp [g, cubeLowerFaceReflection]
    _ = ∫ y in openCubeSet Q, g y ∂volume :=
          setIntegral_cubeLowerFaceNeighbor_comp_reflection Q i g
    _ = ∫ y in openCubeSet Q,
        vecDot (euclideanGradient u y)
          (euclideanGradient (fun z => φ (cubeLowerFaceReflection Q i z)) y) ∂volume := by
          apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
          intro y _hy
          exact vecDot_euclideanGradient_comp_cubeLowerFaceReflection_pairing hu hφ Q i y

theorem euclideanCoordSecondDeriv_comp_cubeUpperFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (i k l : Fin d) (x : Vec d) :
    euclideanCoordSecondDeriv k l
        (fun y => u (cubeUpperFaceReflection Q i y)) x =
      ((if k = i then (-1 : ℝ) else 1) *
        (if l = i then (-1 : ℝ) else 1)) *
        euclideanCoordSecondDeriv k l u (cubeUpperFaceReflection Q i x) := by
  simpa [cubeUpperFaceReflection] using
    euclideanCoordSecondDeriv_comp_coordFaceReflection
      (u := u) hu (cubeUpperFaceCoord Q i) i k l x

theorem euclideanCoordSecondDeriv_comp_cubeLowerFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (i k l : Fin d) (x : Vec d) :
    euclideanCoordSecondDeriv k l
        (fun y => u (cubeLowerFaceReflection Q i y)) x =
      ((if k = i then (-1 : ℝ) else 1) *
        (if l = i then (-1 : ℝ) else 1)) *
        euclideanCoordSecondDeriv k l u (cubeLowerFaceReflection Q i x) := by
  simpa [cubeLowerFaceReflection] using
    euclideanCoordSecondDeriv_comp_coordFaceReflection
      (u := u) hu (cubeLowerFaceCoord Q i) i k l x

theorem euclideanCoordLaplacian_comp_cubeUpperFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    euclideanCoordLaplacian (fun y => u (cubeUpperFaceReflection Q i y)) x =
      euclideanCoordLaplacian u (cubeUpperFaceReflection Q i x) := by
  simpa [cubeUpperFaceReflection] using
    euclideanCoordLaplacian_comp_coordFaceReflection
      (u := u) hu (cubeUpperFaceCoord Q i) i x

theorem euclideanCoordLaplacian_comp_cubeLowerFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    euclideanCoordLaplacian (fun y => u (cubeLowerFaceReflection Q i y)) x =
      euclideanCoordLaplacian u (cubeLowerFaceReflection Q i x) := by
  simpa [cubeLowerFaceReflection] using
    euclideanCoordLaplacian_comp_coordFaceReflection
      (u := u) hu (cubeLowerFaceCoord Q i) i x

theorem sum_sq_euclideanCoordSecondDeriv_comp_cubeUpperFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    (∑ k : Fin d, ∑ l : Fin d,
        (euclideanCoordSecondDeriv k l
          (fun y => u (cubeUpperFaceReflection Q i y)) x) ^ 2) =
      ∑ k : Fin d, ∑ l : Fin d,
        (euclideanCoordSecondDeriv k l u (cubeUpperFaceReflection Q i x)) ^ 2 := by
  simpa [cubeUpperFaceReflection] using
    sum_sq_euclideanCoordSecondDeriv_comp_coordFaceReflection
      (u := u) hu (cubeUpperFaceCoord Q i) i x

theorem sum_sq_euclideanCoordSecondDeriv_comp_cubeLowerFaceReflection {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (Q : TriadicCube d) (i : Fin d) (x : Vec d) :
    (∑ k : Fin d, ∑ l : Fin d,
        (euclideanCoordSecondDeriv k l
          (fun y => u (cubeLowerFaceReflection Q i y)) x) ^ 2) =
      ∑ k : Fin d, ∑ l : Fin d,
        (euclideanCoordSecondDeriv k l u (cubeLowerFaceReflection Q i x)) ^ 2 := by
  simpa [cubeLowerFaceReflection] using
    sum_sq_euclideanCoordSecondDeriv_comp_coordFaceReflection
      (u := u) hu (cubeLowerFaceCoord Q i) i x

end

end Homogenization
