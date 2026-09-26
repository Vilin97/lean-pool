/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Terms
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average

/-! Product rules for the spatial part of the first Caccioppoli term. -/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat


noncomputable section

namespace CKN

theorem caccioppoli_spatialSecondDeriv_mul
    {η φ : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i j : Fin 3) (x : Vec3) :
    mixedSecond (fun y => η y * φ y) i j x =
      mixedSecond η i j x * φ x
      + spatialDeriv η j x * spatialDeriv φ i x
      + spatialDeriv η i x * spatialDeriv φ j x
      + η x * mixedSecond φ i j x := by
  have hηd : Differentiable ℝ η := hη.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hη2d : Differentiable ℝ (spatialDeriv η j) :=
    (contDiff_spatialDeriv_smooth hη j).differentiable (by simp)
  have hφ2d : Differentiable ℝ (spatialDeriv φ j) :=
    (contDiff_spatialDeriv_smooth hφ j).differentiable (by simp)
  have h1 : spatialDeriv (fun y => η y * φ y) j =
      fun y => spatialDeriv η j y * φ y + η y * spatialDeriv φ j y := by
    funext y
    exact spatialDeriv_mul (hηd y) (hφd y) j
  have hadd : spatialDeriv
        (fun y => spatialDeriv η j y * φ y + η y * spatialDeriv φ j y) i x =
      spatialDeriv (fun y => spatialDeriv η j y * φ y) i x +
        spatialDeriv (fun y => η y * spatialDeriv φ j y) i x :=
    spatialDeriv_add ((hη2d x).mul (hφd x)) ((hηd x).mul (hφ2d x)) i
  have hmul1 : spatialDeriv (fun y => spatialDeriv η j y * φ y) i x =
      spatialDeriv (spatialDeriv η j) i x * φ x +
        spatialDeriv η j x * spatialDeriv φ i x :=
    spatialDeriv_mul (hη2d x) (hφd x) i
  have hmul2 : spatialDeriv (fun y => η y * spatialDeriv φ j y) i x =
      spatialDeriv η i x * spatialDeriv φ j x +
        η x * spatialDeriv (spatialDeriv φ j) i x := by
    have h := spatialDeriv_mul (hηd x) (hφ2d x) i
    simpa only [mixedSecond] using h
  rw [show mixedSecond (fun y => η y * φ y) i j x =
      spatialDeriv (spatialDeriv (fun y => η y * φ y) j) i x by rfl]
  rw [h1, hadd, hmul1, hmul2]
  simp only [mixedSecond]
  ring

theorem caccioppoli_spatialLaplacian_mul
    {η φ : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    spatialLaplacian (fun x => η x * φ x) =
      fun x => η x * spatialLaplacian φ x +
        2 * spatialGradDot η φ x + φ x * spatialLaplacian η x := by
  funext x
  unfold spatialLaplacian spatialGradDot
  calc
    ∑ i, mixedSecond (fun y => η y * φ y) i i x =
        ∑ i, (mixedSecond η i i x * φ x +
          spatialDeriv η i x * spatialDeriv φ i x +
          spatialDeriv η i x * spatialDeriv φ i x +
          η x * mixedSecond φ i i x) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact caccioppoli_spatialSecondDeriv_mul hη hφ i i x
    _ = η x * ∑ i, mixedSecond φ i i x +
          2 * ∑ i, spatialDeriv η i x * spatialDeriv φ i x +
          φ x * ∑ i, mixedSecond η i i x := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib]
      ring

end CKN
