/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Measure.RestrictedVolume
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# The Leibniz rule for the spatial Laplacian, in weak form

The paper's identity `eq:leibniz-lap`,
`Δ(η T) = η Δ T + 2 ∂_j η ∂_j T + T Δ η`,
is stated there for a scalar distribution `T` and a smooth `η`.  This file
proves the underlying pointwise second-order product rule for smooth functions
on `Vec3 := Fin 3 → ℝ`, and then integrates it against a locally integrable
weight to obtain the weak (test-function) form used in the paper.

Spatial partial derivatives are ordinary partial derivatives, expressed as the
Fréchet derivative applied to a coordinate basis vector, matching the
convention of `CKN.spatialPartial`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

/-! ## Spatial partial derivatives and their product rules -/

/-- The `i`th spatial partial derivative `∂_i f`, as the Fréchet derivative applied
to the `i`th coordinate basis vector. -/
@[expose]
def spatialDeriv (f : Vec3 → ℝ) (i : Fin 3) : Vec3 → ℝ :=
  fun x => (fderiv ℝ f x) (basisVec i)

/-- The spatial Laplacian `Δ f = ∑_i ∂_i ∂_i f`. -/
@[expose]
def spatialLaplacian (f : Vec3 → ℝ) : Vec3 → ℝ :=
  fun x => ∑ i : Fin 3, spatialDeriv (spatialDeriv f i) i x

/-- The Euclidean gradient pairing `∇f · ∇g = ∑_i ∂_i f ∂_i g`. -/
@[expose]
def spatialGradDot (f g : Vec3 → ℝ) : Vec3 → ℝ :=
  fun x => ∑ i : Fin 3, spatialDeriv f i x * spatialDeriv g i x

/-- The mixed second derivative `∂_i ∂_j f`. -/
@[expose]
def mixedSecond (f : Vec3 → ℝ) (i j : Fin 3) : Vec3 → ℝ :=
  fun x => spatialDeriv (spatialDeriv f j) i x

lemma contDiff_spatialDeriv_smooth {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f i) := by
  have hcomp : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => (fderiv ℝ f x) (basisVec i)) := by
    have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
      (contDiff_infty_iff_fderiv.mp hf).2
    have h := hfd.clm_apply (contDiff_const :
      ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec3 => basisVec i))
    simpa using h
  exact hcomp

lemma contDiff_spatialLaplacian_smooth {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialLaplacian f) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 =>
      ∑ i : Fin 3, spatialDeriv (spatialDeriv f i) i x) :=
    ContDiff.sum (fun i _ =>
      contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hf i) i)
  exact h

lemma contDiff_spatialGradDot_smooth {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialGradDot f g) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 =>
      ∑ i : Fin 3, spatialDeriv f i x * spatialDeriv g i x) :=
    ContDiff.sum (fun i _ =>
      (contDiff_spatialDeriv_smooth hf i).mul (contDiff_spatialDeriv_smooth hg i))
  exact h

lemma contDiff_mixedSecond_smooth {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (mixedSecond f i j) :=
  contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hf j) i

lemma spatialDeriv_add {f g : Vec3 → ℝ} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialDeriv (fun y => f y + g y) i x = spatialDeriv f i x + spatialDeriv g i x := by
  have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) (fderiv_fun_add hf hg)
  simp only [add_apply] at h
  simp only [spatialDeriv]
  exact h

lemma spatialDeriv_mul {f g : Vec3 → ℝ} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialDeriv (fun y => f y * g y) i x =
      spatialDeriv f i x * g x + f x * spatialDeriv g i x := by
  have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) (fderiv_fun_mul hf hg)
  simp only [add_apply, smul_apply, smul_eq_mul] at h
  simp only [spatialDeriv]
  rw [h]
  ring

/-- The pointwise second-order product rule `∂_i ∂_j (η φ)` of `eq:leibniz-lap`
and `eq:commute`. -/
theorem spatialSecondDeriv_mul_smooth {η φ : Vec3 → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i j : Fin 3) (x : Vec3) :
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
  have h1 : spatialDeriv (fun y => η y * φ y) j
      = fun y => spatialDeriv η j y * φ y + η y * spatialDeriv φ j y := by
    funext y
    exact spatialDeriv_mul (hηd y) (hφd y) j
  have hf : DifferentiableAt ℝ (fun y => spatialDeriv η j y * φ y) x :=
    (hη2d x).mul (hφd x)
  have hg : DifferentiableAt ℝ (fun y => η y * spatialDeriv φ j y) x :=
    (hηd x).mul (hφ2d x)
  have hadd : spatialDeriv
        (fun y => spatialDeriv η j y * φ y + η y * spatialDeriv φ j y) i x
      = spatialDeriv (fun y => spatialDeriv η j y * φ y) i x
        + spatialDeriv (fun y => η y * spatialDeriv φ j y) i x :=
    spatialDeriv_add hf hg i
  have hmul1 : spatialDeriv (fun y => spatialDeriv η j y * φ y) i x
      = mixedSecond η i j x * φ x
        + spatialDeriv η j x * spatialDeriv φ i x :=
    spatialDeriv_mul (hη2d x) (hφd x) i
  have hmul2 : spatialDeriv (fun y => η y * spatialDeriv φ j y) i x
      = spatialDeriv η i x * spatialDeriv φ j x
        + η x * mixedSecond φ i j x :=
    spatialDeriv_mul (hηd x) (hφ2d x) i
  simp only [mixedSecond]
  rw [h1, hadd, hmul1, hmul2]
  simp only [mixedSecond]
  ring

/-- The pointwise Leibniz rule `eq:leibniz-lap` for the spatial Laplacian:
`Δ(η φ) = η Δφ + 2 ∇η · ∇φ + φ Δη`. -/
theorem spatialLaplacian_mul_smooth {η φ : Vec3 → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    spatialLaplacian (fun x => η x * φ x)
      = fun x => η x * spatialLaplacian φ x + 2 * spatialGradDot η φ x
          + φ x * spatialLaplacian η x := by
  funext x
  simp only [spatialLaplacian, spatialGradDot]
  trans ∑ i : Fin 3, (mixedSecond η i i x * φ x
      + spatialDeriv η i x * spatialDeriv φ i x
      + spatialDeriv η i x * spatialDeriv φ i x
      + η x * mixedSecond φ i i x)
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    simpa only [mixedSecond] using spatialSecondDeriv_mul_smooth hη hφ i i x
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [mixedSecond]; ring)

end

end CKN
