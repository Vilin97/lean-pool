/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.BlockMatrix
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidal
public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.OriginCubeSymmetry
public import Mathlib.LinearAlgebra.Matrix.Swap

/-! # Potential Solenoidal Origin Cube Symmetry -/

@[expose] public section

namespace Homogenization

private theorem matTranspose_signFlipMatrix {d : ℕ} (i : Fin d) :
    matTranspose (signFlipMatrix i) = signFlipMatrix i := by
  ext r c
  by_cases h : r = c
  · subst h
    by_cases hr : r = i
    · subst hr
      simp [signFlipMatrix, matTranspose]
    · simp [signFlipMatrix, matTranspose, hr]
  · simp [signFlipMatrix, matTranspose, h, eq_comm]

private theorem vecDot_signFlipVecContinuousLinearEquiv {d : ℕ}
    (i : Fin d) (x y : Vec d) :
    vecDot (signFlipVecContinuousLinearEquiv i x) y =
      vecDot x (signFlipVecContinuousLinearEquiv i y) := by
  rw [signFlipVecContinuousLinearEquiv_apply, signFlipVecContinuousLinearEquiv_apply,
    ← vecDot_matVecMul_transpose x y (signFlipMatrix i), matTranspose_signFlipMatrix]

private theorem vecDot_swapVecContinuousLinearEquiv {d : ℕ}
    (i j : Fin d) (x y : Vec d) :
    vecDot (swapVecContinuousLinearEquiv i j x) y =
      vecDot x (swapVecContinuousLinearEquiv i j y) := by
  rw [swapVecContinuousLinearEquiv_apply, swapVecContinuousLinearEquiv_apply,
    ← vecDot_matVecMul_transpose x y (Matrix.swap ℝ i j)]
  simp [matTranspose]

theorem isPotentialOn_signFlip_openCubeSet_originCube
    {d : ℕ} {n : ℤ} {f : Vec d → Vec d}
    (hf : IsPotentialOn (openCubeSet (originCube d n)) f) (i : Fin d) :
    IsPotentialOn (openCubeSet (originCube d n))
      (fun x => signFlipVecContinuousLinearEquiv i (f (signFlipVecContinuousLinearEquiv i x))) := by
  rcases hf with ⟨u, rfl⟩
  exact (u.signFlipOnOpenCubeSetOriginCube i).isPotentialOn

theorem isPotentialOn_swap_openCubeSet_originCube
    {d : ℕ} {n : ℤ} {f : Vec d → Vec d}
    (hf : IsPotentialOn (openCubeSet (originCube d n)) f) (i j : Fin d) :
    IsPotentialOn (openCubeSet (originCube d n))
      (fun x => swapVecContinuousLinearEquiv i j (f (swapVecContinuousLinearEquiv i j x))) := by
  rcases hf with ⟨u, rfl⟩
  simpa [swapVecContinuousLinearEquiv_apply] using!
    (u.swapOnOpenCubeSetOriginCube i j).isPotentialOn

theorem isPotentialZeroTraceOn_signFlip_openCubeSet_originCube
    {d : ℕ} {n : ℤ} {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn (openCubeSet (originCube d n)) f) (i : Fin d) :
    IsPotentialZeroTraceOn (openCubeSet (originCube d n))
      (fun x => signFlipVecContinuousLinearEquiv i (f (signFlipVecContinuousLinearEquiv i x))) := by
  rcases hf with ⟨u, rfl⟩
  exact (H10Function.signFlipOnOpenCubeSetOriginCube u i).isPotentialZeroTraceOn

theorem isPotentialZeroTraceOn_swap_openCubeSet_originCube
    {d : ℕ} {n : ℤ} {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn (openCubeSet (originCube d n)) f) (i j : Fin d) :
    IsPotentialZeroTraceOn (openCubeSet (originCube d n))
      (fun x => swapVecContinuousLinearEquiv i j (f (swapVecContinuousLinearEquiv i j x))) := by
  rcases hf with ⟨u, rfl⟩
  simpa [swapVecContinuousLinearEquiv_apply] using!
    (H10Function.swapOnOpenCubeSetOriginCube u i j).isPotentialZeroTraceOn

theorem isSolenoidalZeroNormalTraceOn_signFlip_openCubeSet_originCube
    {d : ℕ} {n : ℤ} {g : Vec d → Vec d}
    (hg : IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d n)) g) (i : Fin d) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d n))
      (fun x => signFlipVecContinuousLinearEquiv i (g (signFlipVecContinuousLinearEquiv i x))) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  intro φ
  let ψ : H1Function U := φ.signFlipOnOpenCubeSetOriginCube i
  have hψ :
      ∫ x in U, vecDot (g x)
        (signFlipVecContinuousLinearEquiv i (φ.grad (signFlipVecContinuousLinearEquiv i x)))
          ∂MeasureTheory.volume = 0 := by
    simpa [U, ψ, H1Function.signFlipOnOpenCubeSetOriginCube] using hg ψ
  have hchange :
      ∫ x in U, vecDot (g x)
          (signFlipVecContinuousLinearEquiv i (φ.grad (signFlipVecContinuousLinearEquiv i x)))
          ∂MeasureTheory.volume =
        ∫ x in U, vecDot (g (signFlipVecContinuousLinearEquiv i x))
          (signFlipVecContinuousLinearEquiv i (φ.grad x)) ∂MeasureTheory.volume := by
    let f : Vec d → ℝ := fun y =>
      vecDot (g (signFlipVecContinuousLinearEquiv i y))
        (signFlipVecContinuousLinearEquiv i (φ.grad y))
    simpa only [U, f, signFlipVecContinuousLinearEquiv_self_apply] using
      setIntegral_comp_signFlipVecContinuousLinearEquiv_openCubeSet_originCube i n f
  rw [hchange] at hψ
  rw [show (fun x => vecDot (g (signFlipVecContinuousLinearEquiv i x))
      (signFlipVecContinuousLinearEquiv i (φ.grad x))) =
      fun x => vecDot (signFlipVecContinuousLinearEquiv i (g (signFlipVecContinuousLinearEquiv i x)))
        (φ.grad x) by
        funext x
        symm
        exact vecDot_signFlipVecContinuousLinearEquiv i (g (signFlipVecContinuousLinearEquiv i x))
          (φ.grad x)] at hψ
  simpa using hψ

theorem isSolenoidalZeroNormalTraceOn_swap_openCubeSet_originCube
    {d : ℕ} {n : ℤ} {g : Vec d → Vec d}
    (hg : IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d n)) g) (i j : Fin d) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d n))
      (fun x => swapVecContinuousLinearEquiv i j (g (swapVecContinuousLinearEquiv i j x))) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  intro φ
  let ψ : H1Function U := φ.swapOnOpenCubeSetOriginCube i j
  have hψ :
      ∫ x in U, vecDot (g x)
        (swapVecContinuousLinearEquiv i j (φ.grad (swapVecContinuousLinearEquiv i j x)))
          ∂MeasureTheory.volume = 0 := by
    simpa [U, ψ, H1Function.swapOnOpenCubeSetOriginCube] using hg ψ
  have hchange :
      ∫ x in U, vecDot (g x)
          (swapVecContinuousLinearEquiv i j (φ.grad (swapVecContinuousLinearEquiv i j x)))
          ∂MeasureTheory.volume =
        ∫ x in U, vecDot (g (swapVecContinuousLinearEquiv i j x))
          (swapVecContinuousLinearEquiv i j (φ.grad x)) ∂MeasureTheory.volume := by
    let f : Vec d → ℝ := fun y =>
      vecDot (g (swapVecContinuousLinearEquiv i j y))
        (swapVecContinuousLinearEquiv i j (φ.grad y))
    simpa only [U, f, swapVecContinuousLinearEquiv_self_apply] using
      setIntegral_comp_swapVecContinuousLinearEquiv_openCubeSet_originCube i j n f
  rw [hchange] at hψ
  rw [show (fun x => vecDot (g (swapVecContinuousLinearEquiv i j x))
      (swapVecContinuousLinearEquiv i j (φ.grad x))) =
      fun x => vecDot (swapVecContinuousLinearEquiv i j (g (swapVecContinuousLinearEquiv i j x)))
        (φ.grad x) by
        funext x
        symm
        exact vecDot_swapVecContinuousLinearEquiv i j (g (swapVecContinuousLinearEquiv i j x))
          (φ.grad x)] at hψ
  simpa using hψ

end Homogenization
