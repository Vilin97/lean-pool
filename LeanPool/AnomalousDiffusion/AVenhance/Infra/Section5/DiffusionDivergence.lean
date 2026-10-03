/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FluxDivergence
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SpaceLap
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SigmaMat

/-! Divergence-form expansion of the shear diffusion and its induced drift. -/

@[expose] public section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5

open AVenhance

theorem DiffusionDivergence.spaceGrad_hasFDerivAt_of_contDiffAt_two
    {f : Vec 2 → ℝ} {x : Vec 2} (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (spaceGrad f)
      (ContinuousLinearMap.pi fun j : Fin 2 =>
        (fderiv ℝ (fderiv ℝ f) x).flip (basisVec j)) x := by
  let D2 : Vec 2 →L[ℝ] (Vec 2 →L[ℝ] ℝ) := fderiv ℝ (fderiv ℝ f) x
  have hDcont : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    hf.fderiv_right (m := 1) (by norm_num)
  have hD : HasFDerivAt (fderiv ℝ f) D2 x := by
    exact (hDcont.differentiableAt (by norm_num)).hasFDerivAt
  have hcoord (j : Fin 2) : HasFDerivAt
      (fun y => spaceGrad f y j) (D2.flip (basisVec j)) x := by
    change HasFDerivAt (fun y => (fderiv ℝ f y) (basisVec j)) _ x
    simpa [D2, ContinuousLinearMap.comp_zero] using
      hD.clm_apply (hasFDerivAt_const (basisVec j) x)
  apply hasFDerivAt_pi.2
  intro j
  simpa [D2, ContinuousLinearMap.pi_apply, spaceGrad] using hcoord j

theorem DiffusionDivergence.spaceLap_eq_diagonal_deriv
    {f : Vec 2 → ℝ} {x : Vec 2} {L : Vec 2 →L[ℝ] Vec 2}
    (hgrad : HasFDerivAt (spaceGrad f) L x) :
    spaceLap f x = ∑ i : Fin 2, (L (basisVec i)) i := by
  unfold spaceLap
  apply Finset.sum_congr rfl
  intro i hi
  have hcoord : HasFDerivAt (fun y => spaceGrad f y i)
      ((ContinuousLinearMap.proj i).comp L) x :=
    by
      simpa [Function.comp_def] using
        (ContinuousLinearMap.proj i).hasFDerivAt.comp x hgrad
  rw [spaceGrad, hcoord.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-- The source shear drift turns the skew diffusion into divergence form. The
spatial regularity hypotheses are precisely one derivative of `ψ` and two of
`f`; symmetry of the Hessian is derived from the latter. -/
theorem shear_diffusion_eq_negative_div
    {f ψ : Vec 2 → ℝ} {x : Vec 2} (κ : ℝ)
    (hψ : DifferentiableAt ℝ ψ x) (hf : ContDiffAt ℝ 2 f x) :
    -κ * spaceLap f x +
        vecDot (sigmaMat.mulVec (spaceGrad ψ x)) (spaceGrad f x) =
      -vecDiv (fun y =>
        (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + ψ y • sigmaMat).mulVec
          (spaceGrad f y)) x := by
  let Lψ : Vec 2 →L[ℝ] ℝ := fderiv ℝ ψ x
  let A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun y =>
    κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + ψ y • sigmaMat
  let D2 : Vec 2 →L[ℝ] (Vec 2 →L[ℝ] ℝ) := fderiv ℝ (fderiv ℝ f) x
  let Lgrad : Vec 2 →L[ℝ] Vec 2 := ContinuousLinearMap.pi fun j : Fin 2 =>
    D2.flip (basisVec j)
  have hψF : HasFDerivAt ψ Lψ x := hψ.hasFDerivAt
  have hgrad : HasFDerivAt (spaceGrad f) Lgrad x := by
    simpa [Lgrad, D2] using DiffusionDivergence.spaceGrad_hasFDerivAt_of_contDiffAt_two hf
  have hA : ∀ i j, HasFDerivAt (fun y => A y i j)
      ((sigmaMat i j) • Lψ) x := by
    intro i j
    change HasFDerivAt
      (fun y => κ * (if i = j then (1 : ℝ) else 0) +
        ψ y * sigmaMat i j) ((sigmaMat i j) • Lψ) x
    have hconst : HasFDerivAt
        (fun _ : Vec 2 => κ * (if i = j then (1 : ℝ) else 0))
        (0 : Vec 2 →L[ℝ] ℝ) x :=
      hasFDerivAt_const _ x
    have hvar := hψF.const_mul (sigmaMat i j)
    have hadd := hconst.add hvar
    have hfun : (fun y => κ * (if i = j then (1 : ℝ) else 0) +
        ψ y * sigmaMat i j) =
        (fun _ : Vec 2 => κ * (if i = j then (1 : ℝ) else 0)) +
          (fun y => sigmaMat i j * ψ y) := by
      funext y
      change κ * (if i = j then (1 : ℝ) else 0) + ψ y * sigmaMat i j =
        κ * (if i = j then (1 : ℝ) else 0) + sigmaMat i j * ψ y
      ring
    rw [hfun]
    simpa only [zero_add] using hadd
  have hsymm := hf.isSymmSndFDerivAt (by norm_num)
  have hcross : D2 (basisVec (0 : Fin 2)) (basisVec 1) =
      D2 (basisVec (1 : Fin 2)) (basisVec 0) := by
    exact hsymm (basisVec (0 : Fin 2)) (basisVec (1 : Fin 2))
  have hdiv := vecDiv_matrixMulVec hA hgrad
  have hdivExpanded :
    vecDiv (fun y => (A y).mulVec (spaceGrad f y)) x =
        κ * spaceLap f x +
          (spaceGrad ψ x 0 * (-(spaceGrad f x 1)) +
            spaceGrad ψ x 1 * spaceGrad f x 0) := by
    rw [hdiv, DiffusionDivergence.spaceLap_eq_diagonal_deriv hgrad]
    simp only [sigmaMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, smul_apply,
        smul_eq_mul,
      spaceGrad, Matrix.smul_of, Matrix.smul_cons, mul_zero, mul_neg, mul_one, Matrix.smul_empty,
          Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, mul_ite, ContinuousLinearMap.pi_apply,
          ContinuousLinearMap.flip_apply,
      Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul,
          ↓reduceIte, add_zero, zero_add,
      neg_mul, one_mul, zero_ne_one, one_ne_zero, Lψ, A, Lgrad, D2]
    rw [hcross]
    ring
  have hdrift :
      vecDot (sigmaMat.mulVec (spaceGrad ψ x)) (spaceGrad f x) =
        -(spaceGrad ψ x 0 * (-(spaceGrad f x 1)) +
          spaceGrad ψ x 1 * spaceGrad f x 0) := by
    simp [vecDot, sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hdivExpanded, hdrift]
  ring

end AVenhance.Infra.Section5
