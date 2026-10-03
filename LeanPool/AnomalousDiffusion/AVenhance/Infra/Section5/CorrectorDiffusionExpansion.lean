/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.DiffusionDivergence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowPiolaIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenFlowRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorFlux

/-! Algebraic decomposition of the per-index corrector diffusion matrix. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

/-- Expand the diffusion matrix times the twisted corrector gradient into the
base corrector flux, inverse-flow gradient defect, and shear cross term. -/
theorem shear_corrector_flux_matrix_expansion
    (κ q : ℝ) (H C : Matrix (Fin 2) (Fin 2) ℝ) :
    (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + q • sigmaMat) *
        (1 + H * C) =
      κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (q • sigmaMat + κ • C) +
        κ • ((H - 1) * C) +
        (q • sigmaMat) * (H * C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_two, sigmaMat] <;> ring

/-- The shear cross flux has zero divergence whenever its two scalar
potentials obey the skew-gradient orthogonality used by the corrector. -/
theorem shear_cross_flux_vecDiv_eq_zero
    {ψ f : Vec 2 → ℝ} {x : Vec 2}
    (hψ : DifferentiableAt ℝ ψ x) (hf : ContDiffAt ℝ 2 f x)
    (horth : vecDot (spaceGrad ψ x)
      (sigmaMat.mulVec (spaceGrad f x)) = 0) :
    vecDiv (fun y => (ψ y • sigmaMat).mulVec (spaceGrad f y)) x = 0 := by
  have hdiff := shear_diffusion_eq_negative_div (ψ := ψ) (f := f) (x := x)
    0 hψ hf
  have hskew : vecDot (sigmaMat.mulVec (spaceGrad ψ x)) (spaceGrad f x) =
      -vecDot (spaceGrad ψ x) (sigmaMat.mulVec (spaceGrad f x)) := by
    simp [vecDot, sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hzero : vecDot (sigmaMat.mulVec (spaceGrad ψ x))
      (spaceGrad f x) = 0 := by rw [hskew, horth]; ring
  have hdiff' : vecDot (sigmaMat.mulVec (spaceGrad ψ x))
      (spaceGrad f x) =
      -vecDiv (fun y => (ψ y • sigmaMat).mulVec
        (spaceGrad f y)) x := by
    simpa only [neg_zero, zero_mul, zero_add, zero_smul] using hdiff
  rw [hzero] at hdiff'
  linarith

/-- The `k`-th diffusion-corrector matrix splits into its base
corrector flux, inverse-flow gradient defect, and shear cross term. -/
theorem frozen_corrector_diffusion_matrix_expansion
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ) (x : Vec 2)
    (κ : ℝ) :
    correctorFlux I hΦ m κ k t x =
      κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        ((I.zetaProd m k t * psi β I.Λ m k
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) • sigmaMat +
          κ • gradMatrix (fun y => I.chiMK κ m k t y)
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) +
        κ • ((gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x - 1) *
          gradMatrix (fun y => I.chiMK κ m k t y)
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) +
        ((I.zetaProd m k t * psi β I.Λ m k
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) • sigmaMat) *
          (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x *
            gradMatrix (fun y => I.chiMK κ m k t y)
              (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) := by
  let M := I.xFlowInv hΦ m (lIdx β I.Λ m k) t
  let χ : Vec 2 → Vec 2 := fun y => I.chiMK κ m k t y
  have hM : DifferentiableAt ℝ M x :=
    (xFlowInv_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k) t).differentiable
      (by norm_num) x
  have hχ : DifferentiableAt ℝ χ (M x) := by
    have hχ' : ContDiff ℝ 2 χ := by
      let E : Vec 2 → ℝ × Vec 2 := fun y => (t, y)
      have hE : ContDiff ℝ 2 E := by fun_prop
      have hc := (Infra.Section3.chiMK_component_contDiff_two
        I (m := m) κ k 0).comp hE
      have hc' := (Infra.Section3.chiMK_component_contDiff_two
        I (m := m) κ k 1).comp hE
      apply contDiff_pi.2
      intro j
      fin_cases j
      · simpa [χ, E, Function.comp_def] using hc
      · simpa [χ, E, Function.comp_def] using hc'
    exact hχ'.differentiable (by norm_num) (M x)
  have hchain := gradMatrix_comp hχ hM
  have hchiTilde : I.chiTilde hΦ m κ k t = fun y => χ (M y) := rfl
  have hchain' : gradMatrix (I.chiTilde hΦ m κ k t) x =
      gradMatrix M x * gradMatrix χ (M x) := by
    rw [hchiTilde]
    exact hchain
  dsimp [correctorFlux, gradChiTilde, M, χ, Ingredients.zetaProd]
  rw [hchain']
  exact shear_corrector_flux_matrix_expansion κ
    (I.hatZetaML m (lIdx β I.Λ m k) t * I.zetaMK m k t *
      psi β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
    (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x)
    (gradMatrix (fun y => I.chiMK κ m k t y)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))

end AVenhance.Infra.Section5
