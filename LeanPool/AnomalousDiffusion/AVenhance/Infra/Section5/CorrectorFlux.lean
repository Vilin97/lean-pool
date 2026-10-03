/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ChiMKCorrector
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ShearFormula
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowPiola

/-! The unpulled corrector flux divergence identity and its conditional
cofactor push-forward along the inverse flow. -/

@[expose] public section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β)

/-- Flux in the `j`th corrector equation before the inverse-flow push-forward. -/
noncomputable def frozenCorrectorFlux (κ : ℝ) (m : ℕ) (k : ℤ) (j : Fin 2) (t : ℝ)
    (y : Vec 2) : Vec 2 :=
  fun i => I.zetaProd m k t * psi β I.Λ m k y * sigmaMat i j +
    κ * spaceGrad (fun z => I.chiMK κ m k t z j) y i

theorem CorrectorFlux.spaceGrad_add_of_differentiableAt
    {f g : Vec 2 → ℝ} {x : Vec 2} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    spaceGrad (fun y => f y + g y) x i = spaceGrad f x i + spaceGrad g x i := by
  change fderiv ℝ (f + g) x (basisVec i) = _
  rw [fderiv_add hf hg]
  rfl

theorem CorrectorFlux.spaceGrad_const_mul_left
    {f : Vec 2 → ℝ} {x : Vec 2} (c : ℝ)
    (hf : DifferentiableAt ℝ f x) (i : Fin 2) :
    spaceGrad (fun y => c * f y) x i = c * spaceGrad f x i := by
  change fderiv ℝ (fun y => c * f y) x (basisVec i) = _
  rw [fderiv_const_mul hf c]
  simp [spaceGrad, smul_eq_mul]

/-- The corrector equation is exactly the divergence identity for its
base flux. No inverse-flow regularity or Piola premise enters this local step. -/
theorem frozenCorrectorFlux_vecDiv
    (κ : ℝ) (m : ℕ) (k : ℤ) (j : Fin 2) (t : ℝ) (x : Vec 2) :
    vecDiv (frozenCorrectorFlux I κ m k j t) x =
      deriv (fun s => I.chiMK κ m k s x j) t := by
  have hε : epsilon β I.Λ m ≠ 0 := ne_of_gt
    (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  have hpsi : ContDiff ℝ 1 (psi β I.Λ m k) := by
    unfold psi
    have hprofile : ContDiff ℝ 1
        (fun y : Vec 2 => psi0 k ((epsilon β I.Λ m)⁻¹ • y)) := by
      unfold psi0
      split_ifs <;> fun_prop
    exact contDiff_const.mul hprofile
  have hchi : ContDiff ℝ 2 (fun y : Vec 2 => I.chiMK κ m k t y j) := by
    let E : Vec 2 → ℝ × Vec 2 := fun y => (t, y)
    have hE : ContDiff ℝ 2 E := by fun_prop
    have h := (Infra.Section3.chiMK_component_contDiff_two I (m := m) κ k j).comp hE
    simpa [E, Function.comp_def] using h
  have hpsiDiff : DifferentiableAt ℝ (psi β I.Λ m k) x :=
    hpsi.differentiable (by norm_num) x
  have hchiDiff : DifferentiableAt ℝ (fun y => I.chiMK κ m k t y j) x :=
    hchi.differentiable (by norm_num) x
  have hgradChiDiff (i : Fin 2) :
      DifferentiableAt ℝ
        (fun y => spaceGrad (fun z => I.chiMK κ m k t z j) y i) x := by
    have hD : HasFDerivAt
        (fderiv ℝ (fun y => I.chiMK κ m k t y j))
        (fderiv ℝ (fderiv ℝ (fun y => I.chiMK κ m k t y j)) x) x := by
      exact ((hchi.fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num) x).hasFDerivAt
    have h := hD.clm_apply (hasFDerivAt_const (basisVec i) x)
    have h' : HasFDerivAt
        (fun y => spaceGrad (fun z => I.chiMK κ m k t z j) y i)
        ((fderiv ℝ (fderiv ℝ (fun y => I.chiMK κ m k t y j)) x).flip
          (basisVec i)) x := by
      simpa [spaceGrad, ContinuousLinearMap.comp_zero] using h
    exact h'.differentiableAt
  have hterm (i : Fin 2) :
      spaceGrad (fun y => I.zetaProd m k t * psi β I.Λ m k y *
        sigmaMat i j) x i =
          I.zetaProd m k t * sigmaMat i j *
            spaceGrad (psi β I.Λ m k) x i := by
    have hfun : (fun y => I.zetaProd m k t * psi β I.Λ m k y *
        sigmaMat i j) = fun y =>
          (I.zetaProd m k t * sigmaMat i j) * psi β I.Λ m k y := by
      funext y
      ring
    rw [hfun, CorrectorFlux.spaceGrad_const_mul_left _ hpsiDiff i]
  have hterm' (i : Fin 2) :
      spaceGrad (fun y => κ *
        spaceGrad (fun z => I.chiMK κ m k t z j) y i) x i =
          κ * spaceGrad (fun y =>
            spaceGrad (fun z => I.chiMK κ m k t z j) y i) x i :=
    CorrectorFlux.spaceGrad_const_mul_left _ (hgradChiDiff i) i
  have hbaseDiff (i : Fin 2) : DifferentiableAt ℝ
      (fun y => I.zetaProd m k t * psi β I.Λ m k y * sigmaMat i j) x := by
    convert (differentiableAt_const
      (I.zetaProd m k t * sigmaMat i j)).mul hpsiDiff using 1
    ext y
    change I.zetaProd m k t * psi β I.Λ m k y * sigmaMat i j =
      (I.zetaProd m k t * sigmaMat i j) * psi β I.Λ m k y
    ring
  have hcorrDiff (i : Fin 2) : DifferentiableAt ℝ
      (fun y => κ * spaceGrad (fun z => I.chiMK κ m k t z j) y i) x :=
    (differentiableAt_const κ).mul (hgradChiDiff i)
  have hdivFlux :
      vecDiv (frozenCorrectorFlux I κ m k j t) x =
        κ * spaceLap (fun y => I.chiMK κ m k t y j) x -
          I.zetaProd m k t * uShear β I.Λ m k x j := by
    unfold vecDiv frozenCorrectorFlux
    simp only [Fin.sum_univ_two]
    rw [CorrectorFlux.spaceGrad_add_of_differentiableAt
      (f := fun y => I.zetaProd m k t * psi β I.Λ m k y * sigmaMat 0 j)
      (g := fun y => κ * spaceGrad (fun z => I.chiMK κ m k t z j) y 0)
      (hbaseDiff 0) (hcorrDiff 0) 0,
      CorrectorFlux.spaceGrad_add_of_differentiableAt
      (f := fun y => I.zetaProd m k t * psi β I.Λ m k y * sigmaMat 1 j)
      (g := fun y => κ * spaceGrad (fun z => I.chiMK κ m k t z j) y 1)
      (hbaseDiff 1) (hcorrDiff 1) 1,
      hterm 0, hterm 1, hterm' 0, hterm' 1]
    have htransport :
        (∑ i : Fin 2, sigmaMat i j * spaceGrad (psi β I.Λ m k) x i) =
          -uShear β I.Λ m k x j := by
      have hu := congrArg (fun v : Vec 2 => v j)
        (Infra.Section3.uShear_eq_sigma_spaceGrad k x hε)
      fin_cases j <;>
        simp [sigmaMat, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two] at hu ⊢ <;>
        linarith
    calc
      _ = κ * spaceLap (fun y => I.chiMK κ m k t y j) x +
          I.zetaProd m k t *
            (∑ i : Fin 2, sigmaMat i j * spaceGrad (psi β I.Λ m k) x i) := by
              simp [spaceLap, Fin.sum_univ_two]
              ring
      _ = κ * spaceLap (fun y => I.chiMK κ m k t y j) x -
          I.zetaProd m k t * uShear β I.Λ m k x j := by
              rw [htransport]
              ring
  have hPDE :=
    (Infra.Section3.chiMK_component_hasCorrectorPDE I (m := m) κ k j t x).deriv
  have htransport := Infra.Section3.chiMK_transport_identity I (m := m) κ k t x j
  rw [htransport] at hPDE
  exact hdivFlux.trans hPDE.symm

end AVenhance.Infra.Section5
