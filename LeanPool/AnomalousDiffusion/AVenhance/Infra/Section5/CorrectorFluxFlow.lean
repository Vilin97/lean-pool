/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowPiolaDivergence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenFlowRegularity

/-! The corrector equation pushed through its smooth inverse flow. -/

@[expose] public section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β)

theorem frozen_corrector_flux_contDiff_one
    (κ : ℝ) (m : ℕ) (k : ℤ) (j : Fin 2) (t : ℝ) :
    ContDiff ℝ 1 (frozenCorrectorFlux I κ m k j t) := by
  let χ : Vec 2 → ℝ := fun y => I.chiMK κ m k t y j
  have hψ : ContDiff ℝ 1 (psi β I.Λ m k) := by
    unfold psi
    have hprofile : ContDiff ℝ 1
        (fun y : Vec 2 => psi0 k ((epsilon β I.Λ m)⁻¹ • y)) := by
      unfold psi0
      split_ifs <;> fun_prop
    exact contDiff_const.mul hprofile
  have hχ2 : ContDiff ℝ 2 χ := by
    let E : Vec 2 → ℝ × Vec 2 := fun y => (t, y)
    have hE : ContDiff ℝ 2 E := by fun_prop
    have h := (Infra.Section3.chiMK_component_contDiff_two
      I (m := m) κ k j).comp hE
    simpa [χ, E, Function.comp_def] using h
  have hgradχ : ContDiff ℝ 1 (spaceGrad χ) := by
    have hD : ContDiff ℝ 1 (fderiv ℝ χ) :=
      hχ2.fderiv_right (by norm_num)
    apply contDiff_pi.2
    intro i
    have hi : ContDiff ℝ 1 (fun y => fderiv ℝ χ y (basisVec i)) := by
      exact hD.clm_apply contDiff_const
    simpa [spaceGrad, ContinuousLinearMap.comp_zero] using hi
  apply contDiff_pi.2
  intro i
  have hbase : ContDiff ℝ 1
      (fun y => I.zetaProd m k t * psi β I.Λ m k y * sigmaMat i j) := by
    have hmul : ContDiff ℝ 1
        (fun y => (I.zetaProd m k t * sigmaMat i j) * psi β I.Λ m k y) :=
      contDiff_const.mul hψ
    convert hmul using 1
    funext y
    ring
  have hcorrector : ContDiff ℝ 1
      (fun y => κ * spaceGrad χ y i) :=
    contDiff_const.mul (contDiff_pi.1 hgradχ i)
  have hcomponent := hbase.add hcorrector
  simpa [frozenCorrectorFlux, χ] using hcomponent

end AVenhance.Infra.Section5
