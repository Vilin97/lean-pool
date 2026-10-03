/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusion

/-! Exact derivative commutators for the material oscillatory terms. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Commuting a fixed derivative past a variable directional derivative
produces precisely the derivative of the direction field. -/
theorem iterate_directional_commutator
    {f : AmnrSpace → ℝ} {d : AmnrSpace → AmnrSpace} {z : AmnrSpace}
    (hf : ContDiffAt ℝ 2 f z) (hd : DifferentiableAt ℝ d z) (e : AmnrSpace) :
    fderiv ℝ (fun y => fderiv ℝ f y (d y)) z e =
      fderiv ℝ (fun y => fderiv ℝ f y e) z (d z) +
      fderiv ℝ f z (fderiv ℝ d z e) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  rw [fderiv_clm_apply hdf hd,
    fderiv_clm_apply hdf (differentiableAt_const e)]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_fun_const, Pi.zero_apply, zero_apply,
    map_zero, zero_add]
  rw [hs e (d z)]
  ring

/-- The spatial/material commutator is the actual velocity-gradient term.
This identity supplies both flow commutators in the primitive integration by
parts; the velocity gradient is not an assumed error equation. -/
theorem iterate_spatial_material_commutator
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ} {z : AmnrSpace}
    (hf : ContDiffAt ℝ 2 f z) (hb : DifferentiableAt ℝ b z) (i : Fin 2) :
    amnrOp b (some i) (amnrOp b none f) z =
      amnrOp b none (amnrOp b (some i) f) z +
      fderiv ℝ f z (0, fderiv ℝ b z (0, basisVec i)) := by
  have hd : DifferentiableAt ℝ (fun y : AmnrSpace => ((1 : ℝ), b y)) z :=
    differentiableAt_const (1 : ℝ) |>.prodMk hb
  have h := iterate_directional_commutator hf hd ((0, basisVec i) : AmnrSpace)
  have hdir : fderiv ℝ (fun y : AmnrSpace => ((1 : ℝ), b y)) z =
      (0 : AmnrSpace →L[ℝ] ℝ).prod (fderiv ℝ b z) := by
    exact ((hasFDerivAt_const (1 : ℝ) z).prodMk hb.hasFDerivAt).fderiv
  unfold amnrOp amnrDirection
  rw [hdir] at h
  exact h

end AVenhance.Infra.Section4
