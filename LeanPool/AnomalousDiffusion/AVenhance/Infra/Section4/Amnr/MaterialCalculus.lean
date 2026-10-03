/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowAverage
public import Mathlib.Analysis.Calculus.VectorField

/-! Actual spatial/material commutators for the T and flow estimates. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- The spatial directional operator equals the spatial gradient. -/
theorem amnrOp_space {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    {z : AmnrSpace} (hf : DifferentiableAt ℝ f z) (i : Fin 2) :
    amnrOp b (some i) f z = AVenhance.spaceGrad (fun y => f (z.1, y)) z.2 i := by
  have hx := (hf.hasFDerivAt.comp z.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)).fderiv
  unfold AVenhance.spaceGrad amnrOp amnrDirection
  change fderiv ℝ f z (0, basisVec i) =
    fderiv ℝ (f ∘ fun y => (z.1, y)) z.2 (basisVec i)
  rw [hx]
  rfl

/-- Expansion of a vertical differential in the actual two-coordinate basis. -/
theorem amnrFDeriv_vertical (f : AmnrSpace → ℝ) (z : AmnrSpace) (v : Vec 2) :
    fderiv ℝ f z (0, v) =
      ∑ p : Fin 2, v p * fderiv ℝ f z (0, basisVec p) := by
  have hv : ((0, v) : AmnrSpace) =
      ∑ p : Fin 2, v p • ((0, basisVec p) : AmnrSpace) := by
    apply Prod.ext
    · simp
    · funext p
      fin_cases p <;> simp [basisVec_apply]
  rw [hv, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact map_smul _ _ _

/-- The material/spatial commutator in source coordinates, with the precise
transpose contraction on the gradient. -/
theorem amnr_material_spatial_commutator {b : AmnrSpace → Vec 2}
    {f : AmnrSpace → ℝ} {z : AmnrSpace} (hb : DifferentiableAt ℝ b z)
    (hf : ContDiffAt ℝ 2 f z) (i : Fin 2) :
    amnrOp b none (amnrOp b (some i) f) z =
      amnrOp b (some i) (amnrOp b none f) z -
        ∑ p : Fin 2, amnrVelocityGradient b p i z * amnrOp b (some p) f z := by
  have htc : DifferentiableAt ℝ (fun _ : AmnrSpace => (1 : ℝ)) z := differentiableAt_const 1
  have hdir : DifferentiableAt ℝ (amnrDirection b none) z := htc.prodMk hb
  have hconst : DifferentiableAt ℝ (amnrDirection b (some i)) z := differentiableAt_const _
  have hh := VectorField.fderiv_apply_lieBracket hf (by norm_num)
    hconst hdir
  have hd : fderiv ℝ (amnrDirection b none) z =
      (0 : AmnrSpace →L[ℝ] ℝ).prod (fderiv ℝ b z) := by
    change fderiv ℝ (fun y => ((1 : ℝ), b y)) z = _
    simpa only [fderiv_fun_const, Pi.zero_apply] using htc.fderiv_prodMk hb
  have hbracket : VectorField.lieBracket ℝ (amnrDirection b none)
      (amnrDirection b (some i)) z =
        -((0, fderiv ℝ b z (0, basisVec i)) : AmnrSpace) := by
    unfold VectorField.lieBracket
    change fderiv ℝ (fun _ : AmnrSpace => ((0, basisVec i) : AmnrSpace)) z
      (amnrDirection b none z) - fderiv ℝ (amnrDirection b none) z (0, basisVec i) = _
    rw [fderiv_fun_const, hd]
    simp
  rw [hbracket, map_neg, amnrFDeriv_vertical] at hh
  have hcoeff (p : Fin 2) : (fderiv ℝ b z (0, basisVec i)) p = amnrVelocityGradient b p i z := by
    have hp := (differentiable_apply p).differentiableAt.comp z hb
    have heq := fderiv_apply hb p
    have hs := amnrOp_space (b := b) hp i
    change fderiv ℝ (fun y => b y p) z (0, basisVec i) = amnrVelocityGradient b p i z at hs
    rw [heq] at hs
    exact hs
  simp only [hcoeff] at hh
  change -(∑ p : Fin 2, amnrVelocityGradient b p i z * amnrOp b (some p) f z) =
    amnrOp b none (amnrOp b (some i) f) z - amnrOp b (some i) (amnrOp b none f) z at hh
  linarith only [hh]

end AVenhance.Infra.Section4
