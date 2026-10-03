/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Regularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowGradientRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.SMat
public import Mathlib.Analysis.Matrix.Normed

/-! Spatial regularity of the averaged coefficient `sMat`. -/

@[expose] public section

open Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Finite support of `hatXiML` transfers spatial regularity of the pulled
flow Jacobians to their averaged matrix field. -/
theorem sMat_spatial_contDiff
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm t : ℝ)
    {n : ℕ∞ω}
    (hflow : ∀ l : ℤ, ContDiff ℝ n (fun x => I.flowGrad hΦ m l t x)) :
    ContDiff ℝ n (fun x => I.sMat hΦ m κm t x) := by
  exact (Infra.Section4.sMat_coarseCoeffForm I hΦ m κm).spatial_contDiff hm t hflow

theorem sMat_spatial_contDiff_one
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm t : ℝ) :
    ContDiff ℝ 1 (fun x => I.sMat hΦ m κm t x) :=
  sMat_spatial_contDiff I hΦ m hm κm t
    (fun l => flowGrad_spatial_contDiff_one I hΦ m l t)

theorem sMat_spatial_contDiff_two
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm t : ℝ) :
    ContDiff ℝ 2 (fun x => I.sMat hΦ m κm t x) :=
  sMat_spatial_contDiff I hΦ m hm κm t
    (fun l => flowGrad_spatial_contDiff_two I hΦ m l t)

end AVenhance.Infra.Section5
