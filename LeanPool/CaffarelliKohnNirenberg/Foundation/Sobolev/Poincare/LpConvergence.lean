/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.W1p.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The ball Poincare inequality for representative-level `W^{1,p}` functions

The proof uses interior mollification on compactly contained balls and then
exhausts the original ball.
-/

@[expose] public section

open Function Set Filter MeasureTheory Topology
open scoped ENNReal Convolution Pointwise

namespace CKN

noncomputable section
lemma integral_rpow_norm_eq_lpNorm_rpow
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    {f : Vec 3 → ℝ} {μ : Measure (Vec 3)} (hf : MemLp f p μ) :
    (∫ x, ‖f x‖ ^ p.toReal ∂μ) = lpNorm f p μ ^ p.toReal := by
  rw [lpNorm_eq_integral_norm_rpow_toReal hp0 hpTop hf.aestronglyMeasurable]
  exact (Real.rpow_inv_rpow (integral_nonneg_of_ae
    (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _))
    (ENNReal.toReal_ne_zero.mpr ⟨hp0, hpTop⟩)).symm

lemma tendsto_integral_rpow_norm_of_tendsto_lpNorm
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    {f : Vec 3 → ℝ} {μ : Measure (Vec 3)} (hf : MemLp f p μ)
    {g : ℕ → Vec 3 → ℝ} (hg : ∀ n, MemLp (g n) p μ)
    (hconv : Tendsto (fun n => lpNorm (g n) p μ) atTop
    (nhds (lpNorm f p μ))) :
    Tendsto (fun n => ∫ x, ‖g n x‖ ^ p.toReal ∂μ) atTop
      (nhds (∫ x, ‖f x‖ ^ p.toReal ∂μ)) := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hpow : Tendsto (fun n => lpNorm (g n) p μ ^ p.toReal) atTop
      (nhds (lpNorm f p μ ^ p.toReal)) := by
    have hpair : Tendsto (fun n => (lpNorm (g n) p μ, p.toReal)) atTop
        (nhds (lpNorm f p μ, p.toReal)) := by
      simpa only [nhds_prod_eq] using hconv.prodMk
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => p.toReal) atTop
          (nhds p.toReal))
    exact (Real.continuousAt_rpow_of_pos (lpNorm f p μ, p.toReal) hp_pos).tendsto.comp
      hpair
  have hfun :
      (fun n => ∫ x, ‖g n x‖ ^ p.toReal ∂μ) =
        (fun n => lpNorm (g n) p μ ^ p.toReal) := by
    funext n
    exact integral_rpow_norm_eq_lpNorm_rpow hp0 hpTop (hg n)
  have htarget :
      (∫ x, ‖f x‖ ^ p.toReal ∂μ) = lpNorm f p μ ^ p.toReal :=
    integral_rpow_norm_eq_lpNorm_rpow hp0 hpTop hf
  rw [hfun, htarget]
  exact hpow

lemma tendsto_lpNorm_zero_of_tendsto_eLpNorm_zero
    {p : ℝ≥0∞} {μ : Measure (Vec 3)} {f : ℕ → Vec 3 → ℝ}
    (hconv : Tendsto (fun n => eLpNorm (f n) p μ) atTop (nhds 0)) :
    Tendsto (fun n => lpNorm (f n) p μ) atTop (nhds 0) := by
  have hto : Tendsto ENNReal.toReal (nhds (0 : ℝ≥0∞)) (nhds (0 : ℝ)) := by
    simpa only [ENNReal.toReal_zero] using ENNReal.tendsto_toReal ENNReal.zero_ne_top
  change Tendsto (fun n => (eLpNorm (f n) p μ).toReal) atTop (nhds 0)
  exact hto.comp hconv

end
end CKN
