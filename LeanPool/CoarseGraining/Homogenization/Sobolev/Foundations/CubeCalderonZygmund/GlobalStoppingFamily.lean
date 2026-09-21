/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaLargeScale
import Mathlib.MeasureTheory.Function.L2Space

/-! # Global Stopping Family -/

namespace Homogenization

open scoped ENNReal NNReal BigOperators Topology
open Filter MeasureTheory Set

noncomputable section

namespace CubeCalderonZygmund

/-!
# Global stopping families for the cube good-`λ` argument

This module turns the a.e. differentiation theorem and the global `L²`
cutoff into one radius at every relevant centre.  It is deliberately
independent of the PDE comparison: the returned last-exit certificates are
the complete interface consumed by the later Vitali assembly.
-/

/-- Above the global `L²` cutoff, every designated high-field point has an
exact stopping radius below the conservative comparison cutoff.

The differentiation set is constructed internally.  The radius is a total
function only to match the Vitali API; its values away from `target ∩ D` are
irrelevant. -/
theorem exists_globalStoppingFamily
    {d : ℕ} [NeZero d] {m : ℤ} {F G : Type*}
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    (depth : ℕ) (f : Vec d → F) (g : Vec d → G) (eps M level : ℝ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (heps : 0 < eps) (hM : 1 ≤ M)
    (hlevel :
      Real.sqrt (((2 * (cubeRadius (originCube d m) /
        (10 * (3 : ℝ) ^ depth))) ^ d)⁻¹ *
        ((∫ y, ‖f y‖ ^ (2 : ℕ) ∂volume) +
          (eps⁻¹) ^ (2 : ℕ) * ∫ y, ‖g y‖ ^ (2 : ℕ) ∂volume)) < level)
    (target : Set (Vec d))
    (htarget : ∀ x ∈ target, M * level < ‖f x‖) :
    ∃ D : Set (Vec d), ∃ radius : Vec d → ℝ,
      volume Dᶜ = 0 ∧
      ∀ x ∈ target ∩ D,
        0 < radius x ∧
        radius x ≤ cubeRadius (originCube d m) / (10 * (3 : ℝ) ^ depth) ∧
        goodLambdaCombinedEnergy f g eps x (radius x) = level ∧
        ∀ s ∈ Icc (radius x) (cubeRadius (originCube d m)),
          goodLambdaCombinedEnergy f g eps x s ≤ level := by
  have hf_int : Integrable (fun y => ‖f y‖ ^ (2 : ℕ)) volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hg_int : Integrable (fun y => ‖g y‖ ^ (2 : ℕ)) volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  let R : ℝ := cubeRadius (originCube d m)
  let rho : ℝ := R / (10 * (3 : ℝ) ^ depth)
  have hR : 0 < R := cubeRadius_pos _
  have hdenom : 0 < 10 * (3 : ℝ) ^ depth := by positivity
  have hrho : 0 < rho := div_pos hR hdenom
  have hdenom_one : 1 ≤ 10 * (3 : ℝ) ^ depth := by
    have hpow : 1 ≤ (3 : ℝ) ^ depth := one_le_pow₀ (by norm_num)
    nlinarith
  have hrhoR : rho ≤ R := by
    exact div_le_self hR.le hdenom_one
  have hcutoff :
      Real.sqrt (((2 * rho) ^ d)⁻¹ *
        ((∫ y, ‖f y‖ ^ (2 : ℕ) ∂volume) +
          (eps⁻¹) ^ (2 : ℕ) * ∫ y, ‖g y‖ ^ (2 : ℕ) ∂volume)) < level := by
    simpa only [R, rho] using hlevel
  have hlevel_pos : 0 < level :=
    lt_of_le_of_lt (Real.sqrt_nonneg _) hcutoff
  have heps_weight_pos : 0 < (eps⁻¹) ^ (2 : ℕ) := by
    exact sq_pos_of_pos (inv_pos.mpr heps)
  have hlarge : ∀ x : Vec d, ∀ s ∈ Icc rho R,
      goodLambdaCombinedEnergy f g eps x s ≤ level := by
    intro x s hs
    exact (goodLambdaCombinedEnergy_le_globalIntegral f g eps hf_int hg_int x hrho hs.1).trans
      hcutoff.le
  let D : Set (Vec d) := {x |
    Tendsto (fun r => goodLambdaCombinedEnergy f g eps x r) (𝓝[>] 0)
      (𝓝 (Real.sqrt (‖f x‖ ^ 2 + (eps⁻¹) ^ (2 : ℕ) * ‖g x‖ ^ 2)))}
  have hDae : ∀ᵐ x ∂volume, x ∈ D := by
    simpa only [D, Set.mem_ofPred_eq] using
      (ae_tendsto_goodLambdaCombinedEnergy_nhdsGT f g eps hf_int hg_int)
  have hDnull : volume Dᶜ = 0 := by
    simpa only [D, Set.mem_ofPred_eq, Set.compl_ofPred] using (ae_iff.mp hDae)
  have hpoint : ∀ x ∈ target ∩ D,
      level < Real.sqrt (‖f x‖ ^ 2 + (eps⁻¹) ^ (2 : ℕ) * ‖g x‖ ^ 2) := by
    intro x hx
    have htail : M * level < ‖f x‖ := htarget x hx.1
    have hlevel_le_tail : level ≤ M * level := by
      nlinarith
    have hlevel_norm : level < ‖f x‖ := hlevel_le_tail.trans_lt htail
    calc
      level < ‖f x‖ := hlevel_norm
      _ = Real.sqrt (‖f x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖f x‖ ^ 2 + (eps⁻¹) ^ (2 : ℕ) * ‖g x‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact le_add_of_nonneg_right (mul_nonneg heps_weight_pos.le (sq_nonneg _))
  have hstop : ∀ x ∈ target ∩ D, ∃ r, 0 < r ∧ r ≤ rho ∧
      goodLambdaCombinedEnergy f g eps x r = level ∧
      ∀ s ∈ Icc r R, goodLambdaCombinedEnergy f g eps x s ≤ level := by
    intro x hx
    exact exists_stoppingRadius_goodLambdaCombinedEnergy_of_largeScaleBound
      f g eps hf_int hg_int x hrho hx.2 (hpoint x hx)
      (hlarge x rho ⟨le_rfl, hrhoR⟩) (hlarge x)
  classical
  let radius : Vec d → ℝ := fun x =>
    if hx : x ∈ target ∩ D then Classical.choose (hstop x hx) else 0
  refine ⟨D, radius, hDnull, ?_⟩
  intro x hx
  have hchosen := Classical.choose_spec (hstop x hx)
  rw [show radius x = Classical.choose (hstop x hx) by
    simp only [radius, dif_pos hx]]
  simpa only [R, rho] using hchosen

end CubeCalderonZygmund

end

end Homogenization
