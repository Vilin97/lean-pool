/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.ZeroMass
import LeanPool.Zeta5Irrational.Kernel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Lemma 6.2 for the logarithmic kernel

Passing to the limit `a → 0`, `b → ∞` in `energy_Ltr_nonpos` by dominated convergence.
The hypotheses are integrability of `log ‖γ k θ - γ l φ‖` on the torus and the a.e.
distinctness `γ k θ ≠ γ l φ`.
-/

public section

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace Zeta5Irrational

/-- The measure on `[0, 2π]`. -/
noncomputable abbrev μcirc : Measure ℝ :=
  volume.restrict (Ioc 0 (2 * π))

variable {ι : Type*}

/-- `pairInt` as an integral over the product measure. -/
lemma pairInt_eq_prod (γ : ι → ℝ → ℂ) (f : ℂ → ℂ → ℝ) (k l : ι)
    (hf : Integrable (fun p : ℝ × ℝ => f (γ k p.1) (γ l p.2)) (μcirc.prod μcirc)) :
    pairInt γ f k l = ∫ p : ℝ × ℝ, f (γ k p.1) (γ l p.2) ∂(μcirc.prod μcirc) := by
  unfold pairInt
  rw [integral_prod _ hf, intervalIntegral.integral_of_le (by positivity)]
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]

lemma integrable_of_continuous_torus {F : ℝ × ℝ → ℝ} (hF : Continuous F) :
    Integrable F (μcirc.prod μcirc) := by
  rw [Measure.prod_restrict]
  refine IntegrableOn.mono_set ?_ (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hF.continuousOn

/-- Limit of the truncated pair integrals. -/
lemma tendsto_pairInt_Ltr {γ : ι → ℝ → ℂ} (hγ : ∀ k, Continuous (γ k)) (k l : ι)
    (hint : Integrable (fun p : ℝ × ℝ => Real.log ‖γ k p.1 - γ l p.2‖) (μcirc.prod μcirc))
    (hae : ∀ᵐ p ∂(μcirc.prod μcirc), γ k p.1 ≠ γ l p.2) :
    Tendsto
      (fun n : ℕ => pairInt γ (fun z w => Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ‖z - w‖) k l)
      atTop (𝓝 (pairInt γ (fun z w => Real.log ‖z - w‖) k l)) := by
  have hn : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hn' : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := fun n => by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hcont :
    ∀ n : ℕ,
      Continuous fun p : ℝ × ℝ => Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ‖γ k p.1 - γ l p.2‖ :=
    fun n => (continuous_Ltr (hn n) (hn' n)).comp (by fun_prop)
  rw [pairInt_eq_prod γ _ k l hint]
  have e :
    ∀ n : ℕ,
      pairInt γ (fun z w => Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ‖z - w‖) k l =
        ∫ p : ℝ × ℝ,
          Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ‖γ k p.1 - γ l p.2‖ ∂(μcirc.prod μcirc) :=
    fun n =>
    pairInt_eq_prod γ (fun z w => Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ‖z - w‖) k l
      (integrable_of_continuous_torus (hcont n))
  simp_rw [e]
  refine
    tendsto_integral_of_dominated_convergence (fun p => |Real.log ‖γ k p.1 - γ l p.2‖|)
      (fun n => (hcont n).aestronglyMeasurable) hint.abs ?_ ?_
  · intro n
    filter_upwards [hae] with p hp
    rw [Real.norm_eq_abs]
    exact abs_Ltr_le (hn n) (hn' n) (norm_pos_iff.mpr (sub_ne_zero.mpr hp))
  · filter_upwards [hae] with p hp
    exact tendsto_Ltr (norm_pos_iff.mpr (sub_ne_zero.mpr hp))

/-- **Lemma 6.2** (zero-mass logarithmic energy) for explicit atoms. -/
theorem energy_log_nonpos [Fintype ι] {s : ι → ℝ} {γ : ι → ℝ → ℂ} (hγ : ∀ k, Continuous (γ k))
    {R : ℝ} (hR : ∀ k θ, ‖γ k θ‖ ≤ R) (hmass : ∑ k, s k = 0)
    (hint : ∀ k l, Integrable (fun p : ℝ × ℝ => Real.log ‖γ k p.1 - γ l p.2‖) (μcirc.prod μcirc))
    (hae : ∀ k l, ∀ᵐ p ∂(μcirc.prod μcirc), γ k p.1 ≠ γ l p.2) :
    energy s γ (fun z w => Real.log ‖z - w‖) ≤ 0 := by
  have hn : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hn' : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := fun n => by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hle : ∀ n : ℕ, energy s γ (fun z w => Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ‖z - w‖) ≤ 0 :=
    fun n => energy_Ltr_nonpos hγ hR hmass (hn n) (hn' n)
  have hlim :
    Tendsto (fun n : ℕ => energy s γ (fun z w => Ltr (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ‖z - w‖))
      atTop (𝓝 (energy s γ (fun z w => Real.log ‖z - w‖))) := by
    unfold energy
    refine tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ => ?_
    exact (tendsto_pairInt_Ltr hγ k l (hint k l) (hae k l)).const_mul _
  exact le_of_tendsto' hlim hle

end Zeta5Irrational
