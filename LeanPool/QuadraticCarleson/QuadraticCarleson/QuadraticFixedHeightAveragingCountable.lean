/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingAllHeights

/-!
# Countable fixed-height maximal quadratic decay

Finite exhaustion and monotone convergence extend the concrete estimate to
every sequence of nonzero real modulation parameters. No continuity or
separability assertion about the discontinuous scale selector is used here.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson

noncomputable def countableConvolutionMaximal
    (κ : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ i : ℕ, ‖∫ t, κ i (x - t) * f t‖ₑ

theorem countableConvolutionMaximal_eq_iSup_finite
    (κ : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ) :
    countableConvolutionMaximal κ f x =
      ⨆ n : ℕ, finiteConvolutionMaximal (fun i : Fin (n + 1) ↦ κ i.val) f x := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact le_iSup_of_le i (le_iSup (fun j : Fin (i + 1) ↦
      ‖∫ t, κ j.val (x - t) * f t‖ₑ) ⟨i, Nat.lt_succ_self i⟩)
  · apply iSup_le
    intro n
    apply iSup_le
    intro i
    exact le_iSup (fun j : ℕ ↦ ‖∫ t, κ j (x - t) * f t‖ₑ) i.val

theorem monotone_finiteConvolutionMaximal_initial
    (κ : ℕ → ℝ → ℂ) (f : ℝ → ℂ) :
    Monotone (fun n : ℕ ↦ finiteConvolutionMaximal
      (fun i : Fin (n + 1) ↦ κ i.val) f) := by
  intro m n hmn x
  apply iSup_le
  intro i
  exact le_iSup (fun j : Fin (n + 1) ↦ ‖∫ t, κ j.val (x - t) * f t‖ₑ)
    ⟨i.val, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hmn)⟩

theorem countableConvolutionMaximal_congr_ae (κ : ℕ → ℝ → ℂ)
    {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g) :
    countableConvolutionMaximal κ f = countableConvolutionMaximal κ g := by
  funext x
  simp_rw [countableConvolutionMaximal_eq_iSup_finite,
    finiteConvolutionMaximal_congr_ae _ hfg]

theorem measurable_countableConvolutionMaximal
    (κ : ℕ → ℝ → ℂ) (hκ : ∀ i, Measurable (κ i))
    {f : ℝ → ℂ} (hfm : Measurable f) :
    Measurable (countableConvolutionMaximal κ f) := by
  have heq : countableConvolutionMaximal κ f =
      fun x ↦ ⨆ n : ℕ, finiteConvolutionMaximal
        (fun i : Fin (n + 1) ↦ κ i.val) f x := by
    funext x
    exact countableConvolutionMaximal_eq_iSup_finite κ f x
  rw [heq]
  exact Measurable.iSup (fun n ↦
    measurable_finiteConvolutionMaximal _ (fun i ↦ hκ i.val) hfm)

/-- The actual integral action is insensitive to changing its input on a null
set, so even an `L²` input with no pointwise measurability assumption produces
a measurable countable maximal function. -/
theorem measurable_countableConvolutionMaximal_of_memLp
    (κ : ℕ → ℝ → ℂ) (hκ : ∀ i, Measurable (κ i))
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    Measurable (countableConvolutionMaximal κ f) := by
  rw [countableConvolutionMaximal_congr_ae κ hf.aestronglyMeasurable.ae_eq_mk]
  exact measurable_countableConvolutionMaximal κ hκ
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable

theorem countableConvolutionMaximal_sq_lintegral_le_of_finite
    (κ : ℕ → ℝ → ℂ) (hκ : ∀ i, Measurable (κ i)) (C : ℝ≥0∞)
    (hbound : ∀ n : ℕ, ∀ g : ℝ → ℂ, MemLp g 2 →
      (∫⁻ x, finiteConvolutionMaximal (fun i : Fin (n + 1) ↦ κ i.val) g x ^ 2) ≤
        C * ∫⁻ x, ‖g x‖ₑ ^ 2)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, countableConvolutionMaximal κ f x ^ 2) ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  let g := hf.aestronglyMeasurable.mk f
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g 2 := hf.ae_eq hfg
  have hint : (∫⁻ x, ‖g x‖ₑ ^ 2) = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
    apply lintegral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  rw [countableConvolutionMaximal_congr_ae κ hfg, ← hint]
  simp_rw [countableConvolutionMaximal_eq_iSup_finite, ENNReal.iSup_pow]
  rw [lintegral_iSup]
  · exact iSup_le (fun n ↦ hbound n g hg)
  · intro n
    exact (measurable_finiteConvolutionMaximal _ (fun i ↦ hκ i.val) hgm).pow_const 2
  · intro m n hmn x
    exact pow_le_pow_left₀ bot_le (monotone_finiteConvolutionMaximal_initial κ g hmn x) 2

/-- The actual full signed fixed-height quadratic estimate for an arbitrary
countable sequence of nonzero real modulation parameters, at every height. -/
theorem countable_fixedHeightQuadraticKernel_maximal_sq_decay_all_heights
    (height : ℕ) (lam : ℕ → ℝ) (hlam : ∀ i, lam i ≠ 0)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, countableConvolutionMaximal
      (fun i ↦ fixedHeightQuadraticKernel (lam i) height (hlam i)) f x ^ 2) ≤
      ENNReal.ofReal (70996725888 * positiveDyadicAmplitudeBound ^ 2 /
        (2 : ℝ) ^ ((height - 1) / 5)) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  exact countableConvolutionMaximal_sq_lintegral_le_of_finite _
    (fun i ↦ (continuous_fixedHeightQuadraticKernel _ _ _).measurable) _
    (fun n g hg ↦ finite_fixedHeightQuadraticKernel_maximal_sq_decay_all_heights
      n height (fun i ↦ lam i.val) (fun i ↦ hlam i.val) hg) hf

end QuadraticCarleson
