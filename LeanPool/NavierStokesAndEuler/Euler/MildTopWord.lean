/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MildWordEquation

@[expose] public section

/-! Actual highest derivative words preserve the gained-derivative heat mild formula. -/

noncomputable section

namespace EulerMildTopWord

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevHeatGenerator EulerVolterraConvolution EulerDuhamelDifferentiation
  EulerMildEquationBridge EulerMildWordEquation EulerSobolevWordBlocks
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The gained-kernel integral has exactly the ordinary Duhamel value after actual truncation. -/
theorem truncate_mild_integral {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : Icc (0 : ℝ) T) :
    truncateOperator period q
      (∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r))) =
      duhamel period ν T hT f t.val := by
  have h := truncate_heatConvolution period ν hν T hT f t
  rw [convolution_eq_interval T hT (heatKernel period q ν hν) (parabolicKernelBound ν)
    (heatKernel_joint_continuous period q ν hν) (parabolicKernelBound_integrable ν T hT)
    (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
    (fun r hr y => heatKernel_bound period q ν hν r hr.1 y) f t] at h
  exact h

/-- An actual continuous H¹ path is the gained-kernel mild solution as soon as its genuine L² truncation obeys Duhamel. -/
theorem mild_of_truncated_formula (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T, truncateOperator period 0 (u t) =
      heatFlow period 0 ν t.val (truncateOperator period 0 u₀) + duhamel period ν T hT f t.val) :
    ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r)) := by
  intro t
  apply value_injective period
  have h := hsol t
  change truncateOperator period 0 (u t) = heatOperator period 0 (2*ν*t.val).toNNReal
    (truncateOperator period 0 u₀) + _ at h
  rw [← truncate_heatOperator, ← truncate_mild_integral period ν hν T hT f t, ← map_add] at h
  exact congrArg (fun x : SobolevSpace period 0 => value period x) h

/-- A genuine bounded derivative block with an arbitrary available Sobolev margin. -/
def boundedWordBlock (p n : ℕ) {q : ℕ} (h : p+n ≤ q) (w : Fin n → Fin 4) :
    SobolevSpace period q →L[ℝ] SobolevSpace period p :=
  (wordBlock period p n w).comp (restrictOperator period h)

/-- A bounded block has the exact underlying derivative word. -/
theorem boundedWordBlock_value (p n : ℕ) {q : ℕ} (h : p+n ≤ q) (w : Fin n → Fin 4)
    (u : SobolevSpace period q) :
    value period (boundedWordBlock period p n h w u) = word period u (by omega : n ≤ q) w := by
  change value period (wordBlock period p n w (restrictOperator period h u)) = _
  rw [wordBlock_value]
  rfl

/-- Every bounded actual word block commutes with the genuine heat semigroup. -/
theorem boundedWordBlock_heat (p n : ℕ) {q : ℕ} (h : p+n ≤ q) (w : Fin n → Fin 4)
    (v : ℝ≥0) (u : SobolevSpace period q) :
    boundedWordBlock period p n h w (heatOperator period q v u) =
      heatOperator period p v (boundedWordBlock period p n h w u) := by
  apply value_injective period
  rw [boundedWordBlock_value, heatOperator_value, boundedWordBlock_value]
  rfl

/-- Forgetting the last output derivative of a word block agrees with restricting the input. -/
theorem boundedWordBlock_truncate (q : ℕ) (w : Fin q → Fin 4) (u : SobolevSpace period (q+1)) :
    truncateOperator period 0 (boundedWordBlock period 1 q (by omega) w u) =
      boundedWordBlock period 0 q (by omega) w (truncateOperator period q u) := by
  apply value_injective period
  rw [value_truncateOperator, boundedWordBlock_value, boundedWordBlock_value]
  rfl

/-- The actual gained-derivative formula implies its ordinary lower-order form for a continuous source. -/
theorem truncated_formula {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q+1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r)))
    (t : Icc (0 : ℝ) T) :
    truncateOperator period q (u t) = heatFlow period q ν t.val (truncateOperator period q u₀) +
      duhamel period ν T hT f t.val := by
  rw [hsol t, map_add, truncate_heatOperator, truncate_mild_integral]
  rfl

/-- Actual highest derivative blocks satisfy the lower-order Duhamel identity. -/
theorem top_word_truncated {q : ℕ} (ν T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q+1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (hsol : ∀ t : Icc (0 : ℝ) T, truncateOperator period q (u t) =
      heatFlow period q ν t.val (truncateOperator period q u₀) + duhamel period ν T hT f t.val)
    (w : Fin q → Fin 4) (t : Icc (0 : ℝ) T) :
    truncateOperator period 0 (boundedWordBlock period 1 q (by omega) w (u t)) =
      heatFlow period 0 ν t.val (truncateOperator period 0 (boundedWordBlock period 1 q (by omega)
        w u₀)) +
      duhamel period ν T hT (mapPath period T (boundedWordBlock period 0 q (by omega) w) f) t.val
        := by
  let B : SobolevSpace period q →L[ℝ] SobolevSpace period 0 := boundedWordBlock period 0 q (by
    omega) w
  have hh := congrArg B (hsol t)
  have hadd := map_add B (heatFlow period q ν t.val (truncateOperator period q u₀)) (duhamel period
    ν T hT f t.val)
  have hheat := boundedWordBlock_heat period 0 q (by omega) w (2*ν*t.val).toNNReal
    (truncateOperator period q u₀)
  have hduh := map_duhamel period B (boundedWordBlock_heat period 0 q (by omega) w) ν T hT f t.val
  rw [hadd, hduh] at hh
  change B (truncateOperator period q (u t)) = B (heatOperator period q (2*ν*t.val).toNNReal
    (truncateOperator period q u₀)) + _ at hh
  rw [hheat] at hh
  rw [boundedWordBlock_truncate, boundedWordBlock_truncate]
  exact hh

/-- Every highest-order derivative word of an actual H^(q+1) mild solution is itself an actual H¹ mild solution with its differentiated L² source. -/
theorem top_word_mild {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q+1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r)))
    (w : Fin q → Fin 4) :
    ∀ t : Icc (0 : ℝ) T,
      boundedWordBlock period 1 q (by omega) w (u t) =
        heatOperator period 1 (2*ν*t.val).toNNReal (boundedWordBlock period 1 q (by omega) w u₀) +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r
          (extendPath T hT (mapPath period T (boundedWordBlock period 0 q (by omega) w) f)
            (t.val-r)) := by
  exact mild_of_truncated_formula period ν hν T hT
    (boundedWordBlock period 1 q (by omega) w u₀)
    (mapPath period T (boundedWordBlock period 0 q (by omega) w) f)
    (mapPath period T (boundedWordBlock period 1 q (by omega) w) u)
    (top_word_truncated period ν T hT u₀ f u (truncated_formula period ν hν T hT u₀ f u hsol) w)

end EulerMildTopWord
