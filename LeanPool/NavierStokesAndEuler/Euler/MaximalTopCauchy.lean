/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.RegularizedTopBlocks
public import LeanPool.NavierStokesAndEuler.Euler.HeatMaximalCauchy
import LeanPool.NavierStokesAndEuler.Euler.HeatMaximalRegularity
import LeanPool.NavierStokesAndEuler.Euler.SobolevTopBlocks
import LeanPool.NavierStokesAndEuler.Euler.TopBlockCauchy
import Mathlib.Algebra.Order.Star.Real

/-! Actual maximal regularity at arbitrary finite Sobolev order via finitely many top derivative
equations. -/

@[expose] public section


noncomputable section

namespace EulerMaximalTopCauchy

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerTimeLp EulerVolterraConvolution EulerMildWordEquation EulerMildTopWord
  EulerRegularizedMildEquation EulerRegularizedTopBlocks EulerHeatMaximalRegularity
  EulerTopBlockTimeNorm EulerSobolevTopBlocks EulerSobolevWordBlocks EulerHeatMaximalCauchy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The top block norm estimate in the original q+1 indexing used by actual mild solutions. -/
theorem top_blocks_norm_sq_original (q : ℕ) (u : SobolevSpace period (2 + q)) :
    ‖u‖^2 ≤ ‖restrictOperator period (by omega : q+1 ≤ 2+q) u‖^2 +
      ∑ w : Fin q → Fin 4, ‖wordBlock period 2 q w u‖^2 := by
  have h := top_blocks_norm_sq period q u
  have hr := restrictOperator_bound period (by omega : 1+q ≤ q+1)
    (restrictOperator period (by omega : q+1 ≤ 2+q) u)
  rw [restrictOperator_comp] at hr
  nlinarith [norm_nonneg (restrictOperator period (by omega : 1+q ≤ 2+q) u),
    norm_nonneg (restrictOperator period (by omega : q+1 ≤ 2+q) u)]

/-- Every actual top-word regularization is strongly Cauchy in time with its two full extra spatial
derivatives. -/
theorem maximalApproximation_word_cauchy {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r)))
    (w : Fin q → Fin 4) :
    CauchySeq (fun n => pathLp T hT ((wordBlock period 2 q w).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (maximalApproximation period q T n u))) := by
  have h := regularized_mild_cauchy period T hT ν hν
    (boundedWordBlock period 1 q (by omega) w u₀)
    (mapPath period T (boundedWordBlock period 0 q (by omega) w) f)
    (mapPath period T (boundedWordBlock period 1 q (by omega) w) u)
    (top_word_mild period ν hν T hT u₀ f u hsol w)
  simpa only [maximalApproximation_word, higherTime] using h

/-- The genuine full H^(q+2) heat regularizations form a strong Bochner Cauchy sequence, with no
assumed derivative bound. -/
theorem maximalApproximation_cauchy {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r))) :
    CauchySeq (fun n => pathLp T hT (maximalApproximation period q T n u)) := by
  apply cauchy_pathLp_of_blocks (restrictOperator period (by omega : q+1 ≤ 2+q))
    (fun w : Fin q → Fin 4 => wordBlock period 2 q w) (top_blocks_norm_sq_original period q)
    T hT (fun n => maximalApproximation period q T n u)
  · exact (pathLp_tendsto T hT _ u (maximalApproximation_low_tendsto period q T u)).cauchySeq
  · exact maximalApproximation_word_cauchy period ν hν T hT u₀ f u hsol

end EulerMaximalTopCauchy
