/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.RegularizedWordTime
public import LeanPool.NavierStokesAndEuler.Euler.TimePathApply
public import LeanPool.NavierStokesAndEuler.Euler.TransportL2Time

@[expose] public section

/-! Concrete forcing for the regularized word PDE and its strong energy-order time limit. -/

noncomputable section

namespace EulerRegularizedForcingWord

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerMildTopWord EulerRegularizedWordEquation EulerRegularizedWordTime EulerRegularizedTopBlocks
  EulerMetricHeatEnergy EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual transport-pressure forcing in the regularized energy-word PDE. -/
def forcingWordPath {q m : ℕ} (hm : m ≤ q+1) (n : ℕ) (w : Fin m → Fin 4) (T : ℝ)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q)) : C(Icc (0 : ℝ) T, LiftL2 period) :=
  sourceWordPath period hm n w T f +
    timePathApply T A ((truncateOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (regularizedWordPath period hm n w T u)) + timePathApply T G (sourceWordPath period hm n w T
        p)

/-- The regularized forcing has its literal source-plus-transport-plus-pressure value. -/
theorem forcingWordPath_apply {q m : ℕ} (hm : m ≤ q+1) (n : ℕ) (w : Fin m → Fin 4) (T : ℝ)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : Icc (0 : ℝ) T) :
    forcingWordPath period hm n w T A G u f p t =
      value period (regularizedWordBlock period hm n w (f t)) +
      A t (truncateOperator period 1 (regularizedWordPath period hm n w T u t)) +
      G t (value period (regularizedWordBlock period hm n w (p t))) := rfl

/-- The source-plus-transport-plus-pressure definition gives the exact regularized word equation. -/
theorem forcingWordPath_equation {q m : ℕ} (hm : m ≤ q+1) (n : ℕ) (w : Fin m → Fin 4) (T ν : ℝ)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : Icc (0 : ℝ) T) :
    (ν • jetLaplacian period (toJet period (regularizedWordPath period hm n w T u t)) +
      value period (regularizedWordBlock period hm n w (f t))) +
      A t (truncateOperator period 1 (regularizedWordPath period hm n w T u t)) +
      G t (value period (regularizedWordBlock period hm n w (p t))) =
    forcingWordPath period hm n w T A G u f p t +
      ν • jetLaplacian period (toJet period (regularizedWordPath period hm n w T u t)) := by
  rw [forcingWordPath_apply]
  abel

/-- The full energy-order regularized word has the actual clamped-path heat derivative at each interior time. -/
theorem regularized_word_hasDerivAt_clamped {q m : ℕ} (hm : m ≤ q+1) (n : ℕ) (w : Fin m → Fin 4)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q+1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r)))
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT (regularizedWordPath period hm n w T u) r))
      (ν • jetLaplacian period (toJet period (extendPath T hT (regularizedWordPath period hm n w T
        u) t)) +
        extendPath T hT (sourceWordPath period hm n w T f) t) t := by
  have h := regularized_word_hasDerivAt period hm n w ν hν T hT u₀ f u hsol t ht
  change HasDerivAt _ (ν • jetLaplacian period (toJet period
    (regularizedWordPath period hm n w T u (projIcc 0 T hT t))) +
      value period (regularizedWordBlock period hm n w (f (projIcc 0 T hT t)))) t
  rw [projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩]
  exact h

/-- The literal forcing obtained from full energy-order source, state, and pressure time fields. -/
def forcingWordTime {q m : ℕ} (hm : m ≤ q+1) (w : Fin m → Fin 4) (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (U : TimeLp T (SobolevSpace period (2+q))) (F P : TimeLp T (SobolevSpace period (q+1))) :
    TimeLp T (LiftL2 period) :=
  (wordOperator period (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : SobolevWord (q+1))).compLpL 2 (timeMeasure
    T) F +
    timeMultiplier T hT A ((boundedWordBlock period 1 m (by omega : 1+m ≤ 2+q) w).compLpL 2
      (timeMeasure T) U) +
    timeMultiplier T hT G ((wordOperator period (⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ : SobolevWord
      (q+1))).compLpL 2 (timeMeasure T) P)

/-- The concrete regularized PDE forcing converges strongly at the full energy order by maximal regularity and the actual higher-order source/pressure representatives. -/
theorem forcingWordPath_time_tendsto {q m : ℕ} (hm : m ≤ q+1) (w : Fin m → Fin 4)
    (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (U : TimeLp T (SobolevSpace period (2+q))) (F P : TimeLp T (SobolevSpace period (q+1)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop
      (𝓝 U))
    (hF : (fun t => truncateOperator period q (F t)) =ᵐ[timeMeasure T] extendPath T hT f)
    (hP : (fun t => truncateOperator period q (P t)) =ᵐ[timeMeasure T] extendPath T hT p) :
    Filter.Tendsto (fun n => pathLp T hT (forcingWordPath period hm n w T A G u f p)) Filter.atTop
      (𝓝 (forcingWordTime period hm w T hT A G U F P)) := by
  have hs := sourceWordPath_time_tendsto period hm w T hT f F hF
  have ht := timePathApply_tendsto T hT A _ _ (regularizedWordPath_first_tendsto period hm w T hT u
    U hU)
  have hp := timePathApply_tendsto T hT G _ _ (sourceWordPath_time_tendsto period hm w T hT p P hP)
  have h := (hs.add ht).add hp
  simpa only [forcingWordPath, pathLp_add, forcingWordTime] using h

end EulerRegularizedForcingWord
