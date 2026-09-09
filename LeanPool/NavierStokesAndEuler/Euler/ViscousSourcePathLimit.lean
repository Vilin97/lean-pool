/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.QuadraticSourceLimit
public import LeanPool.NavierStokesAndEuler.Euler.ViscosityDefect
public import LeanPool.NavierStokesAndEuler.Euler.ViscosityCauchy
import LeanPool.NavierStokesAndEuler.Euler.SobolevPathLimits

/-! Strong convergence of the actual nonlinear and viscous right-hand sides. -/

@[expose] public section


noncomputable section

namespace EulerViscousSourcePathLimit

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerQuadraticSource EulerQuadraticSourceLimit EulerSobolevPathLimits
  EulerViscosityDefect EulerViscosityCauchy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited normed group on each actual Sobolev value space. -/
local instance sourceLimitGroup (s : ℕ) : NormedAddCommGroup (SobolevSpace period s) :=
    inferInstance

/-- The inherited real normed space on each actual Sobolev value space. -/
local instance sourceLimitSpace (s : ℕ) : NormedSpace ℝ (SobolevSpace period s) := inferInstance

/-- The literal continuous viscous right-hand side with the source evaluated one Sobolev order
lower. -/
def viscousSourcePath {q : ℕ} (hq : 2 ≤ (q + 1) + 1) (ν T : ℝ)
    (C : Coefficients (Icc (0 : ℝ) T) (SobolevSpace period (q + 1)) (SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period ((q + 1) + 1))) :
    C(Icc (0 : ℝ) T,LiftL2 period) :=
  viscousDefect period hq ν T u + valuePath period T
    (sourcePath C ((truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u))

/-- Uniformly bounded strongly convergent states have convergent actual nonlinear-viscous right-hand
sides. -/
theorem viscousSourcePath_tendsto {q : ℕ} (hq : 2 ≤ (q + 1) + 1) (T : ℝ)
    (C : Coefficients (Icc (0 : ℝ) T) (SobolevSpace period (q + 1)) (SobolevSpace period q))
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period ((q + 1) + 1)))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (M : ℝ) (huM : ∀ n, ‖u n‖ ≤ M)
    (hconv : Filter.Tendsto (fun n => (truncateOperator period (q + 1)).compLeftContinuous ℝ (Icc (0
        : ℝ) T) (u n))
      Filter.atTop (𝓝 e)) :
    Filter.Tendsto (fun n => viscousSourcePath period hq (viscositySequence n) T C (u n))
      Filter.atTop (𝓝 (valuePath period T (sourcePath C e))) := by
  let v := fun n => (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n)
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (huM 0)
  have hvM : ∀ n, ‖v n‖ ≤ M := fun n =>
    (restrict_path_norm period (by omega : q+1 ≤ (q+1)+1) T (u n)).trans (huM n)
  have heM : ‖e‖ ≤ M := limit_norm_bound period T M v e hconv hvM
  have hg := sourcePath_tendsto C M hM v e hvM heM hconv
  have hgval := ((valueOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T)).continuous.tendsto
    (sourcePath C e) |>.comp hg
  have hv := viscousDefect_tendsto_zero period hq T M u huM
  simpa only [viscousSourcePath,v,valuePath,Function.comp_def,zero_add] using hv.add hgval

/-- Strong convergence after restriction preserves the underlying continuous L² path. -/
theorem valuePath_tendsto_of_truncate {q : ℕ} (T : ℝ)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (hconv : Filter.Tendsto (fun n => (truncateOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ)
        T) (u n))
      Filter.atTop (𝓝 e)) :
    Filter.Tendsto (fun n => valuePath period T (u n)) Filter.atTop (𝓝 (valuePath period T e)) :=
  ((valueOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T)).continuous.tendsto e |>.comp hconv

end EulerViscousSourcePathLimit
