/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FiniteMetricEnergy
public import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-! Uniform convergence of actual finite metric energies along continuous Hilbert-space paths. -/

@[expose] public section


noncomputable section

namespace EulerMetricPathConvergence

open Set EulerFiniteMetricEnergy

open scoped Topology

variable {I H : Type*} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A finite family metric norm is continuous jointly in its actual bounded metric and field. -/
theorem familyMetricNorm_continuous :
    Continuous (fun p : (H →L[ℝ] H) × (I → H) => familyMetricNorm p.1 p.2) := by
  unfold familyMetricNorm familyEnergy
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro i _
  exact (continuous_fst.clm_apply ((continuous_apply i).comp continuous_snd)).inner
    ((continuous_apply i).comp continuous_snd)

/-- The actual finite-family metric norm along a continuous time path. -/
def metricPath (T : ℝ) (K : C(Icc (0 : ℝ) T, H →L[ℝ] H))
    (u : C(Icc (0 : ℝ) T, I → H)) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t => familyMetricNorm (K t) (u t),
    familyMetricNorm_continuous.comp (K.continuous.prodMk u.continuous)⟩

/-- The actual metric-root path depends continuously on the field path in the uniform topology. -/
theorem metricPath_continuous (T : ℝ) (K : C(Icc (0 : ℝ) T, H →L[ℝ] H)) :
    Continuous (fun u : C(Icc (0 : ℝ) T, I → H) => metricPath T K u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact familyMetricNorm_continuous.comp
    ((K.continuous.comp continuous_snd).prodMk continuous_eval)

/-- Strong uniform field convergence gives uniform convergence of the actual square-root metric
energy, including zeros. -/
theorem metricPath_tendsto (T : ℝ) (K : C(Icc (0 : ℝ) T, H →L[ℝ] H))
    (u : ℕ → C(Icc (0 : ℝ) T, I → H)) (v : C(Icc (0 : ℝ) T, I → H))
    (hu : Filter.Tendsto u Filter.atTop (𝓝 v)) :
    Filter.Tendsto (fun n => metricPath T K (u n)) Filter.atTop (𝓝 (metricPath T K v)) :=
  (metricPath_continuous T K).continuousAt.tendsto.comp hu

/-- A finite weighted sum of actual metric-root paths. -/
def weightedMetricPath {A : Type*} [Fintype A] (T : ℝ)
    (w : A → C(Icc (0 : ℝ) T, ℝ)) (K : C(Icc (0 : ℝ) T, H →L[ℝ] H))
    (u : A → C(Icc (0 : ℝ) T, I → H)) : C(Icc (0 : ℝ) T, ℝ) :=
  ∑ i, w i * metricPath T K (u i)

/-- A bundled finite metric path evaluates to its literal weighted metric-root sum. -/
theorem weightedMetricPath_apply {A : Type*} [Fintype A] (T : ℝ)
    (w : A → C(Icc (0 : ℝ) T, ℝ)) (K : C(Icc (0 : ℝ) T, H →L[ℝ] H))
    (u : A → C(Icc (0 : ℝ) T, I → H)) (t : Icc (0 : ℝ) T) :
    weightedMetricPath T w K u t = ∑ i, w i t * familyMetricNorm (K t) (u i t) := by
  simp only [weightedMetricPath, ContinuousMap.sum_apply, ContinuousMap.mul_apply, metricPath,
      ContinuousMap.coe_mk]

/-- Every finite Gevrey metric sum passes uniformly through actual strong field approximations. -/
theorem weightedMetricPath_tendsto {A : Type*} [Fintype A] (T : ℝ)
    (w : A → C(Icc (0 : ℝ) T, ℝ)) (K : C(Icc (0 : ℝ) T, H →L[ℝ] H))
    (u : ℕ → A → C(Icc (0 : ℝ) T, I → H)) (v : A → C(Icc (0 : ℝ) T, I → H))
    (hu : ∀ i, Filter.Tendsto (fun n => u n i) Filter.atTop (𝓝 (v i))) :
    Filter.Tendsto (fun n => weightedMetricPath T w K (u n)) Filter.atTop
      (𝓝 (weightedMetricPath T w K v)) := by
  exact tendsto_finsetSum Finset.univ (fun i _ =>
    (metricPath_tendsto T K (fun n => u n i) (v i) (hu i)).const_mul (w i))

end EulerMetricPathConvergence
