/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.HeatRegularizedPaths
public import LeanPool.NavierStokesAndEuler.Euler.SobolevLaplacian

/-! Genuine heat regularizations of the constructed mild solution satisfy the differentiated heat
equation. -/

section

/-! Exact heat commutation with the genuine Sobolev derivatives and Laplacian. -/

@[expose] public section

noncomputable section

namespace EulerSobolevLaplacian

open EulerCylinderSobolevSpace EulerSobolevHeat
open scoped NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Actual heat commutes with every strong coordinate derivative between consecutive Sobolev levels.
-/
theorem derivative_heat {q : ℕ} (i : Fin 4) (v : ℝ≥0) (u : SobolevSpace period (q + 1)) :
    derivativeOperator period q i (heatOperator period (q+1) v u) =
      heatOperator period q v (derivativeOperator period q i u) := by
  apply Subtype.ext
  funext w
  rfl

/-- Actual heat commutes with the genuine Laplacian between Sobolev levels. -/
theorem laplacian_heat {q : ℕ} (v : ℝ≥0) (u : SobolevSpace period (q + 2)) :
    laplacianOperator period q (heatOperator period (q+2) v u) =
      heatOperator period q v (laplacianOperator period q u) := by
  rw [laplacianOperator_apply, laplacianOperator_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [derivative_heat, derivative_heat]

end EulerSobolevLaplacian

end
end

end

@[expose] public section

noncomputable section

namespace EulerRegularizedMildEquation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevHeatGenerator EulerSobolevLaplacian EulerHeatRegularizedPaths
  EulerMildWordEquation EulerVolterraConvolution
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The actual three-derivative heat regularization of an H¹ mild state. -/
def regularizedState (T : ℝ) (n : ℕ) (u : C(Icc (0 : ℝ) T, SobolevSpace period 1)) :
    C(Icc (0 : ℝ) T, SobolevSpace period 3) :=
  mapPath period T ((heatRegularizer period 0 n).comp (truncateOperator period 0)) u

/-- The same genuine heat regularization of the source, retained at the gradient-energy source
order. -/
def regularizedForcing (T : ℝ) (n : ℕ) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0)) :
    C(Icc (0 : ℝ) T, SobolevSpace period 1) :=
  mapPath period T ((restrictOperator period (by
      norm_num : 1 ≤ 3)).comp (heatRegularizer period 0 n)) f

/-- The original-order restriction of the regularized state is exactly the actual H¹ heat path. -/
theorem regularizedState_low_eq (T : ℝ) (n : ℕ) (u : C(Icc (0 : ℝ) T, SobolevSpace period 1)) :
    (restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (regularizedState period T n u) = pathHeat period 1 T (regularizerVariance n) u := by
  apply ContinuousMap.ext
  intro t
  apply value_injective period
  change value period (restrictOperator period (by norm_num : 1 ≤ 3)
    (heatRegularizer period 0 n (truncateOperator period 0 (u t)))) =
      value period (heatOperator period 1 (regularizerVariance n) (u t))
  rw [value_restrictOperator, heatRegularizer_value, value_truncateOperator, heatOperator_value]

/-- The regularized state converges uniformly in its original actual H¹ topology. -/
theorem regularizedState_low_tendsto (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period 1)) :
    Filter.Tendsto (fun n => (restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (regularizedState period T n u)) Filter.atTop (𝓝 u) := by
  have h := (pathHeat_continuous period T u).continuousAt.tendsto.comp regularizerVariance_tendsto
  have hzero : pathHeat period 1 T 0 u = u := by
    apply ContinuousMap.ext
    intro t
    exact heatOperator_zero period (u t)
  rw [hzero] at h
  simpa only [regularizedState_low_eq, Function.comp_def] using h

/-- The source's actual L² value is regularized by the same genuine heat operator. -/
theorem regularizedForcing_value_eq (T : ℝ) (n : ℕ) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0)) :
    (valueOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T) (regularizedForcing period T n f)
        =
      (valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ) T)
        (pathHeat period 0 T (regularizerVariance n) f) := by
  apply ContinuousMap.ext
  intro t
  change value period (restrictOperator period (by
      norm_num : 1 ≤ 3) (heatRegularizer period 0 n (f t))) =
    value period (heatOperator period 0 (regularizerVariance n) (f t))
  rw [value_restrictOperator, heatRegularizer_value, heatOperator_value]

/-- The regularized forcing converges uniformly in actual L², with no source derivative premise. -/
theorem regularizedForcing_value_tendsto (T : ℝ) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0)) :
    Filter.Tendsto (fun n => (valueOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (regularizedForcing period T n f)) Filter.atTop
      (𝓝 ((valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ) T) f)) := by
  have h := (pathHeat_continuous period T f).continuousAt.tendsto.comp regularizerVariance_tendsto
  have hzero : pathHeat period 0 T 0 f = f := by
    apply ContinuousMap.ext
    intro t
    exact heatOperator_zero period (f t)
  rw [hzero] at h
  have hv := ((valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ)
      T)).continuous.continuousAt.tendsto.comp h
  simpa only [regularizedForcing_value_eq, Function.comp_def] using hv

/-- The first derivative of the genuine regularizer, as a bounded heat-commuting block. -/
def regularizerFirst (n : ℕ) (i : Fin 4) : SobolevSpace period 0 →L[ℝ] SobolevSpace period 2 :=
  (derivativeOperator period 2 i).comp (heatRegularizer period 0 n)

/-- The regularized first-derivative block commutes with actual heat. -/
theorem regularizerFirst_heat (n : ℕ) (i : Fin 4) (v : ℝ≥0) (x : SobolevSpace period 0) :
    regularizerFirst period n i (heatOperator period 0 v x) =
      heatOperator period 2 v (regularizerFirst period n i x) := by
  change derivativeOperator period 2 i (heatRegularizer period 0 n (heatOperator period 0 v x)) = _
  rw [heatRegularizer_heat, derivative_heat]
  rfl

/-- The regularized first derivative has the exact commuting Laplacian value. -/
theorem regularizerFirst_laplacian (n : ℕ) (i : Fin 4) (x : SobolevSpace period 0) :
    laplacianEvaluation period 2 (by norm_num) (regularizerFirst period n i x) =
      value period (derivativeOperator period 0 i (laplacianOperator period 1 (heatRegularizer
          period 0 n x))) := by
  rw [← laplacianOperator_value]
  exact congrArg (value period) (laplacian_derivative period i (heatRegularizer period 0 n x))

/-- Restriction preserves the source's regularized first derivative exactly. -/
theorem regularizerFirst_source (n : ℕ) (i : Fin 4) (x : SobolevSpace period 0) :
    value period (regularizerFirst period n i x) =
      value period (derivativeOperator period 0 i
        (restrictOperator period (by norm_num : 1 ≤ 3) (heatRegularizer period 0 n x))) := rfl

/-- Actual derivative evaluation is linear in a scaled sum. -/
theorem value_derivative_smul_add (i : Fin 4) (ν : ℝ) (a b : SobolevSpace period 1) :
    value period (derivativeOperator period 0 i (ν • a+b)) =
      ν • value period (derivativeOperator period 0 i a) + value period (derivativeOperator period
          0 i b) := by
  let L := (valueOperator period 0).comp (derivativeOperator period 0 i)
  change L (ν • a+b) = ν • L a + L b
  rw [map_add, map_smul]

/-- The exact algebraic form of the regularized first-word heat right-hand side. -/
theorem regularizerFirst_rhs (n : ℕ) (i : Fin 4) (ν : ℝ)
    (u : SobolevSpace period 1) (f : SobolevSpace period 0) :
    ν • laplacianEvaluation period 2 (by
        norm_num) (regularizerFirst period n i (truncateOperator period 0 u)) +
      value period (regularizerFirst period n i f) =
      value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (heatRegularizer period 0 n (truncateOperator period 0 u)) +
          restrictOperator period (by norm_num : 1 ≤ 3) (heatRegularizer period 0 n f))) := by
  rw [regularizerFirst_laplacian period n i (truncateOperator period 0 u),
    regularizerFirst_source period n i f]
  exact (value_derivative_smul_add period i ν _ _).symm

/-- Every genuine spatial heat regularization of the actual mild solution satisfies the first-word
heat equation used in maximal regularity. -/
theorem regularizedState_first_time_derivative (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r)))
    (n : ℕ) (t : ℝ) (ht : t ∈ Ioo 0 T) (i : Fin 4) :
    HasDerivAt (fun s => value period (derivativeOperator period 2 i
      (extendPath T hT (regularizedState period T n u) s)))
      (value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (extendPath T hT (regularizedState period T n u) t) +
          extendPath T hT (regularizedForcing period T n f) t))) t := by
  have hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period 1 => f p.1) :=
    f.continuous.comp continuous_fst
  have hd := viscous_mild_block_hasDerivAt period (by norm_num : 2 ≤ 2)
    (regularizerFirst period n i) (regularizerFirst_heat period n i) ν hν T hT u₀
    (fun t _ => f t) hF u hsol t ht
  have hd' := hd.congr_deriv (regularizerFirst_rhs period n i ν (u ⟨t, ht.1.le, ht.2.le⟩) (f ⟨t,
      ht.1.le, ht.2.le⟩))
  change HasDerivAt _ (value period (derivativeOperator period 0 i
    (ν • laplacianOperator period 1 (heatRegularizer period 0 n (truncateOperator period 0 (u
        (projIcc 0 T hT t)))) +
      restrictOperator period (by
          norm_num : 1 ≤ 3) (heatRegularizer period 0 n (f (projIcc 0 T hT t)))))) t
  rw [projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩]
  exact hd'

end EulerRegularizedMildEquation
