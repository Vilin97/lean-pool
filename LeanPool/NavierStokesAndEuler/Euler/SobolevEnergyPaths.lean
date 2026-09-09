/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MetricPathConvergence
public import LeanPool.NavierStokesAndEuler.Euler.WeightedForcingTime
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpPairing
public import LeanPool.NavierStokesAndEuler.Euler.SobolevViscousEnergy

@[expose] public section

/-! Genuine continuous energy paths and their weighted strong limits. -/

noncomputable section

namespace EulerSobolevEnergyPaths

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerMetricPathConvergence EulerWeightedForcingTime EulerTimeLpPairing EulerTimeLp
  EulerVolterraConvolution EulerPacketWeights EulerWeightedCylinderEnergy EulerFiniteMetricEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Underlying L² values of a finite actual Sobolev family form a bounded linear map. -/
def familyValueOperator (q : ℕ) {I : Type*} :
    (I → SobolevSpace period q) →L[ℝ] (I → LiftL2 period) :=
  ContinuousLinearMap.pi (fun i => (valueOperator period q).comp (ContinuousLinearMap.proj i))

/-- The genuine L² field-family path underlying an actual Sobolev family path. -/
def familyValuePath (q : ℕ) {I : Type*} (T : ℝ)
    (u : C(Icc (0 : ℝ) T, I → SobolevSpace period q)) : C(Icc (0 : ℝ) T, I → LiftL2 period) :=
  (familyValueOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T) u

/-- Family-path values are the literal underlying L² values of the Sobolev fields. -/
theorem familyValuePath_apply (q : ℕ) {I : Type*} (T : ℝ)
    (u : C(Icc (0 : ℝ) T, I → SobolevSpace period q)) (t : Icc (0 : ℝ) T) (i : I) :
    familyValuePath period q T u t i = value period (u t i) := rfl

omit [Fact (0 < period)] in
/-- The actual factorial Gevrey weight along a continuous radius path. -/
def gevreyWeightPath (T : ℝ) (ρ : C(Icc (0 : ℝ) T, ℝ)) (n : ℕ) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t => weight (ρ t) n, (ρ.continuous.pow n).div_const ((n.factorial : ℝ)^2)⟩

omit [Fact (0 < period)] in
/-- The actual radius-loss weight along the same radius path. -/
def gevreyLossWeightPath (T : ℝ) (ρ : C(Icc (0 : ℝ) T, ℝ)) (n : ℕ) : C(Icc (0 : ℝ) T, ℝ) :=
  (n : ℝ) • gevreyWeightPath T ρ n

/-- A continuous-path weighted forcing integral is exactly its genuine Bochner forcing pairing. -/
theorem forcing_integral_eq {A I : Type*} [Fintype A] [Fintype I]
    (T : ℝ) (hT : 0 ≤ T) (c : C(Icc (0 : ℝ) T, ℝ))
    (w : A → C(Icc (0 : ℝ) T, ℝ)) (F : A → C(Icc (0 : ℝ) T, I → LiftL2 period)) :
    (∫ t, pathLp T hT c t * weightedForcingTime T hT w (fun i => pathLp T hT (F i)) t ∂timeMeasure
      T) =
      ∫ t in (0 : ℝ)..T, extendPath T hT c t * extendPath T hT (weightedForcingPath T w F) t := by
  rw [weightedForcingTime_pathLp, ← inner_eq_integral, path_inner_eq_integral]

/-- Finite actual weighted metric energy passes through uniform field limits and strong L² forcing limits, preserving the signed radius-loss integral. -/
theorem weighted_energy_limit {A I : Type*} [Fintype A] [Fintype I]
    (T : ℝ) (hT : 0 ≤ T) (w loss : A → C(Icc (0 : ℝ) T, ℝ))
    (K : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (a b c : C(Icc (0 : ℝ) T, ℝ))
    (E : ℕ → A → C(Icc (0 : ℝ) T, I → LiftL2 period))
    (F : ℕ → A → C(Icc (0 : ℝ) T, I → LiftL2 period))
    (e : A → C(Icc (0 : ℝ) T, I → LiftL2 period)) (f : A → TimeLp T (I → LiftL2 period))
    (hE : ∀ i, Filter.Tendsto (fun n => E n i) Filter.atTop (𝓝 (e i)))
    (hF : ∀ i, Filter.Tendsto (fun n => pathLp T hT (F n i)) Filter.atTop (𝓝 (f i)))
    (henergy : ∀ n, weightedMetricPath T w K (E n) ⟨T, hT, le_rfl⟩ -
      weightedMetricPath T w K (E n) ⟨0, le_rfl, hT⟩ ≤
      (∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT (weightedMetricPath T w K (E n)) t)
        +
      (∫ t in (0 : ℝ)..T, extendPath T hT b t * extendPath T hT (weightedMetricPath T loss K (E n))
        t) +
      ∫ t in (0 : ℝ)..T, extendPath T hT c t * extendPath T hT (weightedForcingPath T w (F n)) t) :
    weightedMetricPath T w K e ⟨T, hT, le_rfl⟩ - weightedMetricPath T w K e ⟨0, le_rfl, hT⟩ ≤
      (∫ t in (0 : ℝ)..T, extendPath T hT a t * extendPath T hT (weightedMetricPath T w K e) t) +
      (∫ t in (0 : ℝ)..T, extendPath T hT b t * extendPath T hT (weightedMetricPath T loss K e) t) +
      ∫ t, pathLp T hT c t * weightedForcingTime T hT w f t ∂timeMeasure T := by
  apply integral_energy_limit T hT a b (pathLp T hT c)
    (fun n => weightedMetricPath T w K (E n)) (fun n => weightedMetricPath T loss K (E n))
    (fun n => weightedForcingTime T hT w (fun i => pathLp T hT (F n i)))
    (weightedMetricPath T w K e) (weightedMetricPath T loss K e) (weightedForcingTime T hT w f)
    (weightedMetricPath_tendsto T w K E e hE) (weightedMetricPath_tendsto T loss K E e hE)
    (weightedForcingTime_tendsto T hT w (fun n i => pathLp T hT (F n i)) f hF)
  intro n
  rw [forcing_integral_eq period]
  exact henergy n

end EulerSobolevEnergyPaths
