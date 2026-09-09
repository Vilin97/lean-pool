/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.RegularizedMetricPaths
public import LeanPool.NavierStokesAndEuler.Euler.TransportL2Time
import LeanPool.NavierStokesAndEuler.Euler.PDEMajorantLimit

/-! Full energy-order signed Gevrey bounds from genuine viscous mild solutions with continuous
scalar coefficient majorants. -/

@[expose] public section


noncomputable section

namespace EulerMildMajorantEnergy

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerCylinderSobolevSpace EulerSobolevHeat EulerMetricHeatEnergy EulerFiniteMetricEnergy
  EulerSobolevMetricTransport  EulerWeightedCylinderEnergy
  EulerRegularizedWordEquation EulerRegularizedWordTime EulerRegularizedForcingWord
  EulerRegularizedEnergyFamily EulerRegularizedMetricPaths EulerRegularizedTopBlocks
  EulerTransportL2Time EulerMetricPathConvergence EulerWeightedForcingTime EulerSobolevEnergyPaths
  EulerTimeLp EulerVolterraConvolution EulerPDEMajorantLimit EulerPacketWeights
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every full-order finite Gevrey word family of an actual viscous mild solution obeys the signed
integral estimate with continuous scalar majorants on every subinterval.
The derivative and forcing limits are obtained from actual heat regularization; no energy inequality
or differentiability of a zero norm is assumed. -/
theorem mild_majorized_energy_subinterval {α β : Type*} [Fintype α] [Fintype β] {q : ℕ} (hq : 3 ≤
    q + 1)
    (T : ℝ) (hT : 0 ≤ T) (s t : ℝ) (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4) (hw : ∀ i j, d i j ≤ q + 1) (order : α → ℕ)
    (ν : ℝ) (hν : 0 < ν) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (R Rdot : C(Icc (0 : ℝ) T, ℝ)) (hR : ∀ r, 0 < R r)
    (hRd : ∀ r ∈ Ioo 0 T, HasDerivAt (extendPath T hT R) (extendPath T hT Rdot r) r)
    (K G : Icc (0 : ℝ) T → SmoothCoefficient period)
    (hK : Continuous (fun r => (K r).operator)) (hG : Continuous (fun r => (G r).operator))
    (Kdot : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (hKd : ∀ r ∈ Ioo 0 T, HasDerivAt (extendPath T hT (metricOperatorPath period T K hK))
      (extendPath T hT Kdot r) r)
    (hKsym : ∀ r x v v', ⟪(K r).coefficient x v, v'⟫_ℝ = ⟪v, (K r).coefficient x v'⟫_ℝ)
    (hKpos : ∀ r x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪(K r).coefficient x v, v⟫_ℝ)
    (hKG : ∀ r x v, (K r).coefficient x ((G r).coefficient x v) = v)
    (B : Icc (0 : ℝ) T → NNReal)
    (z u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (u₀ : SobolevSpace period (q + 1)) (f p : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (hsol : ∀ r : Icc (0 : ℝ) T, u r = heatOperator period (q+1) (2*ν*r.val).toNNReal u₀ +
      ∫ v in (0 : ℝ)..r.val, heatKernel period q ν hν v (extendPath T hT f (r.val-v)))
    (hu : ∀ r, value period (u r) ∈ divergenceFreeSpace period κ m)
    (hp : ∀ r, value period (p r) ∈ gradientSpace period κ m)
    (hz : ∀ r, value period (z r) ∈ divergenceFreeSpace period κ m)
    (hzB : ∀ r, ∀ᵐ x ∂liftMeasure period, ‖value period (z r) x‖ ≤ B r)
    (U : TimeLp T (SobolevSpace period (2+q))) (F P : TimeLp T (SobolevSpace period (q+1)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop
        (𝓝 U))
    (hF : (fun r => truncateOperator period q (F r)) =ᵐ[timeMeasure T] extendPath T hT f)
    (hP : (fun r => truncateOperator period q (P r)) =ᵐ[timeMeasure T] extendPath T hT p)
    (a b k : C(Icc (0 : ℝ) T, ℝ))
    (ha : ∀ r, viscousGrowthCoefficient period (K r) (Kdot r) κ m c ν (B r) ≤ a r)
    (hb : ∀ r, Rdot r / R r = b r) (hk : ∀ r, ((K r).bound : ℝ) / c ≤ k r) :
    let A := transportL2Path period hq κ m T z
    let Kp := metricOperatorPath period T K hK
    let Gp := metricOperatorPath period T G hG
    let weights := fun i => gevreyWeightPath T R (order i)
    let x := weightedMetricPath T weights Kp (energyValueFamily period d w hw T u)
    let y := weightedMetricPath T (fun i => gevreyLossWeightPath T R (order i)) Kp
      (energyValueFamily period d w hw T u)
    let Z := weightedForcingTime T hT weights (forcingFamilyTime period d w hw T hT A Gp U F P)
    x ⟨t,h0s.trans hst,htT⟩ - x ⟨s,h0s,hst.trans htT⟩ ≤
      (∫ r in s..t, extendPath T hT a r * extendPath T hT x r) +
      (∫ r in s..t, extendPath T hT b r * extendPath T hT y r) +
      ∫ r in Icc s t, pathLp T hT k r * Z r ∂timeMeasure T := by
  let A := transportL2Path period hq κ m T z
  let Kp := metricOperatorPath period T K hK
  let Gp := metricOperatorPath period T G hG
  let weights := fun i => gevreyWeightPath T R (order i)
  let losses := fun i => gevreyLossWeightPath T R (order i)
  let E := fun n i j r => extendPath T hT (regularizedWordPath period (hw i j) n (w i j) T u) r
  let Q := fun n i j r => extendPath T hT (sourceWordPath period (hw i j) n (w i j) T p) r
  let H := fun n i j r => extendPath T hT (forcingWordPath period (hw i j) n (w i j) T A Gp u f p) r
  let Edot := fun n i j r => ν • jetLaplacian period (toJet period (E n i j r)) +
    extendPath T hT (sourceWordPath period (hw i j) n (w i j) T f) r
  let X := fun n => weightedMetricPath T weights Kp (regularizedValueFamily period d w hw n T u)
  let Y := fun n => weightedMetricPath T losses Kp (regularizedValueFamily period d w hw n T u)
  let Z := fun n => weightedForcingPath T weights (regularizedForcingFamily period d w hw n T A Gp
      u f p)
  have hAc (i : α) : IntegrableOn (fun r => weight (extendPath T hT R r) (order i) * extendPath T
      hT a r +
      (extendPath T hT Rdot r / extendPath T hT R r) * (order i : ℝ) * weight (extendPath T hT R r)
          (order i)) (Icc 0 T) := by
    have he : (fun r => weight (extendPath T hT R r) (order i) * extendPath T hT a r +
        (extendPath T hT Rdot r / extendPath T hT R r) * (order i : ℝ) * weight (extendPath T hT R
            r) (order i)) =
        (fun r => extendPath T hT (weights i) r * extendPath T hT a r +
          extendPath T hT b r * (order i : ℝ) * extendPath T hT (weights i) r) := by
      funext r
      change weight (R (projIcc 0 T hT r)) (order i) * a (projIcc 0 T hT r) +
        (Rdot (projIcc 0 T hT r) / R (projIcc 0 T hT r)) * (order i : ℝ) * weight (R (projIcc 0 T
            hT r)) (order i) = _
      rw [hb]
      rfl
    rw [he]
    exact coefficient_path_integrable T hT (weights i) a b (order i)
  have hFc (n : ℕ) (i : α) : IntegrableOn (fun r => weight (extendPath T hT R r) (order i) *
      (extendPath T hT k r * familyNorm (fun j => H n i j r))) (Icc 0 T) :=
    forcing_path_integrable period T hT (weights i) k (regularizedForcingFamily period d w hw n T A
        Gp u f p i)
  apply weighted_pde_majorized_subinterval_limit period hq T hT s t h0s hst htT order a b k
    (extendPath T hT R) (extendPath T hT Rdot) κ m
    (fun r => K (projIcc 0 T hT r)) (fun r => G (projIcc 0 T hT r)) E Edot Q H (extendPath T hT z)
    c ν (extendPath T hT Kdot) (fun r => B (projIcc 0 T hT r)) hc hν.le
    (extendPath_continuous T hT R).continuousOn (fun r _ => hR (projIcc 0 T hT r)) hRd
    (extendPath_continuous T hT Kp).continuousOn
    (fun n i j => ((valueOperator period 2).continuous.comp
      (extendPath_continuous T hT (regularizedWordPath period (hw i j) n (w i j) T
          u))).continuousOn)
    hKd (fun n i j r hr => regularized_word_hasDerivAt_clamped period (hw i j) n (w i j) ν hν T hT
        u₀ f u hsol r hr)
    (fun r _ => hKsym (projIcc 0 T hT r)) (fun r _ => hKpos (projIcc 0 T hT r))
    (fun r _ => hKG (projIcc 0 T hT r))
    (fun n i j r _ => regularized_word_divergenceFree period (hw i j) n (w i j) κ m
      (u (projIcc 0 T hT r)) (hu (projIcc 0 T hT r)))
    (fun n i j r _ => regularizedWordBlock_gradient period (hw i j) n (w i j) κ m
      (p (projIcc 0 T hT r)) (hp (projIcc 0 T hT r)))
    (fun r _ => hz (projIcc 0 T hT r)) (fun r _ => hzB (projIcc 0 T hT r))
    ?_ hAc hFc (fun r _ => ha (projIcc 0 T hT r))
    (fun r _ => hb (projIcc 0 T hT r)) (fun r _ => hk (projIcc 0 T hT r)) X Y Z
    (fun n r _ => regularized_metric_path_eq period d w hw n T hT order R K hK u r)
    (fun n r _ => regularized_loss_path_eq period d w hw n T hT order R K hK u r)
    (fun n r _ => regularized_forcing_path_eq period d w hw n T hT order R A Gp u f p r)
    _ _ _
    (weightedMetricPath_tendsto T weights Kp _ _ (regularizedValueFamily_tendsto period d w hw T u))
    (weightedMetricPath_tendsto T losses Kp _ _ (regularizedValueFamily_tendsto period d w hw T u))
    (regularizedWeightedForcing_tendsto period d w hw T hT weights A Gp u f p U F P hU hF hP)
  intro n i j r _
  have h := forcingWordPath_equation period (hw i j) n (w i j) T ν A Gp u f p (projIcc 0 T hT r)
  rw [transportL2Path_apply] at h
  exact h

end EulerMildMajorantEnergy
