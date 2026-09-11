/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyTime
public import LeanPool.NavierStokesAndEuler.Euler.RegularizedMetricPaths
public import LeanPool.NavierStokesAndEuler.Euler.TransportL2Time
public import LeanPool.NavierStokesAndEuler.Euler.SobolevMetricTransport
public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction
public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
public import LeanPool.NavierStokesAndEuler.Euler.WeightedCylinderEnergy
import LeanPool.NavierStokesAndEuler.Euler.PDESubintervalEnergyLimit
import LeanPool.NavierStokesAndEuler.Euler.TimeLpSubinterval
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricEnergyEvolution
import LeanPool.NavierStokesAndEuler.Euler.WeightedRootLimit
import LeanPool.NavierStokesAndEuler.Euler.SobolevViscousEnergy
import Mathlib.Algebra.Order.Star.Real

/-! Related estimates used together by the same construction modules. -/

section

/-! The constructed higher nonlinear source and pressure restrict exactly to the actual lower mild
equation. -/

@[expose] public section

noncomputable section

namespace EulerCorrectionEnergyRestriction

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerCorrectionOperators
      EulerSobolevTransport
  EulerCorrectionEnergyTime EulerCorrectionLowerData EulerTimeCorrectionSource
      EulerSobolevWordValueIdentity
  EulerTimeLp EulerVolterraConvolution EulerRegularizedTopBlocks
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual higher raw nonlinear time field restricts to the actual continuous source of the
lower equation. -/
theorem rawTime_restriction {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 + q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e)) Filter.atTop
        (𝓝 U)) :
    (fun t => truncateOperator period q (rawTime period (by
        omega : 6 ≤ q+1) T hT D e U t)) =ᵐ[timeMeasure T]
      extendPath T hT (rawPath period hq (lowerData period D KG KL KQ hG hL hQ) e) := by
  have h := rawSourceTime_restriction period hq T hT (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    D.linear D.quadratic KL KQ D.approximation D.residual e (reindexMaximalTime period q T U)
    (reindexMaximalTime_restriction period T hT e U hU)
  filter_upwards [h] with t ht
  exact ht.trans (rawPath_lower period hq D KG KL KQ hG hL hQ e (projIcc 0 T hT t)).symm

/-- The actual full-order projected time forcing restricts to the literal lower mild source without
a source-regularity premise. -/
theorem sourceTime_restriction {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 + q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e)) Filter.atTop
        (𝓝 U)) :
    (fun t => truncateOperator period q (sourceTime period (by
        omega : 6 ≤ q+1) T hT D e U t)) =ᵐ[timeMeasure T]
      extendPath T hT (forcingPath period hq (lowerData period D KG KL KQ hG hL hQ) e) :=
  projectedTime_restriction period T hT D.metric KG D.κ D.direction D.coercivity D.coercivity_pos
      D.metric_pos
    (rawTime period (by omega : 6 ≤ q+1) T hT D e U)
    (extendPath T hT (rawPath period hq (lowerData period D KG KL KQ hG hL hQ) e))
    (rawTime_restriction period hq T hT D KG KL KQ hG hL hQ e U hU)

/-- The actual full-order signed pressure restricts exactly to the continuous pressure in the lower
correction equation. -/
theorem signedPressureTime_restriction {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 + q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e)) Filter.atTop
        (𝓝 U)) :
    (fun t => truncateOperator period q (signedPressureTime period (by
        omega : 6 ≤ q+1) T hT D e U t)) =ᵐ[timeMeasure T]
      extendPath T hT (pressurePath period hq (lowerData period D KG KL KQ hG hL hQ) e) :=
  pressureTime_restriction period T hT D.metric KG D.κ D.direction D.coercivity D.coercivity_pos
      D.metric_pos
    (rawTime period (by omega : 6 ≤ q+1) T hT D e U)
    (extendPath T hT (rawPath period hq (lowerData period D KG KL KQ hG hL hQ) e))
    (rawTime_restriction period hq T hT D KG KL KQ hG hL hQ e U hU)

end EulerCorrectionEnergyRestriction

end
end

end

section

/-! Full energy-order signed Gevrey bounds from genuine viscous mild solutions with continuous
scalar coefficient majorants. -/

section

/-! Actual finite-Sobolev viscous PDE energy with continuous scalar majorants, requiring no
measurability of coefficient-bound witnesses. -/

@[expose] public section

noncomputable section

namespace EulerWeightedSobolevMajorant

open MeasureTheory Set Real InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace
      EulerMetricEnergyEvolution
  EulerMetricHeatEnergy EulerFiniteMetricEnergy EulerCylinderViscousEnergy EulerWeightedRootLimit
  EulerPacketWeights EulerWeightedEnergy EulerWeightedCylinderEnergy EulerSobolevMetricTransport
  EulerSobolevViscousEnergy
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Continuous scalar majorants give the finite Gevrey integral inequality directly from the actual
viscous PDE.
The signed radius term is retained exactly, and no differentiability of the unregularized norm is
assumed. -/
theorem weighted_sobolev_energy_majorized {α β : Type*} [Fintype α] [Fintype β] {q : ℕ} (hq : 3 ≤ q)
    (order : α → ℕ) (ρ ρ' : ℝ → ℝ)
    (κ : ℝ) (m : Vector3) (K G : ℝ → SmoothCoefficient period)
    (e : α → β → ℝ → SobolevSpace period 2) (e' p forcing : α → β → ℝ → LiftL2 period)
    (z : ℝ → SobolevSpace period q)
    (s t c ν : ℝ) (K' : ℝ → LiftL2 period →L[ℝ] LiftL2 period) (B : ℝ → ℝ≥0) (growth multiplier : ℝ
        → ℝ)
    (hst : s ≤ t) (hc : 0 < c) (hν : 0 ≤ ν)
    (hgrowth : ∀ u ∈ Ioo s t, viscousGrowthCoefficient period (K u) (K' u) κ m c ν (B u) ≤ growth u)
    (hmultiplier : ∀ u ∈ Ioo s t, ((K u).bound : ℝ) / c ≤ multiplier u)
    (hρc : ContinuousOn ρ (Icc s t)) (hρpos : ∀ u ∈ Icc s t, 0 < ρ u)
    (hρd : ∀ u ∈ Ioo s t, HasDerivAt ρ (ρ' u) u)
    (hKc : ContinuousOn (fun u => (K u).operator) (Icc s t))
    (hec : ∀ i j, ContinuousOn (fun u => value period (e i j u)) (Icc s t))
    (hKt : ∀ u ∈ Ioo s t, HasDerivAt (fun v => (K v).operator) (K' u) u)
    (het : ∀ i j u, u ∈ Ioo s t → HasDerivAt (fun v => value period (e i j v)) (e' i j u) u)
    (hsym : ∀ u ∈ Ioo s t, ∀ x v w,
      ⟪(K u).coefficient x v, w⟫_ℝ = ⟪v, (K u).coefficient x w⟫_ℝ)
    (hpos : ∀ u ∈ Icc s t, ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪(K u).coefficient x v, v⟫_ℝ)
    (hKG : ∀ u ∈ Ioo s t, ∀ x v, (K u).coefficient x ((G u).coefficient x v) = v)
    (hediv : ∀ i j u, u ∈ Ioo s t → value period (e i j u) ∈ divergenceFreeSpace period κ m)
    (hp : ∀ i j u, u ∈ Ioo s t → p i j u ∈ gradientSpace period κ m)
    (hz : ∀ u ∈ Ioo s t, value period (z u) ∈ divergenceFreeSpace period κ m)
    (hzB : ∀ u ∈ Ioo s t, ∀ᵐ x ∂liftMeasure period, ‖value period (z u) x‖ ≤ B u)
    (heq : ∀ i j u, u ∈ Ioo s t → e' i j u +
      transportOperator period hq κ m (z u) (restrictOperator period (by
          norm_num : 1 ≤ 2) (e i j u)) +
        (G u).operator (p i j u) = forcing i j u + ν • jetLaplacian period (toJet period (e i j u)))
    (hAint : ∀ i, IntegrableOn (fun u => weight (ρ u) (order i) *
        growth u +
      (ρ' u / ρ u) * (order i : ℝ) * weight (ρ u) (order i)) (Icc s t))
    (hFint : ∀ i, IntegrableOn (fun u => weight (ρ u) (order i) *
      (multiplier u * familyNorm (fun j => forcing i j u))) (Icc s t)) :
    weightedMetricSum (ρ t) order (K t).operator (fun i j => value period (e i j t)) -
      weightedMetricSum (ρ s) order (K s).operator (fun i j => value period (e i j s)) ≤
      ∫ u in s..t,
        growth u *
          weightedMetricSum (ρ u) order (K u).operator (fun i j => value period (e i j u)) +
        (ρ' u / ρ u) * weightedMetricLoss (ρ u) order (K u).operator (fun i j => value period (e i
            j u)) +
        multiplier u * weightedForcingSum (ρ u) order (fun i j => forcing i j u) := by
  let Q := fun i u => familyEnergy (K u).operator (fun j => value period (e i j u))
  let a := fun u => growth u
  let F := fun i u => multiplier u * familyNorm (fun j => forcing i j u)
  let w := fun i u => weight (ρ u) (order i)
  let w' := fun i u => (ρ' u / ρ u) * (order i : ℝ) * weight (ρ u) (order i)
  let A := fun i u => w i u * a u + w' i u
  let Ψ := fun i u => A i u * √(Q i u) + w i u * F i u
  have hQ (i : α) : ContinuousOn (Q i) (Icc s t) :=
    continuousOn_finsetSum Finset.univ (fun j _ => (hKc.clm_apply (hec i j)).inner (hec i j))
  have hQ0 (i : α) (u : ℝ) (hu : u ∈ Icc s t) : 0 ≤ Q i u := by
    have hcoer : ∀ v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪(K u).operator v, v⟫_ℝ :=
      coefficientOperator_coercive (K u).coefficient (K u).measurable (K u).bound
        (K u).norm_bound (c ^ 2) (hpos u hu)
    exact (mul_nonneg (sq_nonneg c) (familySquaredNorm_nonneg _)).trans
      (familyEnergy_coercive (K u).operator (fun j => value period (e i j u)) c hcoer)
  have hregd (i : α) (δ : ℝ) (hδ : 0 < δ) (u : ℝ) (hu : u ∈ Ioo s t) :
      DifferentiableAt ℝ (fun v => √(Q i v + δ ^ 2)) u := by
    have hsymL : ∀ v w, ⟪(K u).operator v, w⟫_ℝ = ⟪v, (K u).operator w⟫_ℝ :=
      coefficientOperator_inner_swap (K u).coefficient (K u).measurable
        (K u).bound (K u).norm_bound (hsym u hu)
    have hd : HasDerivAt (Q i) (∑ j, (⟪K' u (value period (e i j u)), value period (e i j u)⟫_ℝ +
        2 * ⟪(K u).operator (value period (e i j u)), e' i j u⟫_ℝ)) u :=
      HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
        metric_energy_hasDerivAt (fun v => (K v).operator) (fun v => value period (e i j v)) u (K'
            u) (e' i j u)
          (hKt u hu) (het i j u hu) hsymL)
    have hq := hQ0 i u ⟨hu.1.le, hu.2.le⟩
    exact (HasDerivAt.sqrt (hd.add_const (δ ^ 2)) (by
        nlinarith : Q i u + δ ^ 2 ≠ 0)).differentiableAt
  have hreg (i : α) (δ : ℝ) (hδ : 0 < δ) (u : ℝ) (hu : u ∈ Ioo s t) :
      deriv (fun v => √(Q i v + δ ^ 2)) u ≤ a u * √(Q i u + δ ^ 2) + F i u := by
    have h := finite_sobolev_viscous_energy period hq κ m K (G u) (e i) u δ c ν (K' u)
      (fun j => e' i j u) (fun j => p i j u) (fun j => forcing i j u) (z u)
      hδ hc hν (hKt u hu) (fun j => het i j u hu)
      (hsym u hu) (hpos u ⟨hu.1.le, hu.2.le⟩) (hKG u hu) (fun j => hediv i j u hu)
      (fun j => hp i j u hu) (hz u hu) (B u) (hzB u hu) (fun j => heq i j u hu)
    exact h.trans (add_le_add
      (mul_le_mul_of_nonneg_right (hgrowth u hu) (sqrt_nonneg _))
      (mul_le_mul_of_nonneg_right (hmultiplier u hu) (familyNorm_nonneg _)))
  have hi (i : α) : w i t * √(Q i t) - w i s * √(Q i s) ≤ ∫ u in s..t, Ψ i u := by
    apply weighted_root_integral_of_deriv_bound (Q i) a (F i) (w i) (w' i) s t
      hst (hQ i) (hQ0 i) ?_ ?_ ?_ (hregd i) (hreg i) (hAint i) (hFint i)
    · exact (hρc.pow (order i)).div_const (((order i).factorial : ℝ) ^ 2)
    · intro u hu
      exact (weight_pos (hρpos u ⟨hu.1.le, hu.2.le⟩) (order i)).le
    · intro u hu
      exact weight_hasDerivAt ρ (ρ' u) u (hρd u hu) (hρpos u ⟨hu.1.le, hu.2.le⟩) (order i)
  have hΨ (i : α) : IntervalIntegrable (Ψ i) volume s t := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr
    exact ((hAint i).mul_continuousOn (hQ i).sqrt isCompact_Icc).add (hFint i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset α)) => hi i)
  rw [Finset.sum_sub_distrib] at hsum
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hΨ i)] at hsum
  have halg (u : ℝ) : (∑ i, Ψ i u) =
      a u * weightedMetricSum (ρ u) order (K u).operator (fun i j => value period (e i j u)) +
      (ρ' u / ρ u) * weightedMetricLoss (ρ u) order (K u).operator (fun i j => value period (e i j
          u)) +
      multiplier u * weightedForcingSum (ρ u) order (fun i j => forcing i j u) := by
    simp only [Ψ, A, w, w', F, Q, weightedMetricSum, weightedMetricLoss, weightedForcingSum,
      familyMetricNorm, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  simpa only [halg, w, Q, a, weightedMetricSum, familyMetricNorm] using hsum

end EulerWeightedSobolevMajorant

end
end

end

section

/-! Actual PDE energy passage with continuous scalar majorants on every time subinterval. -/

@[expose] public section

noncomputable section

namespace EulerPDEMajorantLimit

open MeasureTheory Set Real InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerMetricHeatEnergy EulerFiniteMetricEnergy
  EulerWeightedSobolevMajorant EulerWeightedCylinderEnergy EulerSobolevMetricTransport
  EulerVolterraConvolution EulerTimeLp  EulerPacketWeights EulerTimeLpSubinterval
  EulerPDESubintervalEnergyLimit
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual smooth-in-time finite-Sobolev PDE approximations imply the limiting signed integral
energy bound.
The premises include their literal PDEs and strong convergence, never an assumed energy inequality.
-/
theorem weighted_pde_majorized_subinterval_limit {α β : Type*} [Fintype α] [Fintype β] {q : ℕ} (hq
    : 3 ≤ q)
    (T : ℝ) (hT : 0 ≤ T) (s t : ℝ) (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (order : α → ℕ) (a b d
        : C(Icc (0 : ℝ) T, ℝ)) (ρ ρ' : ℝ → ℝ)
    (κ : ℝ) (m : Vector3) (K G : ℝ → SmoothCoefficient period)
    (e : ℕ → α → β → ℝ → SobolevSpace period 2)
    (e' p forcing : ℕ → α → β → ℝ → LiftL2 period) (z : ℝ → SobolevSpace period q)
    (c ν : ℝ) (K' : ℝ → LiftL2 period →L[ℝ] LiftL2 period) (B : ℝ → NNReal)
    (hc : 0 < c) (hν : 0 ≤ ν)
    (hρc : ContinuousOn ρ (Icc 0 T)) (hρpos : ∀ r ∈ Icc 0 T, 0 < ρ r)
    (hρd : ∀ r ∈ Ioo 0 T, HasDerivAt ρ (ρ' r) r)
    (hKc : ContinuousOn (fun r => (K r).operator) (Icc 0 T))
    (hec : ∀ n i j, ContinuousOn (fun r => value period (e n i j r)) (Icc 0 T))
    (hKt : ∀ r ∈ Ioo 0 T, HasDerivAt (fun v => (K v).operator) (K' r) r)
    (het : ∀ n i j r, r ∈ Ioo 0 T → HasDerivAt (fun v => value period (e n i j v)) (e' n i j r) r)
    (hsym : ∀ r ∈ Ioo 0 T, ∀ x v w, ⟪(K r).coefficient x v, w⟫_ℝ = ⟪v, (K r).coefficient x w⟫_ℝ)
    (hpos : ∀ r ∈ Icc 0 T, ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪(K r).coefficient x v, v⟫_ℝ)
    (hKG : ∀ r ∈ Ioo 0 T, ∀ x v, (K r).coefficient x ((G r).coefficient x v) = v)
    (hediv : ∀ n i j r, r ∈ Ioo 0 T → value period (e n i j r) ∈ divergenceFreeSpace period κ m)
    (hp : ∀ n i j r, r ∈ Ioo 0 T → p n i j r ∈ gradientSpace period κ m)
    (hz : ∀ r ∈ Ioo 0 T, value period (z r) ∈ divergenceFreeSpace period κ m)
    (hzB : ∀ r ∈ Ioo 0 T, ∀ᵐ x ∂liftMeasure period, ‖value period (z r) x‖ ≤ B r)
    (heq : ∀ n i j r, r ∈ Ioo 0 T → e' n i j r +
      transportOperator period hq κ m (z r) (restrictOperator period (by
          norm_num : 1 ≤ 2) (e n i j r)) +
        (G r).operator (p n i j r) = forcing n i j r + ν • jetLaplacian period (toJet period (e n i
            j r)))
    (hAint : ∀ i, IntegrableOn (fun r => weight (ρ r) (order i) * extendPath T hT a r +
      (ρ' r / ρ r) * (order i : ℝ) * weight (ρ r) (order i)) (Icc 0 T))
    (hFint : ∀ n i, IntegrableOn (fun r => weight (ρ r) (order i) *
      (extendPath T hT d r * familyNorm (fun j => forcing n i j r))) (Icc 0 T))
    (ha : ∀ r ∈ Icc 0 T, viscousGrowthCoefficient period (K r) (K' r) κ m c ν (B r) ≤ extendPath T
        hT a r)
    (hb : ∀ r ∈ Icc 0 T, ρ' r / ρ r = extendPath T hT b r)
    (hd : ∀ r ∈ Icc 0 T, ((K r).bound : ℝ) / c ≤ extendPath T hT d r)
    (X Y Z : ℕ → C(Icc (0 : ℝ) T, ℝ))
    (hXdef : ∀ n r, r ∈ Icc 0 T → weightedMetricSum (ρ r) order (K r).operator
      (fun i j => value period (e n i j r)) = extendPath T hT (X n) r)
    (hYdef : ∀ n r, r ∈ Icc 0 T → weightedMetricLoss (ρ r) order (K r).operator
      (fun i j => value period (e n i j r)) = extendPath T hT (Y n) r)
    (hZdef : ∀ n r, r ∈ Icc 0 T → weightedForcingSum (ρ r) order
      (fun i j => forcing n i j r) = extendPath T hT (Z n) r)
    (x y : C(Icc (0 : ℝ) T, ℝ)) (f : TimeLp T ℝ)
    (hX : Filter.Tendsto X Filter.atTop (𝓝 x)) (hY : Filter.Tendsto Y Filter.atTop (𝓝 y))
    (hZ : Filter.Tendsto (fun n => pathLp T hT (Z n)) Filter.atTop (𝓝 f)) :
    x ⟨t, h0s.trans hst, htT⟩ - x ⟨s, h0s, hst.trans htT⟩ ≤
      (∫ r in s..t, extendPath T hT a r * extendPath T hT x r) +
      (∫ r in s..t, extendPath T hT b r * extendPath T hT y r) +
      ∫ r in Icc s t, pathLp T hT d r * f r ∂timeMeasure T := by
  have hsub : Icc s t ⊆ Icc (0 : ℝ) T := fun _ hr => ⟨h0s.trans hr.1, hr.2.trans htT⟩
  have hsubo : Ioo s t ⊆ Ioo (0 : ℝ) T := fun _ hr => ⟨lt_of_le_of_lt h0s hr.1, lt_of_lt_of_le hr.2
      htT⟩
  apply integral_energy_subinterval_limit T hT s t h0s hst htT a b (pathLp T hT d)
    X Y (fun n => pathLp T hT (Z n)) x y f hX hY hZ
  intro n
  have h := weighted_sobolev_energy_majorized period hq order ρ ρ' κ m K G
    (e n) (e' n) (p n) (forcing n) z s t c ν K' B (extendPath T hT a) (extendPath T hT d) hst hc hν
    (fun r hr => ha r (hsub ⟨hr.1.le,hr.2.le⟩)) (fun r hr => hd r (hsub ⟨hr.1.le,hr.2.le⟩))
    (hρc.mono hsub) (fun r hr => hρpos r (hsub hr)) (fun r hr => hρd r (hsubo hr))
    (hKc.mono hsub) (fun i j => (hec n i j).mono hsub) (fun r hr => hKt r (hsubo hr))
    (fun i j r hr => het n i j r (hsubo hr)) (fun r hr => hsym r (hsubo hr))
    (fun r hr => hpos r (hsub hr)) (fun r hr => hKG r (hsubo hr))
    (fun i j r hr => hediv n i j r (hsubo hr)) (fun i j r hr => hp n i j r (hsubo hr))
    (fun r hr => hz r (hsubo hr)) (fun r hr => hzB r (hsubo hr))
    (fun i j r hr => heq n i j r (hsubo hr))
    (fun i => (hAint i).mono_set hsub) (fun i => (hFint n i).mono_set hsub)
  rw [hXdef n t ⟨h0s.trans hst, htT⟩, hXdef n s ⟨h0s, hst.trans htT⟩] at h
  have hevalt : extendPath T hT (X n) t = X n ⟨t, h0s.trans hst, htT⟩ :=
    congrArg (X n) (projIcc_of_mem hT ⟨h0s.trans hst, htT⟩)
  have hevals : extendPath T hT (X n) s = X n ⟨s, h0s, hst.trans htT⟩ :=
    congrArg (X n) (projIcc_of_mem hT ⟨h0s, hst.trans htT⟩)
  rw [hevalt, hevals] at h
  have hi := integral_eq_three_subinterval_paths T hT s t hst a b d (X n) (Y n) (Z n)
    (fun r => extendPath T hT a r *
      weightedMetricSum (ρ r) order (K r).operator (fun i j => value period (e n i j r)) +
      (ρ' r / ρ r) * weightedMetricLoss (ρ r) order (K r).operator (fun i j => value period (e n i
          j r)) +
      extendPath T hT d r * weightedForcingSum (ρ r) order (fun i j => forcing n i j r))
    (fun r hr => by
        rw [hb r (hsub hr), hXdef n r (hsub hr), hYdef n r (hsub hr), hZdef n r (hsub hr)])
  rw [hi] at h
  rw [← subinterval_inner_eq, subinterval_path_inner T hT s t h0s hst htT]
  exact h

end EulerPDEMajorantLimit

end
end

end

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

end
end

end
