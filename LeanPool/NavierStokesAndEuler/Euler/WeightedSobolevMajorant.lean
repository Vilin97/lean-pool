/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevMetricTransport
public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction
public import LeanPool.NavierStokesAndEuler.Euler.WeightedCylinderEnergy
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricEnergyEvolution
import LeanPool.NavierStokesAndEuler.Euler.Foundations.WeightedEnergy
import LeanPool.NavierStokesAndEuler.Euler.SobolevViscousEnergy
import LeanPool.NavierStokesAndEuler.Euler.WeightedRootLimit
import Mathlib.Algebra.Order.Star.Real

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
