/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevMetricTransport
public import LeanPool.NavierStokesAndEuler.Euler.CylinderViscousEnergy
public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction
import Mathlib.Algebra.Order.Star.Real

/-! Finite-family viscous metric energy for actual finite Sobolev solutions. -/

@[expose] public section


noncomputable section

namespace EulerSobolevViscousEnergy

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace
  EulerMetricHeatEnergy EulerFiniteMetricEnergy EulerCylinderViscousEnergy
      EulerSobolevMetricTransport
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine finite-word viscous metric estimate for H² fields and an Hq advecting velocity, q≥3.
No classical smooth representative of the evolving fields is required. -/
theorem finite_sobolev_viscous_energy {ι : Type*} [Fintype ι] {q : ℕ} (hq : 3 ≤ q)
    (κ : ℝ) (m : Vector3) (K : ℝ → SmoothCoefficient period) (G : SmoothCoefficient period)
    (e : ι → ℝ → SobolevSpace period 2) (t δ c ν : ℝ)
    (K' : LiftL2 period →L[ℝ] LiftL2 period)
    (e' p forcing : ι → LiftL2 period) (z : SobolevSpace period q)
    (hδ : 0 < δ) (hc : 0 < c) (hν : 0 ≤ ν)
    (hKt : HasDerivAt (fun s => (K s).operator) K' t)
    (het : ∀ i, HasDerivAt (fun s => value period (e i s)) (e' i) t)
    (hsym : ∀ x v w, ⟪(K t).coefficient x v, w⟫_ℝ = ⟪v, (K t).coefficient x w⟫_ℝ)
    (hpos : ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪(K t).coefficient x v, v⟫_ℝ)
    (hKG : ∀ x v, (K t).coefficient x (G.coefficient x v) = v)
    (hediv : ∀ i, value period (e i t) ∈ divergenceFreeSpace period κ m)
    (hp : ∀ i, p i ∈ gradientSpace period κ m)
    (hz : value period z ∈ divergenceFreeSpace period κ m) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖value period z x‖ ≤ B)
    (heq : ∀ i, e' i + transportOperator period hq κ m z (restrictOperator period (by
        norm_num : 1 ≤ 2) (e i t)) +
      G.operator (p i) = forcing i + ν • jetLaplacian period (toJet period (e i t))) :
    deriv (fun s => √(familyEnergy (K s).operator (fun i => value period (e i s)) + δ ^ 2)) t ≤
      ((‖K'‖ + 2 * transportEnergyConstant period (K t) κ m B +
          2 * ν * heatEnergyConstant period (K t) c) / (2 * c ^ 2)) *
        √(familyEnergy (K t).operator (fun i => value period (e i t)) + δ ^ 2) +
      (((K t).bound : ℝ) / c) * familyNorm forcing := by
  let β := transportEnergyConstant period (K t) κ m B
  let C := heatEnergyConstant period (K t) c
  have hβ : 0 ≤ β := by dsimp [β, transportEnergyConstant]; positivity
  have hC : 0 ≤ C := by dsimp [C, heatEnergyConstant]; positivity
  have hcoer : ∀ u, c ^ 2 * ‖u‖ ^ 2 ≤ ⟪(K t).operator u, u⟫_ℝ :=
    coefficientOperator_coercive (K t).coefficient (K t).measurable
      (K t).bound (K t).norm_bound (c ^ 2) hpos
  have hsymL : ∀ v w, ⟪(K t).operator v, w⟫_ℝ = ⟪v, (K t).operator w⟫_ℝ :=
    coefficientOperator_inner_swap (K t).coefficient (K t).measurable
      (K t).bound (K t).norm_bound hsym
  have hpL (i : ι) : ⟪(K t).operator (value period (e i t)), G.operator (p i)⟫_ℝ = 0 :=
    metric_pressure_cancellation period κ m (K t).coefficient G.coefficient
      (K t).measurable G.measurable (K t).bound G.bound (K t).norm_bound G.norm_bound
      hsym hKG (hediv i) (hp i)
  have htL (i : ι) : |⟪(K t).operator (value period (e i t)),
      transportOperator period hq κ m z (restrictOperator period (by
          norm_num : 1 ≤ 2) (e i t))⟫_ℝ| ≤
      β * ‖value period (e i t)‖ ^ 2 :=
    metric_transport_bound period hq κ m (K t) z (restrictOperator period (by
        norm_num : 1 ≤ 2) (e i t))
      hsym hz B hzB
  have hheat (i : ι) : ⟪(K t).operator (value period (e i t)), jetLaplacian period (toJet period (e
      i t))⟫_ℝ ≤
      C * ‖value period (e i t)‖ ^ 2 := by
    have h := metric_heat_bound period (K t) (value period (e i t)) (toJet period (e i t)) c hc hpos
    have hd : 0 ≤ ∑ j : Fin 4, ‖(toJet period (e i t)).word (fun _ : Fin 1 => j)‖ ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    dsimp [C, heatEnergyConstant]
    nlinarith [sq_nonneg c]
  have h := family_regularized_energy_evolution (fun s => (K s).operator) (fun i s => value period
      (e i s))
    t δ c β C ν K' e'
    (fun i => transportOperator period hq κ m z (restrictOperator period (by
        norm_num : 1 ≤ 2) (e i t)))
    (fun i => G.operator (p i)) forcing (fun i => jetLaplacian period (toJet period (e i t)))
    hδ hc hβ hC hν hcoer hKt het hsymL heq hpL htL hheat
  have hop : ‖(K t).operator‖ ≤ (K t).bound :=
    coefficientOperator_norm_le (K t).coefficient (K t).measurable (K t).bound (K t).norm_bound
  exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hop hc.le) (familyNorm_nonneg forcing)) _)

end EulerSobolevViscousEnergy
