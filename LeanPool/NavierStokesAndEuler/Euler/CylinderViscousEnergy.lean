/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FiniteMetricEnergy

@[expose] public section

/-! Finite-word viscous energy for the actual lifted transport and projected-pressure equation. -/

noncomputable section

namespace EulerCylinderViscousEnergy

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerMetricTransport EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerMetricHeatEnergy EulerFiniteMetricEnergy
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The exact coefficient left after absorbing half the variable-metric heat dissipation. -/
def heatEnergyConstant (K : SmoothCoefficient period) (c : ℝ) : ℝ :=
  2 * (K.firstBound : ℝ) ^ 2 / c ^ 2

/-- The actual transport metric correction for a bounded lifted velocity. -/
def transportEnergyConstant (K : SmoothCoefficient period) (κ : ℝ) (m : Vector3) (B : ℝ≥0) : ℝ :=
  (1 / 2 : ℝ) * K.firstBound * ((|κ| + ‖m‖) * B)

/-- The regularized root of a finite sum of actual cylinder word energies obeys the viscous estimate. -/
theorem finite_cylinder_viscous_energy {ι : Type*} [Fintype ι]
    (κ : ℝ) (m : Vector3) (K : ℝ → SmoothCoefficient period) (G : SmoothCoefficient period)
    (e : ι → ℝ → LiftL2 period) (t δ c ν : ℝ)
    (K' : LiftL2 period →L[ℝ] LiftL2 period)
    (e' p forcing : ι → LiftL2 period) (z : LiftL2 period)
    (J : ∀ i, SpatialJet period standardDirection 2 (e i t))
    (g : ι → LiftDomain period → Vector3)
    (hrep : ∀ i, (e i t : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g i)
    (hg : ∀ i x, ContDiff ℝ ∞ (localFieldLift period (g i) x))
    (hDg : ∀ i, MemLp (fun x => fderiv ℝ (localFieldLift period (g i) x) 0)
      2 (liftMeasure period))
    (hδ : 0 < δ) (hc : 0 < c) (hν : 0 ≤ ν)
    (hKt : HasDerivAt (fun s => (K s).operator) K' t)
    (het : ∀ i, HasDerivAt (e i) (e' i) t)
    (hsym : ∀ x v w, ⟪(K t).coefficient x v, w⟫_ℝ = ⟪v, (K t).coefficient x w⟫_ℝ)
    (hpos : ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪(K t).coefficient x v, v⟫_ℝ)
    (hKG : ∀ x v, (K t).coefficient x (G.coefficient x v) = v)
    (hediv : ∀ i, e i t ∈ divergenceFreeSpace period κ m)
    (hp : ∀ i, p i ∈ gradientSpace period κ m)
    (hz : z ∈ divergenceFreeSpace period κ m) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B)
    (heq : ∀ i, e' i + EulerRepresentativeMetricEvolution.liftedTransport period κ m
        (g i) z (hDg i) B hzB + G.operator (p i) = forcing i + ν • jetLaplacian period (J i)) :
    deriv (fun s => √(familyEnergy (K s).operator (fun i => e i s) + δ ^ 2)) t ≤
      ((‖K'‖ + 2 * transportEnergyConstant period (K t) κ m B +
          2 * ν * heatEnergyConstant period (K t) c) / (2 * c ^ 2)) *
        √(familyEnergy (K t).operator (fun i => e i t) + δ ^ 2) +
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
  have hpL (i : ι) : ⟪(K t).operator (e i t), G.operator (p i)⟫_ℝ = 0 :=
    metric_pressure_cancellation period κ m (K t).coefficient G.coefficient
      (K t).measurable G.measurable (K t).bound G.bound (K t).norm_bound G.norm_bound
      hsym hKG (hediv i) (hp i)
  have htL (i : ι) : |⟪(K t).operator (e i t),
      EulerRepresentativeMetricEvolution.liftedTransport period κ m (g i) z (hDg i) B hzB⟫_ℝ| ≤
      β * ‖e i t‖ ^ 2 :=
    EulerRepresentativeMetricEvolution.metric_transport_inner_bound period κ m (K t).coefficient
      (K t).measurable (e i t) (g i) z (hrep i) (K t).smooth (hg i) (hDg i) hsym hz
      (K t).bound (K t).firstBound B (K t).norm_bound (K t).norm_first hzB
  have hheat (i : ι) : ⟪(K t).operator (e i t), jetLaplacian period (J i)⟫_ℝ ≤ C * ‖e i t‖ ^ 2 := by
    have h := metric_heat_bound period (K t) (e i t) (J i) c hc hpos
    have hd : 0 ≤ ∑ j : Fin 4, ‖(J i).word (fun _ : Fin 1 => j)‖ ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    dsimp [C, heatEnergyConstant]
    nlinarith [sq_nonneg c]
  have h := family_regularized_energy_evolution (fun s => (K s).operator) e t δ c β C ν K' e'
    (fun i => EulerRepresentativeMetricEvolution.liftedTransport period κ m (g i) z (hDg i) B hzB)
    (fun i => G.operator (p i)) forcing (fun i => jetLaplacian period (J i))
    hδ hc hβ hC hν hcoer hKt het hsymL heq hpL htL hheat
  have hop : ‖(K t).operator‖ ≤ (K t).bound :=
    coefficientOperator_norm_le (K t).coefficient (K t).measurable (K t).bound (K t).norm_bound
  exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hop hc.le) (familyNorm_nonneg forcing)) _)

end EulerCylinderViscousEnergy
